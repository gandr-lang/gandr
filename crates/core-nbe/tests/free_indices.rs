//! Every core former reads the free indices its binding structure states.
//!
//! Each row builds one former, or a few side by side in a tuple or a lazy
//! product, with variables placed in every child it has. The expected
//! indices are written out from the former's binding rule alone: a child
//! under `n` binders reads its index `k` as `k - n` when `k >= n` and binds it
//! otherwise. A type reaches the walk through a quote, and a code through a
//! decode, so a variable inside a type is placed in the code an element type
//! decodes.

use alloc::boxed::Box;
use alloc::collections::BTreeMap;
use alloc::string::String;
use alloc::sync::Arc;
use alloc::vec::Vec;

use gandr_core_nbe::CoreTerm;
use gandr_core_nbe::FreeIndices;
use gandr_core_term::CompTypeId;
use gandr_core_term::ComponentCount;
use gandr_core_term::ComputationId;
use gandr_core_term::CoreArena;
use gandr_core_term::Sort;
use gandr_core_term::ValueId;
use gandr_core_term::ValueTypeId;
use gandr_core_term::Zone;
use gandr_core_term::control::EffectClause;
use gandr_core_term::control::StackFrame;
use gandr_core_term::effect::EffectName;
use gandr_core_term::effect::EffectOp;
use gandr_core_term::effect::EffectRow;
use gandr_core_term::effect::EffectSig;
use gandr_core_term::effect::capability::CapabilityGrade;
use gandr_core_term::effect::capability::Region;
use gandr_core_term::hole::HoleId;
use gandr_core_term::hole::MarkIndex;
use gandr_core_term::memory::AccessMode;
use gandr_core_term::memory::HoldGrade;
use gandr_core_term::memory::MemoryForm;
use gandr_core_term::memory::Place;
use gandr_core_term::primitive::Arguments;
use gandr_core_term::primitive::PRELUDE;
use gandr_core_term::primitive::Primitive;
use gandr_core_term::session::PayloadCount;
use gandr_core_term::session::PayloadSlot;
use gandr_core_term::session::Protocol;
use gandr_core_term::session::ProtocolState;
use gandr_core_term::session::ProtocolSyntax;
use gandr_core_term::session::RecordedMove;
use gandr_core_term::session::SessionAction;
use gandr_core_term::session::SessionRelation;
use gandr_core_term::session::SessionType;
use gandr_core_term::ua::Description;
use gandr_core_term::ua::Sides;
use gandr_core_term::ua::Stratum;
use gandr_core_term::world::World;
use gandr_core_term::world::WorldForm;
use gandr_core_term::world::WorldType;
use gandr_kernel_strata::Level;
use gandr_kernel_term::BaseType;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::ConstructorTag;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::FieldLabel;
use gandr_kernel_term::FixpointEvidence;
use gandr_kernel_term::GroundSort;
use gandr_kernel_term::PathEvidence;
use gandr_kernel_term::Stage;
use gandr_kernel_term::StageId;
use gandr_kernel_term::Summand;

/// A de Bruijn index a row places.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
struct Index(u32);

/// A prelude row's name.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
struct Row(&'static str);

/// A record label.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
struct Label(&'static str);

/// One former, and the free indices its binding structure states.
struct Former
{
    /// The former, as the row writes it.
    what: &'static str,
    /// Builds the former in an empty arena.
    build: fn(&mut CoreArena) -> CoreTerm,
    /// Its free intuitionistic indices, ascending.
    intuitionistic: &'static [u32],
    /// Its free linear indices, ascending.
    linear: &'static [u32],
    /// The linear indices it consumes, ascending.
    consumed: &'static [u32],
}

/// The intuitionistic variable at `at`.
///
/// # Specification
/// trivial.
fn x(
    core: &mut CoreArena,
    at: Index,
) -> ValueId
{
    core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(at.0))
}

/// The tuple of the intuitionistic variables at `at`, in order.
///
/// # Specification
/// trivial.
fn tuple_of(
    core: &mut CoreArena,
    at: &[Index],
) -> ValueId
{
    let mut components = Vec::with_capacity(at.len());
    for &index in at {
        components.push(x(core, index));
    }
    core.value_tuple(&components)
}

/// `return (x_at…)`.
///
/// # Specification
/// trivial.
fn returning(
    core: &mut CoreArena,
    at: &[Index],
) -> ComputationId
{
    let tuple = tuple_of(core, at);
    core.computation_return(tuple)
}

/// The type the code `x_at` decodes to, which reads `at`.
///
/// # Specification
/// trivial.
fn decoded(
    core: &mut CoreArena,
    at: Index,
) -> ValueTypeId
{
    let code = x(core, at);
    core.value_type_element(code, Level::zero())
}

/// The computation type returning the type `x_at` decodes to.
///
/// # Specification
/// trivial.
fn returns_decoded(
    core: &mut CoreArena,
    at: Index,
) -> CompTypeId
{
    let result = decoded(core, at);
    core.comp_type_returner(result)
}

/// The interface `Proc`, its one operation `exit` taking the type `x_at`
/// decodes to and answering the unit.
///
/// # Specification
/// trivial.
fn proc_reading(
    core: &mut CoreArena,
    at: Index,
) -> EffectSig
{
    let payload = decoded(core, at);
    let reply = core.value_type_unit();
    EffectSig::new(EffectName::from("Proc"), [EffectOp {
        name: "exit".into(),
        payload,
        reply,
    }])
    .expect("one operation is a signature")
}

/// The interface `Proc`, its one operation `exit` taking and answering the
/// unit.
///
/// # Specification
/// trivial.
fn proc(core: &mut CoreArena) -> EffectSig
{
    let unit = core.value_type_unit();
    EffectSig::new(EffectName::from("Proc"), [EffectOp {
        name: "exit".into(),
        payload: unit,
        reply: unit,
    }])
    .expect("one operation is a signature")
}

/// The session type that sends one `payload` and ends.
///
/// # Specification
/// trivial.
fn sending(
    core: &mut CoreArena,
    payload: ValueTypeId,
) -> ValueTypeId
{
    let protocol = Protocol::new(
        Vec::from([
            ProtocolSyntax::Send {
                payload: PayloadSlot::from(0_usize),
                next: ProtocolState::from(1_usize),
            },
            ProtocolSyntax::End,
        ]),
        ProtocolState::from(0_usize),
        PayloadCount::from(1_usize),
    )
    .expect("a send, then the end");
    let session = SessionType::new(Arc::new(protocol), Arc::from([payload]))
        .expect("one payload for one slot");
    core.value_type_session(session)
}

/// The label `name`.
///
/// # Specification
/// trivial.
fn label(name: Label) -> FieldLabel
{
    FieldLabel::from(String::from(name.0))
}

/// The prelude's row `name`.
///
/// # Specification
/// trivial.
fn prelude(name: Row) -> Primitive
{
    *PRELUDE
        .iter()
        .find(|row| row.name().as_ref() == name.0)
        .expect("the prelude holds the row")
}

/// The tuple of `values`, as a term.
///
/// # Specification
/// trivial.
fn beside(
    core: &mut CoreArena,
    values: &[ValueId],
) -> CoreTerm
{
    CoreTerm::Value(core.value_tuple(values))
}

/// The lazy product of `components`, as a term.
///
/// # Specification
/// trivial.
fn alongside(
    core: &mut CoreArena,
    components: &[ComputationId],
) -> CoreTerm
{
    CoreTerm::Computation(core.computation_with(components))
}

/// The value formers.
///
/// # Specification
/// trivial.
fn values() -> [Former; 18]
{
    [
        Former {
            what: "(x0, x2)",
            build: |a| CoreTerm::Value(tuple_of(a, &[Index(0), Index(2)])),
            intuitionistic: &[0, 2],
            linear: &[],
            consumed: &[],
        },
        Former {
            what: "inr x1",
            build: |a| {
                let body = x(a, Index(1));
                CoreTerm::Value(a.value_injection(Summand::from(1_usize), body))
            },
            intuitionistic: &[1],
            linear: &[],
            consumed: &[],
        },
        Former {
            what: "{a = x3, b = x0}",
            build: |a| {
                let (first, second) = (x(a, Index(3)), x(a, Index(0)));
                let fields =
                    BTreeMap::from([(label(Label("a")), first), (label(Label("b")), second)]);
                CoreTerm::Value(a.value_record(fields))
            },
            intuitionistic: &[0, 3],
            linear: &[],
            consumed: &[],
        },
        Former {
            what: "K(x1) : D(x4)",
            build: |a| {
                let argument = x(a, Index(4));
                let datatype =
                    a.value_type_data(ConstantIndex::from(0_usize), Vec::from([argument]));
                let field = x(a, Index(1));
                CoreTerm::Value(a.value_constructor(
                    datatype,
                    ConstructorTag::from(0_usize),
                    Vec::from([field]),
                ))
            },
            intuitionistic: &[1, 4],
            linear: &[],
            consumed: &[],
        },
        Former {
            what: "x0 :: x1",
            build: |a| {
                let (head, tail) = (x(a, Index(0)), x(a, Index(1)));
                CoreTerm::Value(a.value_list_cons(head, tail))
            },
            intuitionistic: &[0, 1],
            linear: &[],
            consumed: &[],
        },
        Former {
            what: "static λ. (x0, x2)",
            build: |a| {
                let body = tuple_of(a, &[Index(0), Index(2)]);
                CoreTerm::Value(a.value_static_lambda(body))
            },
            intuitionistic: &[1],
            linear: &[],
            consumed: &[],
        },
        Former {
            what: "x1 x0, statically",
            build: |a| {
                let (head, argument) = (x(a, Index(1)), x(a, Index(0)));
                CoreTerm::Value(a.value_static_application(head, argument))
            },
            intuitionistic: &[0, 1],
            linear: &[],
            consumed: &[],
        },
        Former {
            what: "lift x2, and a mark on x1",
            build: |a| {
                let lifted = x(a, Index(2));
                let lifted = a.value_lift(Level::zero(), lifted);
                let marked = x(a, Index(1));
                let marked = a.value_mark(MarkIndex::from(0_u32), marked);
                beside(a, &[lifted, marked])
            },
            intuitionistic: &[1, 2],
            linear: &[],
            consumed: &[],
        },
        Former {
            what: "refl x0, here x1, stay x2, forward x3",
            build: |a| {
                let points = [Index(0), Index(1), Index(2), Index(3)].map(|at| x(a, at));
                let [refl, here, stay, forward] = points;
                let paths = [
                    a.value_path_refl(refl),
                    a.value_here(here),
                    a.value_stay(stay),
                    a.value_forward(forward),
                ];
                beside(a, &paths)
            },
            intuitionistic: &[0, 1, 2, 3],
            linear: &[],
            consumed: &[],
        },
        Former {
            what: "x0 × x1, funext x2 x3, equiv x4 x5, univalence x6 x7",
            build: |a| {
                let ends = [0, 1, 2, 3, 4, 5, 6, 7].map(|at| x(a, Index(at)));
                let [p0, p1, p2, p3, p4, p5, p6, p7] = ends;
                let paths = [
                    a.value_path_product(p0, p1),
                    a.value_funext(p2, p3),
                    a.value_equiv(p4, p5),
                    a.value_univalence(p6, p7),
                ];
                beside(a, &paths)
            },
            intuitionistic: &[0, 1, 2, 3, 4, 5, 6, 7],
            linear: &[],
            consumed: &[],
        },
        Former {
            what: "x0 then x1, x2 × x3, x4 → x5, x6 ≤ x7",
            build: |a| {
                let ends = [0, 1, 2, 3, 4, 5, 6, 7].map(|at| x(a, Index(at)));
                let [f0, f1, f2, f3, f4, f5, f6, f7] = ends;
                let flows = [
                    a.value_then(f0, f1),
                    a.value_flow_product(f2, f3),
                    a.value_function_flow(f4, f5),
                    a.value_session_related(SessionRelation::Subtyping, f6, f7),
                ];
                beside(a, &flows)
            },
            intuitionistic: &[0, 1, 2, 3, 4, 5, 6, 7],
            linear: &[],
            consumed: &[],
        },
        Former {
            what: "equiv(x0, x1) : x4 = x4 over the type x3 decodes",
            build: |a| {
                let carrier = decoded(a, Index(3));
                let end = x(a, Index(4));
                let path_type = a.value_type_path(carrier, end, end);
                let (forward, backward) = (x(a, Index(0)), x(a, Index(1)));
                let evidence = Arc::new(PathEvidence {
                    source: Vec::new(),
                    target: Vec::new(),
                });
                CoreTerm::Value(a.value_path_equiv(path_type, forward, backward, evidence))
            },
            intuitionistic: &[0, 1, 3, 4],
            linear: &[],
            consumed: &[],
        },
        Former {
            what: "ua(x0, x2)",
            build: |a| {
                let empty = || Description {
                    name: From::from("Point"),
                    generators: Box::from([]),
                };
                let sides = Arc::new(Sides {
                    source: empty(),
                    target: empty(),
                });
                let stratum = Stratum {
                    degree: From::from(1_usize),
                    bound: From::from(4_usize),
                };
                let (forward, backward) = (x(a, Index(0)), x(a, Index(2)));
                CoreTerm::Value(a.value_ua(stratum, sides, forward, backward))
            },
            intuitionistic: &[0, 2],
            linear: &[],
            consumed: &[],
        },
        Former {
            what: "returned, nested, run and thunked returns of x0 … x3",
            build: |a| {
                let bodies = [0, 1, 2, 3].map(|at| returning(a, &[Index(at)]));
                let [returned, nested, run, thunked] = bodies;
                let suspended = [
                    a.value_returned(returned),
                    a.value_nested(nested),
                    a.value_run(run),
                    a.value_thunk(thunked),
                ];
                beside(a, &suspended)
            },
            intuitionistic: &[0, 1, 2, 3],
            linear: &[],
            consumed: &[],
        },
        Former {
            what: "recorded [sent x1, selected a, received x2, offered a, closed]",
            build: |a| {
                let (sent, received) = (x(a, Index(1)), x(a, Index(2)));
                CoreTerm::Value(a.value_recorded(Arc::from([
                    RecordedMove::Sent(sent),
                    RecordedMove::Selected(label(Label("a"))),
                    RecordedMove::Received(received),
                    RecordedMove::Offered(label(Label("a"))),
                    RecordedMove::Closed,
                ])))
            },
            intuitionistic: &[1, 2],
            linear: &[],
            consumed: &[],
        },
        Former {
            what: "reify [apply x1; bind y. return (y, x3); project 0]",
            build: |a| {
                let applied = x(a, Index(1));
                let bound = returning(a, &[Index(0), Index(3)]);
                CoreTerm::Value(a.value_reify(Arc::from([
                    StackFrame::Apply(applied),
                    StackFrame::Bind(bound),
                    StackFrame::Project(gandr_core_term::Component::from(0_usize)),
                ])))
            },
            intuitionistic: &[1, 2],
            linear: &[],
            consumed: &[],
        },
        Former {
            what: "a constant, the unit, nil and a hole",
            build: |a| {
                let leaves = [
                    a.value_constant(ConstantIndex::from(0_usize)),
                    a.value_unit(),
                    a.value_list_nil(),
                    a.value_hole(HoleId::from(0_u32)),
                ];
                beside(a, &leaves)
            },
            intuitionistic: &[],
            linear: &[],
            consumed: &[],
        },
        Former {
            what: "the linear variable 2",
            build: |a| CoreTerm::Value(a.value_variable(Zone::Linear, DeBruijnIndex::from(2_u32))),
            intuitionistic: &[],
            linear: &[2],
            consumed: &[],
        },
    ]
}

/// The quoted type formers.
///
/// # Specification
/// trivial.
fn types() -> [Former; 12]
{
    [
        Former {
            what: "type(D(x0))",
            build: |a| {
                let argument = x(a, Index(0));
                let ty = a.value_type_data(ConstantIndex::from(0_usize), Vec::from([argument]));
                CoreTerm::Value(a.value_quote(ty))
            },
            intuitionistic: &[0],
            linear: &[],
            consumed: &[],
        },
        Former {
            what: "type({a : El x1, b : ()})",
            build: |a| {
                let first = decoded(a, Index(1));
                let second = a.value_type_unit();
                let fields =
                    BTreeMap::from([(label(Label("a")), first), (label(Label("b")), second)]);
                let ty = a.value_type_record(fields);
                CoreTerm::Value(a.value_quote(ty))
            },
            intuitionistic: &[1],
            linear: &[],
            consumed: &[],
        },
        Former {
            what: "type(stack(↑El x0, ↑El x1))",
            build: |a| {
                let (input, output) = (returns_decoded(a, Index(0)), returns_decoded(a, Index(1)));
                let ty = a.value_type_stack(input, output);
                CoreTerm::Value(a.value_quote(ty))
            },
            intuitionistic: &[0, 1],
            linear: &[],
            consumed: &[],
        },
        Former {
            what: "types: list El x2, staged El x3, kept El x4",
            build: |a| {
                let elements = [2, 3, 4].map(|at| decoded(a, Index(at)));
                let [listed, staged, kept] = elements;
                let types = [
                    a.value_type_list(listed),
                    a.value_type_staged(staged, Stage::At(StageId::from(0_usize))),
                    a.value_type_kept(kept, Region::Held),
                ];
                let quotes = types.map(|ty| a.value_quote(ty));
                beside(a, &quotes)
            },
            intuitionistic: &[2, 3, 4],
            linear: &[],
            consumed: &[],
        },
        Former {
            what: "types: El x1 at the host, the capability to reach it",
            build: |a| {
                let inner = decoded(a, Index(1));
                let types = [
                    a.value_type_world(WorldType::At {
                        inner,
                        world: World::Host,
                    }),
                    a.value_type_world(WorldType::Capability(World::Host)),
                ];
                let quotes = types.map(|ty| a.value_quote(ty));
                beside(a, &quotes)
            },
            intuitionistic: &[1],
            linear: &[],
            consumed: &[],
        },
        Former {
            what: "types: x0 ≃ x1, x3 = x4 in El x2, a flow x6 ~> x7 in El x5",
            build: |a| {
                let ends = [0, 1, 3, 4, 6, 7].map(|at| x(a, Index(at)));
                let [u0, u1, p3, p4, f6, f7] = ends;
                let (path_carrier, flow_carrier) = (decoded(a, Index(2)), decoded(a, Index(5)));
                let types = [
                    a.value_type_path_universe(u0, u1),
                    a.value_type_path(path_carrier, p3, p4),
                    a.value_type_flow(flow_carrier, f6, f7),
                ];
                let quotes = types.map(|ty| a.value_quote(ty));
                beside(a, &quotes)
            },
            intuitionistic: &[0, 1, 2, 3, 4, 5, 6, 7],
            linear: &[],
            consumed: &[],
        },
        Former {
            what: "types: run x1, El x0 × El x2, El x3 + (), !El x4. end",
            build: |a| {
                let session = x(a, Index(1));
                let parts = [0, 2, 3, 4].map(|at| decoded(a, Index(at)));
                let [first, second, summand, payload] = parts;
                let unit = a.value_type_unit();
                let types = [
                    a.value_type_run(session),
                    a.value_type_product(&[first, second]),
                    a.value_type_sum(&[summand, unit]),
                    sending(a, payload),
                ];
                let quotes = types.map(|ty| a.value_quote(ty));
                beside(a, &quotes)
            },
            intuitionistic: &[0, 1, 2, 3, 4],
            linear: &[],
            consumed: &[],
        },
        Former {
            what: "closed types: Integer, a universe, an abstract type, unknown, buffer",
            build: |a| {
                let types = [
                    a.value_type_base(BaseType::Integer),
                    a.value_type_universe(Sort::Ground(GroundSort::Value), Level::zero()),
                    a.value_type_abstract(ConstantIndex::from(0_usize)),
                    a.value_type_unknown(),
                    a.value_type_buffer(),
                ];
                let quotes = types.map(|ty| a.value_quote(ty));
                beside(a, &quotes)
            },
            intuitionistic: &[],
            linear: &[],
            consumed: &[],
        },
        Former {
            what: "type(cap Proc(El x1))",
            build: |a| {
                let signature = proc_reading(a, Index(1));
                let ty = a.value_type_capability(
                    EffectRow::singleton(signature),
                    CapabilityGrade::Durable,
                    Region::Held,
                );
                CoreTerm::Value(a.value_quote(ty))
            },
            intuitionistic: &[1],
            linear: &[],
            consumed: &[],
        },
        Former {
            what: "types: static El x0 → El x1, Σ (y : El x2). El x4",
            build: |a| {
                let parts = [0, 1, 2, 4].map(|at| decoded(a, Index(at)));
                let [domain, codomain, first, second] = parts;
                let types = [
                    a.value_type_static_pi(domain, codomain),
                    a.value_type_sigma(first, second),
                ];
                let quotes = types.map(|ty| a.value_quote(ty));
                beside(a, &quotes)
            },
            intuitionistic: &[0, 1, 2, 3],
            linear: &[],
            consumed: &[],
        },
        Former {
            what: "types: U ↑El x1, lift El x2, El x3",
            build: |a| {
                let returner = returns_decoded(a, Index(1));
                let lifted = decoded(a, Index(2));
                let types = [
                    a.value_type_thunk(returner),
                    a.value_type_lift(lifted, Level::zero()),
                    decoded(a, Index(3)),
                ];
                let quotes = types.map(|ty| a.value_quote(ty));
                beside(a, &quotes)
            },
            intuitionistic: &[1, 2, 3],
            linear: &[],
            consumed: &[],
        },
        Former {
            what: "computation types: &, ↑ with Proc, →, Π, El, unknown, codata",
            build: |a| {
                let with = [0, 1].map(|at| returns_decoded(a, Index(at)));
                let effectful_result = decoded(a, Index(2));
                let signature = proc_reading(a, Index(3));
                let (arrow_domain, arrow_codomain) =
                    (decoded(a, Index(4)), returns_decoded(a, Index(5)));
                let (pi_domain, pi_codomain) = (decoded(a, Index(6)), returns_decoded(a, Index(8)));
                let element = x(a, Index(9));
                let argument = x(a, Index(10));
                let types = [
                    a.comp_type_with(&with),
                    a.comp_type_returner_with_effects(
                        effectful_result,
                        EffectRow::singleton(signature),
                    ),
                    a.comp_type_arrow(arrow_domain, arrow_codomain),
                    a.comp_type_pi(pi_domain, pi_codomain),
                    a.comp_type_element(element, Level::zero()),
                    a.comp_type_unknown(),
                    a.comp_type_codata(ConstantIndex::from(0_usize), Vec::from([argument])),
                ];
                let quotes = types.map(|ty| a.value_quote_computation(ty));
                beside(a, &quotes)
            },
            intuitionistic: &[0, 1, 2, 3, 4, 5, 6, 7, 9, 10],
            linear: &[],
            consumed: &[],
        },
    ]
}

/// The computation formers.
///
/// # Specification
/// trivial.
fn computations() -> [Former; 27]
{
    [
        Former {
            what: "perform exit(x1) : Proc(El x2)",
            build: |a| {
                let signature = proc_reading(a, Index(2));
                let payload = x(a, Index(1));
                CoreTerm::Computation(a.computation_perform(signature, "exit".into(), payload))
            },
            intuitionistic: &[1, 2],
            linear: &[],
            consumed: &[],
        },
        Former {
            what: "handle { return x0 } with { r ⇒ return (r, x2); exit(p, k) ⇒ return (p, x4) } : Proc(El x5)",
            build: |a| {
                let signature = proc_reading(a, Index(5));
                let subject = returning(a, &[Index(0)]);
                let on_return = returning(a, &[Index(0), Index(2)]);
                let body = returning(a, &[Index(1), Index(4)]);
                CoreTerm::Computation(a.computation_handle(
                    signature,
                    subject,
                    on_return,
                    Arc::from([EffectClause {
                        operation: "exit".into(),
                        body,
                    }]),
                ))
            },
            intuitionistic: &[0, 1, 2, 5],
            linear: &[],
            consumed: &[],
        },
        Former {
            what: "x1.exit(x2)",
            build: |a| {
                let signature = proc(a);
                let (capability, payload) = (x(a, Index(1)), x(a, Index(2)));
                CoreTerm::Computation(a.computation_exercise(
                    capability,
                    signature,
                    "exit".into(),
                    payload,
                ))
            },
            intuitionistic: &[1, 2],
            linear: &[],
            consumed: &[],
        },
        Former {
            what: "handle c { return (c, x1) } with { r ⇒ return x2; exit(p, k) ⇒ return x3 }",
            build: |a| {
                let signature = proc(a);
                let subject = returning(a, &[Index(0), Index(1)]);
                let on_return = returning(a, &[Index(2)]);
                let body = returning(a, &[Index(3)]);
                CoreTerm::Computation(a.computation_scope(
                    signature,
                    subject,
                    on_return,
                    Arc::from([EffectClause {
                        operation: "exit".into(),
                        body,
                    }]),
                ))
            },
            intuitionistic: &[0, 1],
            linear: &[],
            consumed: &[],
        },
        Former {
            what: "resume x1 (return x2)",
            build: |a| {
                let stack = x(a, Index(1));
                let body = returning(a, &[Index(2)]);
                CoreTerm::Computation(a.computation_resume(stack, body))
            },
            intuitionistic: &[1, 2],
            linear: &[],
            consumed: &[],
        },
        Former {
            what: "split x3 as (y, z) in return (y, z, x2)",
            build: |a| {
                let scrutinee = x(a, Index(3));
                let body = returning(a, &[Index(0), Index(1), Index(2)]);
                CoreTerm::Computation(a.computation_split(
                    scrutinee,
                    ComponentCount::from(2_usize),
                    body,
                ))
            },
            intuitionistic: &[0, 3],
            linear: &[],
            consumed: &[],
        },
        Former {
            what: "split x4 as (y, z) at s. ↑El x2 in return x3",
            build: |a| {
                let scrutinee = x(a, Index(4));
                let motive = returns_decoded(a, Index(2));
                let body = returning(a, &[Index(3)]);
                CoreTerm::Computation(a.computation_dependent_split(
                    scrutinee,
                    ComponentCount::from(2_usize),
                    motive,
                    body,
                ))
            },
            intuitionistic: &[1, 4],
            linear: &[],
            consumed: &[],
        },
        Former {
            what: "&(project 1 &(return x0, return x3), reset (return x1))",
            build: |a| {
                let components = [returning(a, &[Index(0)]), returning(a, &[Index(3)])];
                let lazy = a.computation_with(&components);
                let projected =
                    a.computation_project(gandr_core_term::Component::from(1_usize), lazy);
                let reset = returning(a, &[Index(1)]);
                let reset = a.computation_reset(reset);
                alongside(a, &[projected, reset])
            },
            intuitionistic: &[0, 1, 3],
            linear: &[],
            consumed: &[],
        },
        Former {
            what: "return x0 : ↑El x2",
            build: |a| {
                let body = returning(a, &[Index(0)]);
                let ty = returns_decoded(a, Index(2));
                CoreTerm::Computation(a.computation_ascribe(body, ty))
            },
            intuitionistic: &[0, 2],
            linear: &[],
            consumed: &[],
        },
        Former {
            what: "&(shift k. return (k, x2), λy. return (y, x3))",
            build: |a| {
                let shifted = returning(a, &[Index(0), Index(2)]);
                let shifted = a.computation_shift(shifted);
                let abstracted = returning(a, &[Index(0), Index(3)]);
                let abstracted = a.computation_lambda(abstracted);
                alongside(a, &[shifted, abstracted])
            },
            intuitionistic: &[1, 2],
            linear: &[],
            consumed: &[],
        },
        Former {
            what: "fold x0 : list El x5 { nil ⇒ return x1; h, r ⇒ return (h, r, x2, x3) }",
            build: |a| {
                let element = decoded(a, Index(5));
                let result = a.value_type_unit();
                let list = x(a, Index(0));
                let on_nil = returning(a, &[Index(1)]);
                let on_cons = returning(a, &[Index(0), Index(1), Index(2), Index(3)]);
                CoreTerm::Computation(
                    a.computation_list_fold(element, result, list, on_nil, on_cons),
                )
            },
            intuitionistic: &[0, 1, 5],
            linear: &[],
            consumed: &[],
        },
        Former {
            what: "case x2 { nil ⇒ return x0; h :: t ⇒ return (h, x3) }",
            build: |a| {
                let list = x(a, Index(2));
                let on_nil = returning(a, &[Index(0)]);
                let on_cons = returning(a, &[Index(1), Index(3)]);
                CoreTerm::Computation(a.computation_list_case(list, on_nil, on_cons))
            },
            intuitionistic: &[0, 1, 2],
            linear: &[],
            consumed: &[],
        },
        Former {
            what: "&(x0 + x1, neg x2)",
            build: |a| {
                let operands = [x(a, Index(0)), x(a, Index(1))];
                let added =
                    a.computation_primitive(prelude(Row("add")), Arguments::Binary(operands));
                let negated = x(a, Index(2));
                let negated =
                    a.computation_primitive(prelude(Row("neg")), Arguments::Unary(negated));
                alongside(a, &[added, negated])
            },
            intuitionistic: &[0, 1, 2],
            linear: &[],
            consumed: &[],
        },
        Former {
            what: "case x0 at s. ↑El x2 { K ⇒ return x3 }",
            build: |a| {
                let scrutinee = x(a, Index(0));
                let motive = returns_decoded(a, Index(2));
                let branch = returning(a, &[Index(3)]);
                CoreTerm::Computation(a.computation_data_case(
                    scrutinee,
                    motive,
                    Vec::from([branch]),
                    Vec::from([gandr_kernel_term::FieldCount::from(0_usize)]),
                ))
            },
            intuitionistic: &[0, 1, 3],
            linear: &[],
            consumed: &[],
        },
        Former {
            what: "&(x1.a, x2.0)",
            build: |a| {
                let (record, tuple) = (x(a, Index(1)), x(a, Index(2)));
                let projections = [
                    a.computation_record_projection(record, label(Label("a"))),
                    a.computation_tuple_projection(
                        tuple,
                        gandr_kernel_term::Component::from(0_usize),
                    ),
                ];
                alongside(a, &projections)
            },
            intuitionistic: &[1, 2],
            linear: &[],
            consumed: &[],
        },
        Former {
            what: "&(transport x0 x1, transport (y. El x1) x2 x3)",
            build: |a| {
                let (path, operand) = (x(a, Index(0)), x(a, Index(1)));
                let transported = a.computation_transport(path, operand);
                let motive = decoded(a, Index(1));
                let (path, operand) = (x(a, Index(2)), x(a, Index(3)));
                let along = a.computation_path_transport(motive, path, operand);
                alongside(a, &[transported, along])
            },
            intuitionistic: &[0, 1, 2, 3],
            linear: &[],
            consumed: &[],
        },
        Former {
            what: "ride (y. El x2) x0 x4",
            build: |a| {
                let motive = decoded(a, Index(2));
                let (flow, operand) = (x(a, Index(0)), x(a, Index(4)));
                CoreTerm::Computation(a.computation_ride(motive, flow, operand))
            },
            intuitionistic: &[0, 1, 4],
            linear: &[],
            consumed: &[],
        },
        Former {
            what: "transport ↑El x5 along x0 from x1 over x2 of x3",
            build: |a| {
                let motive = returns_decoded(a, Index(5));
                let parts = [0, 1, 2, 3].map(|at| x(a, Index(at)));
                let [path, start, over, operand] = parts;
                CoreTerm::Computation(
                    a.computation_telescope_transport(motive, path, start, over, operand),
                )
            },
            intuitionistic: &[0, 1, 2, 3, 5],
            linear: &[],
            consumed: &[],
        },
        Former {
            what: "&(rec f. return (f, x1), (λy. return x1) x2)",
            build: |a| {
                let recursive = returning(a, &[Index(0), Index(1)]);
                let recursive = a.computation_fixpoint(recursive, FixpointEvidence::Partial);
                let body = returning(a, &[Index(1)]);
                let function = a.computation_lambda(body);
                let argument = x(a, Index(2));
                let applied = a.computation_application(function, argument);
                alongside(a, &[recursive, applied])
            },
            intuitionistic: &[0, 2],
            linear: &[],
            consumed: &[],
        },
        Former {
            what: "&(abandon x1, force x2, hole, a mark on return x3)",
            build: |a| {
                let (stack, thunk) = (x(a, Index(1)), x(a, Index(2)));
                let marked = returning(a, &[Index(3)]);
                let parts = [
                    a.computation_abandon(stack),
                    a.computation_force(thunk),
                    a.computation_hole(HoleId::from(0_u32)),
                    a.computation_mark(MarkIndex::from(0_u32), marked),
                ];
                alongside(a, &parts)
            },
            intuitionistic: &[1, 2, 3],
            linear: &[],
            consumed: &[],
        },
        Former {
            what: "y <- return x0; return (y, x3)",
            build: |a| {
                let bound = returning(a, &[Index(0)]);
                let body = returning(a, &[Index(0), Index(3)]);
                CoreTerm::Computation(a.computation_bind(bound, body))
            },
            intuitionistic: &[0, 2],
            linear: &[],
            consumed: &[],
        },
        Former {
            what: "case x1 { inl y ⇒ return (y, x3); inr y ⇒ return y }",
            build: |a| {
                let scrutinee = x(a, Index(1));
                let branches = [
                    returning(a, &[Index(0), Index(3)]),
                    returning(a, &[Index(0)]),
                ];
                CoreTerm::Computation(a.computation_case(scrutinee, &branches))
            },
            intuitionistic: &[1, 2],
            linear: &[],
            consumed: &[],
        },
        Former {
            what: "send x1 on the endpoint 0",
            build: |a| {
                let payload = x(a, Index(1));
                CoreTerm::Computation(a.computation_session(SessionAction::Send {
                    endpoint: DeBruijnIndex::from(0_u32),
                    payload,
                }))
            },
            intuitionistic: &[1],
            linear: &[0],
            consumed: &[],
        },
        Former {
            what: "&(receive on 3 { close 2 }, select a on 2, offer on 0 { a ⇒ return x1 }, close 1)",
            build: |a| {
                let closed = a.computation_session(SessionAction::Close {
                    endpoint: DeBruijnIndex::from(2_u32),
                });
                let received = a.computation_session(SessionAction::Receive {
                    endpoint: DeBruijnIndex::from(3_u32),
                    body: closed,
                });
                let selected = a.computation_session(SessionAction::Select {
                    endpoint: DeBruijnIndex::from(2_u32),
                    label: label(Label("a")),
                });
                let arm = returning(a, &[Index(1)]);
                let offered = a.computation_session(SessionAction::Offer {
                    endpoint: DeBruijnIndex::from(0_u32),
                    arms: BTreeMap::from([(label(Label("a")), arm)]),
                });
                let closed = a.computation_session(SessionAction::Close {
                    endpoint: DeBruijnIndex::from(1_u32),
                });
                alongside(a, &[received, selected, offered, closed])
            },
            intuitionistic: &[1],
            linear: &[0, 1, 2, 3],
            consumed: &[],
        },
        Former {
            what: "fork (c : !El x2. end) { close c } as d; close 1",
            build: |a| {
                let payload = decoded(a, Index(2));
                let protocol = sending(a, payload);
                let child = a.computation_session(SessionAction::Close {
                    endpoint: DeBruijnIndex::from(0_u32),
                });
                let parent = a.computation_session(SessionAction::Close {
                    endpoint: DeBruijnIndex::from(1_u32),
                });
                CoreTerm::Computation(a.computation_session(SessionAction::Fork {
                    protocol,
                    child,
                    parent,
                }))
            },
            intuitionistic: &[2],
            linear: &[0],
            consumed: &[],
        },
        Former {
            what: "hold h = x0 { access h[x2] as v { resume v x3 } unwind { return x4 } }",
            build: |a| {
                let value = x(a, Index(0));
                let index = x(a, Index(2));
                let written = x(a, Index(3));
                let unwind = returning(a, &[Index(4)]);
                let resumed = a.computation_memory(MemoryForm::Resume {
                    view: DeBruijnIndex::from(0_u32),
                    value: written,
                });
                let access = a.computation_memory(MemoryForm::Access {
                    mode: AccessMode::Exclusive { unwind },
                    held: DeBruijnIndex::from(0_u32),
                    place: Place::At { index },
                    body: resumed,
                });
                CoreTerm::Computation(a.computation_memory(MemoryForm::Hold {
                    value,
                    body: access,
                    grade: HoldGrade::Many,
                }))
            },
            intuitionistic: &[0, 2, 3, 4],
            linear: &[],
            consumed: &[],
        },
        Former {
            what: "&(access shared 1 as v { abort v }, consume 2, world forms on x0 … x3)",
            build: |a| {
                let aborted = a.computation_memory(MemoryForm::Abort {
                    view: DeBruijnIndex::from(0_u32),
                });
                let access = a.computation_memory(MemoryForm::Access {
                    mode: AccessMode::Shared,
                    held: DeBruijnIndex::from(1_u32),
                    place: Place::Whole,
                    body: aborted,
                });
                let consumed = a.computation_memory(MemoryForm::Consume {
                    held: DeBruijnIndex::from(2_u32),
                });
                let held = x(a, Index(1));
                let opened = x(a, Index(0));
                let body = returning(a, &[Index(0), Index(2)]);
                let migrated = returning(a, &[Index(3)]);
                let worlds = [
                    a.computation_world(WorldForm::Hold { value: held }),
                    a.computation_world(WorldForm::Leta {
                        value: opened,
                        body,
                    }),
                    a.computation_world(WorldForm::Migrate {
                        world: World::Host,
                        body: migrated,
                    }),
                ];
                let [hold, leta, migrate] = worlds;
                alongside(a, &[access, consumed, hold, leta, migrate])
            },
            intuitionistic: &[0, 1, 3],
            linear: &[1, 2],
            consumed: &[2],
        },
    ]
}

/// Each former reads the free indices, of each zone, and the consumed slots
/// its binding structure states.
#[test]
fn each_former_reads_the_free_indices_its_binders_leave()
{
    let formers = values().into_iter().chain(types()).chain(computations());
    for Former {
        what,
        build,
        intuitionistic,
        linear,
        consumed,
    } in formers
    {
        let mut core = CoreArena::new();
        let term = build(&mut core);
        let mut free = FreeIndices::default();
        let read = free
            .intuitionistic(&core, term)
            .expect("the former is whole");
        assert!(
            read.iter()
                .copied()
                .eq(intuitionistic.iter().copied().map(DeBruijnIndex::from)),
            "{what}: intuitionistic {read:?}, stated {intuitionistic:?}"
        );
        let read = free.linear(&core, term).expect("the former is whole");
        assert!(
            read.iter()
                .copied()
                .eq(linear.iter().copied().map(DeBruijnIndex::from)),
            "{what}: linear {read:?}, stated {linear:?}"
        );
        let read = free.consumed(&core, term).expect("the former is whole");
        assert!(
            read.iter()
                .copied()
                .eq(consumed.iter().copied().map(DeBruijnIndex::from)),
            "{what}: consumed {read:?}, stated {consumed:?}"
        );
    }
}
