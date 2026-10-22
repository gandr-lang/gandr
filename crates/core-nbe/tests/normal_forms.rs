//! Normalization by evaluation over every former: what each term normalizes
//! to, and that two copies of a normal form convert.
//!
//! A normal row's expected term is the row itself: a term in normal form is
//! a fixed point of normalization, and the stuck rows stand every eliminator
//! on an opaque constant, so evaluation reaches each eliminator's neutral
//! spine. A redex row's expected term is written out by hand from the
//! reduction rule alone. Each row is evaluated and read back in both
//! readback modes, then compared as a tree.
//!
//! Conversion compares two separately built copies of each row's normal
//! form, so neither the node nor the source term is shared and the walk
//! reaches every pair. Two stuck rows over different eliminators are not
//! convertible.

use alloc::collections::BTreeMap;
use alloc::string::String;
use alloc::sync::Arc;
use alloc::vec::Vec;

use gandr_core_nbe::Convertibility;
use gandr_core_nbe::CoreTerm;
use gandr_core_nbe::DeclineReason;
use gandr_core_nbe::Deferral;
use gandr_core_nbe::Definitions;
use gandr_core_nbe::DomainArena;
use gandr_core_nbe::EvalFault;
use gandr_core_nbe::Fuel;
use gandr_core_nbe::LoweredChain;
use gandr_core_nbe::MachineSettings;
use gandr_core_nbe::MachineVerdict;
use gandr_core_nbe::Problem;
use gandr_core_nbe::ReadbackMode;
use gandr_core_nbe::Settlement;
use gandr_core_nbe::convert_computations;
use gandr_core_nbe::convert_values;
use gandr_core_nbe::decide;
use gandr_core_nbe::eval_computation;
use gandr_core_nbe::eval_value;
use gandr_core_nbe::readback_computation;
use gandr_core_nbe::readback_value;
use gandr_core_term::CertificateEquality;
use gandr_core_term::CompTypeId;
use gandr_core_term::ComponentCount;
use gandr_core_term::ComputationId;
use gandr_core_term::CoreArena;
use gandr_core_term::DefinitionChain;
use gandr_core_term::DefinitionalEnvironment;
use gandr_core_term::Sort;
use gandr_core_term::Transparency;
use gandr_core_term::ValueId;
use gandr_core_term::ValueTypeId;
use gandr_core_term::Zone;
use gandr_core_term::effect::EffectName;
use gandr_core_term::effect::EffectOp;
use gandr_core_term::effect::EffectRow;
use gandr_core_term::effect::EffectSig;
use gandr_core_term::effect::capability::CapabilityGrade;
use gandr_core_term::effect::capability::Region;
use gandr_core_term::equal_certificate_syntax;
use gandr_core_term::session::PayloadCount;
use gandr_core_term::session::PayloadSlot;
use gandr_core_term::session::Protocol;
use gandr_core_term::session::ProtocolState;
use gandr_core_term::session::ProtocolSyntax;
use gandr_core_term::session::SessionType;
use gandr_core_term::world::World;
use gandr_core_term::world::WorldType;
use gandr_kernel_check_memo::NullMemo;
use gandr_kernel_conversion_trace::NullSink;
use gandr_kernel_strata::Level;
use gandr_kernel_term::BaseType;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::ConstructorTag;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::FieldLabel;
use gandr_kernel_term::FixpointEvidence;
use gandr_kernel_term::GlobalIndex;
use gandr_kernel_term::GroundSort;
use gandr_kernel_term::IntegerLiteral;
use gandr_kernel_term::Literal;
use gandr_kernel_term::Magnitude;
use gandr_kernel_term::Sign;
use gandr_kernel_term::Stage;
use gandr_kernel_term::StageId;
use gandr_kernel_term::Summand;

/// A de Bruijn index a row reads.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
struct Index(u32);

/// A non-negative integer, as the decimal digits a literal is written in.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
struct Digits(&'static str);

/// A record label.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
struct Label(&'static str);

/// Builds a term in an arena.
type Build = fn(&mut CoreArena) -> CoreTerm;

/// One term and what it normalizes to.
struct Row
{
    /// The term, as the row writes it.
    what: &'static str,
    /// Builds the term.
    build: Build,
    /// Builds its normal form, or `None` when the term is its own.
    normal: Option<Build>,
    /// What two separately built copies of its normal form settle at.
    copies: Settlement,
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

/// The integer literal `digits`.
///
/// # Specification
/// trivial.
fn integer(
    core: &mut CoreArena,
    digits: Digits,
) -> ValueId
{
    let magnitude = Magnitude::from_decimal_text(String::from(digits.0)).expect("decimal digits");
    core.value_literal(Literal::Integer(IntegerLiteral::new(
        Sign::NonNegative,
        magnitude,
    )))
}

/// The opaque constant every stuck row stands on: nothing defines it.
///
/// # Specification
/// trivial.
fn opaque(core: &mut CoreArena) -> ValueId
{
    core.value_constant(ConstantIndex::from(3_usize))
}

/// `return v`, as a term.
///
/// # Specification
/// trivial.
fn returned(
    core: &mut CoreArena,
    value: ValueId,
) -> CoreTerm
{
    CoreTerm::Computation(core.computation_return(value))
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
    let mut components = Vec::with_capacity(at.len());
    for &index in at {
        components.push(x(core, index));
    }
    let tuple = core.value_tuple(&components);
    core.computation_return(tuple)
}

/// The computation type returning the unit.
///
/// # Specification
/// trivial.
fn returns_unit(core: &mut CoreArena) -> CompTypeId
{
    let unit = core.value_type_unit();
    core.comp_type_returner(unit)
}

/// The label `name`.
///
/// # Specification
/// trivial.
fn label(name: Label) -> FieldLabel
{
    FieldLabel::from(String::from(name.0))
}

/// The session type that sends one unit and ends.
///
/// # Specification
/// trivial.
fn sending_unit(core: &mut CoreArena) -> ValueTypeId
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
    let unit = core.value_type_unit();
    let session =
        SessionType::new(Arc::new(protocol), Arc::from([unit])).expect("one payload for one slot");
    core.value_type_session(session)
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

/// Values in normal form, quoted types among them.
///
/// # Specification
/// trivial.
fn values() -> [Row; 18]
{
    [
        Row {
            what: "((), (1, 2), inl (), {a = 1})",
            build: |a| {
                let unit = a.value_unit();
                let numbers = [integer(a, Digits("1")), integer(a, Digits("2"))];
                let pair = a.value_tuple(&numbers);
                let left = a.value_injection(Summand::from(0_usize), unit);
                let one = integer(a, Digits("1"));
                let record = a.value_record(BTreeMap::from([(label(Label("a")), one)]));
                CoreTerm::Value(a.value_tuple(&[unit, pair, left, record]))
            },
            copies: Settlement::StructurallyEqual,
            normal: None,
        },
        Row {
            what: "(K(()) : D, 1 :: nil, lift ())",
            build: |a| {
                let unit = a.value_unit();
                let datatype = a.value_type_data(ConstantIndex::from(0_usize), Vec::new());
                let constructed =
                    a.value_constructor(datatype, ConstructorTag::from(0_usize), Vec::from([unit]));
                let one = integer(a, Digits("1"));
                let nil = a.value_list_nil();
                let cell = a.value_list_cons(one, nil);
                let lifted = a.value_lift(Level::zero(), unit);
                CoreTerm::Value(a.value_tuple(&[constructed, cell, lifted]))
            },
            copies: Settlement::StructurallyEqual,
            normal: None,
        },
        Row {
            what: "thunk { return 1 }",
            build: |a| {
                let one = integer(a, Digits("1"));
                let body = a.computation_return(one);
                CoreTerm::Value(a.value_thunk(body))
            },
            copies: Settlement::Deferred(Deferral::Binder),
            normal: None,
        },
        Row {
            what: "static λy. y",
            build: |a| {
                let y = x(a, Index(0));
                CoreTerm::Value(a.value_static_lambda(y))
            },
            copies: Settlement::StructurallyEqual,
            normal: None,
        },
        Row {
            what: "type(Integer), type(U0), type(A), type(buffer)",
            build: |a| {
                let types = [
                    a.value_type_base(BaseType::Integer),
                    a.value_type_universe(Sort::Ground(GroundSort::Value), Level::zero()),
                    a.value_type_abstract(ConstantIndex::from(0_usize)),
                    a.value_type_buffer(),
                ];
                let quotes = types.map(|ty| a.value_quote(ty));
                CoreTerm::Value(a.value_tuple(&quotes))
            },
            copies: Settlement::StructurallyEqual,
            normal: None,
        },
        Row {
            what: "type(list Integer), type(staged ()), type(kept ()), type(() at host)",
            build: |a| {
                let integer_type = a.value_type_base(BaseType::Integer);
                let unit = a.value_type_unit();
                let types = [
                    a.value_type_list(integer_type),
                    a.value_type_staged(unit, Stage::At(StageId::from(0_usize))),
                    a.value_type_kept(unit, Region::Held),
                    a.value_type_world(WorldType::At {
                        inner: unit,
                        world: World::Host,
                    }),
                    a.value_type_world(WorldType::Capability(World::Host)),
                ];
                let quotes = types.map(|ty| a.value_quote(ty));
                CoreTerm::Value(a.value_tuple(&quotes))
            },
            copies: Settlement::StructurallyEqual,
            normal: None,
        },
        Row {
            what: "type(cap Proc), type({a : ()}), type(!(). end), type(D)",
            build: |a| {
                let signature = proc(a);
                let unit = a.value_type_unit();
                let types = [
                    a.value_type_capability(
                        EffectRow::singleton(signature),
                        CapabilityGrade::Durable,
                        Region::Held,
                    ),
                    a.value_type_record(BTreeMap::from([(label(Label("a")), unit)])),
                    sending_unit(a),
                    a.value_type_data(ConstantIndex::from(0_usize), Vec::new()),
                ];
                let quotes = types.map(|ty| a.value_quote(ty));
                CoreTerm::Value(a.value_tuple(&quotes))
            },
            copies: Settlement::StructurallyEqual,
            normal: None,
        },
        Row {
            what: "type(() × ()), type(() + ()), type(Σ ()). ()), type(static U0 → U0)",
            build: |a| {
                let unit = a.value_type_unit();
                let universe =
                    a.value_type_universe(Sort::Ground(GroundSort::Value), Level::zero());
                let types = [
                    a.value_type_product(&[unit, unit]),
                    a.value_type_sum(&[unit, unit]),
                    a.value_type_sigma(unit, unit),
                    a.value_type_static_pi(universe, universe),
                ];
                let quotes = types.map(|ty| a.value_quote(ty));
                CoreTerm::Value(a.value_tuple(&quotes))
            },
            copies: Settlement::StructurallyEqual,
            normal: None,
        },
        Row {
            what: "type(U ↑()), type(lift ()), type(stack(↑(), ↑()))",
            build: |a| {
                let returner = returns_unit(a);
                let unit = a.value_type_unit();
                let types = [
                    a.value_type_thunk(returner),
                    a.value_type_lift(unit, Level::zero()),
                    a.value_type_stack(returner, returner),
                ];
                let quotes = types.map(|ty| a.value_quote(ty));
                CoreTerm::Value(a.value_tuple(&quotes))
            },
            copies: Settlement::StructurallyEqual,
            normal: None,
        },
        Row {
            what: "computation types: &(↑(), ↑()), ↑() with Proc, () → ↑(), Π (). ↑(), codata C",
            build: |a| {
                let returner = returns_unit(a);
                let unit = a.value_type_unit();
                let signature = proc(a);
                let types = [
                    a.comp_type_with(&[returner, returner]),
                    a.comp_type_returner_with_effects(unit, EffectRow::singleton(signature)),
                    a.comp_type_arrow(unit, returner),
                    a.comp_type_pi(unit, returner),
                    a.comp_type_codata(ConstantIndex::from(0_usize), Vec::new()),
                ];
                let quotes = types.map(|ty| a.value_quote_computation(ty));
                CoreTerm::Value(a.value_tuple(&quotes))
            },
            copies: Settlement::StructurallyEqual,
            normal: None,
        },
        Row {
            what: "type(?), type(? computation)",
            build: |a| {
                let unknown = a.value_type_unknown();
                let unknown_computation = a.comp_type_unknown();
                let quotes = [
                    a.value_quote(unknown),
                    a.value_quote_computation(unknown_computation),
                ];
                CoreTerm::Value(a.value_tuple(&quotes))
            },
            copies: Settlement::Deferred(Deferral::Unfolding),
            normal: None,
        },
        Row {
            what: "type(run c), type(c ≃ c), type(c = c in ()), type(a flow c ~> c in ())",
            build: |a| {
                let held = opaque(a);
                let unit = a.value_type_unit();
                let types = [
                    a.value_type_run(held),
                    a.value_type_path_universe(held, held),
                    a.value_type_path(unit, held, held),
                    a.value_type_flow(unit, held, held),
                ];
                let quotes = types.map(|ty| a.value_quote(ty));
                CoreTerm::Value(a.value_tuple(&quotes))
            },
            copies: Settlement::StructurallyEqual,
            normal: None,
        },
        Row {
            what: "type(D(c)), type(El c), type(codata C(c))",
            build: |a| {
                let held = opaque(a);
                let types = [
                    a.value_type_data(ConstantIndex::from(0_usize), Vec::from([held])),
                    a.value_type_element(held, Level::zero()),
                ];
                let codata = a.comp_type_codata(ConstantIndex::from(0_usize), Vec::from([held]));
                let quotes = [
                    a.value_quote(types[0]),
                    a.value_quote(types[1]),
                    a.value_quote_computation(codata),
                ];
                CoreTerm::Value(a.value_tuple(&quotes))
            },
            copies: Settlement::StructurallyEqual,
            normal: None,
        },
        Row {
            what: "type(El type(Integer))",
            build: |a| {
                let integer_type = a.value_type_base(BaseType::Integer);
                let code = a.value_quote(integer_type);
                let decoded = a.value_type_element(code, Level::zero());
                CoreTerm::Value(a.value_quote(decoded))
            },
            copies: Settlement::StructurallyEqual,
            normal: Some(|a| {
                let integer_type = a.value_type_base(BaseType::Integer);
                CoreTerm::Value(a.value_quote(integer_type))
            }),
        },
        Row {
            what: "(static λy. y) 1",
            build: |a| {
                let y = x(a, Index(0));
                let function = a.value_static_lambda(y);
                let one = integer(a, Digits("1"));
                CoreTerm::Value(a.value_static_application(function, one))
            },
            copies: Settlement::StructurallyEqual,
            normal: Some(|a| CoreTerm::Value(integer(a, Digits("1")))),
        },
        Row {
            what: "(c, nil)",
            build: |a| {
                let held = opaque(a);
                let nil = a.value_list_nil();
                CoreTerm::Value(a.value_tuple(&[held, nil]))
            },
            copies: Settlement::StructurallyEqual,
            normal: None,
        },
        Row {
            what: "refl c",
            build: |a| {
                let held = opaque(a);
                CoreTerm::Value(a.value_path_refl(held))
            },
            copies: Settlement::StructurallyEqual,
            normal: None,
        },
        Row {
            what: "(c ⊗ c, c ⊗~ c)",
            build: |a| {
                let held = opaque(a);
                let paths = a.value_path_product(held, held);
                let flows = a.value_flow_product(held, held);
                CoreTerm::Value(a.value_tuple(&[paths, flows]))
            },
            copies: Settlement::StructurallyEqual,
            normal: None,
        },
    ]
}

/// Every eliminator standing on the opaque constant `c`.
///
/// # Specification
/// trivial.
fn stuck() -> [Row; 14]
{
    [
        Row {
            what: "case c { nil ⇒ return (); h :: t ⇒ return (h, t) }",
            build: |a| {
                let held = opaque(a);
                let unit = a.value_unit();
                let on_nil = a.computation_return(unit);
                let on_cons = returning(a, &[Index(1), Index(0)]);
                CoreTerm::Computation(a.computation_list_case(held, on_nil, on_cons))
            },
            copies: Settlement::Deferred(Deferral::Binder),
            normal: None,
        },
        Row {
            what: "fold c { nil ⇒ return (); h, r ⇒ return (h, r) }",
            build: |a| {
                let held = opaque(a);
                let unit = a.value_unit();
                let unit_type = a.value_type_unit();
                let on_nil = a.computation_return(unit);
                let on_cons = returning(a, &[Index(1), Index(0)]);
                CoreTerm::Computation(
                    a.computation_list_fold(unit_type, unit_type, held, on_nil, on_cons),
                )
            },
            copies: Settlement::Deferred(Deferral::Binder),
            normal: None,
        },
        Row {
            what: "case c at s. ↑() { K ⇒ return () }",
            build: |a| {
                let held = opaque(a);
                let motive = returns_unit(a);
                let unit = a.value_unit();
                let branch = a.computation_return(unit);
                CoreTerm::Computation(a.computation_data_case(held, motive, Vec::from([branch])))
            },
            copies: Settlement::Deferred(Deferral::Binder),
            normal: None,
        },
        Row {
            what: "split c as (y, z) in return (z, y)",
            build: |a| {
                let held = opaque(a);
                let body = returning(a, &[Index(0), Index(1)]);
                CoreTerm::Computation(a.computation_split(
                    held,
                    ComponentCount::from(2_usize),
                    body,
                ))
            },
            copies: Settlement::Deferred(Deferral::Binder),
            normal: None,
        },
        Row {
            what: "split c as (y, z) at s. ↑() in return ()",
            build: |a| {
                let held = opaque(a);
                let motive = returns_unit(a);
                let unit = a.value_unit();
                let body = a.computation_return(unit);
                CoreTerm::Computation(a.computation_dependent_split(
                    held,
                    ComponentCount::from(2_usize),
                    motive,
                    body,
                ))
            },
            copies: Settlement::Deferred(Deferral::Binder),
            normal: None,
        },
        Row {
            what: "c.a",
            build: |a| {
                let held = opaque(a);
                CoreTerm::Computation(a.computation_record_projection(held, label(Label("a"))))
            },
            copies: Settlement::StructurallyEqual,
            normal: None,
        },
        Row {
            what: "c.1",
            build: |a| {
                let held = opaque(a);
                CoreTerm::Computation(a.computation_tuple_projection(
                    held,
                    gandr_kernel_term::Component::from(1_usize),
                ))
            },
            copies: Settlement::StructurallyEqual,
            normal: None,
        },
        Row {
            what: "force c",
            build: |a| {
                let held = opaque(a);
                CoreTerm::Computation(a.computation_force(held))
            },
            copies: Settlement::StructurallyEqual,
            normal: None,
        },
        Row {
            what: "(force c) ()",
            build: |a| {
                let held = opaque(a);
                let forced = a.computation_force(held);
                let unit = a.value_unit();
                CoreTerm::Computation(a.computation_application(forced, unit))
            },
            copies: Settlement::StructurallyEqual,
            normal: None,
        },
        Row {
            what: "case c { inl y ⇒ return y; inr y ⇒ return () }",
            build: |a| {
                let held = opaque(a);
                let y = x(a, Index(0));
                let unit = a.value_unit();
                let branches = [a.computation_return(y), a.computation_return(unit)];
                CoreTerm::Computation(a.computation_case(held, &branches))
            },
            copies: Settlement::Deferred(Deferral::Binder),
            normal: None,
        },
        Row {
            what: "transport c ()",
            build: |a| {
                let held = opaque(a);
                let unit = a.value_unit();
                CoreTerm::Computation(a.computation_transport(held, unit))
            },
            copies: Settlement::StructurallyEqual,
            normal: None,
        },
        Row {
            what: "transport ↑() along c from () over here(()) of ()",
            build: |a| {
                let held = opaque(a);
                let unit = a.value_unit();
                let over = a.value_here(unit);
                let motive = returns_unit(a);
                CoreTerm::Computation(
                    a.computation_telescope_transport(motive, held, unit, over, unit),
                )
            },
            copies: Settlement::Deferred(Deferral::Binder),
            normal: None,
        },
        Row {
            what: "transport (y. El y) along c of ()",
            build: |a| {
                let held = opaque(a);
                let unit = a.value_unit();
                let y = x(a, Index(0));
                let motive = a.value_type_element(y, Level::zero());
                CoreTerm::Computation(a.computation_path_transport(motive, held, unit))
            },
            copies: Settlement::StructurallyEqual,
            normal: None,
        },
        Row {
            what: "ride (y. El y) c ()",
            build: |a| {
                let held = opaque(a);
                let unit = a.value_unit();
                let y = x(a, Index(0));
                let motive = a.value_type_element(y, Level::zero());
                CoreTerm::Computation(a.computation_ride(motive, held, unit))
            },
            copies: Settlement::StructurallyEqual,
            normal: None,
        },
    ]
}

/// Redexes, each with the term its reduction rule leaves.
///
/// # Specification
/// trivial.
fn redexes() -> [Row; 16]
{
    [
        Row {
            what: "split (1, 2) as (y, z) in return (z, y)",
            build: |a| {
                let numbers = [integer(a, Digits("1")), integer(a, Digits("2"))];
                let pair = a.value_tuple(&numbers);
                let body = returning(a, &[Index(0), Index(1)]);
                CoreTerm::Computation(a.computation_split(
                    pair,
                    ComponentCount::from(2_usize),
                    body,
                ))
            },
            copies: Settlement::StructurallyEqual,
            normal: Some(|a| {
                let numbers = [integer(a, Digits("2")), integer(a, Digits("1"))];
                let pair = a.value_tuple(&numbers);
                returned(a, pair)
            }),
        },
        Row {
            what: "case inr 2 { inl y ⇒ return y; inr y ⇒ return (y, y) }",
            build: |a| {
                let two = integer(a, Digits("2"));
                let right = a.value_injection(Summand::from(1_usize), two);
                let y = x(a, Index(0));
                let branches = [a.computation_return(y), returning(a, &[Index(0), Index(0)])];
                CoreTerm::Computation(a.computation_case(right, &branches))
            },
            copies: Settlement::StructurallyEqual,
            normal: Some(|a| {
                let numbers = [integer(a, Digits("2")), integer(a, Digits("2"))];
                let pair = a.value_tuple(&numbers);
                returned(a, pair)
            }),
        },
        Row {
            what: "case 1 :: nil { nil ⇒ return 0; h :: t ⇒ return (h, t) }",
            build: |a| {
                let one = integer(a, Digits("1"));
                let nil = a.value_list_nil();
                let list = a.value_list_cons(one, nil);
                let zero = integer(a, Digits("0"));
                let on_nil = a.computation_return(zero);
                let on_cons = returning(a, &[Index(1), Index(0)]);
                CoreTerm::Computation(a.computation_list_case(list, on_nil, on_cons))
            },
            copies: Settlement::StructurallyEqual,
            normal: Some(|a| {
                let one = integer(a, Digits("1"));
                let nil = a.value_list_nil();
                let pair = a.value_tuple(&[one, nil]);
                returned(a, pair)
            }),
        },
        Row {
            what: "case nil { nil ⇒ return 0; h :: t ⇒ return (h, t) }",
            build: |a| {
                let nil = a.value_list_nil();
                let zero = integer(a, Digits("0"));
                let on_nil = a.computation_return(zero);
                let on_cons = returning(a, &[Index(1), Index(0)]);
                CoreTerm::Computation(a.computation_list_case(nil, on_nil, on_cons))
            },
            copies: Settlement::StructurallyEqual,
            normal: Some(|a| {
                let zero = integer(a, Digits("0"));
                returned(a, zero)
            }),
        },
        Row {
            what: "fold 1 :: nil { nil ⇒ return 0; h, r ⇒ return (h, r) }",
            build: |a| {
                let one = integer(a, Digits("1"));
                let nil = a.value_list_nil();
                let list = a.value_list_cons(one, nil);
                let zero = integer(a, Digits("0"));
                let on_nil = a.computation_return(zero);
                let on_cons = returning(a, &[Index(1), Index(0)]);
                let element = a.value_type_base(BaseType::Integer);
                CoreTerm::Computation(
                    a.computation_list_fold(element, element, list, on_nil, on_cons),
                )
            },
            copies: Settlement::StructurallyEqual,
            normal: Some(|a| {
                let numbers = [integer(a, Digits("1")), integer(a, Digits("0"))];
                let pair = a.value_tuple(&numbers);
                returned(a, pair)
            }),
        },
        Row {
            what: "case K1 at s. ↑() { K0 ⇒ return 0; K1 ⇒ return 1 }",
            build: |a| {
                let datatype = a.value_type_data(ConstantIndex::from(0_usize), Vec::new());
                let scrutinee =
                    a.value_constructor(datatype, ConstructorTag::from(1_usize), Vec::new());
                let motive = returns_unit(a);
                let branches = [Digits("0"), Digits("1")].map(|digits| {
                    let answer = integer(a, digits);
                    a.computation_return(answer)
                });
                CoreTerm::Computation(a.computation_data_case(
                    scrutinee,
                    motive,
                    Vec::from(branches),
                ))
            },
            copies: Settlement::StructurallyEqual,
            normal: Some(|a| {
                let one = integer(a, Digits("1"));
                returned(a, one)
            }),
        },
        Row {
            what: "{a = 1, b = 2}.b",
            build: |a| {
                let numbers = [integer(a, Digits("1")), integer(a, Digits("2"))];
                let [first, second] = numbers;
                let record = a.value_record(BTreeMap::from([
                    (label(Label("a")), first),
                    (label(Label("b")), second),
                ]));
                CoreTerm::Computation(a.computation_record_projection(record, label(Label("b"))))
            },
            copies: Settlement::StructurallyEqual,
            normal: Some(|a| {
                let two = integer(a, Digits("2"));
                returned(a, two)
            }),
        },
        Row {
            what: "(1, 2).1",
            build: |a| {
                let numbers = [integer(a, Digits("1")), integer(a, Digits("2"))];
                let pair = a.value_tuple(&numbers);
                CoreTerm::Computation(a.computation_tuple_projection(
                    pair,
                    gandr_kernel_term::Component::from(1_usize),
                ))
            },
            copies: Settlement::StructurallyEqual,
            normal: Some(|a| {
                let two = integer(a, Digits("2"));
                returned(a, two)
            }),
        },
        Row {
            what: "force thunk { return 1 }",
            build: |a| {
                let one = integer(a, Digits("1"));
                let body = a.computation_return(one);
                let thunk = a.value_thunk(body);
                CoreTerm::Computation(a.computation_force(thunk))
            },
            copies: Settlement::StructurallyEqual,
            normal: Some(|a| {
                let one = integer(a, Digits("1"));
                returned(a, one)
            }),
        },
        Row {
            what: "y <- return 1; return (y, y)",
            build: |a| {
                let one = integer(a, Digits("1"));
                let bound = a.computation_return(one);
                let body = returning(a, &[Index(0), Index(0)]);
                CoreTerm::Computation(a.computation_bind(bound, body))
            },
            copies: Settlement::StructurallyEqual,
            normal: Some(|a| {
                let numbers = [integer(a, Digits("1")), integer(a, Digits("1"))];
                let pair = a.value_tuple(&numbers);
                returned(a, pair)
            }),
        },
        Row {
            what: "rec f. return 1",
            build: |a| {
                let one = integer(a, Digits("1"));
                let body = a.computation_return(one);
                CoreTerm::Computation(a.computation_fixpoint(body, FixpointEvidence::Partial))
            },
            copies: Settlement::Deferred(Deferral::Binder),
            normal: None,
        },
        Row {
            what: "(return 1 : ↑Integer)",
            build: |a| {
                let one = integer(a, Digits("1"));
                let body = a.computation_return(one);
                let integer_type = a.value_type_base(BaseType::Integer);
                let returner = a.comp_type_returner(integer_type);
                CoreTerm::Computation(a.computation_ascribe(body, returner))
            },
            copies: Settlement::StructurallyEqual,
            normal: Some(|a| {
                let one = integer(a, Digits("1"));
                returned(a, one)
            }),
        },
        Row {
            what: "mark 0 { return 1 }",
            build: |a| {
                let one = integer(a, Digits("1"));
                let body = a.computation_return(one);
                CoreTerm::Computation(
                    a.computation_mark(gandr_core_term::hole::MarkIndex::from(0_u32), body),
                )
            },
            copies: Settlement::Deferred(Deferral::Indeterminate),
            normal: None,
        },
        Row {
            what: "transport (y. ()) along c of ()",
            build: |a| {
                let held = opaque(a);
                let unit = a.value_unit();
                let motive = a.value_type_unit();
                CoreTerm::Computation(a.computation_path_transport(motive, held, unit))
            },
            copies: Settlement::StructurallyEqual,
            normal: Some(|a| {
                let unit = a.value_unit();
                returned(a, unit)
            }),
        },
        Row {
            what: "ride (y. ()) c ()",
            build: |a| {
                let held = opaque(a);
                let unit = a.value_unit();
                let motive = a.value_type_unit();
                CoreTerm::Computation(a.computation_ride(motive, held, unit))
            },
            copies: Settlement::StructurallyEqual,
            normal: Some(|a| {
                let unit = a.value_unit();
                returned(a, unit)
            }),
        },
        Row {
            what: "split (1, 2) as (y, z) at s. ↑Integer in return z",
            build: |a| {
                let numbers = [integer(a, Digits("1")), integer(a, Digits("2"))];
                let pair = a.value_tuple(&numbers);
                let integer_type = a.value_type_base(BaseType::Integer);
                let motive = a.comp_type_returner(integer_type);
                let body = returning(a, &[Index(0)]);
                CoreTerm::Computation(a.computation_dependent_split(
                    pair,
                    ComponentCount::from(2_usize),
                    motive,
                    body,
                ))
            },
            copies: Settlement::StructurallyEqual,
            normal: Some(|a| {
                let two = integer(a, Digits("2"));
                let single = a.value_tuple(&[two]);
                returned(a, single)
            }),
        },
    ]
}

/// What a term evaluates to.
#[derive(Clone, Copy, Debug)]
enum Evaluated
{
    /// A domain value.
    Value(gandr_core_nbe::DomainValueId),
    /// A domain computation.
    Computation(gandr_core_nbe::DomainCompId),
}

/// `term` evaluated in `domain` against `chain`.
///
/// # Specification
/// trivial.
fn evaluated(
    core: &CoreArena,
    domain: &mut DomainArena,
    chain: &LoweredChain,
    term: CoreTerm,
) -> Evaluated
{
    let environment = DefinitionalEnvironment::new();
    let definitions = Definitions::new(chain, &environment, environment.root());
    let fuel = Fuel::from(4_096_u32);
    match term {
        CoreTerm::Value(id) => Evaluated::Value(
            eval_value(core, domain, definitions, fuel, id).expect("the row evaluates"),
        ),
        CoreTerm::Computation(id) => Evaluated::Computation(
            eval_computation(core, domain, definitions, fuel, id).expect("the row evaluates"),
        ),
    }
}

/// `term` normalized in `mode` against `chain`.
///
/// # Specification
/// trivial.
fn normalized(
    core: &mut CoreArena,
    chain: &LoweredChain,
    term: CoreTerm,
    mode: ReadbackMode,
) -> CoreTerm
{
    let environment = DefinitionalEnvironment::new();
    let definitions = Definitions::new(chain, &environment, environment.root());
    let fuel = Fuel::from(4_096_u32);
    let mut domain = DomainArena::new();
    match term {
        CoreTerm::Value(id) => {
            let value =
                eval_value(core, &mut domain, definitions, fuel, id).expect("the row evaluates");
            CoreTerm::Value(
                readback_value(core, &mut domain, definitions, mode, fuel, value)
                    .expect("the row reads back"),
            )
        },
        CoreTerm::Computation(id) => {
            let computation = eval_computation(core, &mut domain, definitions, fuel, id)
                .expect("the row evaluates");
            CoreTerm::Computation(
                readback_computation(core, &mut domain, definitions, mode, fuel, computation)
                    .expect("the row reads back"),
            )
        },
    }
}

/// The chain that defines the constant `c` the stuck rows stand on as
/// `body`, transparently.
///
/// # Specification
/// trivial.
fn defining(body: ValueId) -> LoweredChain
{
    let mut definitions = DefinitionChain::new();
    let defined = definitions.define(
        ConstantIndex::from(3_usize),
        GlobalIndex::from(0_u32),
        Transparency::Manifest,
        &[],
    );
    assert!(defined.is_ok(), "one constant, defined once");
    LoweredChain::lower(definitions, |_| Ok::<_, core::convert::Infallible>(body))
        .unwrap_or_else(|never| match never {})
}

/// What the constant `c` of one stuck row is defined as, and the term the
/// row reduces to once `c` unfolds.
struct Unfold
{
    /// The stuck row, as it writes itself.
    what: &'static str,
    /// Builds the definition of `c`.
    definition: fn(&mut CoreArena) -> ValueId,
    /// Builds what the row reduces to.
    unfolded: Build,
}

/// A definition for `c` under each stuck row, in the order of [`stuck`],
/// shaped for that row's eliminator.
///
/// # Specification
/// trivial.
fn unfolds() -> [Unfold; 14]
{
    [
        Unfold {
            what: "case c { nil ⇒ return (); h :: t ⇒ return (h, t) }",
            definition: |a| {
                let one = integer(a, Digits("1"));
                let nil = a.value_list_nil();
                a.value_list_cons(one, nil)
            },
            unfolded: |a| {
                let one = integer(a, Digits("1"));
                let nil = a.value_list_nil();
                let pair = a.value_tuple(&[one, nil]);
                returned(a, pair)
            },
        },
        Unfold {
            what: "fold c { nil ⇒ return (); h, r ⇒ return (h, r) }",
            definition: |a| a.value_list_nil(),
            unfolded: |a| {
                let unit = a.value_unit();
                returned(a, unit)
            },
        },
        Unfold {
            what: "case c at s. ↑() { K ⇒ return () }",
            definition: |a| {
                let datatype = a.value_type_data(ConstantIndex::from(0_usize), Vec::new());
                a.value_constructor(datatype, ConstructorTag::from(0_usize), Vec::new())
            },
            unfolded: |a| {
                let unit = a.value_unit();
                returned(a, unit)
            },
        },
        Unfold {
            what: "split c as (y, z) in return (z, y)",
            definition: |a| {
                let numbers = [integer(a, Digits("1")), integer(a, Digits("2"))];
                a.value_tuple(&numbers)
            },
            unfolded: |a| {
                let numbers = [integer(a, Digits("2")), integer(a, Digits("1"))];
                let swapped = a.value_tuple(&numbers);
                returned(a, swapped)
            },
        },
        Unfold {
            what: "split c as (y, z) at s. ↑() in return ()",
            definition: |a| {
                let numbers = [integer(a, Digits("1")), integer(a, Digits("2"))];
                a.value_tuple(&numbers)
            },
            unfolded: |a| {
                let unit = a.value_unit();
                returned(a, unit)
            },
        },
        Unfold {
            what: "c.a",
            definition: |a| {
                let one = integer(a, Digits("1"));
                a.value_record(BTreeMap::from([(label(Label("a")), one)]))
            },
            unfolded: |a| {
                let one = integer(a, Digits("1"));
                returned(a, one)
            },
        },
        Unfold {
            what: "c.1",
            definition: |a| {
                let numbers = [integer(a, Digits("1")), integer(a, Digits("2"))];
                a.value_tuple(&numbers)
            },
            unfolded: |a| {
                let two = integer(a, Digits("2"));
                returned(a, two)
            },
        },
        Unfold {
            what: "force c",
            definition: |a| {
                let one = integer(a, Digits("1"));
                let body = a.computation_return(one);
                a.value_thunk(body)
            },
            unfolded: |a| {
                let one = integer(a, Digits("1"));
                returned(a, one)
            },
        },
        Unfold {
            what: "(force c) ()",
            definition: |a| {
                let one = integer(a, Digits("1"));
                let body = a.computation_return(one);
                let function = a.computation_lambda(body);
                a.value_thunk(function)
            },
            unfolded: |a| {
                let one = integer(a, Digits("1"));
                returned(a, one)
            },
        },
        Unfold {
            what: "case c { inl y ⇒ return y; inr y ⇒ return () }",
            definition: |a| {
                let one = integer(a, Digits("1"));
                a.value_injection(Summand::from(0_usize), one)
            },
            unfolded: |a| {
                let one = integer(a, Digits("1"));
                returned(a, one)
            },
        },
        Unfold {
            what: "transport c ()",
            definition: |a| {
                let unit = a.value_unit();
                a.value_path_refl(unit)
            },
            unfolded: |a| {
                let unit = a.value_unit();
                returned(a, unit)
            },
        },
        Unfold {
            what: "transport ↑() along c from () over here(()) of ()",
            definition: |a| {
                let unit = a.value_unit();
                a.value_here(unit)
            },
            unfolded: |a| {
                let unit = a.value_unit();
                returned(a, unit)
            },
        },
        Unfold {
            what: "transport (y. El y) along c of ()",
            definition: |a| {
                let unit = a.value_unit();
                a.value_here(unit)
            },
            unfolded: |a| {
                let unit = a.value_unit();
                returned(a, unit)
            },
        },
        Unfold {
            what: "ride (y. El y) c ()",
            definition: |a| {
                let one = integer(a, Digits("1"));
                let body = a.computation_return(one);
                let translate = a.computation_lambda(body);
                let translator = a.value_thunk(translate);
                a.value_forward(translator)
            },
            unfolded: |a| {
                let one = integer(a, Digits("1"));
                returned(a, one)
            },
        },
    ]
}

/// Whether `left` and `right` are one term, former by former, read by the
/// core's own structural equality; a computation is compared as the thunk
/// that holds it.
///
/// # Specification
/// trivial.
fn same(
    core: &mut CoreArena,
    left: CoreTerm,
    right: CoreTerm,
) -> CertificateEquality
{
    let mut held = |term| match term {
        CoreTerm::Value(id) => id,
        CoreTerm::Computation(id) => core.value_thunk(id),
    };
    let (left, right) = (held(left), held(right));
    equal_certificate_syntax(core, left, right)
}

/// What converting two evaluated terms of one kind settles at.
///
/// # Specification
/// trivial.
fn settled(
    core: &CoreArena,
    domain: &DomainArena,
    pair: [Evaluated; 2],
) -> Settlement
{
    match pair {
        [Evaluated::Value(left), Evaluated::Value(right)] => {
            convert_values(core, domain, left, right).expect("both sides are whole")
        },
        [Evaluated::Computation(left), Evaluated::Computation(right)] => {
            convert_computations(core, domain, left, right).expect("both sides are whole")
        },
        [Evaluated::Value(_), Evaluated::Computation(_)]
        | [Evaluated::Computation(_), Evaluated::Value(_)] => {
            panic!("both sides are of one kind")
        },
    }
}

/// Each row normalizes, in both readback modes, to the term its rule
/// leaves: a normal form to itself, a redex to the term written out for it.
#[test]
fn each_former_normalizes_to_the_term_its_rule_leaves()
{
    let rows = values().into_iter().chain(stuck()).chain(redexes());
    for Row {
        what,
        build,
        normal,
        ..
    } in rows
    {
        for mode in [ReadbackMode::ZeroUnfold, ReadbackMode::Unfolding] {
            let mut core = CoreArena::new();
            let term = build(&mut core);
            let expected = normal.unwrap_or(build)(&mut core);
            let read = normalized(&mut core, &LoweredChain::new(), term, mode);
            assert_eq!(
                CertificateEquality::Equal,
                same(&mut core, read, expected),
                "{what} in {mode:?}"
            );
        }
    }
}

/// Once the constant `c` is defined, each stuck row still reads back as it
/// stands without unfolding, and the machine, unfolding `c` and replaying
/// the row's eliminator over its definition, decides the row convertible
/// with the term that eliminator's rule leaves. With `c` undefined the same
/// two terms are apart.
#[test]
fn a_stuck_row_reduces_once_its_constant_unfolds()
{
    for (row, unfold) in stuck().into_iter().zip(unfolds()) {
        assert_eq!(
            row.what, unfold.what,
            "the definitions follow the stuck rows"
        );
        let mut core = CoreArena::new();
        let term = (row.build)(&mut core);
        let body = (unfold.definition)(&mut core);
        let reduct = (unfold.unfolded)(&mut core);
        let chain = defining(body);
        let read = normalized(&mut core, &chain, term, ReadbackMode::ZeroUnfold);
        assert_eq!(
            CertificateEquality::Equal,
            same(&mut core, read, term),
            "{}",
            row.what
        );
        for (chain, verdict) in [
            (&chain, MachineVerdict::Convertible),
            (&LoweredChain::new(), MachineVerdict::NotConvertible),
        ] {
            let mut domain = DomainArena::new();
            let pair = [term, reduct].map(|side| evaluated(&core, &mut domain, chain, side));
            assert_eq!(
                verdict,
                decided(&core, &mut domain, chain, pair),
                "{}",
                row.what
            );
        }
    }
}

/// Two separately built copies of each row's normal form settle as the row
/// states: structurally equal, or deferred where a closure must be opened, an
/// unknown type might unfold, or a mark suspends what it holds. One evaluated
/// node against itself is identical. Two stuck rows over different
/// eliminators never convert.
#[test]
fn two_copies_of_a_normal_form_settle_alike_and_distinct_spines_do_not()
{
    let rows = values().into_iter().chain(stuck()).chain(redexes());
    for Row {
        what,
        build,
        normal,
        copies,
    } in rows
    {
        let written = normal.unwrap_or(build);
        let mut core = CoreArena::new();
        let built = [written(&mut core), written(&mut core)];
        let mut domain = DomainArena::new();
        let pair = built.map(|copy| evaluated(&core, &mut domain, &LoweredChain::new(), copy));
        assert_eq!(copies, settled(&core, &domain, pair), "{what}");
        let [one, _] = pair;
        assert_eq!(
            Settlement::Identical,
            settled(&core, &domain, [one, one]),
            "{what}"
        );
    }
    let spines = stuck();
    for (first, second) in spines.iter().zip(spines.iter().skip(1)) {
        let mut core = CoreArena::new();
        let terms = [(first.build)(&mut core), (second.build)(&mut core)];
        let mut domain = DomainArena::new();
        let pair = terms.map(|term| evaluated(&core, &mut domain, &LoweredChain::new(), term));
        assert_ne!(
            Convertibility::Convertible,
            settled(&core, &domain, pair).verdict(),
            "{} against {}",
            first.what,
            second.what
        );
    }
}

/// What the conversion machine decides of two evaluated terms of one kind,
/// recording nothing.
///
/// # Specification
/// trivial.
fn decided(
    core: &CoreArena,
    domain: &mut DomainArena,
    chain: &LoweredChain,
    pair: [Evaluated; 2],
) -> MachineVerdict
{
    let environment = DefinitionalEnvironment::new();
    let definitions = Definitions::new(chain, &environment, environment.root());
    let problem = match pair {
        [Evaluated::Value(left), Evaluated::Value(right)] => Problem::values(left, right),
        [Evaluated::Computation(left), Evaluated::Computation(right)] => {
            Problem::computations(left, right)
        },
        [Evaluated::Value(_), Evaluated::Computation(_)]
        | [Evaluated::Computation(_), Evaluated::Value(_)] => {
            panic!("both sides are of one kind")
        },
    };
    decide::<NullSink, NullMemo>(
        core,
        domain,
        definitions,
        MachineSettings::default(),
        problem,
        &mut NullSink,
    )
    .expect("both sides are whole")
    .verdict()
}

/// The machine, which opens the binders the search-free steps defer on,
/// decides two copies of each row's normal form convertible, and two stuck
/// rows over different eliminators not. Unknown types, which the steps defer
/// as possibly unfolding, it declines as undecided codes, and a mark, which
/// they defer as indeterminate, it declines as indeterminate.
#[test]
fn the_machine_decides_copies_convertible_and_distinct_spines_not()
{
    let rows = values().into_iter().chain(stuck()).chain(redexes());
    for Row {
        what,
        build,
        normal,
        copies,
    } in rows
    {
        let written = normal.unwrap_or(build);
        let mut core = CoreArena::new();
        let built = [written(&mut core), written(&mut core)];
        let mut domain = DomainArena::new();
        let empty = LoweredChain::new();
        let pair = built.map(|copy| evaluated(&core, &mut domain, &empty, copy));
        let expected = match copies {
            Settlement::Deferred(Deferral::Unfolding) => {
                MachineVerdict::Declined(DeclineReason::UndecidedCodes)
            },
            Settlement::Deferred(Deferral::Indeterminate) => {
                MachineVerdict::Declined(DeclineReason::Indeterminate)
            },
            Settlement::Identical
            | Settlement::GuardedApart
            | Settlement::StructurallyEqual
            | Settlement::StructurallyApart
            | Settlement::Deferred(Deferral::Binder) => MachineVerdict::Convertible,
        };
        assert_eq!(
            expected,
            decided(&core, &mut domain, &empty, pair),
            "{what}"
        );
    }
    let spines = stuck();
    for (first, second) in spines.iter().zip(spines.iter().skip(1)) {
        let mut core = CoreArena::new();
        let terms = [(first.build)(&mut core), (second.build)(&mut core)];
        let mut domain = DomainArena::new();
        let empty = LoweredChain::new();
        let pair = terms.map(|term| evaluated(&core, &mut domain, &empty, term));
        assert_eq!(
            MachineVerdict::NotConvertible,
            decided(&core, &mut domain, &empty, pair),
            "{} against {}",
            first.what,
            second.what
        );
    }
}

/// A code holding a constant under one type former.
struct Code
{
    /// The code, over the constant `h`.
    what: &'static str,
    /// Builds the code over the constant it is given.
    build: fn(&mut CoreArena, ValueId) -> ValueId,
    /// How unfolding readback treats the constant the code holds.
    read: Read,
}

/// How unfolding readback treats a code's constant.
#[derive(Clone, Copy, Debug)]
enum Read
{
    /// The constant is read back, so it comes back as its unfolding.
    Unfolded,
    /// The former is a native path classifier, spliced as it stands.
    Spliced,
}

/// The element type `El held`.
///
/// # Specification
/// trivial.
fn element(
    core: &mut CoreArena,
    held: ValueId,
) -> ValueTypeId
{
    core.value_type_element(held, Level::zero())
}

/// `↑(El held)`.
///
/// # Specification
/// trivial.
fn returns_element(
    core: &mut CoreArena,
    held: ValueId,
) -> CompTypeId
{
    let decoded = element(core, held);
    core.comp_type_returner(decoded)
}

/// Every type former, each holding the constant `h` it is built over.
///
/// # Specification
/// trivial.
fn codes() -> [Code; 27]
{
    [
        Code {
            what: "type(El h)",
            read: Read::Unfolded,
            build: |a, h| {
                let decoded = element(a, h);
                a.value_quote(decoded)
            },
        },
        Code {
            what: "type(list El h)",
            read: Read::Unfolded,
            build: |a, h| {
                let decoded = element(a, h);
                let list = a.value_type_list(decoded);
                a.value_quote(list)
            },
        },
        Code {
            what: "type(staged El h)",
            read: Read::Unfolded,
            build: |a, h| {
                let decoded = element(a, h);
                let staged = a.value_type_staged(decoded, Stage::At(StageId::from(0_usize)));
                a.value_quote(staged)
            },
        },
        Code {
            what: "type(kept El h)",
            read: Read::Unfolded,
            build: |a, h| {
                let decoded = element(a, h);
                let kept = a.value_type_kept(decoded, Region::Held);
                a.value_quote(kept)
            },
        },
        Code {
            what: "type(El h at host)",
            read: Read::Unfolded,
            build: |a, h| {
                let decoded = element(a, h);
                let located = a.value_type_world(WorldType::At {
                    inner: decoded,
                    world: World::Host,
                });
                a.value_quote(located)
            },
        },
        Code {
            what: "type({a : El h})",
            read: Read::Unfolded,
            build: |a, h| {
                let decoded = element(a, h);
                let record = a.value_type_record(BTreeMap::from([(label(Label("a")), decoded)]));
                a.value_quote(record)
            },
        },
        Code {
            what: "type(El h × El h)",
            read: Read::Unfolded,
            build: |a, h| {
                let decoded = element(a, h);
                let product = a.value_type_product(&[decoded, decoded]);
                a.value_quote(product)
            },
        },
        Code {
            what: "type(El h + El h)",
            read: Read::Unfolded,
            build: |a, h| {
                let decoded = element(a, h);
                let sum = a.value_type_sum(&[decoded, decoded]);
                a.value_quote(sum)
            },
        },
        Code {
            what: "type(Σ El h. El h)",
            read: Read::Unfolded,
            build: |a, h| {
                let decoded = element(a, h);
                let sigma = a.value_type_sigma(decoded, decoded);
                a.value_quote(sigma)
            },
        },
        Code {
            what: "type(static El h → El h)",
            read: Read::Unfolded,
            build: |a, h| {
                let decoded = element(a, h);
                let arrow = a.value_type_static_pi(decoded, decoded);
                a.value_quote(arrow)
            },
        },
        Code {
            what: "type(U ↑El h)",
            read: Read::Unfolded,
            build: |a, h| {
                let returner = returns_element(a, h);
                let thunk = a.value_type_thunk(returner);
                a.value_quote(thunk)
            },
        },
        Code {
            what: "type(lift El h)",
            read: Read::Unfolded,
            build: |a, h| {
                let decoded = element(a, h);
                let lifted = a.value_type_lift(decoded, Level::zero());
                a.value_quote(lifted)
            },
        },
        Code {
            what: "type(stack(↑El h, ↑El h))",
            read: Read::Unfolded,
            build: |a, h| {
                let returner = returns_element(a, h);
                let stack = a.value_type_stack(returner, returner);
                a.value_quote(stack)
            },
        },
        Code {
            what: "type(run h)",
            read: Read::Unfolded,
            build: |a, h| {
                let run = a.value_type_run(h);
                a.value_quote(run)
            },
        },
        Code {
            what: "type(h ≃ h)",
            read: Read::Spliced,
            build: |a, h| {
                let path = a.value_type_path_universe(h, h);
                a.value_quote(path)
            },
        },
        Code {
            what: "type(h = h in El h)",
            read: Read::Unfolded,
            build: |a, h| {
                let decoded = element(a, h);
                let path = a.value_type_path(decoded, h, h);
                a.value_quote(path)
            },
        },
        Code {
            what: "type(a flow h ~> h in El h)",
            read: Read::Unfolded,
            build: |a, h| {
                let decoded = element(a, h);
                let flow = a.value_type_flow(decoded, h, h);
                a.value_quote(flow)
            },
        },
        Code {
            what: "type(1 :: h = 1 :: h in El h)",
            read: Read::Unfolded,
            build: |a, h| {
                let decoded = element(a, h);
                let one = integer(a, Digits("1"));
                let cell = a.value_list_cons(one, h);
                let path = a.value_type_path(decoded, cell, cell);
                a.value_quote(path)
            },
        },
        Code {
            what: "type(inl h = inl h in El h)",
            read: Read::Unfolded,
            build: |a, h| {
                let decoded = element(a, h);
                let left = a.value_injection(Summand::from(0_usize), h);
                let path = a.value_type_path(decoded, left, left);
                a.value_quote(path)
            },
        },
        Code {
            what: "type(K(h) = K(h) in El h)",
            read: Read::Unfolded,
            build: |a, h| {
                let decoded = element(a, h);
                let datatype = a.value_type_data(ConstantIndex::from(0_usize), Vec::new());
                let constructed =
                    a.value_constructor(datatype, ConstructorTag::from(0_usize), Vec::from([h]));
                let path = a.value_type_path(decoded, constructed, constructed);
                a.value_quote(path)
            },
        },
        Code {
            what: "type(lift h = lift h in El h)",
            read: Read::Unfolded,
            build: |a, h| {
                let decoded = element(a, h);
                let lifted = a.value_lift(Level::zero(), h);
                let path = a.value_type_path(decoded, lifted, lifted);
                a.value_quote(path)
            },
        },
        Code {
            what: "type(D(h))",
            read: Read::Unfolded,
            build: |a, h| {
                let data = a.value_type_data(ConstantIndex::from(0_usize), Vec::from([h]));
                a.value_quote(data)
            },
        },
        Code {
            what: "type(&(↑El h, ↑El h))",
            read: Read::Unfolded,
            build: |a, h| {
                let returner = returns_element(a, h);
                let with = a.comp_type_with(&[returner, returner]);
                a.value_quote_computation(with)
            },
        },
        Code {
            what: "type(↑El h with Proc)",
            read: Read::Unfolded,
            build: |a, h| {
                let decoded = element(a, h);
                let signature = proc(a);
                let returner =
                    a.comp_type_returner_with_effects(decoded, EffectRow::singleton(signature));
                a.value_quote_computation(returner)
            },
        },
        Code {
            what: "type(El h → ↑El h)",
            read: Read::Unfolded,
            build: |a, h| {
                let decoded = element(a, h);
                let returner = returns_element(a, h);
                let arrow = a.comp_type_arrow(decoded, returner);
                a.value_quote_computation(arrow)
            },
        },
        Code {
            what: "type(Π El h. ↑El h)",
            read: Read::Unfolded,
            build: |a, h| {
                let decoded = element(a, h);
                let returner = returns_element(a, h);
                let pi = a.comp_type_pi(decoded, returner);
                a.value_quote_computation(pi)
            },
        },
        Code {
            what: "type(codata C(h))",
            read: Read::Unfolded,
            build: |a, h| {
                let codata = a.comp_type_codata(ConstantIndex::from(0_usize), Vec::from([h]));
                a.value_quote_computation(codata)
            },
        },
    ]
}

/// A code over the undefined constant `c` and the same code over another
/// undefined constant `d` are deferred by the search-free steps, which read
/// every constant as one that could unfold; the machine, reading the
/// definitions, finds both rigid and separates them, and declines once `c`
/// has a body. Two copies over `c` convert.
#[test]
fn a_code_over_one_constant_is_apart_from_its_twin_over_another_while_both_are_rigid()
{
    for Code { what, build, .. } in codes() {
        let mut core = CoreArena::new();
        let (c, d) = (
            opaque(&mut core),
            core.value_constant(ConstantIndex::from(4_usize)),
        );
        let copies = [build(&mut core, c), build(&mut core, c)];
        let twins = [build(&mut core, c), build(&mut core, d)];
        let body = core.value_unit();
        let (defined, empty) = (defining(body), LoweredChain::new());
        let mut domain = DomainArena::new();
        let held = twins.map(|side| evaluated(&core, &mut domain, &empty, CoreTerm::Value(side)));
        assert_eq!(
            Settlement::Deferred(Deferral::Unfolding),
            settled(&core, &domain, held),
            "{what}"
        );
        for (chain, pair, verdict) in [
            (&empty, copies, MachineVerdict::Convertible),
            (&empty, twins, MachineVerdict::NotConvertible),
            (
                &defined,
                twins,
                MachineVerdict::Declined(DeclineReason::UndecidedCodes),
            ),
        ] {
            let mut domain = DomainArena::new();
            let held = pair.map(|side| evaluated(&core, &mut domain, chain, CoreTerm::Value(side)));
            assert_eq!(verdict, decided(&core, &mut domain, chain, held), "{what}");
        }
    }
}

/// A code over `c` reads back as it stands without unfolding; read back
/// unfolding, with `c` defined as `type(Integer)`, it is the same code over
/// that definition, each decode of it decoded, except under the native path
/// classifier `≃`, which is spliced as it stands.
#[test]
fn a_code_reads_back_over_its_constant_or_over_the_constant_s_definition()
{
    for Code { what, build, read } in codes() {
        for mode in [ReadbackMode::ZeroUnfold, ReadbackMode::Unfolding] {
            let mut core = CoreArena::new();
            let c = opaque(&mut core);
            let code = build(&mut core, c);
            let integer_type = core.value_type_base(BaseType::Integer);
            let body = core.value_quote(integer_type);
            let expected = match (mode, read) {
                (ReadbackMode::ZeroUnfold, _) | (ReadbackMode::Unfolding, Read::Spliced) => {
                    build(&mut core, c)
                },
                (ReadbackMode::Unfolding, Read::Unfolded) => build(&mut core, body),
            };
            let normal = normalized(&mut core, &defining(body), CoreTerm::Value(code), mode);
            assert_eq!(
                CertificateEquality::Equal,
                same(&mut core, normal, CoreTerm::Value(expected)),
                "{what} in {mode:?}"
            );
        }
    }
}

/// A term holding a constant at one position, built over the constant it is
/// given.
struct Twin
{
    /// The term, over the constant `h`.
    what: &'static str,
    /// Builds the term over the constant it is given.
    build: fn(&mut CoreArena, ValueId) -> CoreTerm,
    /// What the machine decides of the term over `c` against its twin over
    /// `d`.
    apart: MachineVerdict,
}

/// `(static λy. type(y = y in Integer)) bound`: a code whose environment binds
/// `bound`, so comparing two such codes reads the bound values.
///
/// # Specification
/// trivial.
fn bound_in_a_code(
    core: &mut CoreArena,
    bound: ValueId,
) -> CoreTerm
{
    let y = x(core, Index(0));
    let integer_type = core.value_type_base(BaseType::Integer);
    let path = core.value_type_path(integer_type, y, y);
    let code = core.value_quote(path);
    let operator = core.value_static_lambda(code);
    CoreTerm::Value(core.value_static_application(operator, bound))
}

/// Terms that hold a constant under a path former, a flow former, a motive or
/// a static operator.
///
/// # Specification
/// trivial.
fn twins() -> [Twin; 24]
{
    [
        Twin {
            what: "(static λy. type(y = y in Integer)) (1 :: h)",
            apart: MachineVerdict::NotConvertible,
            build: |a, h| {
                let one = integer(a, Digits("1"));
                let cell = a.value_list_cons(one, h);
                bound_in_a_code(a, cell)
            },
        },
        Twin {
            what: "(static λy. type(y = y in Integer)) (h :: nil)",
            apart: MachineVerdict::NotConvertible,
            build: |a, h| {
                let nil = a.value_list_nil();
                let cell = a.value_list_cons(h, nil);
                bound_in_a_code(a, cell)
            },
        },
        Twin {
            what: "transport (y. List(El y)) along equiv(id, id) of h",
            apart: MachineVerdict::NotConvertible,
            build: |a, h| {
                let y = x(a, Index(0));
                let returned = a.computation_return(y);
                let lambda = a.computation_lambda(returned);
                let identity = a.value_thunk(lambda);
                let path = a.value_equiv(identity, identity);
                let element = a.value_type_element(y, Level::zero());
                let motive = a.value_type_list(element);
                CoreTerm::Computation(a.computation_path_transport(motive, path, h))
            },
        },
        Twin {
            what: "(static λy. type(y = y in Integer)) (inl h)",
            apart: MachineVerdict::NotConvertible,
            build: |a, h| {
                let left = a.value_injection(Summand::from(0_usize), h);
                bound_in_a_code(a, left)
            },
        },
        Twin {
            what: "(static λy. type(y = y in Integer)) K(h)",
            apart: MachineVerdict::NotConvertible,
            build: |a, h| {
                let datatype = a.value_type_data(ConstantIndex::from(0_usize), Vec::new());
                let constructed =
                    a.value_constructor(datatype, ConstructorTag::from(0_usize), Vec::from([h]));
                bound_in_a_code(a, constructed)
            },
        },
        Twin {
            what: "h ⊗ h",
            apart: MachineVerdict::NotConvertible,
            build: |a, h| CoreTerm::Value(a.value_path_product(h, h)),
        },
        Twin {
            what: "h ⊗~ h",
            apart: MachineVerdict::NotConvertible,
            build: |a, h| CoreTerm::Value(a.value_flow_product(h, h)),
        },
        Twin {
            what: "refl h",
            apart: MachineVerdict::NotConvertible,
            build: |a, h| CoreTerm::Value(a.value_path_refl(h)),
        },
        Twin {
            what: "here(h)",
            apart: MachineVerdict::NotConvertible,
            build: |a, h| CoreTerm::Value(a.value_here(h)),
        },
        Twin {
            what: "forward(h)",
            apart: MachineVerdict::NotConvertible,
            build: |a, h| CoreTerm::Value(a.value_forward(h)),
        },
        Twin {
            what: "static λy. h",
            apart: MachineVerdict::Declined(DeclineReason::UndecidedCodes),
            build: |a, h| CoreTerm::Value(a.value_static_lambda(h)),
        },
        Twin {
            what: "transport h ()",
            apart: MachineVerdict::NotConvertible,
            build: |a, h| {
                let unit = a.value_unit();
                CoreTerm::Computation(a.computation_transport(h, unit))
            },
        },
        Twin {
            what: "transport (y. El y) along h of ()",
            apart: MachineVerdict::NotConvertible,
            build: |a, h| {
                let unit = a.value_unit();
                let y = x(a, Index(0));
                let motive = a.value_type_element(y, Level::zero());
                CoreTerm::Computation(a.computation_path_transport(motive, h, unit))
            },
        },
        Twin {
            what: "transport (y. El y × El h) along c of ()",
            apart: MachineVerdict::NotConvertible,
            build: |a, h| {
                let held = opaque(a);
                let unit = a.value_unit();
                let y = x(a, Index(0));
                let point = a.value_type_element(y, Level::zero());
                let fixed = a.value_type_element(h, Level::zero());
                let motive = a.value_type_product(&[point, fixed]);
                CoreTerm::Computation(a.computation_path_transport(motive, held, unit))
            },
        },
        Twin {
            what: "ride (y. El y) h ()",
            apart: MachineVerdict::NotConvertible,
            build: |a, h| {
                let unit = a.value_unit();
                let y = x(a, Index(0));
                let motive = a.value_type_element(y, Level::zero());
                CoreTerm::Computation(a.computation_ride(motive, h, unit))
            },
        },
        Twin {
            what: "transport ↑() along c from () over here(()) of h",
            apart: MachineVerdict::NotConvertible,
            build: |a, h| {
                let held = opaque(a);
                let unit = a.value_unit();
                let over = a.value_here(unit);
                let motive = returns_unit(a);
                CoreTerm::Computation(
                    a.computation_telescope_transport(motive, held, unit, over, h),
                )
            },
        },
        Twin {
            what: "transport (y. El y) along c of h",
            apart: MachineVerdict::NotConvertible,
            build: |a, h| {
                let held = opaque(a);
                let y = x(a, Index(0));
                let motive = a.value_type_element(y, Level::zero());
                CoreTerm::Computation(a.computation_path_transport(motive, held, h))
            },
        },
        Twin {
            what: "ride (y. El y) c h",
            apart: MachineVerdict::NotConvertible,
            build: |a, h| {
                let held = opaque(a);
                let y = x(a, Index(0));
                let motive = a.value_type_element(y, Level::zero());
                CoreTerm::Computation(a.computation_ride(motive, held, h))
            },
        },
        Twin {
            what: "transport c h",
            apart: MachineVerdict::NotConvertible,
            build: |a, h| {
                let held = opaque(a);
                CoreTerm::Computation(a.computation_transport(held, h))
            },
        },
        Twin {
            what: "(force c) h",
            apart: MachineVerdict::NotConvertible,
            build: |a, h| {
                let held = opaque(a);
                let forced = a.computation_force(held);
                CoreTerm::Computation(a.computation_application(forced, h))
            },
        },
        Twin {
            what: "c h, statically",
            apart: MachineVerdict::NotConvertible,
            build: |a, h| {
                let held = opaque(a);
                CoreTerm::Value(a.value_static_application(held, h))
            },
        },
        Twin {
            what: "transport (c ⊗ c) h",
            apart: MachineVerdict::NotConvertible,
            build: |a, h| {
                let held = opaque(a);
                let paths = a.value_path_product(held, held);
                CoreTerm::Computation(a.computation_transport(paths, h))
            },
        },
        Twin {
            what: "transport (h ⊗ h) c",
            apart: MachineVerdict::NotConvertible,
            build: |a, h| {
                let held = opaque(a);
                let paths = a.value_path_product(h, h);
                CoreTerm::Computation(a.computation_transport(paths, held))
            },
        },
        Twin {
            what: "transport ↑() along c from h over here(()) of ()",
            apart: MachineVerdict::NotConvertible,
            build: |a, h| {
                let held = opaque(a);
                let unit = a.value_unit();
                let over = a.value_here(unit);
                let motive = returns_unit(a);
                CoreTerm::Computation(
                    a.computation_telescope_transport(motive, held, h, over, unit),
                )
            },
        },
    ]
}

/// Two copies of a term over `c` convert, and the term over `c` against its
/// twin over another undefined constant `d` is never convertible to the
/// search-free steps; the machine separates the two, except under a static
/// lambda, which η could still equate with a stuck operator, so the machine
/// declines it as undecided.
#[test]
fn a_term_over_one_constant_is_apart_from_its_twin_over_another()
{
    for Twin { what, build, apart } in twins() {
        let mut core = CoreArena::new();
        let (c, d) = (
            opaque(&mut core),
            core.value_constant(ConstantIndex::from(4_usize)),
        );
        let copies = [build(&mut core, c), build(&mut core, c)];
        let twins = [build(&mut core, c), build(&mut core, d)];
        let empty = LoweredChain::new();
        let mut domain = DomainArena::new();
        let held = twins.map(|side| evaluated(&core, &mut domain, &empty, side));
        assert_ne!(
            Convertibility::Convertible,
            settled(&core, &domain, held).verdict(),
            "{what}"
        );
        for (pair, verdict) in [(copies, MachineVerdict::Convertible), (twins, apart)] {
            let mut domain = DomainArena::new();
            let held = pair.map(|side| evaluated(&core, &mut domain, &empty, side));
            assert_eq!(verdict, decided(&core, &mut domain, &empty, held), "{what}");
        }
    }
}

/// A constant defined as a code reads back as itself without unfolding, and
/// as the code it is defined as, value type or computation type, when read
/// back unfolding.
#[test]
fn a_constant_defined_as_a_code_reads_back_as_that_code_once_unfolded()
{
    let definitions: [fn(&mut CoreArena) -> ValueId; 2] = [
        |a| {
            let integer_type = a.value_type_base(BaseType::Integer);
            a.value_quote(integer_type)
        },
        |a| {
            let returner = returns_unit(a);
            a.value_quote_computation(returner)
        },
    ];
    for definition in definitions {
        for mode in [ReadbackMode::ZeroUnfold, ReadbackMode::Unfolding] {
            let mut core = CoreArena::new();
            let c = opaque(&mut core);
            let body = definition(&mut core);
            let expected = match mode {
                ReadbackMode::ZeroUnfold => c,
                ReadbackMode::Unfolding => definition(&mut core),
            };
            let normal = normalized(&mut core, &defining(body), CoreTerm::Value(c), mode);
            assert_eq!(
                CertificateEquality::Equal,
                same(&mut core, normal, CoreTerm::Value(expected)),
                "{mode:?}"
            );
        }
    }
}

/// Transport along a product of paths over an undefined operand stands on
/// the operand, and reads back as the transport it is, in either mode.
#[test]
fn a_product_transport_over_a_stuck_operand_reads_back_as_written()
{
    for mode in [ReadbackMode::ZeroUnfold, ReadbackMode::Unfolding] {
        let mut core = CoreArena::new();
        let build = |a: &mut CoreArena| {
            let held = opaque(a);
            let other = a.value_constant(ConstantIndex::from(4_usize));
            let paths = a.value_path_product(other, other);
            CoreTerm::Computation(a.computation_transport(paths, held))
        };
        let term = build(&mut core);
        let expected = build(&mut core);
        let normal = normalized(&mut core, &LoweredChain::new(), term, mode);
        assert_eq!(
            CertificateEquality::Equal,
            same(&mut core, normal, expected),
            "{mode:?}"
        );
    }
}

/// A stuck function is its own η-expansion: the machine decides `force c`
/// convertible with `λx. (force c) x` on either side, and apart from
/// `λx. (force d) x` over another undefined constant.
#[test]
fn a_stuck_function_converts_with_its_eta_expansion()
{
    let mut core = CoreArena::new();
    let c = opaque(&mut core);
    let d = core.value_constant(ConstantIndex::from(4_usize));
    let mut expanded = |head| {
        let forced = core.computation_force(head);
        let bound = x(&mut core, Index(0));
        let applied = core.computation_application(forced, bound);
        CoreTerm::Computation(core.computation_lambda(applied))
    };
    let (over_c, over_d) = (expanded(c), expanded(d));
    let stuck = CoreTerm::Computation(core.computation_force(c));
    let empty = LoweredChain::new();
    for (pair, verdict) in [
        ([stuck, over_c], MachineVerdict::Convertible),
        ([over_c, stuck], MachineVerdict::Convertible),
        ([stuck, over_d], MachineVerdict::NotConvertible),
    ] {
        let mut domain = DomainArena::new();
        let held = pair.map(|side| evaluated(&core, &mut domain, &empty, side));
        assert_eq!(verdict, decided(&core, &mut domain, &empty, held));
    }
}

/// A static operator returning a code, applied, reads back as the code with
/// the argument in place of the bound variable, in either mode: the code over
/// `1 :: c` is `type(1 :: c = 1 :: c in Integer)`.
#[test]
fn a_code_under_a_static_operator_reads_back_with_its_argument_in_place()
{
    for mode in [ReadbackMode::ZeroUnfold, ReadbackMode::Unfolding] {
        let mut core = CoreArena::new();
        let c = opaque(&mut core);
        let one = integer(&mut core, Digits("1"));
        let cell = core.value_list_cons(one, c);
        let term = bound_in_a_code(&mut core, cell);
        let integer_type = core.value_type_base(BaseType::Integer);
        let path = core.value_type_path(integer_type, cell, cell);
        let expected = CoreTerm::Value(core.value_quote(path));
        let normal = normalized(&mut core, &LoweredChain::new(), term, mode);
        assert_eq!(
            CertificateEquality::Equal,
            same(&mut core, normal, expected),
            "{mode:?}"
        );
    }
}

/// Transport refuses what is no path: along the unit, along a product of
/// paths over the unit, and along a product of paths over a literal.
#[test]
fn transport_along_what_is_no_path_or_over_what_no_product_moves_is_refused()
{
    let builds: [fn(&mut CoreArena) -> ComputationId; 3] = [
        |a| {
            let unit = a.value_unit();
            a.computation_transport(unit, unit)
        },
        |a| {
            let held = opaque(a);
            let paths = a.value_path_product(held, held);
            let unit = a.value_unit();
            a.computation_transport(paths, unit)
        },
        |a| {
            let held = opaque(a);
            let paths = a.value_path_product(held, held);
            let one = integer(a, Digits("1"));
            a.computation_transport(paths, one)
        },
    ];
    for build in builds {
        let mut core = CoreArena::new();
        let transported = build(&mut core);
        let chain = LoweredChain::new();
        let environment = DefinitionalEnvironment::new();
        let definitions = Definitions::new(&chain, &environment, environment.root());
        let refused = eval_computation(
            &core,
            &mut DomainArena::new(),
            definitions,
            Fuel::from(4_096_u32),
            transported,
        );
        assert!(
            matches!(refused, Err(EvalFault::TransportedNonPath)),
            "{refused:?}"
        );
    }
}
