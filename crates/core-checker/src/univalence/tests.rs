use alloc::vec::Vec;

use gandr_core_term::CertificateEquality;
use gandr_core_term::CoreArena;
use gandr_core_term::Sort;
use gandr_core_term::ValueId;
use gandr_core_term::ValueTypeId;
use gandr_core_term::Zone;
use gandr_core_term::equal_certificate_syntax;
use gandr_core_term::identity::bi_invertible;
use gandr_core_term::identity::univalence_forward;
use gandr_kernel_strata::Level;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::GroundSort;
use quenchant_shape::shape::Maybe;

use crate::bridge::Outcome;
use crate::bridge::Readmission;
use crate::bridge::readmit;
use crate::context::CheckBudget;
use crate::context::CheckingContext;
use crate::declaration::Declaration;
use crate::declaration::OriginToken;
use crate::declaration::signature;
use crate::module::ModuleReport;
use crate::module::Verdict;
use crate::module::check_module;
use crate::refusal::CheckRefusal;
use crate::refusal::ExpectedShape;

/// A declaration position in a fixture module.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
struct At(usize);

/// A de Bruijn index in a fixture term.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
struct Index(u32);

/// How many binders a fixture abstraction stands under.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
struct Binders(usize);

/// Whether the kernel admitted the declarations a witness names.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Admission
{
    /// Each was admitted as a definition.
    Defined,
    /// One was not.
    Withheld,
}

/// The declaration at `position`, signed `declared` when one is given, its
/// origin the position itself.
///
/// # Specification
/// trivial.
fn declaration(
    At(position): At,
    declared: Maybe<ValueTypeId, signature::Absent>,
    defined: ValueId,
) -> Declaration
{
    Declaration::new(
        ConstantIndex::from(position),
        declared,
        Maybe::Present(defined),
        OriginToken::from(position),
    )
}

/// `module`, judged and offered to the kernel.
///
/// # Specification
/// trivial.
fn judged(
    arena: &mut CoreArena,
    module: &[Declaration],
) -> (ModuleReport, Readmission)
{
    let report = {
        let mut context = CheckingContext::new(arena, CheckBudget::DEFAULT);
        check_module(&mut context, module)
    };
    let readmission = readmit(arena, &report);
    (report, readmission)
}

/// The verdict at `position` of `report`.
///
/// # Specification
/// trivial.
fn verdict(
    report: &ModuleReport,
    At(position): At,
) -> Verdict
{
    report.judged()[position].verdict()
}

/// Whether the kernel admitted the declarations at `positions` as
/// definitions.
///
/// # Specification
/// trivial.
fn defined(
    readmission: &Readmission,
    positions: &[At],
) -> Admission
{
    let all = positions.iter().all(|&At(position)| {
        matches!(
            readmission.readmitted()[position].outcome(),
            Outcome::Defined { .. }
        )
    });
    if all {
        Admission::Defined
    }
    else {
        Admission::Withheld
    }
}

/// The intuitionistic variable at `index`.
///
/// # Specification
/// trivial.
fn variable(
    arena: &mut CoreArena,
    Index(index): Index,
) -> ValueId
{
    arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(index))
}

/// The value universe `Type` at level zero.
///
/// # Specification
/// trivial.
fn universe(arena: &mut CoreArena) -> ValueTypeId
{
    arena.value_type_universe(Sort::Ground(GroundSort::Value), Level::zero())
}

/// The decode `El #index` at level zero.
///
/// # Specification
/// trivial.
fn decoded(
    arena: &mut CoreArena,
    index: Index,
) -> ValueTypeId
{
    let code = variable(arena, index);
    arena.value_type_element(code, Level::zero())
}

/// The map `thunk (λx. body)`, `body` reading the bound point as `#0`.
///
/// # Specification
/// trivial.
fn map(
    arena: &mut CoreArena,
    body: fn(&mut CoreArena, ValueId) -> ValueId,
) -> ValueId
{
    let point = variable(arena, Index(0));
    let image = body(arena, point);
    let returned = arena.computation_return(image);
    let lambda = arena.computation_lambda(returned);
    arena.value_thunk(lambda)
}

/// The record `#{to, #{#{g, law}, #{h, law}}}`, each law reflexivity at the
/// bound point.
///
/// # Specification
/// trivial.
fn record(
    arena: &mut CoreArena,
    [to, g, h]: [ValueId; 3],
) -> ValueId
{
    let law = map(arena, CoreArena::value_here);
    let left = arena.value_tuple(&[g, law]);
    let right = arena.value_tuple(&[h, law]);
    let inverses = arena.value_tuple(&[left, right]);
    arena.value_tuple(&[to, inverses])
}

/// `ua(record)`, carrying the forward map the lowering derives.
///
/// # Specification
/// trivial.
fn univalence(
    arena: &mut CoreArena,
    record: ValueId,
) -> ValueId
{
    let forward = univalence_forward(arena, record);
    arena.value_univalence(record, forward)
}

/// `U ((x : domain) → body)` for each domain in turn, outermost first.
///
/// # Specification
/// trivial.
fn function(
    arena: &mut CoreArena,
    domains: &[ValueTypeId],
    result: ValueTypeId,
) -> ValueTypeId
{
    let returner = arena.comp_type_returner(result);
    let body = domains.iter().rev().fold(returner, |codomain, &domain| {
        arena.comp_type_pi(domain, codomain)
    });
    arena.value_type_thunk(body)
}

/// `thunk (λ … λ. return value)` under `binders` binders.
///
/// # Specification
/// trivial.
fn abstraction(
    arena: &mut CoreArena,
    Binders(binders): Binders,
    value: ValueId,
) -> ValueId
{
    let returned = arena.computation_return(value);
    let body = (0 .. binders).fold(returned, |body, _| arena.computation_lambda(body));
    arena.value_thunk(body)
}

/// The list of booleans, a recursive type outside the first-order stratum
/// `equiv` decides.
///
/// # Specification
/// trivial.
fn booleans_list(arena: &mut CoreArena) -> ValueTypeId
{
    let unit = arena.value_type_unit();
    let boolean = arena.value_type_sum(&[unit, unit]);
    arena.value_type_list(boolean)
}

#[test]
fn ua_is_admitted_on_the_record_s_laws_beyond_the_first_order_stratum()
{
    let mut arena = CoreArena::new();
    let list = booleans_list(&mut arena);
    let code = arena.value_quote(list);
    let at_type = universe(&mut arena);
    let identity = arena.value_type_path(at_type, code, code);
    let same = map(&mut arena, |_, point| point);
    let written = record(&mut arena, [same, same, same]);
    let record_type = bi_invertible(&mut arena, list, list);

    // `e : List Bool ≃ List Bool`, checked at its type.
    let named = declaration(At(0), Maybe::Present(record_type), written);
    // `ua(#{…}) : Path(Type, ⌜List Bool⌝, ⌜List Bool⌝)`, the literal checked
    // against the record type the identity names.
    let literal = univalence(&mut arena, written);
    let checked = declaration(At(1), Maybe::Present(identity), literal);
    // `ua(e)`, unsigned: the identity synthesised from the record's type.
    let constant = arena.value_constant(ConstantIndex::from(0_usize));
    let along = univalence(&mut arena, constant);
    let synthesised = declaration(At(2), Maybe::Absent(signature::Absent::Unsigned), along);
    // `(a b : Type) (e : El a ≃ El b) => Path(Type, a, b)`, `ua(e)`: a decoded
    // variable code crosses as the variable.
    let decoded_record = {
        let from = decoded(&mut arena, Index(1));
        let to = decoded(&mut arena, Index(0));
        bi_invertible(&mut arena, from, to)
    };
    let between = {
        let left = variable(&mut arena, Index(2));
        let right = variable(&mut arena, Index(1));
        let at_type = universe(&mut arena);
        arena.value_type_path(at_type, left, right)
    };
    let open = function(&mut arena, &[at_type, at_type, decoded_record], between);
    let bound = variable(&mut arena, Index(0));
    let along_bound = univalence(&mut arena, bound);
    let body = abstraction(&mut arena, Binders(3), along_bound);
    let parametric = declaration(At(3), Maybe::Present(open), body);

    let (report, readmission) = judged(&mut arena, &[named, checked, synthesised, parametric]);
    for position in [At(0), At(1), At(3)] {
        assert!(
            matches!(verdict(&report, position), Verdict::Checked { .. }),
            "{position:?} checks: {report:?}"
        );
    }
    let Verdict::Synthesised { synthesised, .. } = verdict(&report, At(2))
    else {
        panic!("an unsigned `ua` synthesises its identity: {report:?}");
    };
    let produced = arena.value_quote(synthesised.produced().id());
    let written = arena.value_quote(identity);
    assert_eq!(
        equal_certificate_syntax(&arena, produced, written),
        CertificateEquality::Equal,
        "the identity relates the quotes of the record's types"
    );
    assert_eq!(
        defined(&readmission, &[At(0), At(1), At(2), At(3)]),
        Admission::Defined,
        "the kernel admits each on the record alone: {:?}",
        readmission.readmitted()
    );

    // A carried map other than the record's is malformed core; a record that
    // synthesises no dependent pair names no codes, nor one whose first
    // component is no map.
    let negated = map(&mut arena, |arena, point| {
        arena.value_injection(1_usize.into(), point)
    });
    let forged = arena.value_univalence(written, negated);
    let unit = arena.value_unit();
    let bare = univalence(&mut arena, unit);
    let unit_type = arena.value_type_unit();
    let pair_type = arena.value_type_sigma(unit_type, unit_type);
    let pair = arena.value_tuple(&[unit, unit]);
    let paired = arena.value_constant(ConstantIndex::from(2_usize));
    let mapless = univalence(&mut arena, paired);
    let (report, _) = judged(&mut arena, &[
        declaration(At(0), Maybe::Present(identity), forged),
        declaration(At(1), Maybe::Absent(signature::Absent::Unsigned), bare),
        declaration(At(2), Maybe::Present(pair_type), pair),
        declaration(At(3), Maybe::Absent(signature::Absent::Unsigned), mapless),
    ]);
    assert_eq!(
        verdict(&report, At(0)),
        Verdict::Refused(CheckRefusal::MachineInvariant)
    );
    assert!(
        matches!(
            verdict(&report, At(1)),
            Verdict::Refused(CheckRefusal::ShapeMismatch {
                wanted: ExpectedShape::Sigma,
                ..
            })
        ),
        "{report:?}"
    );
    assert!(
        matches!(
            verdict(&report, At(3)),
            Verdict::Refused(CheckRefusal::ShapeMismatch {
                wanted: ExpectedShape::Thunk,
                ..
            })
        ),
        "{report:?}"
    );
}

#[test]
fn a_record_whose_law_fails_does_not_build_a_path()
{
    // Over the booleans, negation with the identity as its left inverse: the
    // section reads `id(not(x))` against `x`.
    let mut arena = CoreArena::new();
    let unit = arena.value_type_unit();
    let boolean = arena.value_type_sum(&[unit, unit]);
    let code = arena.value_quote(boolean);
    let at_type = universe(&mut arena);
    let identity = arena.value_type_path(at_type, code, code);
    let same = map(&mut arena, |_, point| point);
    let not = {
        let point = variable(&mut arena, Index(0));
        let empty = arena.value_unit();
        let [truth, falsity] = [0_usize, 1_usize].map(|summand| {
            let injected = arena.value_injection(summand.into(), empty);
            arena.computation_return(injected)
        });
        let case = arena.computation_case(point, &[falsity, truth]);
        let lambda = arena.computation_lambda(case);
        arena.value_thunk(lambda)
    };
    let failing = record(&mut arena, [not, same, not]);
    let refused = univalence(&mut arena, failing);
    let holding = record(&mut arena, [same, same, same]);
    let admitted_path = univalence(&mut arena, holding);
    // `(a b : Type) => Path(Type, a, b)`, `ua` of the identity record: the
    // codes read as decodes, and the identity map is no map `El a → El b`.
    let between = {
        let left = variable(&mut arena, Index(1));
        let right = variable(&mut arena, Index(0));
        arena.value_type_path(at_type, left, right)
    };
    let open = function(&mut arena, &[at_type, at_type], between);
    let across = univalence(&mut arena, holding);
    let body = abstraction(&mut arena, Binders(2), across);

    let (report, readmission) = judged(&mut arena, &[
        declaration(At(0), Maybe::Present(identity), admitted_path),
        declaration(At(1), Maybe::Present(identity), refused),
        declaration(At(2), Maybe::Present(open), body),
    ]);
    assert!(
        matches!(verdict(&report, At(0)), Verdict::Checked { .. }),
        "laws that hold build the path: {report:?}"
    );
    assert!(
        matches!(
            verdict(&report, At(1)),
            Verdict::Refused(CheckRefusal::EndpointMismatch { .. })
        ),
        "a section that fails is a field that does not check: {report:?}"
    );
    assert!(
        matches!(
            verdict(&report, At(2)),
            Verdict::Refused(CheckRefusal::TypeMismatch(_))
        ),
        "the identity's maps relate no two distinct decodes: {report:?}"
    );
    assert_eq!(
        defined(&readmission, &[At(0)]),
        Admission::Defined,
        "the kernel admits what checked: {:?}",
        readmission.readmitted()
    );
}

#[test]
fn transport_along_ua_computes_the_forward_map()
{
    // `(A : Type) (e : El A ≃ El A) (x : El A)`: transport in the decoded
    // binder along `ua(e)` is the forward map applied to `x`, not `x`.
    let mut arena = CoreArena::new();
    let at_type = universe(&mut arena);
    let record_type = {
        let carrier = decoded(&mut arena, Index(0));
        bi_invertible(&mut arena, carrier, carrier)
    };
    let point_type = decoded(&mut arena, Index(1));
    let carrier = decoded(&mut arena, Index(2));
    let transported = {
        let record = variable(&mut arena, Index(1));
        let path = univalence(&mut arena, record);
        let motive = decoded(&mut arena, Index(0));
        let point = variable(&mut arena, Index(0));
        let transport = arena.computation_path_transport(motive, path, point);
        arena.value_returned(transport)
    };
    let applied = {
        let record = variable(&mut arena, Index(1));
        let projected =
            arena.computation_tuple_projection(record, gandr_core_term::Component::from(0_usize));
        let forward = variable(&mut arena, Index(0));
        let forced = arena.computation_force(forward);
        let point = variable(&mut arena, Index(1));
        let application = arena.computation_application(forced, point);
        let bound = arena.computation_bind(projected, application);
        arena.value_returned(bound)
    };
    let unmoved = variable(&mut arena, Index(0));
    let mut module = Vec::new();
    for (position, right) in [applied, unmoved].into_iter().enumerate() {
        let path = arena.value_type_path(carrier, transported, right);
        let declared = function(&mut arena, &[at_type, record_type, point_type], path);
        let here = arena.value_here(transported);
        let body = abstraction(&mut arena, Binders(3), here);
        module.push(declaration(At(position), Maybe::Present(declared), body));
    }

    let (report, readmission) = judged(&mut arena, &module);
    assert!(
        matches!(verdict(&report, At(0)), Verdict::Checked { .. }),
        "the transport converts with the forward map applied: {report:?}"
    );
    assert!(
        matches!(
            verdict(&report, At(1)),
            Verdict::Refused(CheckRefusal::EndpointMismatch { .. })
        ),
        "and not with the point it moved: {report:?}"
    );
    assert_eq!(
        defined(&readmission, &[At(0)]),
        Admission::Defined,
        "the kernel computes the same transport: {:?}",
        readmission.readmitted()
    );
}
