//! Codata declarations: admission, reading through observations, the guard on
//! self reference, kernel readmission and adoption.

use alloc::sync::Arc;

use anodized::spec;
use gandr_core_checker::CheckBudget;
use gandr_core_checker::CheckRefusal;
use gandr_core_checker::CheckingContext;
use gandr_core_checker::CoreNode;
use gandr_core_checker::Declaration;
use gandr_core_checker::DeclarationContent;
use gandr_core_checker::ExpectedShape;
use gandr_core_checker::ModuleReport;
use gandr_core_checker::OriginToken;
use gandr_core_checker::TypeNode;
use gandr_core_checker::Verdict;
use gandr_core_checker::bridge;
use gandr_core_checker::bridge::Outcome;
use gandr_core_checker::check_declaration;
use gandr_core_checker::check_declaration_supported;
use gandr_core_checker::check_module;
use gandr_core_checker::codata::CodataFault;
use gandr_core_term::CodataSignature;
use gandr_core_term::CompTypeId;
use gandr_core_term::CoreArena;
use gandr_core_term::DataSignature;
use gandr_core_term::Sort;
use gandr_core_term::ValueId;
use gandr_core_term::ValueTypeId;
use gandr_core_term::Zone;
use gandr_kernel_strata::Level;
use gandr_kernel_term::Component;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::FixpointEvidence;
use gandr_kernel_term::GroundSort;
use quenchant_shape::shape::Maybe;

/// A definition at its source position.
///
/// # Specification
/// trivial.
fn definition(
    constant: ConstantIndex,
    declared: ValueTypeId,
    body: ValueId,
) -> Declaration
{
    Declaration::new(
        constant,
        Maybe::Present(declared),
        Maybe::Present(body),
        OriginToken::from(usize::from(constant)),
    )
}

/// A codata declaration at its source position.
///
/// # Specification
/// trivial.
fn codata(
    constant: ConstantIndex,
    signature: CodataSignature,
) -> Declaration
{
    Declaration::codata(
        constant,
        Arc::new(signature),
        OriginToken::from(usize::from(constant)),
    )
}

/// Run the producer and its independent kernel boundary.
///
/// # Specification
/// - requires: declaration ids refer to `arena`.
/// - ensures: each source position has a producer verdict and a boundary
///   outcome.
/// - panics: only if a called judgment violates its contract.
///
/// # Adequacy
/// - hypothesis: L3 — the witnesses inspect exact verdicts and outcomes.
/// - witness: `tests::codata::a_stream_is_admitted_observed_and_adopted`
#[spec(ensures: |ret| ret.0.judged().len() == declarations.len() && ret.1.readmitted().len() == declarations.len())]
fn run(
    arena: &mut CoreArena,
    declarations: &[Declaration],
) -> (ModuleReport, bridge::Readmission)
{
    let report = check_module(
        &mut CheckingContext::new(arena, CheckBudget::DEFAULT),
        declarations,
    );
    let crossed = bridge::readmit(arena, &report);
    (report, crossed)
}

/// `Stream(A : Type) : CompType` with `head : F A` and the observation `tail`
/// builds at the parameter variable.
///
/// # Specification
/// trivial.
fn stream<Tail>(
    arena: &mut CoreArena,
    tail: Tail,
) -> CodataSignature
where
    Tail: FnOnce(&mut CoreArena, ValueId) -> CompTypeId,
{
    let parameter_kind = arena.value_type_universe(Sort::Ground(GroundSort::Value), Level::zero());
    let kind = arena.value_type_universe(Sort::Ground(GroundSort::Computation), Level::zero());
    let parameter = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let element = arena.value_type_element(parameter, Level::zero());
    let head = arena.comp_type_returner(element);
    let tail = tail(arena, parameter);
    CodataSignature::new(vec![parameter_kind], vec![head, tail], kind)
}

/// The stream of units, `ones = fix s. return () & force s`, at `Stream(Unit)`.
///
/// # Specification
/// trivial.
fn ones(
    arena: &mut CoreArena,
    family: ConstantIndex,
) -> (ValueTypeId, ValueId)
{
    let unit_type = arena.value_type_unit();
    let unit_code = arena.value_quote(unit_type);
    let units = arena.comp_type_codata(family, vec![unit_code]);
    let declared = arena.value_type_thunk(units);
    let unit = arena.value_unit();
    let head = arena.computation_return(unit);
    let own = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let tail = arena.computation_force(own);
    let pair = arena.computation_with(&[head, tail]);
    let fixpoint = arena.computation_fixpoint(pair, FixpointEvidence::Partial);
    (declared, arena.value_thunk(fixpoint))
}

#[test]
fn a_stream_is_admitted_observed_and_adopted()
{
    let mut arena = CoreArena::new();
    let family = ConstantIndex::from(0_usize);
    let signature = stream(&mut arena, |arena, parameter| {
        arena.comp_type_codata(family, vec![parameter])
    });
    let declaration = codata(family, signature);
    let (declared, body) = ones(&mut arena, family);
    let use_site = definition(ConstantIndex::from(1_usize), declared, body);
    // `second = π₁ (π₂ (force ones)) : F Unit` reads the tail's type through
    // its observations again.
    let ones_constant = arena.value_constant(ConstantIndex::from(1_usize));
    let forced = arena.computation_force(ones_constant);
    let tail = arena.computation_project(Component::from(1_usize), forced);
    let second = arena.computation_project(Component::from(0_usize), tail);
    let unit_type = arena.value_type_unit();
    let returner = arena.comp_type_returner(unit_type);
    let second_type = arena.value_type_thunk(returner);
    let second_body = arena.value_thunk(second);
    let declarations = [
        declaration.clone(),
        use_site.clone(),
        definition(ConstantIndex::from(2_usize), second_type, second_body),
    ];
    let (report, crossed) = run(&mut arena, &declarations);
    assert_eq!(report.judged()[0].verdict(), Verdict::Data);
    for position in [1_usize, 2] {
        assert!(
            matches!(report.judged()[position].verdict(), Verdict::Checked { .. }),
            "{:?}",
            report.judged()[position].verdict()
        );
        assert!(
            matches!(
                crossed.readmitted()[position].outcome(),
                Outcome::Defined { .. }
            ),
            "{:?}",
            crossed.readmitted()[position].outcome()
        );
    }
    assert!(
        matches!(crossed.readmitted()[0].outcome(), Outcome::Data { admitted, .. } if admitted.position() == family),
        "{:?}",
        crossed.readmitted()[0].outcome()
    );
    assert!(crossed.audit().axioms().is_empty());

    let fresh = {
        let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        assert_eq!(check_declaration(&mut context, &declaration), Verdict::Data);
        check_declaration_supported(&mut context, &use_site)
    };
    let DeclarationContent::Codata(ref signature) = *(declaration.content())
    else {
        panic!("a codata signature");
    };
    let adopted = {
        let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        context.adopt_codata(family, Arc::clone(signature)).unwrap();
        check_declaration_supported(&mut context, &use_site)
    };
    assert!(matches!(adopted.verdict(), Verdict::Checked { .. }));
    assert_eq!(fresh.verdict(), adopted.verdict());
    assert_eq!(fresh.support(), adopted.support());
    let [ref answer] = *(fresh.support().codata_consulted())
    else {
        panic!("one codata consultation despite formation and reading");
    };
    assert_eq!(answer.constant(), family);
    assert_eq!(answer.signature(), Some(signature.as_ref()));
}

#[test]
fn a_single_observation_reads_as_a_lazy_product_of_one()
{
    let mut arena = CoreArena::new();
    let family = ConstantIndex::from(0_usize);
    let unit_type = arena.value_type_unit();
    let returner = arena.comp_type_returner(unit_type);
    let kind = arena.value_type_universe(Sort::Ground(GroundSort::Computation), Level::zero());
    let boxed = arena.comp_type_codata(family, vec![]);
    let boxed_type = arena.value_type_thunk(boxed);
    let unit = arena.value_unit();
    let returned = arena.computation_return(unit);
    let product = arena.computation_with(&[returned]);
    let body = arena.value_thunk(product);
    let unwrapped = arena.value_thunk(returned);
    // `b : U Box = thunk &{.0 => return ()}`, then `x ← (force b).0; return
    // x : F Unit` reads the box through its one observation; `force b : F
    // Unit` meets no η, and `thunk (return ())` is not the box.
    let held = arena.value_constant(ConstantIndex::from(1_usize));
    let forced = arena.computation_force(held);
    let observed = arena.computation_project(Component::from(0_usize), forced);
    let bound = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let rest = arena.computation_return(bound);
    let unboxed = arena.computation_bind(observed, rest);
    let unboxed = arena.value_thunk(unboxed);
    let bare = arena.computation_force(held);
    let bare = arena.value_thunk(bare);
    let returner_type = arena.value_type_thunk(returner);
    let declarations = [
        codata(family, CodataSignature::new(vec![], vec![returner], kind)),
        definition(ConstantIndex::from(1_usize), boxed_type, body),
        definition(ConstantIndex::from(2_usize), returner_type, unboxed),
        definition(ConstantIndex::from(3_usize), returner_type, bare),
        definition(ConstantIndex::from(4_usize), boxed_type, unwrapped),
    ];
    let (report, crossed) = run(&mut arena, &declarations);
    assert_eq!(report.judged()[0].verdict(), Verdict::Data);
    for position in [1_usize, 2] {
        assert!(
            matches!(report.judged()[position].verdict(), Verdict::Checked { .. }),
            "{:?}",
            report.judged()[position].verdict()
        );
        assert!(
            matches!(
                crossed.readmitted()[position].outcome(),
                Outcome::Defined { .. }
            ),
            "{:?}",
            crossed.readmitted()[position].outcome()
        );
    }
    assert!(
        matches!(
            report.judged()[3].verdict(),
            Verdict::Refused(CheckRefusal::TypeMismatch(_))
        ),
        "{:?}",
        report.judged()[3].verdict()
    );
    assert!(
        matches!(
            report.judged()[4].verdict(),
            Verdict::Refused(CheckRefusal::ShapeMismatch {
                wanted: ExpectedShape::Returner,
                ..
            })
        ),
        "a return checked at the box meets a lazy product, not a returner: {:?}",
        report.judged()[4].verdict()
    );
}

#[test]
fn a_value_universe_is_no_codata_kind()
{
    let mut arena = CoreArena::new();
    let family = ConstantIndex::from(0_usize);
    let unit_type = arena.value_type_unit();
    let returner = arena.comp_type_returner(unit_type);
    let kind = arena.value_type_universe(Sort::Ground(GroundSort::Value), Level::zero());
    let declarations = [codata(
        family,
        CodataSignature::new(vec![], vec![returner], kind),
    )];
    let (report, _crossed) = run(&mut arena, &declarations);
    assert_eq!(
        report.judged()[0].verdict(),
        Verdict::Refused(CheckRefusal::Codata {
            at: CoreNode::Type(TypeNode::Value(kind)),
            fault: CodataFault::KindNotUniverse,
        })
    );
}

#[test]
fn a_self_reference_off_an_observations_result_is_refused()
{
    let mut arena = CoreArena::new();
    let family = ConstantIndex::from(0_usize);
    // `tail : U Stream(A) → F A`: the declaration in a domain.
    let mut in_domain = None;
    let domain = stream(&mut arena, |arena, parameter| {
        let own = arena.comp_type_codata(family, vec![parameter]);
        in_domain = Some(own);
        let thunk = arena.value_type_thunk(own);
        let element = arena.value_type_element(parameter, Level::zero());
        let returner = arena.comp_type_returner(element);
        arena.comp_type_arrow(thunk, returner)
    });
    // `tail : Stream(Unit)`: the declaration at another argument.
    let mut elsewhere = None;
    let other_argument = stream(&mut arena, |arena, _parameter| {
        let unit_type = arena.value_type_unit();
        let unit_code = arena.value_quote(unit_type);
        let own = arena.comp_type_codata(family, vec![unit_code]);
        elsewhere = Some(own);
        own
    });
    for (signature, at) in [(domain, in_domain), (other_argument, elsewhere)] {
        let at = at.expect("the self reference was built");
        let (report, _crossed) = run(&mut arena, &[codata(family, signature)]);
        assert_eq!(
            report.judged()[0].verdict(),
            Verdict::Refused(CheckRefusal::Codata {
                at: CoreNode::Type(TypeNode::Computation(at)),
                fault: CodataFault::Occurrence,
            })
        );
    }
}

#[test]
fn a_codata_application_names_an_admitted_declaration_at_its_arity()
{
    let mut arena = CoreArena::new();
    let data = ConstantIndex::from(0_usize);
    let family = ConstantIndex::from(1_usize);
    let unit_type = arena.value_type_unit();
    let data_kind = arena.value_type_universe(Sort::Ground(GroundSort::Value), Level::zero());
    let signature = stream(&mut arena, |arena, parameter| {
        arena.comp_type_codata(family, vec![parameter])
    });
    let unit_code = arena.value_quote(unit_type);
    let wide = arena.comp_type_codata(family, vec![unit_code, unit_code]);
    let wide_type = arena.value_type_thunk(wide);
    let undeclared = arena.comp_type_codata(data, vec![]);
    let undeclared_type = arena.value_type_thunk(undeclared);
    let (declared, body) = ones(&mut arena, family);
    let declarations = [
        Declaration::data(
            data,
            DataSignature::new(vec![], vec![vec![]], data_kind).into(),
            OriginToken::from(0_usize),
        ),
        codata(family, signature),
        definition(ConstantIndex::from(2_usize), declared, body),
        definition(ConstantIndex::from(3_usize), wide_type, body),
        definition(ConstantIndex::from(4_usize), undeclared_type, body),
    ];
    let (report, _crossed) = run(&mut arena, &declarations);
    assert!(
        matches!(report.judged()[2].verdict(), Verdict::Checked { .. }),
        "{:?}",
        report.judged()[2].verdict()
    );
    assert_eq!(
        report.judged()[3].verdict(),
        Verdict::Refused(CheckRefusal::Codata {
            at: CoreNode::Type(TypeNode::Computation(wide)),
            fault: CodataFault::Arity,
        })
    );
    assert_eq!(
        report.judged()[4].verdict(),
        Verdict::Refused(CheckRefusal::Codata {
            at: CoreNode::Type(TypeNode::Computation(undeclared)),
            fault: CodataFault::Undeclared,
        })
    );
}
