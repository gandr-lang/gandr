//! Modules judged, then readmitted through the bridge: runs, record updates,
//! patched types, models and literals as the kernel reads them.

use alloc::vec::Vec;

use gandr_core_checker_base::context::CheckBudget;
use gandr_core_checker_base::context::CheckingContext;
use gandr_core_checker_base::fixture::integer_literal;
use gandr_core_checker_base::fixture::module::At;
use gandr_core_checker_base::fixture::module::HOLE;
use gandr_core_checker_base::fixture::module::UNSIGNED;
use gandr_core_checker_base::fixture::module::call;
use gandr_core_checker_base::fixture::module::declaration;
use gandr_core_checker_base::fixture::module::integer_function;
use gandr_core_checker_base::fixture::module::naturals;
use gandr_core_checker_base::fixture::module::read_literal;
use gandr_core_checker_base::fixture::text_literal;
use gandr_core_checker_base::module::check_module;
use gandr_core_checker_base::nested::Nesting;
use gandr_core_checker_base::refusal::CheckRefusal;
use gandr_core_checker_base::report::Verdict;
use gandr_core_term::CoreArena;
use gandr_core_term::Sort;
use gandr_core_term::ValueId;
use gandr_core_term::ValueTypeId;
use gandr_core_term::effect::Purity;
use gandr_kernel_strata::Level;
use gandr_kernel_term::BaseType;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::GroundSort;
use quenchant_shape::shape::Maybe;

#[test]
fn a_nested_run_elaborates_into_a_bind_before_its_region()
{
    let mut arena = CoreArena::new();
    let (function, identity) = integer_function(&mut arena);
    let [inner_x, expected_x, expected_inner_r] = [(); 3].map(|()| {
        arena.value_variable(
            gandr_core_term::Zone::Intuitionistic,
            DeBruijnIndex::from(0_u32),
        )
    });
    let inner = call(&mut arena, ConstantIndex::from(0_usize), inner_x);
    let inner = arena.value_nested(inner);
    let outer = call(&mut arena, ConstantIndex::from(0_usize), inner);
    let outer = arena.value_nested(outer);
    let returned = arena.computation_return(outer);
    let lambda = arena.computation_lambda(returned);
    let twice = arena.value_thunk(lambda);
    let expected = {
        let first = call(&mut arena, ConstantIndex::from(0_usize), expected_x);
        let second = call(&mut arena, ConstantIndex::from(0_usize), expected_inner_r);
        let ran = arena.computation_bind(first, second);
        let lambda = arena.computation_lambda(ran);
        arena.value_thunk(lambda)
    };
    let report = {
        let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        check_module(&mut context, &[
            declaration(At(0), Maybe::Present(function), Maybe::Present(identity)),
            declaration(At(1), Maybe::Present(function), Maybe::Present(twice)),
        ])
    };
    let Verdict::Checked { body, .. } = report.judged()[1].verdict()
    else {
        panic!("the nested calls check: {:?}", report.judged()[1].verdict());
    };
    assert_ne!(body, twice, "the verdict carries the elaborated body");
    assert_eq!(
        gandr_core_term::equal_certificate_syntax(&arena, body, expected),
        gandr_core_term::CertificateEquality::Equal,
        "the inner call runs inside the outer one's computation, and the outer, which the \
         return only returns, is the body"
    );
    assert_eq!(
        report.definitions().get(&ConstantIndex::from(1_usize)),
        Some(&body),
        "the constant is defined as the elaborated body"
    );
    let elaboration = &report.nested_elaborations()[&ConstantIndex::from(1_usize)];
    assert_eq!(
        elaboration
            .decisions()
            .iter()
            .map(|(&at, &decided)| (at, decided))
            .collect::<Vec<_>>(),
        [
            (inner, Nesting::Ran(Purity::Pure)),
            (outer, Nesting::Ran(Purity::Pure))
        ],
        "both nested calls run, and neither performs an effect"
    );
    assert_eq!(
        elaboration
            .binds()
            .iter()
            .map(|&(run, _)| run)
            .collect::<Vec<_>>(),
        [inner],
        "the inner run is reported beside the bind minted for it; the outer, which its region \
         only returns, mints none"
    );
    assert!(
        elaboration
            .carried()
            .contains(&gandr_core_term::Carried::Value(twice, body)),
        "the rebuild reports the body it stands for the written one: {:?}",
        elaboration.carried()
    );
    assert!(
        !report
            .nested_elaborations()
            .contains_key(&ConstantIndex::from(0_usize)),
        "a body holding no nested computation is not elaborated"
    );
    let readmission = gandr_core_checker_bridge::bridge::readmit(&mut arena, &report);
    assert!(
        readmission.readmitted().iter().all(|readmitted| matches!(
            readmitted.outcome(),
            gandr_core_checker_bridge::bridge::Outcome::Defined { .. }
        )),
        "the kernel re-derives the elaborated body: {readmission:?}"
    );
}

/// A checked record update elaborates to the record of the fields its overlay
/// writes beside each kept field of its base, read off the base by a
/// projection; a base written as a call runs once, bound before the record,
/// and each kept field reads the record it bound. The kernel re-derives both
/// bodies.
#[test]
fn a_record_update_builds_its_base_s_kept_fields_beside_its_overlay()
{
    let mut arena = CoreArena::new();
    let label = |name: &str| gandr_kernel_term::FieldLabel::from(alloc::string::String::from(name));
    let integer = arena.value_type_base(BaseType::Integer);
    let string = arena.value_type_base(BaseType::String);
    let zero = arena.value_literal(integer_literal());
    let word = arena.value_literal(text_literal());
    let [bound, argument, expected_argument, expected_bound] = [(); 4].map(|()| {
        arena.value_variable(
            gandr_core_term::Zone::Intuitionistic,
            DeBruijnIndex::from(0_u32),
        )
    });
    // `r = #{a = 0, b = 0}` and `s = #{r | b = "", c = 0}`.
    let pair_type = arena.value_type_record(alloc::collections::BTreeMap::from([
        (label("a"), integer),
        (label("b"), integer),
    ]));
    let updated_type = arena.value_type_record(alloc::collections::BTreeMap::from([
        (label("a"), integer),
        (label("b"), string),
        (label("c"), integer),
    ]));
    let pair = arena.value_record(alloc::collections::BTreeMap::from([
        (label("a"), zero),
        (label("b"), zero),
    ]));
    let r = arena.value_constant(ConstantIndex::from(0_usize));
    let overlay = arena.value_record(alloc::collections::BTreeMap::from([
        (label("b"), word),
        (label("c"), zero),
    ]));
    let updated = arena.value_record_update(r, overlay);
    let kept_a = arena.computation_record_projection(r, label("a"));
    let kept_a = arena.value_returned(kept_a);
    let expected_updated = arena.value_record(alloc::collections::BTreeMap::from([
        (label("a"), kept_a),
        (label("b"), word),
        (label("c"), zero),
    ]));
    // `point = fun (n) { return #{a = n, b = n} }` and
    // `moved = fun (n) { return #{point(n) | a = 0} }`.
    let returns_pair = arena.comp_type_returner(pair_type);
    let to_pair = arena.comp_type_arrow(integer, returns_pair);
    let to_pair = arena.value_type_thunk(to_pair);
    let point = {
        let both = arena.value_record(alloc::collections::BTreeMap::from([
            (label("a"), bound),
            (label("b"), bound),
        ]));
        let returned = arena.computation_return(both);
        let lambda = arena.computation_lambda(returned);
        arena.value_thunk(lambda)
    };
    let written_a = arena.value_record(alloc::collections::BTreeMap::from([(label("a"), zero)]));
    let moved = {
        let called = call(&mut arena, ConstantIndex::from(2_usize), argument);
        let called = arena.value_nested(called);
        let update = arena.value_record_update(called, written_a);
        let returned = arena.computation_return(update);
        let lambda = arena.computation_lambda(returned);
        arena.value_thunk(lambda)
    };
    let expected_moved = {
        let called = call(&mut arena, ConstantIndex::from(2_usize), expected_argument);
        let kept_b = arena.computation_record_projection(expected_bound, label("b"));
        let kept_b = arena.value_returned(kept_b);
        let record = arena.value_record(alloc::collections::BTreeMap::from([
            (label("a"), zero),
            (label("b"), kept_b),
        ]));
        let returned = arena.computation_return(record);
        let bound = arena.computation_bind(called, returned);
        let lambda = arena.computation_lambda(bound);
        arena.value_thunk(lambda)
    };
    let report = {
        let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        check_module(&mut context, &[
            declaration(At(0), Maybe::Present(pair_type), Maybe::Present(pair)),
            declaration(At(1), Maybe::Present(updated_type), Maybe::Present(updated)),
            declaration(At(2), Maybe::Present(to_pair), Maybe::Present(point)),
            declaration(At(3), Maybe::Present(to_pair), Maybe::Present(moved)),
        ])
    };
    for (position, expected, what) in [
        (
            1_usize,
            expected_updated,
            "the kept `a` is read off `r` beside the written fields",
        ),
        (
            3_usize,
            expected_moved,
            "the call is bound once, and the kept `b` is read off the record it bound",
        ),
    ] {
        let Verdict::Checked { body, .. } = report.judged()[position].verdict()
        else {
            panic!(
                "the update checks: {:?}",
                report.judged()[position].verdict()
            );
        };
        assert_eq!(
            gandr_core_term::equal_certificate_syntax(&arena, body, expected),
            gandr_core_term::CertificateEquality::Equal,
            "{what}"
        );
    }
    let readmission = gandr_core_checker_bridge::bridge::readmit(&mut arena, &report);
    assert!(
        readmission.readmitted().iter().all(|readmitted| matches!(
            readmitted.outcome(),
            gandr_core_checker_bridge::bridge::Outcome::Defined { .. }
        )),
        "the kernel re-derives the built records: {readmission:?}"
    );
}

/// #5578: a value of a record type stands at a patched type of it by the
/// coercion in. The judgement records the fixed fields it compared at the
/// value, and the value crosses as its restriction to the free fields, whose
/// conversions the kernel replays. A value whose field is another value is
/// refused at the value, least label first. A crossing with one comparison
/// removed keeps that field, and the kernel refuses it by the field's label.
#[test]
fn a_base_value_at_a_patched_type_crosses_as_a_restriction_5578()
{
    let mut arena = CoreArena::new();
    let label = |name: &str| gandr_kernel_term::FieldLabel::from(alloc::string::String::from(name));
    let integer = arena.value_type_base(BaseType::Integer);
    let zero = arena.value_literal(integer_literal());
    let one = arena.value_literal(gandr_kernel_term::Literal::Integer(
        gandr_kernel_term::IntegerLiteral::new(
            gandr_kernel_term::Sign::NonNegative,
            gandr_kernel_term::Magnitude::from_decimal_text(alloc::string::String::from("1"))
                .expect("decimal digits"),
        ),
    ));
    // `base : *{host, port, tls : Integer} = *{.host = 0, .port = 0, .tls = 0}`
    // and `other` the same record with its port at 1.
    let record_type = arena.value_type_record(alloc::collections::BTreeMap::from([
        (label("host"), integer),
        (label("port"), integer),
        (label("tls"), integer),
    ]));
    let base = arena.value_record(alloc::collections::BTreeMap::from([
        (label("host"), zero),
        (label("port"), zero),
        (label("tls"), zero),
    ]));
    let other = arena.value_record(alloc::collections::BTreeMap::from([
        (label("host"), zero),
        (label("port"), one),
        (label("tls"), zero),
    ]));
    // `secured : *{…}[.port = 0, .tls = 0] = base` and the same of `other`.
    let fixed = alloc::collections::BTreeMap::from([(label("port"), zero), (label("tls"), zero)]);
    let patched = arena.value_type_patched(record_type, fixed.clone());
    let named = arena.value_constant(ConstantIndex::from(0_usize));
    let named_other = arena.value_constant(ConstantIndex::from(2_usize));
    let mut report = {
        let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        check_module(&mut context, &[
            declaration(At(0), Maybe::Present(record_type), Maybe::Present(base)),
            declaration(At(1), Maybe::Present(patched), Maybe::Present(named)),
            declaration(At(2), Maybe::Present(record_type), Maybe::Present(other)),
            declaration(At(3), Maybe::Present(patched), Maybe::Present(named_other)),
        ])
    };
    let Verdict::Checked { body, .. } = report.judged()[1].verdict()
    else {
        panic!(
            "a value whose fixed fields convert checks: {:?}",
            report.judged()[1].verdict()
        );
    };
    assert_eq!(
        body, named,
        "the body runs as written: the coercion copies no record at run time"
    );
    assert_eq!(
        report.coercions().get(&named),
        Some(&fixed),
        "the judgement records both fixed fields at the value it coerced in"
    );
    assert_eq!(
        report.judged()[3].verdict(),
        Verdict::Refused(CheckRefusal::FixedFieldDiffers {
            at: named_other,
            fixed: zero,
        }),
        "a value whose port is another value is refused at the value, by the port"
    );
    let readmission = gandr_core_checker_bridge::bridge::readmit(&mut arena, &report);
    let gandr_core_checker_bridge::bridge::Outcome::Defined { admitted, .. } =
        *readmission.readmitted()[1].outcome()
    else {
        panic!(
            "the kernel admits the restriction: {:?}",
            readmission.readmitted()[1].outcome()
        );
    };
    let environment = readmission.environment();
    let entry = environment
        .entries()
        .get(usize::from(admitted.position()))
        .expect("the admitted position holds an entry");
    let gandr_kernel_term::DeclarationContent::Def { body, .. } = *entry.declaration().content()
    else {
        panic!("the coerced value is admitted as a definition");
    };
    assert!(
        matches!(environment.arena().value(body), Some(gandr_kernel_term::Value::Restrict { fixed, .. })
            if fixed.keys().eq([&label("port"), &label("tls")])),
        "the value crosses as its restriction at both fixed fields: {:?}",
        environment.arena().value(body)
    );
    report
        .coercions_mut()
        .get_mut(&named)
        .expect("the coercion is recorded")
        .remove(&label("tls"));
    let readmission = gandr_core_checker_bridge::bridge::readmit(&mut arena, &report);
    assert_eq!(
        readmission.readmitted()[1].outcome(),
        &gandr_core_checker_bridge::bridge::Outcome::Rejected(
            gandr_kernel_core::KernelError::KeptRecordField {
                label: label("tls"),
            }
        ),
        "a crossing that drops the comparison of `tls` keeps it, and the kernel refuses it by `tls`"
    );
}

/// #5663: the kernel replays the formation of a patched type and the meets of
/// its faces. Each crossing admits a record of the fixed fields at their
/// field's types and that record's restriction at the glued values, so a meet
/// costs one kernel conversion. A crossing whose meet value differs from the
/// glued value, or whose glued value has another type, is refused by `port`.
#[test]
fn a_patched_type_crosses_its_formation_and_the_meets_of_its_faces_5663()
{
    let mut arena = CoreArena::new();
    let label = |name: &str| gandr_kernel_term::FieldLabel::from(alloc::string::String::from(name));
    let integer = arena.value_type_base(BaseType::Integer);
    let zero = arena.value_literal(integer_literal());
    let also_zero = arena.value_literal(integer_literal());
    let eighty = arena.value_literal(gandr_kernel_term::Literal::Integer(
        gandr_kernel_term::IntegerLiteral::new(
            gandr_kernel_term::Sign::NonNegative,
            gandr_kernel_term::Magnitude::from_decimal_text(alloc::string::String::from("80"))
                .expect("decimal digits"),
        ),
    ));
    let unit = arena.value_unit();
    let truth = arena.value_injection(gandr_core_term::Summand::from(1_usize), unit);
    // `*{host, port, tls, mode : Integer}[secure ↦ {port, tls}, addr ↦ {host,
    // port}]`, whose faces agree on `port`.
    let record_type = arena.value_type_record(alloc::collections::BTreeMap::from([
        (label("host"), integer),
        (label("mode"), integer),
        (label("port"), integer),
        (label("tls"), integer),
    ]));
    let fixed = alloc::collections::BTreeMap::from([
        (label("host"), zero),
        (label("port"), zero),
        (label("tls"), zero),
    ]);
    let agreeing = arena.value_type_system(record_type, fixed.clone(), alloc::vec![(
        label("port"),
        also_zero
    )]);
    let free = arena.value_record(alloc::collections::BTreeMap::from([(label("mode"), zero)]));
    let mut report = {
        let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        check_module(&mut context, &[declaration(
            At(0),
            Maybe::Present(agreeing),
            Maybe::Present(free),
        )])
    };
    let Verdict::Checked { body, evidence, .. } = report.judged()[0].verdict()
    else {
        panic!(
            "faces that agree on their meet form a type: {:?}",
            report.judged()[0].verdict()
        );
    };
    let readmission = gandr_core_checker_bridge::bridge::readmit(&mut arena, &report);
    let gandr_core_checker_bridge::bridge::Outcome::Defined { admitted, .. } =
        *readmission.readmitted()[0].outcome()
    else {
        panic!(
            "the kernel admits the declaration after its formation: {:?}",
            readmission.readmitted()[0].outcome()
        );
    };
    let environment = readmission.environment();
    let restriction = usize::from(admitted.position())
        .checked_sub(1)
        .and_then(|at| environment.entries().get(at))
        .expect("the formation's restriction crosses just before the declaration");
    let gandr_kernel_term::DeclarationContent::Def { body: crossed, .. } =
        *restriction.declaration().content()
    else {
        panic!("the meet crosses as a definition");
    };
    assert!(
        matches!(environment.arena().value(crossed), Some(gandr_kernel_term::Value::Restrict { fixed, .. })
            if fixed.keys().eq([&label("port")])),
        "the meet crosses as the restriction at `port` alone, one conversion for its one meet \
         field: {:?}",
        environment.arena().value(crossed)
    );
    // A crossing whose later face holds 80 at the meet: the kernel converts
    // it with the glued 0 and refuses it by `port`.
    let differing = arena.value_type_system(record_type, fixed.clone(), alloc::vec![(
        label("port"),
        eighty
    )]);
    let entry = &mut report.judged_mut()[0];
    *entry = gandr_core_checker_base::report::Judged::new(
        entry.constant(),
        entry.origin(),
        Verdict::Checked {
            declared: gandr_core_checker_base::fixture::formed(differing),
            body,
            evidence,
        },
    );
    assert_eq!(
        gandr_core_checker_bridge::bridge::readmit(&mut arena, &report).readmitted()[0].outcome(),
        &gandr_core_checker_bridge::bridge::Outcome::Rejected(
            gandr_kernel_core::KernelError::FixedFieldDiffers {
                label: label("port"),
            }
        ),
        "a meet value that does not convert with the glued value is refused by its label"
    );
    // A crossing whose glued value at `port` is `true`, of another type
    // than the port's: the kernel refuses it at `port`.
    let mut mistyped = fixed;
    mistyped.insert(label("port"), truth);
    let mistyped = arena.value_type_system(record_type, mistyped, alloc::vec![(
        label("port"),
        also_zero
    )]);
    let entry = &mut report.judged_mut()[0];
    *entry = gandr_core_checker_base::report::Judged::new(
        entry.constant(),
        entry.origin(),
        Verdict::Checked {
            declared: gandr_core_checker_base::fixture::formed(mistyped),
            body,
            evidence,
        },
    );
    let readmission = gandr_core_checker_bridge::bridge::readmit(&mut arena, &report);
    assert!(
        matches!(
            readmission.readmitted()[0].outcome(),
            gandr_core_checker_bridge::bridge::Outcome::Rejected(gandr_kernel_core::KernelError::FieldRefused {
                label: refused,
                ..
            }) if *refused == label("port")
        ),
        "a glued value of another type than its field's is refused at its label: {:?}",
        readmission.readmitted()[0].outcome()
    );
}

/// #5748: two equal patched types at two core nodes cross one formation, and
/// two that differ in one fixed value cross two. A formation with no meet
/// crosses one record witness, ahead of the first declaration that holds it.
#[test]
fn equal_patched_types_share_one_formation_5748()
{
    let label = |name: &str| gandr_kernel_term::FieldLabel::from(alloc::string::String::from(name));
    let one = || {
        gandr_kernel_term::Literal::Integer(gandr_kernel_term::IntegerLiteral::new(
            gandr_kernel_term::Sign::NonNegative,
            gandr_kernel_term::Magnitude::from_decimal_text(alloc::string::String::from("1"))
                .expect("decimal digits"),
        ))
    };
    // `*{port, tls : Integer}[.port = n]`, minted at a node of its own for each
    // declaration, and each declaration's body the record of its free field.
    let crossed = |ports: [gandr_kernel_term::Literal; 2]| {
        let mut arena = CoreArena::new();
        let integer = arena.value_type_base(BaseType::Integer);
        let record_type = arena.value_type_record(alloc::collections::BTreeMap::from([
            (label("port"), integer),
            (label("tls"), integer),
        ]));
        let module = ports.map(|port| {
            let port = arena.value_literal(port);
            let system = arena.value_type_system(
                record_type,
                alloc::collections::BTreeMap::from([(label("port"), port)]),
                alloc::vec::Vec::new(),
            );
            let tls = arena.value_literal(integer_literal());
            let free =
                arena.value_record(alloc::collections::BTreeMap::from([(label("tls"), tls)]));
            (system, free)
        });
        assert_ne!(
            module[0].0, module[1].0,
            "each declaration holds its own core node"
        );
        let module = [0_usize, 1].map(|at| {
            declaration(
                At(at),
                Maybe::Present(module[at].0),
                Maybe::Present(module[at].1),
            )
        });
        let report = {
            let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
            check_module(&mut context, &module)
        };
        let readmission = gandr_core_checker_bridge::bridge::readmit(&mut arena, &report);
        for entry in readmission.readmitted() {
            assert!(
                matches!(
                    entry.outcome(),
                    gandr_core_checker_bridge::bridge::Outcome::Defined { .. }
                ),
                "each declaration crosses after its formation: {:?}",
                entry.outcome()
            );
        }
        readmission.environment().entries().len()
    };
    assert_eq!(
        crossed([integer_literal(), integer_literal()]),
        3,
        "two equal formations cross one record witness, then the two declarations"
    );
    assert_eq!(
        crossed([integer_literal(), one()]),
        4,
        "formations that differ at `port` cross one record witness each"
    );
}

/// #5748: the key of a formation holds its glued values beside its meets. Two
/// formations whose meets hold 80 at `port` share no witness when one glues 80
/// and the other glues 0 there. Their first witnesses are equal records, but
/// the kernel still converts the second meet and refuses it by `port`.
#[test]
fn equal_meets_over_other_glued_values_share_no_formation_5748()
{
    let mut arena = CoreArena::new();
    let label = |name: &str| gandr_kernel_term::FieldLabel::from(alloc::string::String::from(name));
    let eighty = || {
        gandr_kernel_term::Literal::Integer(gandr_kernel_term::IntegerLiteral::new(
            gandr_kernel_term::Sign::NonNegative,
            gandr_kernel_term::Magnitude::from_decimal_text(alloc::string::String::from("80"))
                .expect("decimal digits"),
        ))
    };
    let integer = arena.value_type_base(BaseType::Integer);
    let record_type = arena.value_type_record(alloc::collections::BTreeMap::from([
        (label("port"), integer),
        (label("tls"), integer),
    ]));
    // `*{port, tls : Integer}` whose later face holds 80 at its meet `port`,
    // glued at `glued`.
    let system = |arena: &mut CoreArena, glued: gandr_kernel_term::Literal| {
        let glued = arena.value_literal(glued);
        let meet = arena.value_literal(eighty());
        arena.value_type_system(
            record_type,
            alloc::collections::BTreeMap::from([(label("port"), glued)]),
            alloc::vec![(label("port"), meet)],
        )
    };
    let agreeing = [system(&mut arena, eighty()), system(&mut arena, eighty())];
    let module = [0_usize, 1].map(|at| {
        let tls = arena.value_literal(integer_literal());
        let free = arena.value_record(alloc::collections::BTreeMap::from([(label("tls"), tls)]));
        declaration(At(at), Maybe::Present(agreeing[at]), Maybe::Present(free))
    });
    let mut report = {
        let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        check_module(&mut context, &module)
    };
    let Verdict::Checked { body, evidence, .. } = report.judged()[1].verdict()
    else {
        panic!(
            "faces that agree on their meet form a type: {:?}",
            report.judged()[1].verdict()
        );
    };
    let differing = system(&mut arena, integer_literal());
    let entry = &mut report.judged_mut()[1];
    *entry = gandr_core_checker_base::report::Judged::new(
        entry.constant(),
        entry.origin(),
        Verdict::Checked {
            declared: gandr_core_checker_base::fixture::formed(differing),
            body,
            evidence,
        },
    );
    let readmission = gandr_core_checker_bridge::bridge::readmit(&mut arena, &report);
    assert!(
        matches!(
            readmission.readmitted()[0].outcome(),
            gandr_core_checker_bridge::bridge::Outcome::Defined { .. }
        ),
        "the glued 80 converts with its meet: {:?}",
        readmission.readmitted()[0].outcome()
    );
    assert_eq!(
        readmission.readmitted()[1].outcome(),
        &gandr_core_checker_bridge::bridge::Outcome::Rejected(
            gandr_kernel_core::KernelError::FixedFieldDiffers {
                label: label("port"),
            }
        ),
        "the glued 0 shares no formation with the glued 80, so its meet is refused by its label"
    );
}

/// #5579: an element of a patched type stands at its base by the coercion out,
/// as the record of its free fields beside the values the type fixes; a
/// selection of a fixed field reads the fixed value. A nested computation
/// whose result stands at the base runs before the record is built. The
/// kernel admits each body as it admits any record.
#[test]
fn an_element_of_a_patched_type_stands_at_its_base_as_its_record_5579()
{
    let mut arena = CoreArena::new();
    let label = |name: &str| gandr_kernel_term::FieldLabel::from(alloc::string::String::from(name));
    let integer = arena.value_type_base(BaseType::Integer);
    let zero = arena.value_literal(integer_literal());
    // `secured : *{host, port, tls : Integer}[.port = 0, .tls = 0] = *{.host = 0}`.
    let record_type = arena.value_type_record(alloc::collections::BTreeMap::from([
        (label("host"), integer),
        (label("port"), integer),
        (label("tls"), integer),
    ]));
    let fixed = alloc::collections::BTreeMap::from([(label("port"), zero), (label("tls"), zero)]);
    let patched = arena.value_type_patched(record_type, fixed);
    let free = arena.value_record(alloc::collections::BTreeMap::from([(label("host"), zero)]));
    // `whole : *{…} = secured`, `port : Integer = ⟨secured.port⟩` and
    // `ran : *{…} = ⟨return secured⟩`.
    let whole = arena.value_constant(ConstantIndex::from(0_usize));
    let selected = arena.value_constant(ConstantIndex::from(0_usize));
    let projection = arena.computation_record_projection(selected, label("port"));
    let port = arena.value_returned(projection);
    let returned = arena.value_constant(ConstantIndex::from(0_usize));
    let returning = arena.computation_return(returned);
    let ran = arena.value_nested(returning);
    let report = {
        let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        check_module(&mut context, &[
            declaration(At(0), Maybe::Present(patched), Maybe::Present(free)),
            declaration(At(1), Maybe::Present(record_type), Maybe::Present(whole)),
            declaration(At(2), Maybe::Present(integer), Maybe::Present(port)),
            declaration(At(3), Maybe::Present(record_type), Maybe::Present(ran)),
        ])
    };
    let body = |at: usize| {
        let Verdict::Checked { body, .. } = report.judged()[at].verdict()
        else {
            panic!(
                "declaration {at} checks: {:?}",
                report.judged()[at].verdict()
            );
        };
        body
    };
    assert_eq!(
        body(0),
        free,
        "the element keeps the record of its free fields"
    );
    let Some(gandr_core_term::Value::Record(fields)) = arena.value(body(1)).cloned()
    else {
        panic!("the element stands as a record: {:?}", arena.value(body(1)));
    };
    assert_eq!(
        (fields.get(&label("port")), fields.get(&label("tls"))),
        (Some(&zero), Some(&zero)),
        "the record holds the values the type fixes"
    );
    assert!(
        matches!(
            fields.get(&label("host")).and_then(|&host| arena.value(host)),
            Some(&gandr_core_term::Value::Returned(read))
                if arena.computation(read) == Some(&gandr_core_term::Computation::RecordProjection(whole, label("host")))
        ),
        "the record reads its free field off the element: {fields:?}"
    );
    let Some(&gandr_core_term::Value::Returned(read)) = arena.value(body(2))
    else {
        panic!(
            "the selection stands as what it returns: {:?}",
            arena.value(body(2))
        );
    };
    let Some(&gandr_core_term::Computation::RecordProjection(record, ref projected)) =
        arena.computation(read)
    else {
        panic!("the selection projects: {:?}", arena.computation(read));
    };
    assert_eq!(projected, &label("port"));
    assert_eq!(
        arena.value(record),
        Some(&gandr_core_term::Value::Record(
            alloc::collections::BTreeMap::from([(label("port"), zero)])
        )),
        "a fixed field is read off the record of the value the type fixes"
    );
    // `ran` binds the run once, and its record reads the free field off what
    // the run bound: `⟨x ← return secured; return *{.host = ⟨x.host⟩, …}⟩`.
    let expected_ran = {
        let bound = arena.value_variable(
            gandr_core_term::Zone::Intuitionistic,
            DeBruijnIndex::from(0_u32),
        );
        let host = arena.computation_record_projection(bound, label("host"));
        let host = arena.value_returned(host);
        let record = arena.value_record(alloc::collections::BTreeMap::from([
            (label("host"), host),
            (label("port"), zero),
            (label("tls"), zero),
        ]));
        let built = arena.computation_return(record);
        let secured = arena.value_constant(ConstantIndex::from(0_usize));
        let first = arena.computation_return(secured);
        let bind = arena.computation_bind(first, built);
        arena.value_returned(bind)
    };
    assert_eq!(
        gandr_core_term::equal_certificate_syntax(&arena, body(3), expected_ran),
        gandr_core_term::CertificateEquality::Equal,
        "the run is bound once, before the record of what it returns"
    );
    let readmission = gandr_core_checker_bridge::bridge::readmit(&mut arena, &report);
    assert!(
        readmission.readmitted().iter().all(|readmitted| matches!(
            readmitted.outcome(),
            gandr_core_checker_bridge::bridge::Outcome::Defined { .. }
        )),
        "the kernel admits each record at the base: {readmission:?}"
    );
}

/// #2159: a record update written in a signature reads the record it builds,
/// so a path between two updates at distinct labels, or between an update
/// writing a field's own value and its base, holds at one point. The kernel
/// re-derives both.
#[test]
fn a_record_update_in_a_signature_reads_its_record_2159()
{
    let mut arena = CoreArena::new();
    let label = |name: &str| gandr_kernel_term::FieldLabel::from(alloc::string::String::from(name));
    let integer = arena.value_type_base(BaseType::Integer);
    let zero = arena.value_literal(integer_literal());
    // `point = #{x = 0, y = 0}`.
    let pair_type = arena.value_type_record(alloc::collections::BTreeMap::from([
        (label("x"), integer),
        (label("y"), integer),
    ]));
    let pair = arena.value_record(alloc::collections::BTreeMap::from([
        (label("x"), zero),
        (label("y"), zero),
    ]));
    let point = arena.value_constant(ConstantIndex::from(0_usize));
    let written = |arena: &mut CoreArena, base, name| {
        let overlay = arena.value_record(alloc::collections::BTreeMap::from([(label(name), zero)]));
        arena.value_record_update(base, overlay)
    };
    // `commute : Path[.A = R](#{#{point | x = 0} | y = 0}, #{#{point | y = 0} | x =
    // 0})`.
    let commuted = {
        let first = written(&mut arena, point, "x");
        let left = written(&mut arena, first, "y");
        let second = written(&mut arena, point, "y");
        let right = written(&mut arena, second, "x");
        arena.value_type_path(pair_type, left, right)
    };
    let commute = arena.value_here(pair);
    // `unchanged : Path[.A = R](#{point | x = 0}, point)`.
    let unchanged_type = {
        let left = written(&mut arena, point, "x");
        arena.value_type_path(pair_type, left, point)
    };
    let unchanged = arena.value_here(point);
    let report = {
        let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        check_module(&mut context, &[
            declaration(At(0), Maybe::Present(pair_type), Maybe::Present(pair)),
            declaration(At(1), Maybe::Present(commuted), Maybe::Present(commute)),
            declaration(
                At(2),
                Maybe::Present(unchanged_type),
                Maybe::Present(unchanged),
            ),
        ])
    };
    for (position, what) in [
        (1_usize, "updates at distinct labels commute"),
        (2_usize, "an update writing a field's own value is its base"),
    ] {
        assert!(
            matches!(report.judged()[position].verdict(), Verdict::Checked { .. }),
            "{what}: {:?}",
            report.judged()[position].verdict()
        );
    }
    let readmission = gandr_core_checker_bridge::bridge::readmit(&mut arena, &report);
    assert!(
        readmission.readmitted().iter().all(|readmitted| matches!(
            readmitted.outcome(),
            gandr_core_checker_bridge::bridge::Outcome::Defined { .. }
        )),
        "the kernel re-derives each built signature: {readmission:?}"
    );
}

#[test]
fn a_model_crosses_to_an_included_theory_s_by_its_reduct()
{
    let variable = |arena: &mut CoreArena, index: u32| {
        arena.value_variable(
            gandr_core_term::Zone::Intuitionistic,
            DeBruijnIndex::from(index),
        )
    };
    // The narrow pair keeps the first two of the wide nesting's three
    // components, as a theory included in another keeps some of its members.
    let check = |kept: &[ConstantIndex]| {
        let mut arena = CoreArena::new();
        let integer = arena.value_type_base(BaseType::Integer);
        let narrow = arena.value_type_product(&[integer, integer]);
        let wide = arena.value_type_product(&[integer, narrow]);
        let thunk_of = |arena: &mut CoreArena, domain, result| {
            let returns = arena.comp_type_returner(result);
            let arrow = arena.comp_type_arrow(domain, returns);
            arena.value_type_thunk(arrow)
        };
        // `reduct = thunk(λm. split m as (a, r). split r as (b, c). return (a, b))`.
        let reduct_type = thunk_of(&mut arena, wide, narrow);
        let reduct = {
            let a = variable(&mut arena, 3);
            let b = variable(&mut arena, 1);
            let pair = arena.value_tuple(&[a, b]);
            let returned = arena.computation_return(pair);
            let pair_of = gandr_core_term::ComponentCount::from(2_usize);
            let rest = variable(&mut arena, 0);
            let inner = arena.computation_split(rest, pair_of, returned);
            let model = variable(&mut arena, 0);
            let outer = arena.computation_split(model, pair_of, inner);
            let lambda = arena.computation_lambda(outer);
            arena.value_thunk(lambda)
        };
        // `taker = thunk(λn. return 0)`, asking for the narrow pair.
        let taker_type = thunk_of(&mut arena, narrow, integer);
        let taker = {
            let zero = arena.value_literal(gandr_core_checker_base::fixture::integer_literal());
            let returned = arena.computation_return(zero);
            let lambda = arena.computation_lambda(returned);
            arena.value_thunk(lambda)
        };
        // `user = thunk(λm. taker(m))`, `m` the wide nesting.
        let user_type = thunk_of(&mut arena, wide, integer);
        let site = variable(&mut arena, 0);
        let user = {
            let called = call(&mut arena, ConstantIndex::from(1_usize), site);
            let lambda = arena.computation_lambda(called);
            arena.value_thunk(lambda)
        };
        // `thunk(λm. bind reduct(m) as n. taker(n))`.
        let expected = {
            let model = variable(&mut arena, 0);
            let reduced = call(&mut arena, ConstantIndex::from(0_usize), model);
            let bound = variable(&mut arena, 0);
            let called = call(&mut arena, ConstantIndex::from(1_usize), bound);
            let ran = arena.computation_bind(reduced, called);
            let lambda = arena.computation_lambda(ran);
            arena.value_thunk(lambda)
        };
        let report = {
            let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
            context.keep_reducts(kept);
            check_module(&mut context, &[
                declaration(At(0), Maybe::Present(reduct_type), Maybe::Present(reduct)),
                declaration(At(1), Maybe::Present(taker_type), Maybe::Present(taker)),
                declaration(At(2), Maybe::Present(user_type), Maybe::Present(user)),
            ])
        };
        (arena, report, site, expected)
    };
    let (mut arena, report, site, expected) = check(&[ConstantIndex::from(0_usize)]);
    let Verdict::Checked { body, .. } = report.judged()[2].verdict()
    else {
        panic!(
            "the wide nesting checks where the narrow pair is asked: {:?}",
            report.judged()[2].verdict()
        );
    };
    assert_eq!(
        gandr_core_term::equal_certificate_syntax(&arena, body, expected),
        gandr_core_term::CertificateEquality::Equal,
        "the reduct runs at the wide nesting, and the call reads what it returns"
    );
    assert_eq!(
        report.nested_elaborations()[&ConstantIndex::from(2_usize)]
            .crossings()
            .iter()
            .map(|(&at, crossing)| (at, crossing.by, crossing.carriers.len()))
            .collect::<Vec<_>>(),
        [(site, Maybe::Present(ConstantIndex::from(0_usize)), 0)],
        "the crossing is recorded at the argument, by the reduct, at no carrier"
    );
    let readmission = gandr_core_checker_bridge::bridge::readmit(&mut arena, &report);
    assert!(
        readmission.readmitted().iter().all(|readmitted| matches!(
            readmitted.outcome(),
            gandr_core_checker_bridge::bridge::Outcome::Defined { .. }
        )),
        "the kernel re-derives the application of the reduct: {readmission:?}"
    );
    let (_, unkept, ..) = check(&[]);
    assert!(
        matches!(
            unkept.judged()[2].verdict(),
            Verdict::Refused(CheckRefusal::TypeMismatch(_))
        ),
        "with no reduct kept, the wide nesting is refused where the narrow pair is asked: {:?}",
        unkept.judged()[2].verdict()
    );
}

/// #4528: a natural literal checked at a type apart from `Integer` crosses by
/// the one kept reader whose result is that type, recorded at the literal, and
/// the kernel re-derives the application; with no reader kept it is refused.
#[test]
fn a_natural_literal_crosses_by_the_reader_of_its_type_4528()
{
    let readers = naturals(&[ConstantIndex::from(0_usize), ConstantIndex::from(1_usize)]);
    let (mut arena, report, literal) =
        read_literal(&readers, ConstantIndex::from(3_usize), integer_literal());
    assert!(
        matches!(report.judged()[5].verdict(), Verdict::Checked { .. }),
        "the literal checks where text is asked: {:?}",
        report.judged()[5].verdict()
    );
    assert_eq!(
        report.nested_elaborations()[&ConstantIndex::from(5_usize)]
            .crossings()
            .iter()
            .map(|(&at, crossing)| (at, crossing.by, crossing.carriers.len()))
            .collect::<Vec<_>>(),
        [(literal, Maybe::Present(ConstantIndex::from(0_usize)), 0)],
        "the crossing is recorded at the literal, by the text reader alone"
    );
    let readmission = gandr_core_checker_bridge::bridge::readmit(&mut arena, &report);
    assert!(
        readmission.readmitted().iter().all(|readmitted| matches!(
            readmitted.outcome(),
            gandr_core_checker_bridge::bridge::Outcome::Defined { .. }
                | gandr_core_checker_bridge::bridge::Outcome::Assumed { .. }
        )),
        "the kernel re-derives the application of the reader: {readmission:?}"
    );
    let (_, unkept, _) = read_literal(&[], ConstantIndex::from(3_usize), integer_literal());
    assert!(
        matches!(
            unkept.judged()[5].verdict(),
            Verdict::Refused(CheckRefusal::TypeMismatch(_))
        ),
        "with no reader kept, the literal is refused where text is asked: {:?}",
        unkept.judged()[5].verdict()
    );
}

/// #4812: a natural literal written as a definition's own value, at a type a
/// reader answers, crosses by the reader, and the reader's call is pure: the
/// definition stands as the value the call returns, which the kernel types.
#[test]
fn a_literal_read_in_a_definition_s_own_value_stands_as_its_reading_4812()
{
    let mut arena = CoreArena::new();
    let integer = arena.value_type_base(BaseType::Integer);
    let text = arena.value_type_base(BaseType::String);
    let word_type = {
        let returns = arena.comp_type_returner(text);
        let arrow = arena.comp_type_arrow(integer, returns);
        arena.value_type_thunk(arrow)
    };
    let word = {
        let read = arena.value_literal(text_literal());
        let returned = arena.computation_return(read);
        let lambda = arena.computation_lambda(returned);
        arena.value_thunk(lambda)
    };
    let literal = arena.value_literal(integer_literal());
    let report = {
        let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        context.keep_readers(&naturals(&[ConstantIndex::from(0_usize)]));
        check_module(&mut context, &[
            declaration(At(0), Maybe::Present(word_type), Maybe::Present(word)),
            declaration(At(1), Maybe::Present(text), Maybe::Present(literal)),
        ])
    };
    assert!(
        matches!(report.judged()[1].verdict(), Verdict::Checked { .. }),
        "the reader's call stands in the definition's own value, and it is pure: {:?}",
        report.judged()[1].verdict()
    );
    assert!(
        matches!(
            report
                .definitions()
                .get(&ConstantIndex::from(1_usize))
                .and_then(|&body| arena.value(body)),
            Some(&gandr_core_term::Value::Returned(_))
        ),
        "the definition is the value the reader's call returns"
    );
    let readmission = gandr_core_checker_bridge::bridge::readmit(&mut arena, &report);
    assert!(
        readmission.readmitted().iter().all(|readmitted| matches!(
            readmitted.outcome(),
            gandr_core_checker_bridge::bridge::Outcome::Defined { .. }
                | gandr_core_checker_bridge::bridge::Outcome::Assumed { .. }
        )),
        "the kernel types the returned call: {readmission:?}"
    );
}

/// #4732: a negative literal checked at a type apart from `Integer` crosses by
/// the one kept negative reader whose result is that type, applied to the
/// literal's magnitude; a natural reader of the type does not carry it.
#[test]
fn a_negative_literal_crosses_by_from_neg_at_its_magnitude_4732()
{
    let negative = gandr_kernel_term::Literal::Integer(gandr_kernel_term::IntegerLiteral::new(
        gandr_kernel_term::Sign::Negative,
        gandr_kernel_term::Magnitude::from_decimal_text(alloc::string::String::from("4"))
            .expect("decimal digits"),
    ));
    let readers = [
        gandr_core_term::LiteralReader {
            by: ConstantIndex::from(0_usize),
            reads: gandr_core_term::LiteralKind::Negative,
        },
        gandr_core_term::LiteralReader {
            by: ConstantIndex::from(1_usize),
            reads: gandr_core_term::LiteralKind::Natural,
        },
    ];
    let (mut arena, report, literal) =
        read_literal(&readers, ConstantIndex::from(3_usize), negative.clone());
    assert!(
        matches!(report.judged()[5].verdict(), Verdict::Checked { .. }),
        "the negative literal checks where text is asked: {:?}",
        report.judged()[5].verdict()
    );
    let crossings = report.nested_elaborations()[&ConstantIndex::from(5_usize)].crossings();
    let [(&at, crossing)] = crossings.iter().collect::<Vec<_>>()[..]
    else {
        panic!("one crossing is recorded: {crossings:?}");
    };
    assert_eq!(
        (at, crossing.by),
        (literal, Maybe::Present(ConstantIndex::from(0_usize))),
        "the crossing is recorded at the literal, by the negative reader"
    );
    let gandr_core_term::CrossedOperand::Standing(standing) = crossing.operand
    else {
        panic!("the reader takes a value standing for the literal: {crossing:?}");
    };
    assert!(
        matches!(
            arena.value(standing),
            Some(&gandr_core_term::Value::Literal(gandr_kernel_term::Literal::Integer(ref magnitude)))
                if magnitude.sign() == gandr_kernel_term::Sign::NonNegative
                    && magnitude.magnitude().as_ref() == "4"
        ),
        "the reader is applied to the magnitude: {:?}",
        arena.value(standing)
    );
    let readmission = gandr_core_checker_bridge::bridge::readmit(&mut arena, &report);
    assert!(
        readmission.readmitted().iter().all(|readmitted| matches!(
            readmitted.outcome(),
            gandr_core_checker_bridge::bridge::Outcome::Defined { .. }
                | gandr_core_checker_bridge::bridge::Outcome::Assumed { .. }
        )),
        "the kernel re-derives the reader's application: {readmission:?}"
    );
    let (_, natural, _) = read_literal(
        &naturals(&[ConstantIndex::from(0_usize)]),
        ConstantIndex::from(3_usize),
        negative,
    );
    assert!(
        matches!(
            natural.judged()[5].verdict(),
            Verdict::Refused(CheckRefusal::TypeMismatch(_))
        ),
        "a natural reader does not carry a negative literal: {:?}",
        natural.judged()[5].verdict()
    );
}

/// The decimal literal `1.25`.
///
/// # Specification
/// trivial.
fn decimal_literal() -> gandr_kernel_term::Literal
{
    gandr_kernel_term::Literal::Numeric(gandr_kernel_term::NumericLiteral::new(
        gandr_kernel_term::Sign::NonNegative,
        gandr_kernel_term::Magnitude::from_decimal_text(alloc::string::String::from("1"))
            .expect("decimal digits"),
        gandr_kernel_term::FractionDigits::from_decimal_text(alloc::string::String::from("25"))
            .expect("decimal digits"),
    ))
}

/// Assert that the kernel re-derives or assumes every declaration of
/// `report`, a decimal's crossing among them.
///
/// # Specification
/// trivial.
fn assert_readmitted(
    arena: &mut CoreArena,
    report: &gandr_core_checker_base::report::ModuleReport,
)
{
    let readmission = gandr_core_checker_bridge::bridge::readmit(arena, report);
    assert!(
        readmission.readmitted().iter().all(|readmitted| matches!(
            readmitted.outcome(),
            gandr_core_checker_bridge::bridge::Outcome::Defined { .. }
                | gandr_core_checker_bridge::bridge::Outcome::Assumed { .. }
        )),
        "the kernel re-derives every declaration, the decimal's crossing among them: \
         {readmission:?}"
    );
}

/// #4807: a decimal checked at `f64` crosses by no map and stands as the
/// float it rounds to, so the kernel re-derives a float where the source
/// wrote a decimal; a decimal synthesised with no type stated is refused.
#[test]
fn a_decimal_at_f64_stands_as_its_float_4807()
{
    let mut arena = CoreArena::new();
    let integer = arena.value_type_base(BaseType::Integer);
    let float = arena.value_type_base(BaseType::Float64);
    let taker_type = {
        let returns = arena.comp_type_returner(integer);
        let arrow = arena.comp_type_arrow(float, returns);
        arena.value_type_thunk(arrow)
    };
    let user_type = {
        let returns = arena.comp_type_returner(integer);
        arena.value_type_thunk(returns)
    };
    let literal = arena.value_literal(decimal_literal());
    let user = {
        let called = call(&mut arena, ConstantIndex::from(0_usize), literal);
        arena.value_thunk(called)
    };
    let report = {
        let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        check_module(&mut context, &[
            declaration(At(0), Maybe::Present(taker_type), HOLE),
            declaration(At(1), Maybe::Present(user_type), Maybe::Present(user)),
        ])
    };
    assert!(
        matches!(report.judged()[1].verdict(), Verdict::Checked { .. }),
        "the decimal checks where a float is asked: {:?}",
        report.judged()[1].verdict()
    );
    let crossings = report.nested_elaborations()[&ConstantIndex::from(1_usize)].crossings();
    let [(&at, crossing)] = crossings.iter().collect::<Vec<_>>()[..]
    else {
        panic!("one crossing is recorded: {crossings:?}");
    };
    let gandr_core_term::CrossedOperand::Standing(standing) = crossing.operand
    else {
        panic!("the decimal stands as a value of its own: {crossing:?}");
    };
    assert_eq!(
        (at, crossing.by, arena.value(standing)),
        (
            literal,
            Maybe::Absent(()),
            Some(&gandr_core_term::Value::Literal(
                gandr_kernel_term::Literal::Float64(gandr_kernel_term::Float64Literal::from(
                    1.25_f64
                ))
            ))
        ),
        "the decimal stands as its float, by no map"
    );
    assert_readmitted(&mut arena, &report);
    let unsigned = {
        let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        check_module(&mut context, &[declaration(
            At(0),
            UNSIGNED,
            Maybe::Present(literal),
        )])
    };
    assert!(
        matches!(
            unsigned.judged()[0].verdict(),
            Verdict::Refused(CheckRefusal::NotSynthesisable {
                form: gandr_core_checker_base::refusal::CheckingForm::Decimal(_),
            })
        ),
        "a decimal with no type stated is refused: {:?}",
        unsigned.judged()[0].verdict()
    );
}

/// #4807: a decimal checked at a type a kept decimal reader carries crosses
/// by it, applied to the decimal's digits and then its exponent; two readers
/// refuse it naming the type, and with none it is refused as a float.
#[test]
fn a_decimal_crosses_by_from_decimal_at_its_digits_and_exponent_4807()
{
    let judged = |kept: &[ConstantIndex]| {
        let mut arena = CoreArena::new();
        let integer = arena.value_type_base(BaseType::Integer);
        let text = arena.value_type_base(BaseType::String);
        let reader_type = {
            let returns = arena.comp_type_returner(text);
            let inner = arena.comp_type_arrow(integer, returns);
            let outer = arena.comp_type_arrow(integer, inner);
            arena.value_type_thunk(outer)
        };
        let reader = {
            let read = arena.value_literal(text_literal());
            let returned = arena.computation_return(read);
            let inner = arena.computation_lambda(returned);
            let outer = arena.computation_lambda(inner);
            arena.value_thunk(outer)
        };
        let taker_type = {
            let returns = arena.comp_type_returner(integer);
            let arrow = arena.comp_type_arrow(text, returns);
            arena.value_type_thunk(arrow)
        };
        let user_type = {
            let returns = arena.comp_type_returner(integer);
            arena.value_type_thunk(returns)
        };
        let literal = arena.value_literal(decimal_literal());
        let user = {
            let called = call(&mut arena, ConstantIndex::from(2_usize), literal);
            arena.value_thunk(called)
        };
        let report = {
            let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
            let readers: Vec<gandr_core_term::LiteralReader> = kept
                .iter()
                .map(|&by| gandr_core_term::LiteralReader {
                    by,
                    reads: gandr_core_term::LiteralKind::Decimal,
                })
                .collect();
            context.keep_readers(&readers);
            check_module(&mut context, &[
                declaration(At(0), Maybe::Present(reader_type), Maybe::Present(reader)),
                declaration(At(1), Maybe::Present(reader_type), Maybe::Present(reader)),
                declaration(At(2), Maybe::Present(taker_type), HOLE),
                declaration(At(3), Maybe::Present(user_type), Maybe::Present(user)),
            ])
        };
        (arena, report, literal)
    };
    let (mut arena, report, literal) = judged(&[ConstantIndex::from(0_usize)]);
    assert!(
        matches!(report.judged()[3].verdict(), Verdict::Checked { .. }),
        "the decimal checks where text is asked: {:?}",
        report.judged()[3].verdict()
    );
    let crossings = report.nested_elaborations()[&ConstantIndex::from(3_usize)].crossings();
    let [(&at, crossing)] = crossings.iter().collect::<Vec<_>>()[..]
    else {
        panic!("one crossing is recorded: {crossings:?}");
    };
    let (&[digits], gandr_core_term::CrossedOperand::Standing(exponent)) =
        (crossing.carriers.as_slice(), crossing.operand)
    else {
        panic!("the reader takes the digits, then the exponent: {crossing:?}");
    };
    let integer_of = |value| match arena.value(value) {
        Some(&gandr_core_term::Value::Literal(gandr_kernel_term::Literal::Integer(
            ref integer,
        ))) => Some((
            integer.sign(),
            alloc::string::String::from(integer.magnitude().as_ref()),
        )),
        _ => None,
    };
    assert_eq!(
        (at, crossing.by, integer_of(digits), integer_of(exponent)),
        (
            literal,
            Maybe::Present(ConstantIndex::from(0_usize)),
            Some((
                gandr_kernel_term::Sign::NonNegative,
                alloc::string::String::from("125")
            )),
            Some((
                gandr_kernel_term::Sign::Negative,
                alloc::string::String::from("2")
            )),
        ),
        "1.25 crosses by the reader at 125 and -2"
    );
    assert_readmitted(&mut arena, &report);
    let (_, both, _) = judged(&[ConstantIndex::from(0_usize), ConstantIndex::from(1_usize)]);
    assert!(
        matches!(
            both.judged()[3].verdict(),
            Verdict::Refused(CheckRefusal::LiteralAmbiguous { .. })
        ),
        "two readers of the type refuse the decimal: {:?}",
        both.judged()[3].verdict()
    );
    let (_, none, _) = judged(&[]);
    assert!(
        matches!(
            none.judged()[3].verdict(),
            Verdict::Refused(CheckRefusal::TypeMismatch(_))
        ),
        "with no reader the decimal is refused: {:?}",
        none.judged()[3].verdict()
    );
}

#[test]
fn a_manifest_model_crosses_by_its_forgetting_map_at_its_carrier()
{
    let variable = |arena: &mut CoreArena, index: u32| {
        arena.value_variable(
            gandr_core_term::Zone::Intuitionistic,
            DeBruijnIndex::from(index),
        )
    };
    // A pointed type's models, `Σ(c : U). El(c)`; with its carrier manifest
    // at `x`, a model is the point alone, `El(x)`.
    let check = |kept: &[ConstantIndex]| {
        let mut arena = CoreArena::new();
        let integer = arena.value_type_base(BaseType::Integer);
        let small = arena.value_type_universe(Sort::Ground(GroundSort::Value), Level::zero());
        let bound = variable(&mut arena, 0);
        let point = arena.value_type_element(bound, Level::zero());
        let model = arena.value_type_sigma(small, point);
        // `forget : U(Π(x : U). El(x) → F Σ(c : U). El(c))`.
        let forget_type = {
            let returns = arena.comp_type_returner(model);
            let arrow = arena.comp_type_arrow(point, returns);
            let pi = arena.comp_type_pi(small, arrow);
            arena.value_type_thunk(pi)
        };
        // `forget = thunk(λx. λm. return (x, m))`.
        let forget = {
            let carrier = variable(&mut arena, 1);
            let manifest = variable(&mut arena, 0);
            let pair = arena.value_tuple(&[carrier, manifest]);
            let returned = arena.computation_return(pair);
            let inner = arena.computation_lambda(returned);
            let outer = arena.computation_lambda(inner);
            arena.value_thunk(outer)
        };
        // `taker = thunk(λp. return 0)`, asking for a pointed type's model.
        let integer_returns = arena.comp_type_returner(integer);
        let taker_arrow = arena.comp_type_arrow(model, integer_returns);
        let taker_type = arena.value_type_thunk(taker_arrow);
        let taker = {
            let zero = arena.value_literal(gandr_core_checker_base::fixture::integer_literal());
            let returned = arena.computation_return(zero);
            let lambda = arena.computation_lambda(returned);
            arena.value_thunk(lambda)
        };
        // `user = thunk(λm. taker(m))`, `m` an integer: a model whose carrier
        // is manifest at the integers.
        let user_arrow = arena.comp_type_arrow(integer, integer_returns);
        let user_type = arena.value_type_thunk(user_arrow);
        let site = variable(&mut arena, 0);
        let user = {
            let called = call(&mut arena, ConstantIndex::from(1_usize), site);
            let lambda = arena.computation_lambda(called);
            arena.value_thunk(lambda)
        };
        // `thunk(λm. bind forget(⌜Integer⌝, m) as n. taker(n))`.
        let quoted = arena.value_quote(integer);
        let expected = {
            let manifest = variable(&mut arena, 0);
            let map = arena.value_constant(ConstantIndex::from(0_usize));
            let forced = arena.computation_force(map);
            let at_carrier = arena.computation_application(forced, quoted);
            let forgot = arena.computation_application(at_carrier, manifest);
            let bound = variable(&mut arena, 0);
            let called = call(&mut arena, ConstantIndex::from(1_usize), bound);
            let ran = arena.computation_bind(forgot, called);
            let lambda = arena.computation_lambda(ran);
            arena.value_thunk(lambda)
        };
        let report = {
            let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
            context.keep_reducts(kept);
            check_module(&mut context, &[
                declaration(At(0), Maybe::Present(forget_type), Maybe::Present(forget)),
                declaration(At(1), Maybe::Present(taker_type), Maybe::Present(taker)),
                declaration(At(2), Maybe::Present(user_type), Maybe::Present(user)),
            ])
        };
        (arena, report, (site, quoted), expected)
    };
    let (mut arena, report, (site, quoted), expected) = check(&[ConstantIndex::from(0_usize)]);
    let Verdict::Checked { body, .. } = report.judged()[2].verdict()
    else {
        panic!(
            "the manifest model checks where the pointed type's model is asked: {:?}",
            report.judged()[2].verdict()
        );
    };
    assert_eq!(
        gandr_core_term::equal_certificate_syntax(&arena, body, expected),
        gandr_core_term::CertificateEquality::Equal,
        "the forgetting map runs at the integers' code and the manifest model"
    );
    let crossings = report.nested_elaborations()[&ConstantIndex::from(2_usize)].crossings();
    let [(&at, crossing)] = crossings.iter().collect::<Vec<_>>()[..]
    else {
        panic!("one crossing is recorded: {crossings:?}");
    };
    assert_eq!(
        (at, crossing.by),
        (site, Maybe::Present(ConstantIndex::from(0_usize))),
        "the crossing is recorded at the argument, by the forgetting map"
    );
    let &[carrier] = crossing.carriers.as_slice()
    else {
        panic!("the map takes one carrier: {crossing:?}");
    };
    assert_eq!(
        gandr_core_term::equal_certificate_syntax(&arena, carrier, quoted),
        gandr_core_term::CertificateEquality::Equal,
        "the carrier solved is the integers' code"
    );
    let readmission = gandr_core_checker_bridge::bridge::readmit(&mut arena, &report);
    assert!(
        readmission.readmitted().iter().all(|readmitted| matches!(
            readmitted.outcome(),
            gandr_core_checker_bridge::bridge::Outcome::Defined { .. }
        )),
        "the kernel re-derives the application of the forgetting map: {readmission:?}"
    );
    let (_, unkept, ..) = check(&[]);
    assert!(
        matches!(
            unkept.judged()[2].verdict(),
            Verdict::Refused(CheckRefusal::TypeMismatch(_))
        ),
        "with no forgetting map kept, the manifest model is refused where the model is asked: {:?}",
        unkept.judged()[2].verdict()
    );
}

#[test]
fn a_pure_run_a_type_reads_stands_as_what_it_returns_444()
{
    let mut arena = CoreArena::new();
    let (function, identity) = integer_function(&mut arena);
    let integer = arena.value_type_base(BaseType::Integer);
    // `Σ (y : Integer). Path[.A = Integer](y, y)`.
    let bound = arena.value_variable(
        gandr_core_term::Zone::Intuitionistic,
        DeBruijnIndex::from(0_u32),
    );
    let looped = arena.value_type_path(integer, bound, bound);
    let sigma = arena.value_type_sigma(integer, looped);
    let returns = arena.comp_type_returner(sigma);
    let arrow = arena.comp_type_arrow(integer, returns);
    let pairing_type = arena.value_type_thunk(arrow);
    // `λx. return (id(x), here(⟨id(x)⟩))`, the first component a nested
    // call the second's type reads.
    let [nested_x, point_x] = [(); 2].map(|()| {
        arena.value_variable(
            gandr_core_term::Zone::Intuitionistic,
            DeBruijnIndex::from(0_u32),
        )
    });
    let first = call(&mut arena, ConstantIndex::from(0_usize), nested_x);
    let first = arena.value_nested(first);
    let point = call(&mut arena, ConstantIndex::from(0_usize), point_x);
    let point = arena.value_returned(point);
    let reflexive = arena.value_here(point);
    let pair = arena.value_tuple(&[first, reflexive]);
    let returned = arena.computation_return(pair);
    let lambda = arena.computation_lambda(returned);
    let pairing = arena.value_thunk(lambda);
    let report = {
        let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        check_module(&mut context, &[
            declaration(At(0), Maybe::Present(function), Maybe::Present(identity)),
            declaration(At(1), Maybe::Present(pairing_type), Maybe::Present(pairing)),
        ])
    };
    let Verdict::Checked { body, .. } = report.judged()[1].verdict()
    else {
        panic!(
            "the second component checks at the first's call: {:?}",
            report.judged()[1].verdict()
        );
    };
    let elaboration = &report.nested_elaborations()[&ConstantIndex::from(1_usize)];
    assert_eq!(
        elaboration.decisions().get(&first),
        Some(&Nesting::Returned),
        "a pure call the second component's type reads stands as what it returns"
    );
    assert!(elaboration.binds().is_empty(), "and mints no bind");
    let Some(&gandr_core_term::Value::Thunk(lambda)) = arena.value(body)
    else {
        panic!("the body stays a thunk");
    };
    let Some(&gandr_core_term::Computation::Lambda(returned)) = arena.computation(lambda)
    else {
        panic!("over its lambda");
    };
    let Some(&gandr_core_term::Computation::Return(pair)) = arena.computation(returned)
    else {
        panic!("returning the pair, with nothing bound before it");
    };
    assert!(
        matches!(
            arena.value(pair).and_then(gandr_core_term::Value::components),
            Some(&[component, _]) if matches!(arena.value(component), Some(&gandr_core_term::Value::Returned(_)))
        ),
        "the first component is the call's returned value"
    );
    let readmission = gandr_core_checker_bridge::bridge::readmit(&mut arena, &report);
    assert!(
        readmission.readmitted().iter().all(|readmitted| matches!(
            readmitted.outcome(),
            gandr_core_checker_bridge::bridge::Outcome::Defined { .. }
        )),
        "the kernel re-derives the elaborated body: {readmission:?}"
    );
}

/// A reflexivity over `carrier`, `U ((y : carrier) -> F Path[.A = carrier](y,
/// y))`, and its body `λy. return here(y)`.
///
/// # Specification
/// trivial.
fn reflexivity(
    arena: &mut CoreArena,
    carrier: ValueTypeId,
) -> (ValueTypeId, ValueId)
{
    let [left, right, point] = [(); 3].map(|()| {
        arena.value_variable(
            gandr_core_term::Zone::Intuitionistic,
            DeBruijnIndex::from(0_u32),
        )
    });
    let path = arena.value_type_path(carrier, left, right);
    let returns = arena.comp_type_returner(path);
    let pi = arena.comp_type_pi(carrier, returns);
    let here = arena.value_here(point);
    let returned = arena.computation_return(here);
    let lambda = arena.computation_lambda(returned);
    (arena.value_type_thunk(pi), arena.value_thunk(lambda))
}

#[test]
fn a_call_beneath_a_type_read_argument_stands_as_written_762()
{
    let mut arena = CoreArena::new();
    let (function, identity) = integer_function(&mut arena);
    let integer = arena.value_type_base(BaseType::Integer);
    let pair = arena.value_type_product(&[integer, integer]);
    let (at_integer, integer_body) = reflexivity(&mut arena, integer);
    let (at_pair, pair_body) = reflexivity(&mut arena, pair);
    let variable = |arena: &mut CoreArena| {
        arena.value_variable(
            gandr_core_term::Zone::Intuitionistic,
            DeBruijnIndex::from(0_u32),
        )
    };
    // `id(id(x))` as a written type reads it, and as an argument writes it:
    // the inner call nested beneath the outer.
    let returned_twice = |arena: &mut CoreArena| {
        let x = variable(arena);
        let inner = call(arena, ConstantIndex::from(0_usize), x);
        let inner = arena.value_returned(inner);
        let outer = call(arena, ConstantIndex::from(0_usize), inner);
        arena.value_returned(outer)
    };
    // `(id(x), x)` likewise, the call beneath a tuple.
    let returned_paired = |arena: &mut CoreArena| {
        let x = variable(arena);
        let inner = call(arena, ConstantIndex::from(0_usize), x);
        let inner = arena.value_returned(inner);
        let x = variable(arena);
        arena.value_tuple(&[inner, x])
    };
    let declared = |arena: &mut CoreArena, carrier: ValueTypeId, endpoint: ValueId| {
        let path = arena.value_type_path(carrier, endpoint, endpoint);
        let returns = arena.comp_type_returner(path);
        let pi = arena.comp_type_pi(integer, returns);
        arena.value_type_thunk(pi)
    };
    let twice_endpoint = returned_twice(&mut arena);
    let twice_type = declared(&mut arena, integer, twice_endpoint);
    let x = variable(&mut arena);
    let inner_twice = call(&mut arena, ConstantIndex::from(0_usize), x);
    let inner_twice = arena.value_nested(inner_twice);
    let outer_twice = call(&mut arena, ConstantIndex::from(0_usize), inner_twice);
    let outer_twice = arena.value_nested(outer_twice);
    let twice_call = call(&mut arena, ConstantIndex::from(1_usize), outer_twice);
    let twice_lambda = arena.computation_lambda(twice_call);
    let twice_body = arena.value_thunk(twice_lambda);
    let paired_endpoint = returned_paired(&mut arena);
    let paired_type = declared(&mut arena, pair, paired_endpoint);
    let x = variable(&mut arena);
    let inner_paired = call(&mut arena, ConstantIndex::from(0_usize), x);
    let inner_paired = arena.value_nested(inner_paired);
    let x = variable(&mut arena);
    let paired_argument = arena.value_tuple(&[inner_paired, x]);
    let paired_call = call(&mut arena, ConstantIndex::from(2_usize), paired_argument);
    let paired_lambda = arena.computation_lambda(paired_call);
    let paired_body = arena.value_thunk(paired_lambda);
    let report = {
        let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        check_module(&mut context, &[
            declaration(At(0), Maybe::Present(function), Maybe::Present(identity)),
            declaration(
                At(1),
                Maybe::Present(at_integer),
                Maybe::Present(integer_body),
            ),
            declaration(At(2), Maybe::Present(at_pair), Maybe::Present(pair_body)),
            declaration(
                At(3),
                Maybe::Present(twice_type),
                Maybe::Present(twice_body),
            ),
            declaration(
                At(4),
                Maybe::Present(paired_type),
                Maybe::Present(paired_body),
            ),
        ])
    };
    for (constant, nested) in [
        (3_usize, [inner_twice, outer_twice]),
        (4_usize, [inner_paired, inner_paired]),
    ] {
        assert!(
            matches!(report.judged()[constant].verdict(), Verdict::Checked { .. }),
            "the argument converts with the type written with it: {:?}",
            report.judged()[constant].verdict()
        );
        let elaboration = &report.nested_elaborations()[&ConstantIndex::from(constant)];
        for at in nested {
            assert_eq!(
                elaboration.decisions().get(&at),
                Some(&Nesting::Returned),
                "a pure call beneath the argument stands as what it returns"
            );
        }
        assert!(elaboration.binds().is_empty(), "and mints no bind");
    }
    let readmission = gandr_core_checker_bridge::bridge::readmit(&mut arena, &report);
    assert!(
        readmission.readmitted().iter().all(|readmitted| matches!(
            readmitted.outcome(),
            gandr_core_checker_bridge::bridge::Outcome::Defined { .. }
        )),
        "the kernel re-derives the elaborated bodies: {readmission:?}"
    );
}

/// #2327: a call returning a function, read where that function's thunk is
/// read, runs before the call it is passed to; a call returning an integer,
/// read where a thunk of its returner is read, stays suspended.
#[test]
fn a_call_returning_a_function_runs_where_one_is_read_2327()
{
    let mut arena = CoreArena::new();
    let (function, identity) = integer_function(&mut arena);
    let integer = arena.value_type_base(BaseType::Integer);
    let returns = arena.comp_type_returner(integer);
    // `maker : U (Integer -> F (U (Integer -> F Integer)))`, `λn. return identity`.
    let makes = arena.comp_type_returner(function);
    let maker_arrow = arena.comp_type_arrow(integer, makes);
    let maker_type = arena.value_type_thunk(maker_arrow);
    let maker = {
        let held = arena.value_constant(ConstantIndex::from(0_usize));
        let returned = arena.computation_return(held);
        let lambda = arena.computation_lambda(returned);
        arena.value_thunk(lambda)
    };
    // `at_zero : U (U (Integer -> F Integer) -> F Integer)`, `λg. force g 0`.
    let at_zero_arrow = arena.comp_type_arrow(function, returns);
    let at_zero_type = arena.value_type_thunk(at_zero_arrow);
    let at_zero = {
        let applied = arena.value_variable(
            gandr_core_term::Zone::Intuitionistic,
            DeBruijnIndex::from(0_u32),
        );
        let forced = arena.computation_force(applied);
        let zero = arena.value_literal(integer_literal());
        let application = arena.computation_application(forced, zero);
        let lambda = arena.computation_lambda(application);
        arena.value_thunk(lambda)
    };
    let suspended_type = arena.value_type_thunk(returns);
    // `passed : U (F Integer)`, `thunk (at_zero (maker 0))`, `maker 0` nested.
    let made_at = arena.value_literal(integer_literal());
    let made = call(&mut arena, ConstantIndex::from(1_usize), made_at);
    let ran = arena.value_nested(made);
    let passed_call = call(&mut arena, ConstantIndex::from(2_usize), ran);
    let passed = arena.value_thunk(passed_call);
    // `held : U (F Integer)`, `identity 0` nested.
    let held_at = arena.value_literal(integer_literal());
    let held_call = call(&mut arena, ConstantIndex::from(0_usize), held_at);
    let held = arena.value_nested(held_call);
    let report = {
        let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        check_module(&mut context, &[
            declaration(At(0), Maybe::Present(function), Maybe::Present(identity)),
            declaration(At(1), Maybe::Present(maker_type), Maybe::Present(maker)),
            declaration(At(2), Maybe::Present(at_zero_type), Maybe::Present(at_zero)),
            declaration(
                At(3),
                Maybe::Present(suspended_type),
                Maybe::Present(passed),
            ),
            declaration(At(4), Maybe::Present(suspended_type), Maybe::Present(held)),
        ])
    };
    assert!(
        matches!(report.judged()[3].verdict(), Verdict::Checked { .. }),
        "the call returning a function checks where the function is read: {:?}",
        report.judged()[3].verdict()
    );
    let passing = &report.nested_elaborations()[&ConstantIndex::from(3_usize)];
    assert_eq!(
        passing.decisions().get(&ran),
        Some(&Nesting::Ran(Purity::Pure)),
        "it runs, purely"
    );
    assert_eq!(
        passing
            .binds()
            .iter()
            .map(|&(run, _)| run)
            .collect::<Vec<_>>(),
        [ran],
        "and binds what it returns before the call it is passed to"
    );
    assert!(
        matches!(report.judged()[4].verdict(), Verdict::Checked { .. }),
        "the call returning an integer checks at a thunk of its returner: {:?}",
        report.judged()[4].verdict()
    );
    assert_eq!(
        report.nested_elaborations()[&ConstantIndex::from(4_usize)]
            .decisions()
            .get(&held),
        Some(&Nesting::Suspended),
        "it is suspended, as a thunk of its returner reads it"
    );
    let readmission = gandr_core_checker_bridge::bridge::readmit(&mut arena, &report);
    assert!(
        readmission.readmitted().iter().all(|readmitted| matches!(
            readmitted.outcome(),
            gandr_core_checker_bridge::bridge::Outcome::Defined { .. }
        )),
        "the kernel re-derives the elaborated bodies: {readmission:?}"
    );
}
