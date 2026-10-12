//! Native interpretation witnesses for the first-order description fragment.

use gandr_kernel_strata::Level;
use gandr_theory_levitation::AtomSort;
use gandr_theory_levitation::Attrs;
use gandr_theory_levitation::CtorDesc;
use gandr_theory_levitation::NominalId;
use gandr_theory_levitation::NominalSerial;
use gandr_theory_levitation::SortDesc;

use super::*;
use crate::CertificateEquality;
use crate::Sort;
use crate::Value;
use crate::ValueType;
use crate::equal_certificate_syntax;

/// A primitive field carrying an erased unit grade.
///
/// # Specification
/// trivial.
fn field(primitive: PrimTy) -> Code<()>
{
    Code::field(ValueTypeRef::prim(primitive), (), Attrs::empty())
}

/// The interpretation environment shared by the fixtures.
///
/// # Specification
/// trivial.
fn context(
    self_type: ValueTypeId,
    types: &BTreeMap<Name, TypeBinding>,
) -> DecodeContext<'_>
{
    DecodeContext {
        self_sort: NameRef::from("Self"),
        self_type,
        types,
        locals: &[],
        depth: super::ParameterDepth(0),
    }
}

/// A one-sort data description with the supplied constructor payloads.
///
/// # Specification
/// trivial.
fn description(codes: Vec<Code<()>>) -> SignDesc<()>
{
    SignDesc::new(
        NominalId::new(NominalSerial::from(0_u64), "Self"),
        Vec::new(),
        codes
            .into_iter()
            .enumerate()
            .map(|(index, code)| {
                CtorDesc::new(alloc::format!("C{index}"), code, "Self", Attrs::empty())
            })
            .collect::<Vec<_>>(),
        Vec::new(),
        Vec::new(),
        DeclPolarity::Data,
        Attrs::empty(),
    )
}

#[test]
fn decode_interprets_the_first_order_fragment()
{
    let mut arena = CoreArena::new();
    let carrier = arena.value_type_data(ConstantIndex::from(7_usize), Vec::new());
    let types = BTreeMap::new();
    let context = context(carrier, &types);
    let unit = decode(&mut arena, &Code::<()>::unit(), context).unwrap();
    assert_eq!(arena.value_type(unit), Some(&ValueType::unit()));
    assert_eq!(
        decode(&mut arena, &Code::<()>::var("Self"), context),
        Ok(carrier)
    );
    let code = Code::prod(
        field(PrimTy::Integer),
        Code::sum(Code::unit(), Code::var("Self")),
    );
    let result = decode(&mut arena, &code, context).unwrap();
    let Some(held) = arena.value_type(result)
    else {
        panic!("product");
    };
    let ValueType::Product(ref components) = *held
    else {
        panic!("product");
    };
    let [integer, sum] = **components
    else {
        panic!("a product of two components")
    };
    assert_eq!(
        arena.value_type(integer),
        Some(&ValueType::Base(BaseType::Integer))
    );
    let Some(held) = arena.value_type(sum)
    else {
        panic!("sum");
    };
    let ValueType::Sum(ref summands) = *held
    else {
        panic!("sum");
    };
    let [unit, recursive] = **summands
    else {
        panic!("a sum of two summands")
    };
    assert_eq!(arena.value_type(unit), Some(&ValueType::unit()));
    assert_eq!(recursive, carrier);
}

#[test]
fn decode_declines_a_foreign_sort_var()
{
    let mut arena = CoreArena::new();
    let carrier = arena.value_type_unit();
    assert_eq!(
        decode(
            &mut arena,
            &Code::<()>::var("Tree"),
            context(carrier, &BTreeMap::new())
        ),
        Err(DecodeError::ForeignSort(Name::from("Tree")))
    );
}

#[test]
fn decode_erases_field_grade_and_attributes()
{
    let mut arena = CoreArena::new();
    let carrier = arena.value_type_unit();
    let types = BTreeMap::new();
    let context = context(carrier, &types);
    let plain = Code::field(
        ValueTypeRef::prim(PrimTy::Integer),
        TypeArity(1),
        Attrs::empty(),
    );
    let decorated = Code::field(
        ValueTypeRef::prim(PrimTy::Integer),
        TypeArity(42),
        Attrs::new([gandr_theory_levitation::Attr::marker("boxed")]),
    );
    for code in [plain, decorated] {
        let result = decode(&mut arena, &code, context).unwrap();
        assert_eq!(
            arena.value_type(result),
            Some(&ValueType::Base(BaseType::Integer))
        );
    }
}

#[test]
fn decode_boolean_retrofits_to_one_plus_one()
{
    let mut arena = CoreArena::new();
    let carrier = arena.value_type_unit();
    let result = decode(
        &mut arena,
        &field(PrimTy::Boolean),
        context(carrier, &BTreeMap::new()),
    )
    .unwrap();
    let Some(held) = arena.value_type(result)
    else {
        panic!("boolean sum");
    };
    let ValueType::Sum(ref summands) = *held
    else {
        panic!("boolean sum");
    };
    let [left, right] = **summands
    else {
        panic!("a sum of two summands")
    };
    assert_eq!(arena.value_type(left), Some(&ValueType::unit()));
    assert_eq!(arena.value_type(right), Some(&ValueType::unit()));
}

#[test]
fn decode_declines_the_deferred_leaves()
{
    let mut arena = CoreArena::new();
    let carrier = arena.value_type_unit();
    let mut types = BTreeMap::new();
    types.insert(Name::from("Vec"), TypeBinding::Type(carrier));
    let context = context(carrier, &types);
    let bind = Code::<()>::bind(AtomSort::named("v"), Code::var("Self"));
    assert_eq!(
        decode(&mut arena, &bind, context),
        Err(DecodeError::AtomAbstraction)
    );
    let applied = Code::field(
        ValueTypeRef::ctor("Vec", [ValueTypeRef::param("a")]),
        (),
        Attrs::empty(),
    );
    assert_eq!(
        decode(&mut arena, &applied, context),
        Err(DecodeError::AppliedType(Name::from("Vec")))
    );
    for primitive in [
        PrimTy::Char,
        PrimTy::U32,
        PrimTy::U64,
        PrimTy::I32,
        PrimTy::I64,
        PrimTy::F32,
        PrimTy::F64,
        PrimTy::Unknown,
    ] {
        assert_eq!(
            decode(&mut arena, &field(primitive), context),
            Err(DecodeError::Primitive(primitive))
        );
    }
    assert_eq!(
        decode_ref(&mut arena, &ValueTypeRef::param("missing"), context),
        Err(DecodeError::UnresolvedType(Name::from("missing")))
    );
}

#[test]
fn decode_desc_is_the_constructor_coproduct()
{
    let mut arena = CoreArena::new();
    let carrier = arena.value_type_unit();
    let types = BTreeMap::new();
    let context = context(carrier, &types);
    let maybe = description(vec![Code::unit(), field(PrimTy::Integer)]);
    let result = decode_desc(&mut arena, &maybe, context).unwrap();
    let Some(held) = arena.value_type(result)
    else {
        panic!("constructor sum");
    };
    let ValueType::Sum(ref summands) = *held
    else {
        panic!("constructor sum");
    };
    let [left, right] = **summands
    else {
        panic!("a sum of two summands")
    };
    assert_eq!(arena.value_type(left), Some(&ValueType::unit()));
    assert_eq!(
        arena.value_type(right),
        Some(&ValueType::Base(BaseType::Integer))
    );
    let wrapper = description(vec![field(PrimTy::StringTy)]);
    let result = decode_desc(&mut arena, &wrapper, context).unwrap();
    assert_eq!(
        arena.value_type(result),
        Some(&ValueType::Base(BaseType::String))
    );
}

#[test]
fn decode_desc_declines_codata_and_the_uninhabited()
{
    let mut arena = CoreArena::new();
    let carrier = arena.value_type_unit();
    let types = BTreeMap::new();
    let context = context(carrier, &types);
    let mut desc = description(Vec::new());
    assert_eq!(
        decode_desc(&mut arena, &desc, context),
        Err(DecodeError::Uninhabited)
    );
    desc.polarity = DeclPolarity::Codata;
    assert_eq!(
        decode_desc(&mut arena, &desc, context),
        Err(DecodeError::CodataNu)
    );
}

#[test]
fn decode_desc_declines_a_multi_sorted_signature()
{
    let mut arena = CoreArena::new();
    let carrier = arena.value_type_unit();
    let desc = description(vec![Code::unit()]).with_sorts([
        SortDesc::new("Self", DeclPolarity::Data),
        SortDesc::new("Other", DeclPolarity::Data),
    ]);
    assert_eq!(
        decode_desc(&mut arena, &desc, context(carrier, &BTreeMap::new())),
        Err(DecodeError::MultiSorted)
    );
}

#[test]
fn decode_respects_code_equality()
{
    let mut arena = CoreArena::new();
    let carrier = arena.value_type_unit();
    let types = BTreeMap::new();
    let context = context(carrier, &types);
    let product = Code::prod(field(PrimTy::Integer), field(PrimTy::StringTy));
    let same = product.clone();
    let sum = Code::sum(field(PrimTy::Integer), field(PrimTy::StringTy));
    let swapped = Code::prod(field(PrimTy::StringTy), field(PrimTy::Integer));
    let first = decode(&mut arena, &product, context).unwrap();
    let first = arena.value_quote(first);
    for (code, expected) in [
        (same, CertificateEquality::Equal),
        (sum, CertificateEquality::Different),
        (swapped, CertificateEquality::Different),
    ] {
        let other = decode(&mut arena, &code, context).unwrap();
        let other = arena.value_quote(other);
        assert_eq!(equal_certificate_syntax(&arena, first, other), expected);
    }
}

#[test]
fn native_applications_preserve_heads_and_arguments()
{
    let mut arena = CoreArena::new();
    let carrier = arena.value_type_unit();
    let declaration = ConstantIndex::from(9_usize);
    let types = BTreeMap::from([(Name::from("Box"), TypeBinding::Nominal {
        declaration,
        arity: TypeArity(1),
    })]);
    let context = context(carrier, &types);
    let applied = ValueTypeRef::ctor("Box", [ValueTypeRef::prim(PrimTy::StringTy)]);
    let result = decode_ref(&mut arena, &applied, context).unwrap();
    let Some(&ValueType::Data {
        declaration: actual,
        ref arguments,
    }) = arena.value_type(result)
    else {
        panic!("nominal application")
    };
    assert_eq!(actual, declaration);
    let &[argument] = arguments.as_slice()
    else {
        panic!("one argument")
    };
    let Some(&Value::Quote(ty)) = arena.value(argument)
    else {
        panic!("quoted argument")
    };
    assert_eq!(
        arena.value_type(ty),
        Some(&ValueType::Base(BaseType::String))
    );
    assert_eq!(
        decode_ref(&mut arena, &ValueTypeRef::ctor("Box", []), context),
        Err(DecodeError::AppliedType(Name::from("Box")))
    );
}

#[test]
fn native_signatures_keep_nominality_and_empty_data()
{
    let mut arena = CoreArena::new();
    let carrier = arena.value_type_data(ConstantIndex::from(3_usize), Vec::new());
    let kind = arena.value_type_universe(
        Sort::Ground(gandr_kernel_term::GroundSort::Value),
        Level::zero(),
    );
    let types = BTreeMap::new();
    let context = context(carrier, &types);
    let desc = description(vec![
        Code::unit(),
        Code::prod(field(PrimTy::Integer), Code::var("Self")),
    ]);
    let signature = decode_signature(&mut arena, &desc, context, Vec::new(), kind).unwrap();
    let [ref empty, ref fields] = *signature.constructors()
    else {
        panic!("two tags")
    };
    assert_eq!(empty, &Vec::<ValueTypeId>::new());
    let &[integer, recursive] = fields.as_slice()
    else {
        panic!("two fields")
    };
    assert_eq!(
        arena.value_type(integer),
        Some(&ValueType::Base(BaseType::Integer))
    );
    assert_eq!(recursive, carrier);
    let empty = decode_signature(
        &mut arena,
        &description(Vec::new()),
        context,
        Vec::new(),
        kind,
    )
    .unwrap();
    assert_eq!(empty.constructors().iter().next(), None);
    assert_eq!(empty.kind(), kind);
}

#[test]
fn native_indices_remain_values_under_telescope_scope()
{
    let mut arena = CoreArena::new();
    let carrier = arena.value_type_unit();
    let kind = arena.value_type_universe(
        Sort::Ground(gandr_kernel_term::GroundSort::Value),
        Level::zero(),
    );
    let integer = arena.value_type_base(BaseType::Integer);
    let declaration = ConstantIndex::from(4_usize);
    let types = BTreeMap::from([
        (Name::from("Indexed"), TypeBinding::Nominal {
            declaration,
            arity: TypeArity(2),
        }),
        (Name::from("a"), TypeBinding::Type(integer)),
        (Name::from("n"), TypeBinding::Parameter {
            level: super::ParameterLevel(1),
            classifier: integer,
        }),
    ]);
    let local_name = Name::from("a");
    let locals = [super::LocalBinding {
        name: &local_name,
        binding: TypeBinding::Parameter {
            level: super::ParameterLevel(0),
            classifier: kind,
        },
    }];
    let context = DecodeContext {
        locals: &locals,
        depth: super::ParameterDepth(2),
        ..context(carrier, &types)
    };
    let applied = ValueTypeRef::ctor("Indexed", [
        ValueTypeRef::param("a"),
        ValueTypeRef::param("n"),
    ]);
    let result = decode_ref(&mut arena, &applied, context).unwrap();
    let Some(&ValueType::Data {
        declaration: actual,
        ref arguments,
    }) = arena.value_type(result)
    else {
        panic!("native nominal application")
    };
    assert_eq!(actual, declaration);
    let &[first, second] = arguments.as_slice()
    else {
        panic!("type and value arguments")
    };
    assert_eq!(
        arena.value(first),
        Some(&Value::Variable {
            zone: crate::Zone::Intuitionistic,
            index: gandr_kernel_term::DeBruijnIndex::from(1_u32)
        })
    );
    assert_eq!(
        arena.value(second),
        Some(&Value::Variable {
            zone: crate::Zone::Intuitionistic,
            index: gandr_kernel_term::DeBruijnIndex::from(0_u32)
        })
    );
    assert_eq!(
        decode_ref(&mut arena, &ValueTypeRef::param("n"), context),
        Err(DecodeError::AppliedType(Name::from("n")))
    );
    assert_eq!(
        decode_ref(&mut arena, &applied, DecodeContext {
            depth: super::ParameterDepth(1),
            ..context
        }),
        Err(DecodeError::ParameterArity)
    );
}
