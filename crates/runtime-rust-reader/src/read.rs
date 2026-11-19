//! The record of the requested functions, from rustc's own answers.
//!
//! The symbol is `symbol_name` of the function's instance. The convention is
//! `fn_abi_of_instance`, and each LLVM type is spelled as rustc's LLVM
//! backend spells it for that passage. Each layout is `layout_of` the
//! operand's type.

use std::collections::HashMap;

use gandr_runtime_rust_record::Arm;
use gandr_runtime_rust_record::Available;
use gandr_runtime_rust_record::Bytes;
use gandr_runtime_rust_record::Discriminant;
use gandr_runtime_rust_record::Extension;
use gandr_runtime_rust_record::Field;
use gandr_runtime_rust_record::FieldName;
use gandr_runtime_rust_record::Function;
use gandr_runtime_rust_record::FunctionPath;
use gandr_runtime_rust_record::Layout;
use gandr_runtime_rust_record::LlvmType;
use gandr_runtime_rust_record::Niche;
use gandr_runtime_rust_record::Operand;
use gandr_runtime_rust_record::Outcome;
use gandr_runtime_rust_record::Part;
use gandr_runtime_rust_record::Passage;
use gandr_runtime_rust_record::Refusal;
use gandr_runtime_rust_record::Shape;
use gandr_runtime_rust_record::Symbol;
use gandr_runtime_rust_record::TypeName;
use gandr_runtime_rust_record::Unstatable;
use gandr_runtime_rust_record::VariantName;
use rustc_abi::AddressSpace;
use rustc_abi::BackendRepr;
use rustc_abi::FieldsShape;
use rustc_abi::Float;
use rustc_abi::Integer;
use rustc_abi::Primitive;
use rustc_abi::Reg;
use rustc_abi::RegKind;
use rustc_abi::Scalar;
use rustc_abi::Size;
use rustc_abi::TagEncoding;
use rustc_abi::Variants;
use rustc_hir::def::DefKind;
use rustc_hir::def_id::LocalDefId;
use rustc_middle::ty;
use rustc_middle::ty::Ty;
use rustc_middle::ty::TyCtxt;
use rustc_middle::ty::layout::TyAndLayout;
use rustc_target::callconv::ArgAbi;
use rustc_target::callconv::ArgExtension;
use rustc_target::callconv::CastTarget;
use rustc_target::callconv::IndirectMode;
use rustc_target::callconv::PassMode;

/// The record of each requested path: each function, or each refusal.
pub(crate) fn outcome(
    tcx: TyCtxt<'_>,
    paths: &[FunctionPath],
) -> Outcome
{
    let mut local = HashMap::new();
    for def_id in tcx.hir_crate_items(()).definitions() {
        if tcx.def_kind(def_id) == DefKind::Fn
            && let Some(path) = path_of(tcx, def_id)
        {
            local.insert(path, def_id);
        }
    }
    let mut functions = Vec::with_capacity(paths.len());
    let mut refusals = Vec::new();
    for path in paths {
        match function(tcx, &local, path) {
            Ok(function) => functions.push(function),
            Err(refusal) => refusals.push(refusal),
        }
    }
    if refusals.is_empty() {
        Outcome::Read(functions)
    }
    else {
        Outcome::Refused(refusals)
    }
}

/// A function's path inside its crate, or nothing when a segment has no
/// name, as in a function inside a block.
fn path_of(
    tcx: TyCtxt<'_>,
    def_id: LocalDefId,
) -> Option<String>
{
    let mut path = String::new();
    for segment in tcx.def_path(def_id.to_def_id()).data {
        let name = segment.data.get_opt_name()?;
        if !path.is_empty() {
            path.push_str("::");
        }
        path.push_str(name.as_str());
    }
    Some(path)
}

/// The record of one function, or why the record cannot state it.
fn function(
    tcx: TyCtxt<'_>,
    local: &HashMap<String, LocalDefId>,
    path: &FunctionPath,
) -> Result<Function, Refusal>
{
    let Some(&def_id) = local.get(path.as_ref())
    else {
        return Err(Refusal::Missing(path.clone()));
    };
    if tcx.generics_of(def_id).count() != 0 {
        return Err(Refusal::Generic(path.clone()));
    }
    if !tcx.effective_visibilities(()).is_exported(def_id) {
        return Err(Refusal::NotPublic(path.clone()));
    }
    if tcx.cross_crate_inlinable(def_id) {
        return Err(Refusal::Inlined(path.clone()));
    }
    let instance = ty::Instance::mono(tcx, def_id.to_def_id());
    let symbol = Symbol::from(tcx.symbol_name(instance).name);
    let input = ty::TypingEnv::fully_monomorphized().as_query_input((instance, ty::List::empty()));
    let Ok(abi) = tcx.fn_abi_of_instance(input)
    else {
        let ty = TypeName::from(tcx.def_path_str(def_id.to_def_id()));
        return Err(Refusal::Unstated {
            function: path.clone(),
            ty,
            why: Unstatable::Passage,
        });
    };
    let mut arguments = Vec::with_capacity(abi.args.len());
    for argument in &abi.args {
        arguments.push(operand(tcx, path, argument)?);
    }
    let result = operand(tcx, path, &abi.ret)?;
    Ok(Function {
        path: path.clone(),
        symbol,
        arguments,
        result,
    })
}

/// One operand: its passage and its layout.
fn operand<'tcx>(
    tcx: TyCtxt<'tcx>,
    path: &FunctionPath,
    argument: &ArgAbi<'tcx, Ty<'tcx>>,
) -> Result<Operand, Refusal>
{
    let unstated = |why| Refusal::Unstated {
        function: path.clone(),
        ty: TypeName::from(argument.layout.ty.to_string()),
        why,
    };
    let layout = layout(tcx, argument.layout).map_err(unstated)?;
    let passage = passage(tcx, argument).map_err(unstated)?;
    Ok(Operand { passage, layout })
}

/// How an operand passes, as rustc's LLVM backend spells it.
fn passage<'tcx>(
    tcx: TyCtxt<'tcx>,
    argument: &ArgAbi<'tcx, Ty<'tcx>>,
) -> Result<Passage, Unstatable>
{
    match argument.mode {
        PassMode::Ignore => Ok(Passage::Ignore),
        PassMode::Direct(attributes) => {
            let ty = match argument.layout.backend_repr {
                BackendRepr::Scalar(scalar) => immediate(tcx, scalar),
                BackendRepr::SimdVector { element, count } => LlvmType::from(format!(
                    "<{} x {}>",
                    count.as_u64(),
                    primitive(tcx, element.primitive())
                )),
                BackendRepr::ScalarPair { .. }
                | BackendRepr::SimdScalableVector { .. }
                | BackendRepr::Memory { .. } => {
                    return Err(Unstatable::Passage);
                },
            };
            Ok(Passage::Direct(Part {
                ty,
                extension: extension(attributes.arg_ext),
            }))
        },
        PassMode::Pair(first, second) => {
            let BackendRepr::ScalarPair { a, b, .. } = argument.layout.backend_repr
            else {
                return Err(Unstatable::Passage);
            };
            Ok(Passage::Pair(
                Part {
                    ty: immediate(tcx, a),
                    extension: extension(first.arg_ext),
                },
                Part {
                    ty: immediate(tcx, b),
                    extension: extension(second.arg_ext),
                },
            ))
        },
        PassMode::Cast {
            pad_i32_count,
            ref cast,
        } => {
            if pad_i32_count != 0 {
                return Err(Unstatable::Passage);
            }
            Ok(Passage::Cast(Part {
                ty: cast_type(cast)?,
                extension: extension(cast.attrs.arg_ext),
            }))
        },
        PassMode::Indirect {
            meta_attrs: Some(_),
            ..
        } => Err(Unstatable::Unsized),
        PassMode::Indirect {
            attrs,
            meta_attrs: None,
            address_space,
            mode,
        } => {
            let part = Part {
                ty: pointer(address_space.unwrap_or(AddressSpace::ZERO)),
                extension: extension(attrs.arg_ext),
            };
            match mode {
                IndirectMode::Pointer => Ok(Passage::Indirect(part)),
                IndirectMode::OnStack => Ok(Passage::OnStack(part)),
                IndirectMode::AmdgpuKernelArg => Err(Unstatable::Passage),
            }
        },
    }
}

/// The extension of a value.
fn extension(extension: ArgExtension) -> Extension
{
    match extension {
        ArgExtension::None => Extension::Plain,
        ArgExtension::Zext => Extension::Zero,
        ArgExtension::Sext => Extension::Sign,
    }
}

/// The LLVM type of a scalar passed as a value: `i1` for a `bool`.
fn immediate(
    tcx: TyCtxt<'_>,
    scalar: Scalar,
) -> LlvmType
{
    if scalar.is_bool() {
        LlvmType::from("i1")
    }
    else {
        primitive(tcx, scalar.primitive())
    }
}

/// The LLVM type of a primitive.
fn primitive(
    _tcx: TyCtxt<'_>,
    primitive: Primitive,
) -> LlvmType
{
    match primitive {
        Primitive::Int(integer, _) => LlvmType::from(match integer {
            Integer::I8 => "i8",
            Integer::I16 => "i16",
            Integer::I32 => "i32",
            Integer::I64 => "i64",
            Integer::I128 => "i128",
        }),
        Primitive::Float(float) => LlvmType::from(match float {
            Float::F16 => "half",
            Float::F16B => "bfloat",
            Float::F32 => "float",
            Float::F64 => "double",
            Float::F128 => "fp128",
        }),
        Primitive::Pointer(space) => pointer(space),
    }
}

/// The LLVM type of an address in an address space.
fn pointer(space: AddressSpace) -> LlvmType
{
    if space == AddressSpace::ZERO {
        LlvmType::from("ptr")
    }
    else {
        LlvmType::from(format!("ptr addrspace({})", space.0))
    }
}

/// The LLVM type of a register.
fn register(reg: Reg) -> Result<String, Unstatable>
{
    match reg.kind {
        RegKind::Integer => Ok(format!("i{}", reg.size.bits())),
        RegKind::Float => match reg.size.bits() {
            16 => Ok(String::from("half")),
            32 => Ok(String::from("float")),
            64 => Ok(String::from("double")),
            128 => Ok(String::from("fp128")),
            _ => Err(Unstatable::Passage),
        },
        RegKind::Vector { hint_vector_elem } => {
            let element = match hint_vector_elem {
                Primitive::Int(integer, _) => format!("i{}", integer.size().bits()),
                Primitive::Float(Float::F16) => String::from("half"),
                Primitive::Float(Float::F16B) => String::from("bfloat"),
                Primitive::Float(Float::F32) => String::from("float"),
                Primitive::Float(Float::F64) => String::from("double"),
                Primitive::Float(Float::F128) => String::from("fp128"),
                Primitive::Pointer(_) => String::from("ptr"),
            };
            let width = match hint_vector_elem {
                Primitive::Int(integer, _) => integer.size(),
                Primitive::Float(float) => float.size(),
                Primitive::Pointer(_) => return Err(Unstatable::Passage),
            };
            if width == Size::ZERO || !reg.size.bytes().is_multiple_of(width.bytes()) {
                return Err(Unstatable::Passage);
            }
            Ok(format!(
                "<{} x {element}>",
                reg.size.bytes() / width.bytes()
            ))
        },
    }
}

/// The LLVM type of a cast, as rustc's LLVM backend builds it.
fn cast_type(cast: &CastTarget) -> Result<LlvmType, Unstatable>
{
    let unit = register(cast.rest.unit)?;
    let count = if cast.rest.total == Size::ZERO {
        0
    }
    else if cast.rest.unit.size == Size::ZERO {
        return Err(Unstatable::Passage);
    }
    else {
        cast.rest
            .total
            .bytes()
            .div_ceil(cast.rest.unit.size.bytes())
    };
    if cast.prefix.is_empty() {
        if count == 1 && (!cast.rest.is_consecutive || cast.rest.unit != Reg::i128()) {
            return Ok(LlvmType::from(unit));
        }
        return Ok(LlvmType::from(format!("[{count} x {unit}]")));
    }
    let mut parts = Vec::with_capacity(cast.prefix.len());
    for reg in &cast.prefix {
        parts.push(register(*reg)?);
    }
    for _ in 0 .. count {
        parts.push(unit.clone());
    }
    Ok(LlvmType::from(format!("{{ {} }}", parts.join(", "))))
}

/// The layout of a type: size, stride, alignment, the offset of each field
/// and the niche.
fn layout<'tcx>(
    tcx: TyCtxt<'tcx>,
    layout: TyAndLayout<'tcx>,
) -> Result<Layout, Unstatable>
{
    if layout.backend_repr.is_unsized() {
        return Err(Unstatable::Unsized);
    }
    if layout.is_uninhabited() {
        return Err(Unstatable::Uninhabited);
    }
    let niche = layout.largest_niche.map_or(Niche::None, |niche| Niche::At {
        offset: Bytes::from(niche.offset.bytes()),
        width: Bytes::from(niche.value.size(&tcx).bytes()),
        available: Available::from(niche.available(&tcx)),
    });
    let shape = match layout.variants {
        Variants::Empty => return Err(Unstatable::Uninhabited),
        Variants::Single { index } => match *layout.ty.kind() {
            ty::Adt(adt, _) if adt.is_enum() => {
                let variant = adt.variant(index);
                let offsets = (0 .. layout.fields.count()).map(|field| layout.fields.offset(field));
                Shape::Enum {
                    discriminant: Discriminant::Unneeded,
                    arms: vec![Arm {
                        name: VariantName::from(variant.name.as_str()),
                        fields: named(
                            variant.fields.iter().map(|field| field.name.to_string()),
                            offsets,
                        ),
                    }],
                }
            },
            ty::Adt(adt, _) if adt.is_union() => return Err(Unstatable::Union),
            _ => match layout.fields {
                FieldsShape::Primitive => Shape::Scalar,
                FieldsShape::Union(_) => return Err(Unstatable::Union),
                FieldsShape::Array { .. } => return Err(Unstatable::Array),
                FieldsShape::Arbitrary { ref offsets, .. } => {
                    let names: Vec<String> = match *layout.ty.kind() {
                        ty::Adt(adt, _) => adt
                            .non_enum_variant()
                            .fields
                            .iter()
                            .map(|field| field.name.to_string())
                            .collect(),
                        _ => (0 .. offsets.len())
                            .map(|index| index.to_string())
                            .collect(),
                    };
                    Shape::Struct(named(names.into_iter(), offsets.iter().copied()))
                },
            },
        },
        Variants::Multiple {
            tag,
            ref tag_encoding,
            tag_field,
            ref variants,
        } => {
            let ty::Adt(adt, _) = *layout.ty.kind()
            else {
                return Err(Unstatable::Passage);
            };
            let offset = Bytes::from(layout.fields.offset(tag_field.as_usize()).bytes());
            let discriminant = match *tag_encoding {
                TagEncoding::Direct => Discriminant::Tag {
                    offset,
                    size: Bytes::from(tag.size(&tcx).bytes()),
                },
                TagEncoding::Niche { .. } => Discriminant::Niche { offset },
            };
            let mut arms = Vec::with_capacity(variants.len());
            for (index, variant) in variants.iter_enumerated() {
                let declared = adt.variant(index);
                let names = declared.fields.iter().map(|field| field.name.to_string());
                arms.push(Arm {
                    name: VariantName::from(declared.name.as_str()),
                    fields: named(names, variant.field_offsets.iter().copied()),
                });
            }
            Shape::Enum { discriminant, arms }
        },
    };
    Ok(Layout {
        ty: TypeName::from(layout.ty.to_string()),
        size: Bytes::from(layout.size.bytes()),
        stride: Bytes::from(layout.size.align_to(layout.align.abi).bytes()),
        align: Bytes::from(layout.align.abi.bytes()),
        niche,
        shape,
    })
}

/// Each field's name beside its offset, in declared order.
fn named(
    names: impl Iterator<Item = String>,
    offsets: impl Iterator<Item = Size>,
) -> Vec<Field>
{
    names
        .zip(offsets)
        .map(|(name, offset)| Field {
            name: FieldName::from(name),
            offset: Bytes::from(offset.bytes()),
        })
        .collect()
}
