use alloc::vec;
use alloc::vec::Vec;

use gandr_kernel_strata::Level;
use gandr_kernel_term::BaseType;
use gandr_kernel_term::Builtin;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::ConstructorTag;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::Departure;
use gandr_kernel_term::FieldPosition;
use gandr_kernel_term::GroundSort;
use gandr_kernel_term::LevelSignature;
use gandr_kernel_term::TermArena;
use gandr_kernel_term::ValueTypeId;

use crate::env::Environment;
use crate::error::KernelError;

/// Which part of a canonical form a fixture departs at.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Shape
{
    /// The canonical form.
    Canonical,
    /// The signature type with `σ` and `δ` in the other order, or the pair
    /// type with a second field of the first type.
    Departing,
}

/// The value universe at level `level`.
///
/// # Specification
/// trivial.
fn universe(
    arena: &mut TermArena,
    level: Level,
) -> ValueTypeId
{
    arena.value_type_universe(GroundSort::Value, level)
}

/// The type the variable `index` binders out decodes to.
///
/// # Specification
/// trivial.
fn element(
    arena: &mut TermArena,
    index: DeBruijnIndex,
) -> ValueTypeId
{
    let code = arena.value_variable(index);
    arena.value_type_element(code, Level::zero())
}

/// Admit the signature type at the next position, holding `irSignature`,
/// in `shape`.
///
/// # Specification
/// trivial.
fn admit_signature(
    environment: &mut Environment,
    shape: Shape,
) -> Result<(), KernelError>
{
    let holder = ConstantIndex::from(usize::from(environment.entries().len()));
    let mut staging = environment.stage();
    let arena = staging.arena();
    let Ok(one) = Level::zero().succ()
    else {
        return Err(KernelError::ArenaFault);
    };
    let parameter = universe(arena, Level::zero());
    let sig = |arena: &mut TermArena, index: u32| {
        let output = arena.value_variable(DeBruijnIndex::from(index));
        let applied = arena.value_type_data(holder, vec![output]);
        arena.comp_type_returner(applied)
    };
    // ι(e : O).
    let stop = element(arena, DeBruijnIndex::from(0_u32));
    // σ(A : Type, f : A -> Sig(O)).
    let shape_sigma = universe(arena, Level::zero());
    let domain = element(arena, DeBruijnIndex::from(0_u32));
    let codomain = sig(arena, 1);
    let picked = arena.comp_type_arrow(domain, codomain);
    let picked = arena.value_type_thunk(picked);
    // δ(A : Type, f : (A -> O) -> Sig(O)).
    let shape_delta = universe(arena, Level::zero());
    let inner = element(arena, DeBruijnIndex::from(0_u32));
    let output = element(arena, DeBruijnIndex::from(1_u32));
    let output = arena.comp_type_returner(output);
    let decode = arena.comp_type_arrow(inner, output);
    let decode = arena.value_type_thunk(decode);
    let codomain = sig(arena, 1);
    let decoded = arena.comp_type_arrow(decode, codomain);
    let decoded = arena.value_type_thunk(decoded);
    let kind = universe(arena, one);
    let (sigma, delta) = (vec![shape_sigma, picked], vec![shape_delta, decoded]);
    let constructors = match shape {
        Shape::Canonical => vec![vec![stop], sigma, delta],
        Shape::Departing => vec![vec![stop], delta, sigma],
    };
    let declaration = staging
        .indexed(
            LevelSignature::monomorphic(),
            vec![parameter],
            (Vec::new(), constructors, Vec::new()),
            kind,
        )
        .held(Builtin::IrSignature);
    environment.add_decl(declaration).map(|_admitted| ())
}

/// Admit the pair type at the next position, holding `role`, in `shape`.
///
/// # Specification
/// trivial.
fn admit_pair(
    environment: &mut Environment,
    shape: Shape,
    role: Builtin,
) -> Result<(), KernelError>
{
    let mut staging = environment.stage();
    let arena = staging.arena();
    let first = universe(arena, Level::zero());
    // B : A -> Type, A at 0.
    let domain = element(arena, DeBruijnIndex::from(0_u32));
    let codes = universe(arena, Level::zero());
    let codomain = arena.comp_type_returner(codes);
    let family = arena.comp_type_arrow(domain, codomain);
    let family = arena.value_type_thunk(family);
    // x : A, A at 1 under B.
    let x = element(arena, DeBruijnIndex::from(1_u32));
    // y : B(x), B at 1 and x at 0.
    let read = arena.value_variable(DeBruijnIndex::from(1_u32));
    let forced = arena.computation_force(read);
    let at = arena.value_variable(DeBruijnIndex::from(0_u32));
    let applied = arena.computation_application(forced, at);
    let returned = arena.value_returned(applied);
    let y = arena.value_type_element(returned, Level::zero());
    let kind = universe(arena, Level::zero());
    // A second field of the first type, `A` at 2 under `B` and `x`: the
    // declaration still forms, and only its role departs.
    let plain = element(arena, DeBruijnIndex::from(2_u32));
    let fields = match shape {
        Shape::Canonical => vec![x, y],
        Shape::Departing => vec![x, plain],
    };
    let declaration = staging
        .indexed(
            LevelSignature::monomorphic(),
            vec![first, family],
            (Vec::new(), vec![fields], Vec::new()),
            kind,
        )
        .held(role);
    environment.add_decl(declaration).map(|_admitted| ())
}

/// Admit, holding `role`, the definition `λ O c X t. return Integer`: a
/// holder of `E` whose answer is `Integer` at every constructor.
///
/// # Specification
/// trivial.
fn admit_integer(
    environment: &mut Environment,
    role: Builtin,
) -> Result<(), KernelError>
{
    let mut staging = environment.stage();
    let arena = staging.arena();
    let unit = arena.value_type_unit();
    let codes = universe(arena, Level::zero());
    let returner = arena.comp_type_returner(codes);
    let arrows = (0_u32 .. 4_u32).fold(returner, |codomain, _| {
        arena.comp_type_arrow(unit, codomain)
    });
    let declared = arena.value_type_thunk(arrows);
    let integer = arena.value_type_base(BaseType::Integer);
    let integer = arena.value_quote(integer);
    let answer = arena.computation_return(integer);
    let curried = (0_u32 .. 4_u32).fold(answer, |body, _| arena.computation_lambda(body));
    let body = arena.value_thunk(curried);
    let declaration = staging
        .def(LevelSignature::monomorphic(), declared, body)
        .held(role);
    environment.add_decl(declaration).map(|_admitted| ())
}

#[test]
fn a_role_s_holder_is_admitted_in_its_canonical_form_5304()
{
    let mut environment = Environment::new();
    assert_eq!(
        admit_signature(&mut environment, Shape::Canonical),
        Ok(()),
        "the canonical signature type holds its role in the kernel"
    );
    assert_eq!(
        admit_signature(&mut environment, Shape::Canonical),
        Err(KernelError::BuiltinRepeated {
            role: Builtin::IrSignature,
            holder: ConstantIndex::from(0_usize),
        }),
        "a second holder is refused by the first's position"
    );
    assert_eq!(
        admit_pair(&mut environment, Shape::Canonical, Builtin::IrPair),
        Ok(()),
        "the canonical pair type holds its role in the kernel"
    );
}

#[test]
fn a_departing_holder_is_refused_at_its_departure_5304()
{
    let mut environment = Environment::new();
    assert_eq!(
        admit_signature(&mut environment, Shape::Departing),
        Err(KernelError::BuiltinNotCanonical {
            role: Builtin::IrSignature,
            departure: Departure::Field {
                tag: ConstructorTag::from(1_usize),
                field: FieldPosition::from(1_usize),
            },
        }),
        "σ and δ in the other order depart at σ's function"
    );
    assert_eq!(
        admit_signature(&mut environment, Shape::Canonical),
        Ok(()),
        "the refused datatype held no role"
    );
    assert_eq!(
        admit_integer(&mut environment, Builtin::IrArgs),
        Err(KernelError::BuiltinNotCanonical {
            role: Builtin::IrArgs,
            departure: Departure::Reads(Builtin::IrPair),
        }),
        "`E` reads the pair type, which no declaration holds yet"
    );
    assert_eq!(
        admit_pair(&mut environment, Shape::Departing, Builtin::IrPair),
        Err(KernelError::BuiltinNotCanonical {
            role: Builtin::IrPair,
            departure: Departure::Field {
                tag: ConstructorTag::from(0_usize),
                field: FieldPosition::from(1_usize),
            },
        }),
        "a second field of the first type departs at the second field"
    );
    assert_eq!(
        admit_pair(&mut environment, Shape::Canonical, Builtin::IrPair),
        Ok(())
    );
    assert_eq!(
        admit_integer(&mut environment, Builtin::IrArgs),
        Err(KernelError::BuiltinNotCanonical {
            role: Builtin::IrArgs,
            departure: Departure::Answer(ConstructorTag::from(0_usize)),
        }),
        "an answer of `Integer` at `ι` departs from the unit type there"
    );
}

#[test]
fn a_departing_family_and_decoder_are_refused_3575()
{
    let mut environment = Environment::new();
    assert_eq!(
        admit_integer(&mut environment, Builtin::IrDecoder),
        Err(KernelError::BuiltinNotCanonical {
            role: Builtin::IrDecoder,
            departure: Departure::Reads(Builtin::IrFamily),
        }),
        "the decoder reads the family, which no declaration holds yet"
    );
    assert_eq!(
        admit_pair(&mut environment, Shape::Canonical, Builtin::IrFamily),
        Err(KernelError::BuiltinNotCanonical {
            role: Builtin::IrFamily,
            departure: Departure::Reads(Builtin::IrSignature),
        }),
        "the family reads the signature type, which no declaration holds yet"
    );
    assert_eq!(admit_signature(&mut environment, Shape::Canonical), Ok(()));
    assert_eq!(
        admit_pair(&mut environment, Shape::Canonical, Builtin::IrFamily),
        Err(KernelError::BuiltinNotCanonical {
            role: Builtin::IrFamily,
            departure: Departure::Reads(Builtin::IrArgs),
        }),
        "the family reads `E`, which no declaration holds yet"
    );
}

#[test]
fn the_hypotheses_map_and_eliminator_read_their_roles_first_5160()
{
    let mut environment = Environment::new();
    assert_eq!(
        admit_integer(&mut environment, Builtin::IrHypotheses),
        Err(KernelError::BuiltinNotCanonical {
            role: Builtin::IrHypotheses,
            departure: Departure::Reads(Builtin::IrSignature),
        }),
        "the hypotheses read the signature type, which no declaration holds yet"
    );
    assert_eq!(
        admit_integer(&mut environment, Builtin::IrEliminator),
        Err(KernelError::BuiltinNotCanonical {
            role: Builtin::IrEliminator,
            departure: Departure::Reads(Builtin::IrFamily),
        }),
        "the eliminator reads the family, which no declaration holds yet"
    );
    assert_eq!(admit_signature(&mut environment, Shape::Canonical), Ok(()));
    assert_eq!(
        admit_pair(&mut environment, Shape::Canonical, Builtin::IrPair),
        Ok(())
    );
    assert_eq!(
        admit_integer(&mut environment, Builtin::IrMap),
        Err(KernelError::BuiltinNotCanonical {
            role: Builtin::IrMap,
            departure: Departure::Reads(Builtin::IrArgs),
        }),
        "the map reads `E`, which no declaration holds yet"
    );
}
