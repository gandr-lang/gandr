//! The canonical forms that the holder of a built-in role answers.
//!
//! A role's holder is ordinary source, so the checker never believes its
//! mark. It compares the holder with the form that the role states, and
//! refuses a holder that departs from it, naming the first place where it
//! departs.
//!
//! The signature type of an inductive-recursive definition is a data
//! declaration over one parameter `O : Type`. Its constructors are, in this
//! order, `ι(e : O)`, `σ(A : Type, f : A -> Sig(O))` and
//! `δ(A : Type, f : (A -> O) -> Sig(O))`, where `Sig` is the holder applied to
//! its parameter (Kovács 2026, § 2.2). A field's type stands under the
//! parameter and the fields before it, so `O` is the variable one binder out
//! inside `ι` and two binders out inside `σ` and `δ`.
//!
//! The pair type is a data declaration over `A : Type` and `B : A -> Type`,
//! with one constructor `(x : A, y : B(x))`.
//!
//! `E` and `F` are value declarations by recursion on the signature. Their
//! holders are compared by their answers at each constructor of the
//! signature type, under rigid variables for the parameters and the fields:
//!
//! |Constructor|`E(O, c, X, t)`|`F(O, c, X, t, v)`|
//! |---|---|---|
//! |`ι(e)`|the unit type|`e`|
//! |`σ(A, f)`|`Pair(A, λ a. E(O, f(a), X, t))`|at `v = (a, r)`: `F(O, f(a), X, t, r)`|
//! |`δ(A, f)`|`Pair(A -> X, λ h. E(O, f(t ∘ h), X, t))`|at `v = (h, r)`: `F(O, f(t ∘ h), X, t, r)`|
//!
//! `Pair` is the holder of the pair type. Each recursive call is the
//! holder's own body, so an answer that agrees at every constructor makes the
//! holder the canonical body: both recurse on the same signature by the same
//! steps.
//!
//! # References
//!
//! - `vault:01a183fc-63df-77a0-9df0-1c3f0b02ddf6` — anchor: the signature type
//!   of § 2.2 and its three constructors, and `E` and `F` by recursion on a
//!   signature.

use anodized::spec;
use gandr_core_term::CertificateEquality;
use gandr_core_term::CompType;
use gandr_core_term::CompTypeId;
use gandr_core_term::Computation;
use gandr_core_term::ComputationId;
use gandr_core_term::CoreArena;
use gandr_core_term::DataSignature;
use gandr_core_term::Sort;
use gandr_core_term::Value;
use gandr_core_term::ValueId;
use gandr_core_term::ValueType;
use gandr_core_term::ValueTypeId;
use gandr_core_term::Zone;
use gandr_core_term::effect::Purity;
use gandr_core_term::equal_certificate_syntax;
use gandr_kernel_strata::Level;
use gandr_kernel_term::Builtin;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::ConstructorTag;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::Departure;
use gandr_kernel_term::FieldPosition;
use gandr_kernel_term::GroundSort;

use crate::context::CheckingContext;

/// Compare the data declaration at `holder` with the canonical signature
/// type of an inductive-recursive definition.
///
/// # Specification
/// - requires: `signature` is the signature of the data declaration at
///   `holder`, its nodes in `arena`.
/// - ensures: `Ok(())` exactly when the signature has one value-universe
///   parameter, no index and the constructors `ι(e : O)`, `σ(A : Type, f : A ->
///   Sig(O))` and `δ(A : Type, f : (A -> O) -> Sig(O))` in this order, each
///   arrow pure and `Sig` the holder at its parameter.
/// - fails: the first [`Departure`] in the order parameters, indices,
///   constructors, then each constructor's arity and fields in tag and field
///   order.
/// - panics: none.
///
/// # Errors
/// - [`Departure::Parameters`]: another number of parameters, or one that is no
///   value universe.
/// - [`Departure::Indices`]: an index telescope.
/// - [`Departure::Constructors`]: another number of constructors.
/// - [`Departure::Arity`]: a constructor with another number of fields.
/// - [`Departure::Field`]: the first field whose type departs.
///
/// # Adequacy
/// - hypothesis: L3 — the canonical signature is admitted. A signature with `σ`
///   and `δ` swapped, a second parameter, two constructors, a `δ` of one field,
///   an `ι` field that is a universe and a `σ` returning another family are
///   each refused at their first departure.
/// - witness: `canonical::tests::the_canonical_signature_type_is_admitted_5254`
/// - witness: `canonical::tests::a_signature_type_is_refused_at_its_first_departure_5254`
#[spec(ensures: |ret| ret.is_err()
    || (signature.parameters().len() == 1
        && signature.indices().is_empty()
        && signature.constructors().iter().map(alloc::vec::Vec::len).eq([1_usize, 2, 2])))]
pub fn signature(
    arena: &CoreArena,
    holder: ConstantIndex,
    signature: &DataSignature,
) -> Result<(), Departure>
{
    let field = |tag: usize, position: usize| Departure::Field {
        tag: ConstructorTag::from(tag),
        field: FieldPosition::from(position),
    };
    // A variable `index` binders out, as a value of the intuitionistic zone.
    let variable = |value: ValueId, index: u32| {
        matches!(
            arena.value(value),
            Some(&Value::Variable {
                zone: Zone::Intuitionistic,
                index: found,
            }) if found == DeBruijnIndex::from(index)
        )
    };
    let universe = |value_type: ValueTypeId| {
        matches!(
            arena.value_type(value_type),
            Some(&ValueType::Universe {
                sort: Sort::Ground(GroundSort::Value),
                ..
            })
        )
    };
    // The type that the variable `index` binders out decodes to.
    let element = |value_type: ValueTypeId, index: u32| {
        matches!(
            arena.value_type(value_type),
            Some(&ValueType::Element { code, .. }) if variable(code, index)
        )
    };
    // The domain and codomain of a thunked arrow.
    let arrow = |value_type: ValueTypeId| -> Result<(ValueTypeId, CompTypeId), ()> {
        let Some(&ValueType::Thunk(body)) = arena.value_type(value_type)
        else {
            return Err(());
        };
        match arena.comp_type(body) {
            Some(&CompType::Arrow { domain, codomain }) => Ok((domain, codomain)),
            Some(_) | None => Err(()),
        }
    };
    // The result of a pure returner.
    let returned = |comp_type: CompTypeId| -> Result<ValueTypeId, ()> {
        match arena.comp_type(comp_type) {
            Some(&CompType::Returner {
                result,
                ref effects,
            }) if effects.purity() == Purity::Pure => Ok(result),
            Some(_) | None => Err(()),
        }
    };
    // The holder applied to the variable `index` binders out.
    let family = |value_type: ValueTypeId, index: u32| {
        matches!(
            arena.value_type(value_type),
            Some(&ValueType::Data { declaration, ref arguments })
                if declaration == holder
                    && matches!(**arguments, [argument] if variable(argument, index))
        )
    };
    let [parameter] = *signature.parameters()
    else {
        return Err(Departure::Parameters);
    };
    if !universe(parameter) {
        return Err(Departure::Parameters);
    }
    if !signature.indices().is_empty() {
        return Err(Departure::Indices);
    }
    let [ref iota, ref sigma, ref delta] = *signature.constructors()
    else {
        return Err(Departure::Constructors);
    };
    // ι(e : O).
    let [stop] = **iota
    else {
        return Err(Departure::Arity(ConstructorTag::from(0_usize)));
    };
    if !element(stop, 0) {
        return Err(field(0, 0));
    }
    // σ(A : Type, f : A -> Sig(O)).
    let [shape, rest] = **sigma
    else {
        return Err(Departure::Arity(ConstructorTag::from(1_usize)));
    };
    if !universe(shape) {
        return Err(field(1, 0));
    }
    let picked = arrow(rest).and_then(|(domain, codomain)| {
        let result = returned(codomain)?;
        if element(domain, 0) && family(result, 1) {
            Ok(())
        }
        else {
            Err(())
        }
    });
    if picked.is_err() {
        return Err(field(1, 1));
    }
    // δ(A : Type, f : (A -> O) -> Sig(O)).
    let [shape, rest] = **delta
    else {
        return Err(Departure::Arity(ConstructorTag::from(2_usize)));
    };
    if !universe(shape) {
        return Err(field(2, 0));
    }
    let decoded = arrow(rest).and_then(|(domain, codomain)| {
        let result = returned(codomain)?;
        let (inner, decode) = arrow(domain)?;
        let output = returned(decode)?;
        if element(inner, 0) && element(output, 1) && family(result, 1) {
            Ok(())
        }
        else {
            Err(())
        }
    });
    if decoded.is_err() {
        return Err(field(2, 1));
    }
    Ok(())
}

/// Compare the data declaration whose signature is `signature` with the
/// canonical pair type that `E` asks for.
///
/// # Specification
/// - requires: `signature`'s nodes are in `arena`.
/// - ensures: `Ok(())` exactly when the signature has the parameters `A : Type`
///   and `B : A -> Type`, no index and the one constructor `(x : A, y : B(x))`,
///   the arrow pure and `B(x)` the decode of `B` run at `x`.
/// - fails: the first [`Departure`] in the order parameters, indices,
///   constructors, then the constructor's arity and its fields in order.
/// - panics: none.
///
/// # Errors
/// - [`Departure::Parameters`]: another number of parameters, a first that is
///   no value universe or a second that is no family over the first.
/// - [`Departure::Indices`]: an index telescope.
/// - [`Departure::Constructors`]: another number of constructors.
/// - [`Departure::Arity`]: a constructor with another number of fields.
/// - [`Departure::Field`]: the first field whose type departs.
///
/// # Adequacy
/// - hypothesis: L3 — the canonical pair type is admitted. A pair type with its
///   fields swapped, a second field of the first type, a third parameter, a
///   second constructor and a constructor of one field are each refused at
///   their first departure.
/// - witness: `canonical::tests::the_canonical_pair_type_is_admitted_5255`
/// - witness: `canonical::tests::a_pair_type_is_refused_at_its_first_departure_5255`
#[spec(ensures: |ret| ret.is_err()
    || (signature.parameters().len() == 2
        && signature.indices().is_empty()
        && signature.constructors().iter().map(alloc::vec::Vec::len).eq([2_usize])))]
pub fn pair(
    arena: &CoreArena,
    signature: &DataSignature,
) -> Result<(), Departure>
{
    let field = |position: usize| Departure::Field {
        tag: ConstructorTag::from(0_usize),
        field: FieldPosition::from(position),
    };
    // A variable `index` binders out, as a value of the intuitionistic zone.
    let variable = |value: ValueId, index: u32| {
        matches!(
            arena.value(value),
            Some(&Value::Variable {
                zone: Zone::Intuitionistic,
                index: found,
            }) if found == DeBruijnIndex::from(index)
        )
    };
    let universe = |value_type: ValueTypeId| {
        matches!(
            arena.value_type(value_type),
            Some(&ValueType::Universe {
                sort: Sort::Ground(GroundSort::Value),
                ..
            })
        )
    };
    // The type that the variable `index` binders out decodes to.
    let element = |value_type: ValueTypeId, index: u32| {
        matches!(
            arena.value_type(value_type),
            Some(&ValueType::Element { code, .. }) if variable(code, index)
        )
    };
    // `A -> Type` under `A`: a thunked pure arrow from the decode of `A` into
    // the value universe.
    let family = |value_type: ValueTypeId| {
        let Some(&ValueType::Thunk(body)) = arena.value_type(value_type)
        else {
            return false;
        };
        let Some(&CompType::Arrow { domain, codomain }) = arena.comp_type(body)
        else {
            return false;
        };
        element(domain, 0)
            && matches!(
                arena.comp_type(codomain),
                Some(&CompType::Returner { result, ref effects })
                    if effects.purity() == Purity::Pure && universe(result)
            )
    };
    // `B(x)` under `A`, `B` and `x`: the decode of the code that `B` returns
    // at `x`.
    let applied = |value_type: ValueTypeId| {
        let Some(&ValueType::Element { code, .. }) = arena.value_type(value_type)
        else {
            return false;
        };
        let Some(&Value::Returned(run)) = arena.value(code)
        else {
            return false;
        };
        let Some(&Computation::Application(head, argument)) = arena.computation(run)
        else {
            return false;
        };
        variable(argument, 0)
            && matches!(arena.computation(head), Some(&Computation::Force(read)) if variable(read, 1))
    };
    let [first, second] = *signature.parameters()
    else {
        return Err(Departure::Parameters);
    };
    if !universe(first) || !family(second) {
        return Err(Departure::Parameters);
    }
    if !signature.indices().is_empty() {
        return Err(Departure::Indices);
    }
    let [ref only] = *signature.constructors()
    else {
        return Err(Departure::Constructors);
    };
    let [x, y] = **only
    else {
        return Err(Departure::Arity(ConstructorTag::from(0_usize)));
    };
    // `x : A`, under `A` and `B`.
    if !element(x, 1) {
        return Err(field(0));
    }
    if !applied(y) {
        return Err(field(1));
    }
    Ok(())
}

/// Compare the data declaration at `holder` with the canonical family that a
/// signature defines.
///
/// # Specification
/// - requires: `signature` is the signature of the data declaration at
///   `holder`, its nodes in `arena`; `signed` holds the signature role and
///   `fields` the role of `E`.
/// - ensures: `Ok(())` exactly when the signature has the parameters `O : Type`
///   and `S : Sig(O)`, no index and one constructor of one field, the decode of
///   `E(O, S, ⌜IR(O, S)⌝, λ m. el(O, S, m))`, as syntax: `Sig` the holder at
///   `signed`, `E` the holder at `fields`, `IR` the holder at its parameters
///   and `el` the declaration right after it. The arena keeps the minted
///   canonical code.
/// - fails: the first [`Departure`] in the order parameters, indices,
///   constructors, then the constructor's arity and its field.
/// - panics: none.
///
/// # Errors
/// - [`Departure::Parameters`]: another number of parameters, a first that is
///   no value universe, or a second that is no signature over the first.
/// - [`Departure::Indices`]: an index telescope.
/// - [`Departure::Constructors`]: another number of constructors.
/// - [`Departure::Arity`]: a constructor with another number of fields.
/// - [`Departure::Field`]: a field that is no decode of the canonical `E`.
///
/// # Adequacy
/// - hypothesis: L3 — the canonical family is admitted. A family whose field
///   asks for `E` over another type, one with a second field, one with a third
///   parameter and one over another signature type are each refused at their
///   first departure.
/// - witness: `canonical::tests::the_canonical_family_is_admitted_3575`
/// - witness: `canonical::tests::a_family_is_refused_at_its_first_departure_3575`
#[spec(ensures: |ret| ret.is_err()
    || (signature.parameters().len() == 2
        && signature.indices().is_empty()
        && signature.constructors().iter().map(alloc::vec::Vec::len).eq([1_usize])))]
pub fn family(
    arena: &mut CoreArena,
    holder: ConstantIndex,
    (signed, fields): (ConstantIndex, ConstantIndex),
    signature: &DataSignature,
) -> Result<(), Departure>
{
    let [output, code] = *signature.parameters()
    else {
        return Err(Departure::Parameters);
    };
    let universe = matches!(
        arena.value_type(output),
        Some(&ValueType::Universe {
            sort: Sort::Ground(GroundSort::Value),
            ..
        })
    );
    // `Sig(O)` under `O`.
    let over = matches!(
        arena.value_type(code),
        Some(&ValueType::Data { declaration, ref arguments })
            if declaration == signed
                && matches!(**arguments, [argument] if matches!(
                    arena.value(argument),
                    Some(&Value::Variable { zone: Zone::Intuitionistic, index })
                        if index == DeBruijnIndex::from(0_u32)
                ))
    );
    if !universe || !over {
        return Err(Departure::Parameters);
    }
    if !signature.indices().is_empty() {
        return Err(Departure::Indices);
    }
    let [ref only] = *signature.constructors()
    else {
        return Err(Departure::Constructors);
    };
    let [field] = **only
    else {
        return Err(Departure::Arity(ConstructorTag::from(0_usize)));
    };
    let departs = Departure::Field {
        tag: ConstructorTag::from(0_usize),
        field: FieldPosition::from(0_usize),
    };
    let Some(&ValueType::Element { code: written, .. }) = arena.value_type(field)
    else {
        return Err(departs);
    };
    let var = |arena: &mut CoreArena, index: u32| {
        arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(index))
    };
    // `force head a₀ … aₙ`.
    let call = |arena: &mut CoreArena, head: ValueId, arguments: &[ValueId]| {
        let forced = arena.computation_force(head);
        arguments.iter().fold(forced, |applied, &argument| {
            arena.computation_application(applied, argument)
        })
    };
    // Under `O` at 1 and `S` at 0: `⌜IR(O, S)⌝`.
    let (o, s) = (var(arena, 1), var(arena, 0));
    let own = arena.value_type_data(holder, alloc::vec![o, s]);
    let quoted = arena.value_quote(own);
    // `λ m. el(O, S, m)`, under `m` too.
    let decoder = arena.value_constant(ConstantIndex::from(usize::from(holder).saturating_add(1)));
    let passed = [var(arena, 2), var(arena, 1), var(arena, 0)];
    let decoded = call(arena, decoder, &passed);
    let lambda = arena.computation_lambda(decoded);
    let decode = arena.value_thunk(lambda);
    let asks = arena.value_constant(fields);
    let (o, s) = (var(arena, 1), var(arena, 0));
    let run = call(arena, asks, &[o, s, quoted, decode]);
    let canonical = arena.value_returned(run);
    if equal_certificate_syntax(arena, written, canonical) != CertificateEquality::Equal {
        return Err(departs);
    }
    Ok(())
}

/// Compare `defined`, the judged body of the holder of `E` or `F` at
/// `holder`, with the canonical body of its role by their answers at each
/// constructor of the signature type.
///
/// # Specification
/// - requires: `role` is [`Builtin::IrArgs`] or [`Builtin::IrDecode`];
///   `defined` is a closed value in the context's arena, the thunk of the
///   holder's curried function, and the table defines nothing at `holder`.
/// - ensures: `Ok(())` exactly when, at `ι`, `σ` and `δ` in turn, the holder
///   applied to the constructor over rigid fields reads to the normal form of
///   the answer that the module lead's table states, the two normal forms
///   agreeing as syntax. Every definition unfolds, and the holder unfolds to
///   `defined` in a copy of the table. Each recursive call on both sides is the
///   holder itself. So a holder writes each call as `std.ir` writes it: `E`'s
///   rest takes the value its code's call returns, and `F`'s `δ` rest decodes
///   through `λ z. w ← h z; t w`. The arena keeps the minted terms, and the
///   context's table is unchanged.
/// - fails: [`Departure::Reads`] naming the first role the canonical body reads
///   that no declaration holds: the signature type, the pair type and, for `F`,
///   `E`. Then [`Departure::Answer`] at the first constructor whose answer
///   departs, or whose reading runs past its budget.
/// - panics: none.
/// - executable: none — the verdict is the normaliser's, and restating it would
///   run it twice.
///
/// # Errors
/// [`Departure::Reads`] and [`Departure::Answer`], as above.
///
/// # Adequacy
/// - hypothesis: L3 — an `E` that reads an unheld pair type is refused for it,
///   and an `E` whose answer at `ι` is no unit type is refused at `ι`.
///   `std.ir`'s `args` and `decodeArgs` answer, and an `E` whose `δ` case asks
///   for `h : X -> A` is refused at `δ`, each in the corpus.
/// - witness: `canonical::tests::a_holder_of_e_is_refused_at_its_first_departing_answer_5255`
pub fn answers(
    context: &mut CheckingContext<'_>,
    role: Builtin,
    (holder, defined): (ConstantIndex, ValueId),
) -> Result<(), Departure>
{
    let signature = context.builtin_holder(Builtin::IrSignature)?;
    let pair = context.builtin_holder(Builtin::IrPair)?;
    let fields = match role {
        Builtin::IrDecode => Some(context.builtin_holder(Builtin::IrArgs)?),
        Builtin::IrSignature
        | Builtin::IrPair
        | Builtin::IrArgs
        | Builtin::IrFamily
        | Builtin::IrDecoder
        | Builtin::IrHypotheses
        | Builtin::IrMap
        | Builtin::IrEliminator => None,
    };
    let arena = context.arena_mut();
    let body = arena.value_constant(holder);
    let var = |arena: &mut CoreArena, index: u32| {
        arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(index))
    };
    // `force head a₀ … aₙ`.
    let call = |arena: &mut CoreArena, head: ValueId, arguments: &[ValueId]| {
        let forced = arena.computation_force(head);
        arguments.iter().fold(forced, |applied, &argument| {
            arena.computation_application(applied, argument)
        })
    };
    // The signature at the output type the variable `index` binders out.
    let ir = |arena: &mut CoreArena, index: u32| {
        let output = var(arena, index);
        arena.value_type_data(signature, alloc::vec![output])
    };
    // The constructor `tag` of the signature over the output `output` binders
    // out, its fields the variables at `fields`.
    let code = |arena: &mut CoreArena, output: u32, tag: usize, fields: &[u32]| {
        let datatype = ir(arena, output);
        let fields = fields.iter().map(|&index| var(arena, index)).collect();
        arena.value_constructor(datatype, ConstructorTag::from(tag), fields)
    };
    let decode = |arena: &mut CoreArena, index: u32| {
        let code = var(arena, index);
        arena.value_type_element(code, Level::zero())
    };
    // The code of `A -> X`, for `A` at `a` and `X` at `x`.
    let arrow = |arena: &mut CoreArena, a: u32, x: u32| {
        let domain = decode(arena, a);
        let decoded = decode(arena, x);
        let codomain = arena.comp_type_returner(decoded);
        let arrow = arena.comp_type_arrow(domain, codomain);
        let thunk = arena.value_type_thunk(arrow);
        arena.value_quote(thunk)
    };
    // The value that `read` returns at `argument`, where a value stands.
    let returned = |arena: &mut CoreArena, read: ValueId, argument: ValueId| {
        let run = call(arena, read, &[argument]);
        arena.value_returned(run)
    };
    // `t ∘ h`, for `h` at `h` and `t` at `t`: `λ z. t (h z)`, as a type writes
    // it, `h z` standing as the value it returns.
    let composite = |arena: &mut CoreArena, h: u32, t: u32| {
        let z = var(arena, 0);
        let read = var(arena, h.saturating_add(1));
        let inner = returned(arena, read, z);
        let decoder = var(arena, t.saturating_add(1));
        let outer = call(arena, decoder, &[inner]);
        let lambda = arena.computation_lambda(outer);
        arena.value_thunk(lambda)
    };
    // `t ∘ h` as a term writes it: `λ z. w ← h z; t w`.
    let sequenced = |arena: &mut CoreArena, h: u32, t: u32| {
        let z = var(arena, 0);
        let read = var(arena, h.saturating_add(1));
        let inner = call(arena, read, &[z]);
        let w = var(arena, 0);
        let decoder = var(arena, t.saturating_add(2));
        let outer = call(arena, decoder, &[w]);
        let bound = arena.computation_bind(inner, outer);
        let lambda = arena.computation_lambda(bound);
        arena.value_thunk(lambda)
    };
    // `λ a. head(O, f(a), X, t)` at `σ`, and `λ h. head(O, f(t ∘ h), X, t)` at
    // `δ`, for `f`, `O`, `X` and `t` at `f`, `d`, `x` and `t`.
    let family = |arena: &mut CoreArena,
                  head: ValueId,
                  (f, d, x, t): (u32, u32, u32, u32),
                  decoded: bool| {
        let argument = if decoded {
            composite(arena, 0, t.saturating_add(1))
        }
        else {
            var(arena, 0)
        };
        let picker = var(arena, f.saturating_add(1));
        let next = returned(arena, picker, argument);
        let output = var(arena, d.saturating_add(1));
        let over = var(arena, x.saturating_add(1));
        let decoder = var(arena, t.saturating_add(1));
        let rest = call(arena, head, &[output, next, over, decoder]);
        let lambda = arena.computation_lambda(rest);
        arena.value_thunk(lambda)
    };
    let pair_code = |arena: &mut CoreArena, first: ValueId, asked: ValueId| {
        let pairs = arena.value_type_data(pair, alloc::vec![first, asked]);
        arena.value_quote(pairs)
    };
    // Each equation's two sides, and the binders they stand under.
    let equations: [(ComputationId, ComputationId, usize); 3] = if let Some(fields) = fields {
        let fields = arena.value_constant(fields);
        let unit = arena.value_unit();
        // ι, under `O` 3, `X` 2, `t` 1 and `e` 0.
        let iota = {
            let stop = code(arena, 3, 0, &[0]);
            let (output, over, decoder) = (var(arena, 3), var(arena, 2), var(arena, 1));
            let left = call(arena, body, &[output, stop, over, decoder, unit]);
            let e = var(arena, 0);
            (left, arena.computation_return(e), 4)
        };
        // σ and δ, under `O` 6, `X` 5, `t` 4, `A` 3, `f` 2, the first field 1
        // and the rest 0.
        let mut step = |tag: usize, decoded: bool| {
            let read = code(arena, 6, tag, &[3, 2]);
            let first = if decoded {
                arrow(arena, 3, 5)
            }
            else {
                var(arena, 3)
            };
            let asked = family(arena, fields, (2, 6, 5, 4), decoded);
            let datatype = arena.value_type_data(pair, alloc::vec![first, asked]);
            let (head, rest) = (var(arena, 1), var(arena, 0));
            let given =
                arena.value_constructor(datatype, ConstructorTag::from(0_usize), alloc::vec![
                    head, rest
                ]);
            let (output, over, decoder) = (var(arena, 6), var(arena, 5), var(arena, 4));
            let left = call(arena, body, &[output, read, over, decoder, given]);
            let argument = if decoded {
                sequenced(arena, 1, 4)
            }
            else {
                var(arena, 1)
            };
            let picker = var(arena, 2);
            let next = returned(arena, picker, argument);
            let (output, over, decoder, rest) =
                (var(arena, 6), var(arena, 5), var(arena, 4), var(arena, 0));
            (
                left,
                call(arena, body, &[output, next, over, decoder, rest]),
                7,
            )
        };
        [iota, step(1, false), step(2, true)]
    }
    else {
        // ι, under `O` 3, `X` 2, `t` 1 and `e` 0.
        let iota = {
            let stop = code(arena, 3, 0, &[0]);
            let (output, over, decoder) = (var(arena, 3), var(arena, 2), var(arena, 1));
            let left = call(arena, body, &[output, stop, over, decoder]);
            let unit = arena.value_type_unit();
            let quoted = arena.value_quote(unit);
            (left, arena.computation_return(quoted), 4)
        };
        // σ and δ, under `O` 4, `X` 3, `t` 2, `A` 1 and `f` 0.
        let mut step = |tag: usize, decoded: bool| {
            let read = code(arena, 4, tag, &[1, 0]);
            let (output, over, decoder) = (var(arena, 4), var(arena, 3), var(arena, 2));
            let left = call(arena, body, &[output, read, over, decoder]);
            let first = if decoded {
                arrow(arena, 1, 3)
            }
            else {
                var(arena, 1)
            };
            let asked = family(arena, body, (0, 4, 3, 2), decoded);
            let quoted = pair_code(arena, first, asked);
            (left, arena.computation_return(quoted), 5)
        };
        [iota, step(1, false), step(2, true)]
    };
    // The holder unfolds to its judged body in a copy of the table: the table
    // takes the definition only once the holder answers. Each side reads to its
    // normal form, and the two normal forms agree as syntax: a recursive call
    // stuck on a rigid field reads as one fixpoint on both sides.
    let mut trial = context.definitions().clone();
    trial.define(holder, defined);
    for (tag, (left, right, open)) in equations.into_iter().enumerate() {
        let departs = Departure::Answer(ConstructorTag::from(tag));
        let arena = context.arena_mut();
        let mut read = |body: ComputationId| {
            let suspended = (0 .. open).fold(body, |inner, _| arena.computation_lambda(inner));
            let claim = arena.value_thunk(suspended);
            trial
                .read_normal(arena, claim)
                .map_err(|_undecided| departs)
        };
        let (left, right) = (read(left)?, read(right)?);
        if equal_certificate_syntax(context.arena(), left, right) != CertificateEquality::Equal {
            return Err(departs);
        }
    }
    Ok(())
}

/// Compare `defined`, the judged body of the holder of the hypotheses or the
/// map at `holder`, with the canonical body of its role by their answers at
/// each constructor of the signature type.
///
/// # Specification
/// - requires: `role` is [`Builtin::IrHypotheses`] or [`Builtin::IrMap`];
///   `defined` is a closed value in the context's arena, the thunk of the
///   holder's curried function, and the table defines nothing at `holder`.
/// - ensures: `Ok(())` exactly when, at `ι`, `σ` and `δ` in turn, the holder
///   applied to the constructor over rigid fields reads to the normal form of
///   the answer that the module lead's table states, the two normal forms
///   agreeing as syntax. Every definition unfolds, and the holder unfolds to
///   `defined` in a copy of the table. Each recursive call on both sides is the
///   holder itself. The arena keeps the minted terms, and the context's table
///   is unchanged.
/// - fails: [`Departure::Reads`] naming the first role the canonical body reads
///   that no declaration holds: the signature type, the pair type, `E` and, for
///   the map, the hypotheses. Then [`Departure::Answer`] at the first
///   constructor whose answer departs, or whose reading runs past its budget.
/// - panics: none.
///
/// # Errors
/// [`Departure::Reads`] and [`Departure::Answer`], as above.
///
/// # Adequacy
/// - hypothesis: L3 — `std.ir`'s `hyps` and `mapArgs` answer. Hypotheses of the
///   unit type at every code answer at `ι` and `σ` and are refused at `δ`, both
///   in the unit case and in the corpus.
/// - witness: `canonical::tests::the_hypotheses_and_the_eliminator_are_refused_at_their_departures_5160`
#[spec(ensures: |ret| ret.is_ok() || matches!(ret, Err(Departure::Reads(_) | Departure::Answer(_))))]
pub fn induction(
    context: &mut CheckingContext<'_>,
    role: Builtin,
    (holder, defined): (ConstantIndex, ValueId),
) -> Result<(), Departure>
{
    let signature = context.builtin_holder(Builtin::IrSignature)?;
    let pair = context.builtin_holder(Builtin::IrPair)?;
    let fields = context.builtin_holder(Builtin::IrArgs)?;
    let mapping = role == Builtin::IrMap;
    let hypotheses = if mapping {
        context.builtin_holder(Builtin::IrHypotheses)?
    }
    else {
        holder
    };
    // The map takes the function `g` past the predicate, one binder more.
    let extra = u32::from(mapping);
    let arena = context.arena_mut();
    let body = arena.value_constant(holder);
    let fields = arena.value_constant(fields);
    let var = |arena: &mut CoreArena, index: u32| {
        arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(index))
    };
    // `force head a₀ … aₙ`.
    let call = |arena: &mut CoreArena, head: ValueId, arguments: &[ValueId]| {
        let forced = arena.computation_force(head);
        arguments.iter().fold(forced, |applied, &argument| {
            arena.computation_application(applied, argument)
        })
    };
    // The value that `read` returns at `argument`, where a value stands.
    let returned = |arena: &mut CoreArena, read: ValueId, argument: ValueId| {
        let run = call(arena, read, &[argument]);
        arena.value_returned(run)
    };
    // The constructor `tag` of the signature over the output `output` binders
    // out, its fields the variables at `fields`.
    let code = |arena: &mut CoreArena, output: u32, tag: usize, fields: &[u32]| {
        let output = var(arena, output);
        let datatype = arena.value_type_data(signature, alloc::vec![output]);
        let fields = fields.iter().map(|&index| var(arena, index)).collect();
        arena.value_constructor(datatype, ConstructorTag::from(tag), fields)
    };
    let decode =
        |arena: &mut CoreArena, code: ValueId| arena.value_type_element(code, Level::zero());
    // The code of `A -> X`, for `A` at `first` and `X` at `over`.
    let arrow = |arena: &mut CoreArena, first: u32, over: u32| {
        let first = var(arena, first);
        let domain = decode(arena, first);
        let over = var(arena, over);
        let decoded = decode(arena, over);
        let codomain = arena.comp_type_returner(decoded);
        let arrow = arena.comp_type_arrow(domain, codomain);
        let thunk = arena.value_type_thunk(arrow);
        arena.value_quote(thunk)
    };
    // `t ∘ h` as a type writes it, `h z` standing as the value it returns, for
    // `h` at `inner` and `t` at `outer`.
    let composite = |arena: &mut CoreArena, inner: u32, outer: u32| {
        let point = var(arena, 0);
        let read = var(arena, inner.saturating_add(1));
        let inner = returned(arena, read, point);
        let decoder = var(arena, outer.saturating_add(1));
        let outer = call(arena, decoder, &[inner]);
        let lambda = arena.computation_lambda(outer);
        arena.value_thunk(lambda)
    };
    // `t ∘ h` as a term writes it: `λ z. w ← h z; t w`.
    let sequenced = |arena: &mut CoreArena, inner: u32, outer: u32| {
        let point = var(arena, 0);
        let read = var(arena, inner.saturating_add(1));
        let inner = call(arena, read, &[point]);
        let bound = var(arena, 0);
        let decoder = var(arena, outer.saturating_add(2));
        let outer = call(arena, decoder, &[bound]);
        let bound = arena.computation_bind(inner, outer);
        let lambda = arena.computation_lambda(bound);
        arena.value_thunk(lambda)
    };
    // The binders of `σ` and `δ`: `O`, `X`, `t`, `P` and, for the map, `g`
    // outermost, then `A` 3, `f` 2, the first field 1 and the rest 0.
    let (output, over, decoder, predicate) = (7 + extra, 6 + extra, 5 + extra, 4 + extra);
    // The pair type of `E`'s answer at `σ` or `δ`: `Pair(A, λ y. E(O, f(y),
    // X, t))`, or `Pair(A -> X, λ h. E(O, f(t ∘ h), X, t))` when `decoded`.
    let asked = |arena: &mut CoreArena, decoded: bool| {
        let first = if decoded {
            arrow(arena, 3, over)
        }
        else {
            var(arena, 3)
        };
        let argument = if decoded {
            composite(arena, 0, decoder.saturating_add(1))
        }
        else {
            var(arena, 0)
        };
        let picker = var(arena, 3);
        let next = returned(arena, picker, argument);
        let passed = [
            var(arena, output + 1),
            next,
            var(arena, over + 1),
            var(arena, decoder + 1),
        ];
        let rest = call(arena, fields, &passed);
        let lambda = arena.computation_lambda(rest);
        let family = arena.value_thunk(lambda);
        arena.value_type_data(pair, alloc::vec![first, family])
    };
    // The pair type of `H`'s answer at `δ`, `shift` binders in: `Pair((z : A)
    // -> P(h(z)), λ k. H(O, f(t ∘ h), X, t, P, r))`, the hypothesis at each
    // point of the field before those of the rest.
    let hypothesised = |arena: &mut CoreArena, shift: u32| {
        let point = var(arena, 0);
        let read = var(arena, 2 + shift);
        let point = returned(arena, read, point);
        let proving = var(arena, predicate + 1 + shift);
        let proved = returned(arena, proving, point);
        let decoded = decode(arena, proved);
        let codomain = arena.comp_type_returner(decoded);
        let first = var(arena, 3 + shift);
        let domain = decode(arena, first);
        let each = arena.comp_type_pi(domain, codomain);
        let each = arena.value_type_thunk(each);
        let first = arena.value_quote(each);
        let argument = composite(arena, 2 + shift, decoder + 1 + shift);
        let picker = var(arena, 3 + shift);
        let next = returned(arena, picker, argument);
        let hypotheses = arena.value_constant(hypotheses);
        let passed = [
            var(arena, output + 1 + shift),
            next,
            var(arena, over + 1 + shift),
            var(arena, decoder + 1 + shift),
            var(arena, predicate + 1 + shift),
            var(arena, 1 + shift),
        ];
        let rest = call(arena, hypotheses, &passed);
        let lambda = arena.computation_lambda(rest);
        let family = arena.value_thunk(lambda);
        arena.value_type_data(pair, alloc::vec![first, family])
    };
    // The holder's parameters before its argument, `shift` binders in and
    // `past` binders out, the code `code` in place.
    let parameters = |arena: &mut CoreArena, code: ValueId, (shift, past): (u32, u32)| {
        let mut passed = alloc::vec![
            var(arena, output - past + shift),
            code,
            var(arena, over - past + shift),
            var(arena, decoder - past + shift),
            var(arena, predicate - past + shift),
        ];
        if mapping {
            passed.push(var(arena, 4 - past + shift));
        }
        passed
    };
    // Each equation's two sides, and the binders they stand under. ι stands
    // under the parameters and `e` 0.
    let iota = {
        let stop = code(arena, output - 3, 0, &[0]);
        let mut passed = parameters(arena, stop, (0, 3));
        let unit = arena.value_unit();
        passed.push(unit);
        let left = call(arena, body, &passed);
        let right = if mapping {
            let unit = arena.value_unit();
            arena.computation_return(unit)
        }
        else {
            let unit = arena.value_type_unit();
            let quoted = arena.value_quote(unit);
            arena.computation_return(quoted)
        };
        (left, right, 5 + extra)
    };
    let mut step = |tag: usize, decoded: bool| {
        let read = code(arena, output, tag, &[3, 2]);
        let datatype = asked(arena, decoded);
        let (head, rest) = (var(arena, 1), var(arena, 0));
        let given = arena.value_constructor(datatype, ConstructorTag::from(0_usize), alloc::vec![
            head, rest
        ]);
        let mut passed = parameters(arena, read, (0, 0));
        passed.push(given);
        let left = call(arena, body, &passed);
        let argument = if decoded {
            sequenced(arena, 1, decoder)
        }
        else {
            var(arena, 1)
        };
        let picker = var(arena, 2);
        let next = returned(arena, picker, argument);
        let mut passed = parameters(arena, next, (0, 0));
        passed.push(var(arena, 0));
        let recursed = call(arena, body, &passed);
        let right = if !decoded {
            // `P`'s hypotheses or `g`'s map over the rest at `f(y)`.
            recursed
        }
        else if mapping {
            // `w ← M(O, f(t ∘ h), X, t, P, g, r); return (λ z. g(h z), w)`,
            // `h z` standing as the value it returns.
            let point = var(arena, 0);
            let read = var(arena, 3);
            let point = returned(arena, read, point);
            let function = var(arena, 6);
            let applied = call(arena, function, &[point]);
            let lambda = arena.computation_lambda(applied);
            let each = arena.value_thunk(lambda);
            let rest = var(arena, 0);
            let datatype = hypothesised(arena, 1);
            let made =
                arena.value_constructor(datatype, ConstructorTag::from(0_usize), alloc::vec![
                    each, rest
                ]);
            let made = arena.computation_return(made);
            arena.computation_bind(recursed, made)
        }
        else {
            let datatype = hypothesised(arena, 0);
            let quoted = arena.value_quote(datatype);
            arena.computation_return(quoted)
        };
        (left, right, 8 + extra)
    };
    let equations = [iota, step(1, false), step(2, true)];
    let mut trial = context.definitions().clone();
    trial.define(holder, defined);
    for (tag, (left, right, open)) in equations.into_iter().enumerate() {
        let departs = Departure::Answer(ConstructorTag::from(tag));
        let arena = context.arena_mut();
        let mut read = |body: ComputationId| {
            let suspended = (0 .. open).fold(body, |inner, _| arena.computation_lambda(inner));
            let claim = arena.value_thunk(suspended);
            trial
                .read_normal(arena, claim)
                .map_err(|_undecided| departs)
        };
        let (left, right) = (read(left)?, read(right)?);
        if equal_certificate_syntax(context.arena(), left, right) != CertificateEquality::Equal {
            return Err(departs);
        }
    }
    Ok(())
}

/// Compare `defined`, the judged body of the holder of the decoder role at
/// `holder`, with the canonical decoder by its answer at the family's one
/// constructor.
///
/// # Specification
/// - requires: `defined` is a closed value in the context's arena, the thunk of
///   the holder's curried function, and the table defines nothing at `holder`.
/// - ensures: `Ok(())` exactly when the family's holder stands right before
///   `holder` and, under rigid variables for `O`, `S` and the field `x`, the
///   holder at `intro(x)` and `F(O, S, ⌜IR(O, S)⌝, λ n. el(O, S, n), x)` read
///   to normal forms that agree as syntax, with `defined` the holder's body in
///   a copy of the table. Every value of the family is `intro(x)` for some `x`,
///   so the holder answers as the canonical decoder at every value. The arena
///   keeps the minted terms, and the context's table is unchanged.
/// - fails: [`Departure::Reads`] for a role the canonical form reads that no
///   declaration holds, the family's role too when its holder stands elsewhere;
///   [`Departure::Answer`] at the one constructor otherwise.
/// - panics: none.
///
/// # Errors
/// As `- fails:`.
///
/// # Adequacy
/// - hypothesis: L3 — a decoder read before the family has a holder is refused
///   for the role it reads. In the corpus, `std.ir`'s `el` answers, and a
///   decoder that calls itself on its own value is refused at `intro(x)`.
/// - witness: `canonical::tests::a_decoder_is_refused_at_its_departing_answer_3575`
pub fn decoder(
    context: &mut CheckingContext<'_>,
    (holder, defined): (ConstantIndex, ValueId),
) -> Result<(), Departure>
{
    let family = context.builtin_holder(Builtin::IrFamily)?;
    if usize::from(family).saturating_add(1) != usize::from(holder) {
        return Err(Departure::Reads(Builtin::IrFamily));
    }
    let decode = context.builtin_holder(Builtin::IrDecode)?;
    let arena = context.arena_mut();
    let var = |arena: &mut CoreArena, index: u32| {
        arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(index))
    };
    // `force head a₀ … aₙ`.
    let call = |arena: &mut CoreArena, head: ValueId, arguments: &[ValueId]| {
        let forced = arena.computation_force(head);
        arguments.iter().fold(forced, |applied, &argument| {
            arena.computation_application(applied, argument)
        })
    };
    let body = arena.value_constant(holder);
    // Under `O` 2, `S` 1 and `x` 0: `el(O, S, intro(x))`.
    let (o, s, x) = (var(arena, 2), var(arena, 1), var(arena, 0));
    let own = arena.value_type_data(family, alloc::vec![o, s]);
    let intro = arena.value_constructor(own, ConstructorTag::from(0_usize), alloc::vec![x]);
    let (o, s) = (var(arena, 2), var(arena, 1));
    let left = call(arena, body, &[o, s, intro]);
    // `F(O, S, ⌜IR(O, S)⌝, λ n. el(O, S, n), x)`.
    let (o, s) = (var(arena, 2), var(arena, 1));
    let own = arena.value_type_data(family, alloc::vec![o, s]);
    let quoted = arena.value_quote(own);
    let passed = [var(arena, 3), var(arena, 2), var(arena, 0)];
    let decoded = call(arena, body, &passed);
    let lambda = arena.computation_lambda(decoded);
    let decoder = arena.value_thunk(lambda);
    let fields = arena.value_constant(decode);
    let (o, s, x) = (var(arena, 2), var(arena, 1), var(arena, 0));
    let right = call(arena, fields, &[o, s, quoted, decoder, x]);
    // The holder unfolds to its judged body in a copy of the table, as the
    // holders of `E` and `F` do.
    let mut trial = context.definitions().clone();
    trial.define(holder, defined);
    let departs = Departure::Answer(ConstructorTag::from(0_usize));
    let arena = context.arena_mut();
    let mut read = |body: ComputationId| {
        let suspended = (0_u32 .. 3_u32).fold(body, |inner, _| arena.computation_lambda(inner));
        let claim = arena.value_thunk(suspended);
        trial
            .read_normal(arena, claim)
            .map_err(|_undecided| departs)
    };
    let (left, right) = (read(left)?, read(right)?);
    if equal_certificate_syntax(context.arena(), left, right) != CertificateEquality::Equal {
        return Err(departs);
    }
    Ok(())
}

/// Compare `defined`, the judged body of the holder of the eliminator role at
/// `holder`, with the canonical eliminator by its answer at the family's one
/// constructor.
///
/// # Specification
/// - requires: `defined` is a closed value in the context's arena, the thunk of
///   the holder's curried function, and the table defines nothing at `holder`.
/// - ensures: `Ok(())` exactly when, under rigid variables for `O`, `S`, `P`,
///   the step `s` and the field `x`, the holder at `intro(x)` and `w ← M(O, S,
///   ⌜IR(O, S)⌝, λ m. el(O, S, m), P, λ n. elim(O, S, P, s, n), x); s(x, w)`
///   read to normal forms that agree as syntax. Only the holder unfolds, to
///   `defined`, in a table of its own: every other constant stays rigid. `M` is
///   the map's holder, and the holder recurses only through it. Every value of
///   the family is `intro(x)` for some `x`, so the holder answers as the
///   canonical eliminator at every value. The arena keeps the minted terms, and
///   the context's table is unchanged.
/// - fails: [`Departure::Reads`] for a role the canonical form reads that no
///   declaration holds; [`Departure::Answer`] at the one constructor otherwise.
/// - panics: none.
///
/// # Errors
/// As `- fails:`.
///
/// # Adequacy
/// - hypothesis: L3 — an eliminator read before the map has a holder is refused
///   for the role it reads, and one that returns its value with no step is
///   refused at `intro(x)`. In the corpus, `std.ir`'s `elim` answers, and an
///   eliminator that calls itself on its own value is refused at `intro(x)`.
/// - witness: `canonical::tests::the_hypotheses_and_the_eliminator_are_refused_at_their_departures_5160`
#[spec(ensures: |ret| ret.is_ok() || matches!(ret, Err(Departure::Reads(_) | Departure::Answer(_))))]
pub fn eliminator(
    context: &mut CheckingContext<'_>,
    (holder, defined): (ConstantIndex, ValueId),
) -> Result<(), Departure>
{
    let family = context.builtin_holder(Builtin::IrFamily)?;
    let decoder = context.builtin_holder(Builtin::IrDecoder)?;
    let map = context.builtin_holder(Builtin::IrMap)?;
    let arena = context.arena_mut();
    let var = |arena: &mut CoreArena, index: u32| {
        arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(index))
    };
    // `force head a₀ … aₙ`.
    let call = |arena: &mut CoreArena, head: ValueId, arguments: &[ValueId]| {
        let forced = arena.computation_force(head);
        arguments.iter().fold(forced, |applied, &argument| {
            arena.computation_application(applied, argument)
        })
    };
    let body = arena.value_constant(holder);
    // `IR(O, S)`, under `O` 4 and `S` 3.
    let own = |arena: &mut CoreArena| {
        let (output, signature) = (var(arena, 4), var(arena, 3));
        arena.value_type_data(family, alloc::vec![output, signature])
    };
    // Under `O` 4, `S` 3, `P` 2, `s` 1 and `x` 0: `elim(O, S, P, s, intro(x))`.
    let datatype = own(arena);
    let field = var(arena, 0);
    let intro =
        arena.value_constructor(datatype, ConstructorTag::from(0_usize), alloc::vec![field]);
    let passed = [
        var(arena, 4),
        var(arena, 3),
        var(arena, 2),
        var(arena, 1),
        intro,
    ];
    let left = call(arena, body, &passed);
    // `w ← M(O, S, ⌜IR(O, S)⌝, λ m. el(O, S, m), P, λ n. elim(O, S, P, s, n),
    // x); s(x, w)`.
    let datatype = own(arena);
    let quoted = arena.value_quote(datatype);
    let decodes = {
        let decoder = arena.value_constant(decoder);
        let passed = [var(arena, 5), var(arena, 4), var(arena, 0)];
        let decoded = call(arena, decoder, &passed);
        let lambda = arena.computation_lambda(decoded);
        arena.value_thunk(lambda)
    };
    let recurses = {
        let passed = [
            var(arena, 5),
            var(arena, 4),
            var(arena, 3),
            var(arena, 2),
            var(arena, 0),
        ];
        let recursed = call(arena, body, &passed);
        let lambda = arena.computation_lambda(recursed);
        arena.value_thunk(lambda)
    };
    let mapped = {
        let map = arena.value_constant(map);
        let passed = [
            var(arena, 4),
            var(arena, 3),
            quoted,
            decodes,
            var(arena, 2),
            recurses,
            var(arena, 0),
        ];
        call(arena, map, &passed)
    };
    let right = {
        let step = var(arena, 2);
        let passed = [var(arena, 1), var(arena, 0)];
        let stepped = call(arena, step, &passed);
        arena.computation_bind(mapped, stepped)
    };
    // Only the holder unfolds, in a table of its own. The map at the open
    // signature `S` holds a call of the eliminator in each `δ` arm, and that
    // call holds the map again, so a reading that unfolds the map never ends.
    // Each side calls the map's holder by its name.
    let mut trial = crate::code::CodeDefinitions::new();
    trial.define(holder, defined);
    let departs = Departure::Answer(ConstructorTag::from(0_usize));
    let arena = context.arena_mut();
    let mut read = |body: ComputationId| {
        let suspended = (0_u32 .. 5_u32).fold(body, |inner, _| arena.computation_lambda(inner));
        let claim = arena.value_thunk(suspended);
        trial
            .read_normal(arena, claim)
            .map_err(|_undecided| departs)
    };
    let (left, right) = (read(left)?, read(right)?);
    if equal_certificate_syntax(context.arena(), left, right) != CertificateEquality::Equal {
        return Err(departs);
    }
    Ok(())
}

#[cfg(test)]
mod tests;
