//! The built-in roles in the kernel: a declaration that holds a role answers
//! the role's canonical form, decided by the kernel at admission.
//!
//! The checker validates every holder (`gandr_core_checker::canonical`), and
//! the kernel decides the same forms again over its own terms. It never takes
//! a producer's mark on trust. A role has one holder: the signature type and
//! the pair type are data declarations, and `E` and `F` are definitions.
//!
//! |Role|The canonical form|
//! |---|---|
//! |`irSignature`|one parameter `O : Type`, no index, and the constructors `ι(e : O)`, `σ(A : Type, f : A -> Sig(O))` and `δ(A : Type, f : (A -> O) -> Sig(O))` in this order|
//! |`irPair`|the parameters `A : Type` and `B : A -> Type`, no index, and one constructor `(x : A, y : B(x))`|
//! |`irArgs`|the answers of `E` at `ι`, `σ` and `δ`, decided by conversion|
//! |`irDecode`|the answers of `F` at `ι`, `σ` and `δ`, decided by conversion|
//!
//! # References
//!
//! - `vault:01a183fc-63df-77a0-9df0-1c3f0b02ddf6` — anchor: the signature type
//!   of § 2.2 and its three constructors, and `E` and `F` by recursion on a
//!   signature.

use alloc::vec::Vec;

use anodized::spec;
use gandr_kernel_term::Builtin;
use gandr_kernel_term::CompType;
use gandr_kernel_term::Computation;
use gandr_kernel_term::ComputationId;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::ConstructorTag;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::Declaration;
use gandr_kernel_term::DeclarationContent;
use gandr_kernel_term::Departure;
use gandr_kernel_term::FieldPosition;
use gandr_kernel_term::GroundSort;
use gandr_kernel_term::Holder;
use gandr_kernel_term::TermArena;
use gandr_kernel_term::Value;
use gandr_kernel_term::ValueId;
use gandr_kernel_term::ValueType;
use gandr_kernel_term::ValueTypeId;
use quenchant_shape::shape::Maybe;

use crate::KernelVerdict;
use crate::env::Entries;
use crate::error::KernelError;
use crate::replay::ReplayBudget;
use crate::replay::ReplaySides;
use crate::replay::Unfoldable;
use crate::replay::Unfoldings;

/// Admit the role `declaration` holds, if it holds one: the declaration is of
/// the role's judgement, no earlier entry holds the role, and the declaration
/// answers the role's canonical form.
///
/// # Specification
/// - requires: `declaration`'s nodes and every entry's live in `arena`; the
///   declaration takes the position after the last entry.
/// - ensures: `Ok(())` for a declaration that holds no role, and for a holder
///   that the four conditions above admit. `arena` holds what it held on entry.
/// - fails: [`KernelError::BuiltinMisplaced`] for a holder of another
///   judgement, then [`KernelError::BuiltinRepeated`] naming the earlier
///   holder, then [`KernelError::BuiltinNotCanonical`] naming the first
///   departure.
/// - panics: none.
///
/// # Errors
/// As `- fails:`.
///
/// # Adequacy
/// - hypothesis: L3 — the canonical signature and pair types admit and a second
///   holder is refused; a signature with `σ` and `δ` swapped, a pair with its
///   fields swapped, and an `E` whose `ι` case is no unit type are each refused
///   at their departure.
/// - witness: `builtin::tests::a_role_s_holder_is_admitted_in_its_canonical_form_5304`
/// - witness: `builtin::tests::a_departing_holder_is_refused_at_its_departure_5304`
#[spec(
    captures: before = arena.watermark(),
    ensures: |ret| arena.watermark() == before && (ret.is_ok() || matches!(ret, Err(KernelError::BuiltinMisplaced(_) | KernelError::BuiltinRepeated { .. } | KernelError::BuiltinNotCanonical { .. }))),
)]
pub fn admit(
    arena: &mut TermArena,
    entries: &Entries,
    declaration: &Declaration,
) -> Result<(), KernelError>
{
    let Maybe::Present(role) = declaration.role()
    else {
        return Ok(());
    };
    let fits = matches!(
        (role.holder(), declaration.content()),
        (Holder::Data, DeclarationContent::Data { .. })
            | (Holder::Value, DeclarationContent::Def { .. })
    );
    if !fits {
        return Err(KernelError::BuiltinMisplaced(role));
    }
    if let Some(holder) = entries
        .iter()
        .position(|entry| entry.declaration().role() == Maybe::Present(role))
    {
        return Err(KernelError::BuiltinRepeated {
            role,
            holder: ConstantIndex::from(holder),
        });
    }
    let position = ConstantIndex::from(usize::from(entries.len()));
    let canonical = match *declaration.content() {
        DeclarationContent::Data {
            ref parameters,
            ref indices,
            ref constructors,
            ..
        } => match role {
            Builtin::IrSignature => signature(arena, position, (parameters, indices, constructors)),
            Builtin::IrPair => pair(arena, (parameters, indices, constructors)),
            Builtin::IrArgs | Builtin::IrDecode => Err(Departure::Constructors),
        },
        DeclarationContent::Def { body, .. } => {
            let watermark = arena.watermark();
            let answered = answers(arena, entries, role, (position, body));
            arena.truncate_to(watermark);
            answered
        },
        DeclarationContent::Codata { .. }
        | DeclarationContent::Axiom { .. }
        | DeclarationContent::AbstractType { .. } => Err(Departure::Constructors),
    };
    canonical.map_err(|departure| KernelError::BuiltinNotCanonical { role, departure })
}

/// The shape readings the two data roles share, over `arena`.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy)]
struct Shapes<'arena>
{
    /// The arena the nodes live in.
    arena: &'arena TermArena,
}

impl Shapes<'_>
{
    /// Whether `value` is the variable `index` binders out.
    ///
    /// # Specification
    /// trivial.
    fn variable(
        self,
        value: ValueId,
        index: DeBruijnIndex,
    ) -> Fits
    {
        Fits(matches!(self.arena.value(value), Some(&Value::Variable(found)) if found == index))
    }

    /// Whether `value_type` is the value universe.
    ///
    /// # Specification
    /// trivial.
    fn universe(
        self,
        value_type: ValueTypeId,
    ) -> Fits
    {
        Fits(matches!(
            self.arena.value_type(value_type),
            Some(&ValueType::Universe {
                sort: GroundSort::Value,
                ..
            })
        ))
    }

    /// Whether `value_type` decodes the variable `index` binders out.
    ///
    /// # Specification
    /// trivial.
    fn element(
        self,
        value_type: ValueTypeId,
        index: DeBruijnIndex,
    ) -> Fits
    {
        Fits(matches!(
            self.arena.value_type(value_type),
            Some(&ValueType::Element { code, .. }) if self.variable(code, index).0
        ))
    }

    /// The domain and the returned result of `value_type`, a thunked arrow
    /// into a returner.
    ///
    /// # Specification
    /// trivial.
    fn arrow(
        self,
        value_type: ValueTypeId,
    ) -> Maybe<(ValueTypeId, ValueTypeId), Unshaped>
    {
        let Some(&ValueType::Thunk(body)) = self.arena.value_type(value_type)
        else {
            return Maybe::Absent(Unshaped);
        };
        let Some(&CompType::Arrow { domain, codomain }) = self.arena.comp_type(body)
        else {
            return Maybe::Absent(Unshaped);
        };
        match self.arena.comp_type(codomain) {
            Some(&CompType::Returner(result)) => Maybe::Present((domain, result)),
            Some(_) | None => Maybe::Absent(Unshaped),
        }
    }

    /// Whether `value_type` is the datatype `holder` at the variable `index`
    /// binders out.
    ///
    /// # Specification
    /// trivial.
    fn family(
        self,
        value_type: ValueTypeId,
        (holder, index): (ConstantIndex, DeBruijnIndex),
    ) -> Fits
    {
        Fits(matches!(
            self.arena.value_type(value_type),
            Some(&ValueType::Data { declaration, ref arguments })
                if declaration == holder
                    && matches!(**arguments, [argument] if self.variable(argument, index).0)
        ))
    }
}

/// Whether a node has the shape a reading asks for.
#[repr(transparent)]
#[derive(Clone, Copy)]
struct Fits(bool);

/// A node with no shape a reading asks for.
#[derive(Clone, Copy)]
struct Unshaped;

/// Compare a data signature with the canonical signature type held at
/// `holder`.
///
/// # Specification
/// - requires: the signature's nodes live in `arena`.
/// - ensures: `Ok(())` exactly when the signature is the canonical signature
///   type the module lead states, `Sig` the holder at its parameter.
/// - fails: the first [`Departure`] in the order parameters, indices,
///   constructors, then each constructor's arity and fields in order.
/// - panics: none.
///
/// # Errors
/// As `- fails:`.
///
/// # Adequacy
/// - hypothesis: L3 — as [`admit`].
/// - witness: `builtin::tests::a_departing_holder_is_refused_at_its_departure_5304`
#[spec(ensures: |ret| ret.is_err()
    || (parameters.len() == 1
        && indices.is_empty()
        && constructors.iter().map(Vec::len).eq([1_usize, 2, 2])))]
fn signature(
    arena: &TermArena,
    holder: ConstantIndex,
    (parameters, indices, constructors): (&[ValueTypeId], &[ValueTypeId], &[Vec<ValueTypeId>]),
) -> Result<(), Departure>
{
    let shapes = Shapes { arena };
    let index = DeBruijnIndex::from;
    let at = |tag: usize, field: usize| Departure::Field {
        tag: ConstructorTag::from(tag),
        field: FieldPosition::from(field),
    };
    let [parameter] = *parameters
    else {
        return Err(Departure::Parameters);
    };
    if !shapes.universe(parameter).0 {
        return Err(Departure::Parameters);
    }
    if !indices.is_empty() {
        return Err(Departure::Indices);
    }
    let [ref iota, ref sigma, ref delta] = *constructors
    else {
        return Err(Departure::Constructors);
    };
    let [stop] = **iota
    else {
        return Err(Departure::Arity(ConstructorTag::from(0_usize)));
    };
    if !shapes.element(stop, index(0_u32)).0 {
        return Err(at(0, 0));
    }
    let [shape, rest] = **sigma
    else {
        return Err(Departure::Arity(ConstructorTag::from(1_usize)));
    };
    if !shapes.universe(shape).0 {
        return Err(at(1, 0));
    }
    let picked = matches!(shapes.arrow(rest), Maybe::Present((domain, result))
        if shapes.element(domain, index(0_u32)).0 && shapes.family(result, (holder, index(1_u32))).0);
    if !picked {
        return Err(at(1, 1));
    }
    let [shape, rest] = **delta
    else {
        return Err(Departure::Arity(ConstructorTag::from(2_usize)));
    };
    if !shapes.universe(shape).0 {
        return Err(at(2, 0));
    }
    let decoded = match shapes.arrow(rest) {
        Maybe::Present((decode, result)) => {
            matches!(shapes.arrow(decode), Maybe::Present((inner, output))
                if shapes.element(inner, index(0_u32)).0 && shapes.element(output, index(1_u32)).0)
                && shapes.family(result, (holder, index(1_u32))).0
        },
        Maybe::Absent(Unshaped) => false,
    };
    if !decoded {
        return Err(at(2, 1));
    }
    Ok(())
}

/// Compare a data signature with the canonical pair type.
///
/// # Specification
/// - requires: the signature's nodes live in `arena`.
/// - ensures: `Ok(())` exactly when the signature is the canonical pair type
///   the module lead states, `B(x)` the decode of `B` run at `x`.
/// - fails: the first [`Departure`] in the order parameters, indices,
///   constructors, then the constructor's arity and its fields in order.
/// - panics: none.
///
/// # Errors
/// As `- fails:`.
///
/// # Adequacy
/// - hypothesis: L3 — as [`admit`].
/// - witness: `builtin::tests::a_departing_holder_is_refused_at_its_departure_5304`
#[spec(ensures: |ret| ret.is_err()
    || (parameters.len() == 2
        && indices.is_empty()
        && constructors.iter().map(Vec::len).eq([2_usize])))]
fn pair(
    arena: &TermArena,
    (parameters, indices, constructors): (&[ValueTypeId], &[ValueTypeId], &[Vec<ValueTypeId>]),
) -> Result<(), Departure>
{
    let shapes = Shapes { arena };
    let index = DeBruijnIndex::from;
    let at = |tag: usize, field: usize| Departure::Field {
        tag: ConstructorTag::from(tag),
        field: FieldPosition::from(field),
    };
    let [first, family] = *parameters
    else {
        return Err(Departure::Parameters);
    };
    let fibred = matches!(shapes.arrow(family), Maybe::Present((domain, result))
        if shapes.element(domain, index(0_u32)).0 && shapes.universe(result).0);
    if !shapes.universe(first).0 || !fibred {
        return Err(Departure::Parameters);
    }
    if !indices.is_empty() {
        return Err(Departure::Indices);
    }
    let [ref only] = *constructors
    else {
        return Err(Departure::Constructors);
    };
    let [x, y] = **only
    else {
        return Err(Departure::Arity(ConstructorTag::from(0_usize)));
    };
    if !shapes.element(x, index(1_u32)).0 {
        return Err(at(0, 0));
    }
    let applied = match arena.value_type(y) {
        Some(&ValueType::Element { code, .. }) => match arena.value(code) {
            Some(&Value::Returned(run)) => matches!(
                arena.computation(run),
                Some(&Computation::Application(head, argument))
                    if shapes.variable(argument, index(0_u32)).0
                        && matches!(arena.computation(head), Some(&Computation::Force(read)) if shapes.variable(read, index(1_u32)).0)
            ),
            Some(_) | None => false,
        },
        Some(_) | None => false,
    };
    if !applied {
        return Err(at(0, 1));
    }
    Ok(())
}

/// Compare `defined`, the body of the holder of `E` or `F` at `holder`, with
/// the canonical body of its role by their answers at each constructor of the
/// signature type, decided by the kernel's conversion.
///
/// # Specification
/// - requires: `defined` and every entry's nodes live in `arena`; `holder` is
///   the position after the last entry.
/// - ensures: `Ok(())` exactly when, at `ι`, `σ` and `δ` in turn, the holder
///   applied to the constructor over rigid fields converts with the canonical
///   answer, every definition and the holder unfolding.
/// - fails: [`Departure::Reads`] for an unheld role the canonical body reads,
///   then [`Departure::Answer`] at the first constructor whose answer the
///   conversion does not relate.
/// - panics: none.
///
/// # Errors
/// As `- fails:`.
///
/// # Adequacy
/// - hypothesis: L3 — as [`admit`].
/// - witness: `builtin::tests::a_departing_holder_is_refused_at_its_departure_5304`
#[spec(ensures: |ret| ret.is_ok() || matches!(ret, Err(Departure::Reads(_) | Departure::Answer(_))))]
fn answers(
    arena: &mut TermArena,
    entries: &Entries,
    role: Builtin,
    (holder, defined): (ConstantIndex, ValueId),
) -> Result<(), Departure>
{
    let held = |wanted: Builtin| {
        entries
            .iter()
            .position(|entry| entry.declaration().role() == Maybe::Present(wanted))
            .map(ConstantIndex::from)
            .ok_or(Departure::Reads(wanted))
    };
    let signature = held(Builtin::IrSignature)?;
    let pairs = held(Builtin::IrPair)?;
    let fields = match role {
        Builtin::IrDecode => Some(held(Builtin::IrArgs)?),
        Builtin::IrSignature | Builtin::IrPair | Builtin::IrArgs => None,
    };
    let body = arena.value_constant(holder);
    let var = |arena: &mut TermArena, index: u32| arena.value_variable(DeBruijnIndex::from(index));
    // `force head a₀ … aₙ`.
    let call = |arena: &mut TermArena, head: ValueId, arguments: &[ValueId]| {
        let forced = arena.computation_force(head);
        arguments.iter().fold(forced, |applied, &argument| {
            arena.computation_application(applied, argument)
        })
    };
    // The constructor `tag` of the signature over the output `output`
    // binders out, its fields the variables at `fields`.
    let code = |arena: &mut TermArena, output: u32, tag: usize, fields: &[u32]| {
        let output = var(arena, output);
        let datatype = arena.value_type_data(signature, alloc::vec![output]);
        let fields = fields.iter().map(|&index| var(arena, index)).collect();
        arena.value_constructor(datatype, ConstructorTag::from(tag), fields)
    };
    // The code of `A -> X`, for `A` at `a` and `X` at `x`.
    let arrow = |arena: &mut TermArena, a: u32, x: u32| {
        let level = gandr_kernel_strata::Level::zero();
        let code = var(arena, a);
        let domain = arena.value_type_element(code, level.clone());
        let code = var(arena, x);
        let decoded = arena.value_type_element(code, level);
        let codomain = arena.comp_type_returner(decoded);
        let arrow = arena.comp_type_arrow(domain, codomain);
        let thunk = arena.value_type_thunk(arrow);
        arena.value_quote(thunk)
    };
    // The value that `read` returns at `argument`, where a value stands.
    let returned = |arena: &mut TermArena, read: ValueId, argument: ValueId| {
        let run = call(arena, read, &[argument]);
        arena.value_returned(run)
    };
    // `t ∘ h` as a type writes it: `λ z. t (h z)`, `h z` standing as the value
    // it returns.
    let composite = |arena: &mut TermArena, h: u32, t: u32| {
        let z = var(arena, 0);
        let read = var(arena, h.saturating_add(1));
        let inner = returned(arena, read, z);
        let decoder = var(arena, t.saturating_add(1));
        let outer = call(arena, decoder, &[inner]);
        let lambda = arena.computation_lambda(outer);
        arena.value_thunk(lambda)
    };
    // `t ∘ h` as a term writes it: `λ z. w ← h z; t w`.
    let sequenced = |arena: &mut TermArena, h: u32, t: u32| {
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
    let family = |arena: &mut TermArena,
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
    let equations: [(ComputationId, ComputationId); 3] = if let Some(fields) = fields {
        let fields = arena.value_constant(fields);
        let unit = arena.value_unit();
        // ι, under `O` 3, `X` 2, `t` 1 and `e` 0.
        let stop = code(arena, 3, 0, &[0]);
        let (output, over, decoder) = (var(arena, 3), var(arena, 2), var(arena, 1));
        let left = call(arena, body, &[output, stop, over, decoder, unit]);
        let e = var(arena, 0);
        let iota = (left, arena.computation_return(e));
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
            let datatype = arena.value_type_data(pairs, alloc::vec![first, asked]);
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
            )
        };
        [iota, step(1, false), step(2, true)]
    }
    else {
        // ι, under `O` 3, `X` 2, `t` 1 and `e` 0.
        let stop = code(arena, 3, 0, &[0]);
        let (output, over, decoder) = (var(arena, 3), var(arena, 2), var(arena, 1));
        let left = call(arena, body, &[output, stop, over, decoder]);
        let unit = arena.value_type_unit();
        let quoted = arena.value_quote(unit);
        let iota = (left, arena.computation_return(quoted));
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
            let pairs = arena.value_type_data(pairs, alloc::vec![first, asked]);
            let quoted = arena.value_quote(pairs);
            (left, arena.computation_return(quoted))
        };
        [iota, step(1, false), step(2, true)]
    };
    let mut bodies: Vec<Unfoldable> = entries
        .iter()
        .map(|entry| match *entry.content() {
            DeclarationContent::Def { body, .. } => Unfoldable::Body(body),
            DeclarationContent::Data { .. }
            | DeclarationContent::Codata { .. }
            | DeclarationContent::Axiom { .. }
            | DeclarationContent::AbstractType { .. } => Unfoldable::Opaque,
        })
        .collect();
    bodies.push(Unfoldable::Body(defined));
    let unfoldings = Unfoldings::new(bodies)
        .presenting(crate::presented::Presentations::of(entries))
        .identifying(entries);
    for (tag, (left, right)) in equations.into_iter().enumerate() {
        let verdict = crate::replay::convert_unfolding(
            arena,
            &unfoldings,
            ReplaySides::Computations(left, right),
            ReplayBudget::DEFAULT,
        );
        if verdict != KernelVerdict::Convertible {
            return Err(Departure::Answer(ConstructorTag::from(tag)));
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests;
