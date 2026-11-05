//! The built-in roles in the kernel: a declaration that holds a role answers
//! the role's canonical form, decided by the kernel at admission.
//!
//! The checker validates every holder (`gandr_core_checker::canonical`), and
//! the kernel decides the same forms again over its own terms. It never takes
//! a producer's mark on trust. A role has one holder: the signature type, the
//! pair type and the family are data declarations, and `E`, `F`, the decoder,
//! the hypotheses `H`, the map `M` and the eliminator are definitions.
//!
//! |Role|The canonical form|
//! |---|---|
//! |`irSignature`|one parameter `O : Type`, no index, and the constructors `ι(e : O)`, `σ(A : Type, f : A -> Sig(O))` and `δ(A : Type, f : (A -> O) -> Sig(O))` in this order|
//! |`irPair`|the parameters `A : Type` and `B : A -> Type`, no index, and one constructor `(x : A, y : B(x))`|
//! |`irArgs`|the answers of `E` at `ι`, `σ` and `δ`, decided by conversion|
//! |`irDecode`|the answers of `F` at `ι`, `σ` and `δ`, decided by conversion|
//! |`irFamily`|the parameters `O : Type` and `S : Sig(O)`, no index, and one constructor of one field, the decode of `E(O, S, ⌜IR(O, S)⌝, λ m. el(O, S, m))`, `el` the declaration after it|
//! |`irDecoder`|the answer `F(O, S, ⌜IR(O, S)⌝, λ n. el(O, S, n), x)` at `intro(x)`, decided by conversion|
//! |`irHypotheses`|the answers of `H(O, S, X, t, P, a)` at `ι`, `σ` and `δ`: the unit type, `H` at the rest, and the pair of `(z : A) -> P(h(z))` and `H` at the rest|
//! |`irMap`|the answers of `M(O, S, X, t, P, g, a)` at `ι`, `σ` and `δ`: the unit, `M` at the rest, and the pair of `λ z. g(h(z))` and `M` at the rest|
//! |`irEliminator`|the answer `w ← M(O, S, ⌜IR(O, S)⌝, λ m. el(O, S, m), P, λ n. elim(O, S, P, s, n), x); s(x, w)` at `intro(x)`, decided by conversion with only the holder unfolding|
//!
//! The family keeps no occurrence walk, and the own fixpoints of the decoder
//! and the eliminator open no stage (`check::check_declaration_with_memo`):
//! their canonical forms are strictly positive and structural by construction.
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
            Builtin::IrFamily => family(
                arena,
                entries,
                position,
                (parameters, indices, constructors),
            ),
            Builtin::IrArgs
            | Builtin::IrDecode
            | Builtin::IrDecoder
            | Builtin::IrHypotheses
            | Builtin::IrMap
            | Builtin::IrEliminator => Err(Departure::Constructors),
        },
        DeclarationContent::Def { body, .. } => match role {
            Builtin::IrArgs | Builtin::IrDecode => {
                let watermark = arena.watermark();
                let answered = answers(arena, entries, role, (position, body));
                arena.truncate_to(watermark);
                answered
            },
            Builtin::IrDecoder => {
                let watermark = arena.watermark();
                let answered = decoder(arena, entries, (position, body));
                arena.truncate_to(watermark);
                answered
            },
            Builtin::IrHypotheses | Builtin::IrMap => {
                let watermark = arena.watermark();
                let answered = induction(arena, entries, role, (position, body));
                arena.truncate_to(watermark);
                answered
            },
            Builtin::IrEliminator => {
                let watermark = arena.watermark();
                let answered = eliminator(arena, entries, (position, body));
                arena.truncate_to(watermark);
                answered
            },
            Builtin::IrSignature | Builtin::IrPair | Builtin::IrFamily => {
                Err(Departure::Constructors)
            },
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
        Builtin::IrSignature
        | Builtin::IrPair
        | Builtin::IrArgs
        | Builtin::IrFamily
        | Builtin::IrDecoder
        | Builtin::IrHypotheses
        | Builtin::IrMap
        | Builtin::IrEliminator => None,
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

/// Compare the data declaration at `holder` with the canonical family that a
/// signature defines.
///
/// # Specification
/// - requires: the signature's nodes live in `arena`; the declaration takes the
///   position `holder`, after the last entry.
/// - ensures: `Ok(())` exactly when the signature has the parameters `O : Type`
///   and `S : Sig(O)`, no index and one constructor of one field, the decode of
///   `E(O, S, ⌜IR(O, S)⌝, λ m. el(O, S, m))`: `Sig` and `E` the holders of
///   their roles, `IR` the holder at its parameters and `el` the declaration
///   right after it.
/// - fails: [`Departure::Reads`] for an unheld role the canonical form reads,
///   then the first [`Departure`] in the order parameters, indices,
///   constructors, then the constructor's arity and its field.
/// - panics: none.
///
/// # Errors
/// As `- fails:`.
///
/// # Adequacy
/// - hypothesis: L3 — `std.ir`'s `IR` admits, and the family forged with a
///   second field is refused at its arity.
/// - witness: `kernel_export::kernel_presented_readmission::the_holders_of_std_ir_cross_with_their_roles_and_a_forged_one_is_refused_5304`
/// - witness: `builtin::tests::a_departing_family_and_decoder_are_refused_3575`
fn family(
    arena: &TermArena,
    entries: &Entries,
    holder: ConstantIndex,
    (parameters, indices, constructors): (&[ValueTypeId], &[ValueTypeId], &[Vec<ValueTypeId>]),
) -> Result<(), Departure>
{
    let held = |wanted: Builtin| {
        entries
            .iter()
            .position(|entry| entry.declaration().role() == Maybe::Present(wanted))
            .map(ConstantIndex::from)
            .ok_or(Departure::Reads(wanted))
    };
    let signed = held(Builtin::IrSignature)?;
    let fields = held(Builtin::IrArgs)?;
    let shapes = Shapes { arena };
    let zero = DeBruijnIndex::from(0_u32);
    let [output, code] = *parameters
    else {
        return Err(Departure::Parameters);
    };
    if !shapes.universe(output).0 || !shapes.family(code, (signed, zero)).0 {
        return Err(Departure::Parameters);
    }
    if !indices.is_empty() {
        return Err(Departure::Indices);
    }
    let [ref only] = *constructors
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
    let variable =
        |value: ValueId, index: u32| shapes.variable(value, DeBruijnIndex::from(index)).0;
    // The spine of `force head a₀ … aₙ`, innermost argument last.
    let spine = |run: ComputationId| {
        let mut arguments = Vec::new();
        let mut cursor = run;
        while let Some(&Computation::Application(head, argument)) = arena.computation(cursor) {
            arguments.push(argument);
            cursor = head;
        }
        arguments.reverse();
        match arena.computation(cursor) {
            Some(&Computation::Force(head)) => Maybe::Present((head, arguments)),
            Some(_) | None => Maybe::Absent(Unshaped),
        }
    };
    let constant = |value: ValueId, wanted: ConstantIndex| matches!(arena.value(value), Some(&Value::Constant(found)) if found == wanted);
    // `E(O, S, ⌜IR(O, S)⌝, λ m. el(O, S, m))` under `O` 1 and `S` 0.
    let canonical = (|| {
        let Some(&ValueType::Element { code, .. }) = arena.value_type(field)
        else {
            return Fits(false);
        };
        let Some(&Value::Returned(run)) = arena.value(code)
        else {
            return Fits(false);
        };
        let Maybe::Present((head, arguments)) = spine(run)
        else {
            return Fits(false);
        };
        let [outputs, signature, own, decode] = *arguments
        else {
            return Fits(false);
        };
        let own = matches!(
            arena.value(own),
            Some(&Value::Quote(quoted)) if matches!(
                arena.value_type(quoted),
                Some(&ValueType::Data { declaration, ref arguments })
                    if declaration == holder
                        && matches!(**arguments, [a, b] if variable(a, 1) && variable(b, 0))
            )
        );
        let decoder = ConstantIndex::from(usize::from(holder).saturating_add(1));
        let decodes = match arena.value(decode) {
            Some(&Value::Thunk(lambda)) => match arena.computation(lambda) {
                Some(&Computation::Lambda(body)) => match spine(body) {
                    Maybe::Present((called, ref passed)) => {
                        constant(called, decoder)
                            && matches!(**passed, [a, b, m] if variable(a, 2) && variable(b, 1) && variable(m, 0))
                    },
                    Maybe::Absent(Unshaped) => false,
                },
                Some(_) | None => false,
            },
            Some(_) | None => false,
        };
        Fits(
            constant(head, fields)
                && variable(outputs, 1)
                && variable(signature, 0)
                && own
                && decodes,
        )
    })();
    if !canonical.0 {
        return Err(departs);
    }
    Ok(())
}

/// Compare `defined`, the body of the holder of the decoder role at `holder`,
/// with the canonical decoder by its answer at the family's one constructor.
///
/// # Specification
/// - requires: `arena` holds `defined` and every entry's nodes; the holder
///   takes the position `holder`, after the last entry.
/// - ensures: `Ok(())` exactly when the family's holder stands right before
///   `holder` and, under rigid variables for `O`, `S` and the field `x`, the
///   holder at `intro(x)` converts with `F(O, S, ⌜IR(O, S)⌝, λ n. el(O, S, n),
///   x)`, every definition and the holder unfolding. Every value of the family
///   is `intro(x)` for some `x`, so the holder answers as the canonical decoder
///   at every value.
/// - fails: [`Departure::Reads`] for an unheld role the canonical form reads,
///   the family's role too when its holder stands elsewhere, then
///   [`Departure::Answer`] at the one constructor.
/// - panics: none.
///
/// # Errors
/// As `- fails:`.
///
/// # Adequacy
/// - hypothesis: L3 — `std.ir`'s `el` admits, and a decoder that answers the
///   field itself is refused at the constructor.
/// - witness: `builtin::tests::a_departing_family_and_decoder_are_refused_3575`
#[spec(ensures: |ret| ret.is_ok() || matches!(ret, Err(Departure::Reads(_) | Departure::Answer(_))))]
fn decoder(
    arena: &mut TermArena,
    entries: &Entries,
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
    let family = held(Builtin::IrFamily)?;
    if usize::from(family).saturating_add(1) != usize::from(holder) {
        return Err(Departure::Reads(Builtin::IrFamily));
    }
    let decode = held(Builtin::IrDecode)?;
    let var = |arena: &mut TermArena, index: u32| arena.value_variable(DeBruijnIndex::from(index));
    // `force head a₀ … aₙ`.
    let call = |arena: &mut TermArena, head: ValueId, arguments: &[ValueId]| {
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
    let unfoldings = holding(entries, defined);
    let verdict = crate::replay::convert_unfolding(
        arena,
        &unfoldings,
        ReplaySides::Computations(left, right),
        ReplayBudget::DEFAULT,
    );
    if verdict != KernelVerdict::Convertible {
        return Err(Departure::Answer(ConstructorTag::from(0_usize)));
    }
    Ok(())
}

/// Compare `defined`, the body of the holder of the hypotheses or the map at
/// `holder`, with the canonical body of its role by their answers at each
/// constructor of the signature type, decided by the kernel's conversion.
///
/// # Specification
/// - requires: `role` is [`Builtin::IrHypotheses`] or [`Builtin::IrMap`];
///   `arena` holds `defined` and every entry's nodes; the holder takes the
///   position `holder`, after the last entry.
/// - ensures: `Ok(())` exactly when, at `ι`, `σ` and `δ` in turn, the holder
///   applied to the constructor over rigid fields converts with the answer the
///   module lead states, every definition and the holder unfolding.
/// - fails: [`Departure::Reads`] for an unheld role the canonical body reads,
///   then [`Departure::Answer`] at the first constructor whose answer the
///   conversion does not relate.
/// - panics: none.
///
/// # Errors
/// As `- fails:`.
///
/// # Adequacy
/// - hypothesis: L3 — the hypotheses read the signature type and the map reads
///   `E` before any answer. `std.ir`'s `hyps` and `mapArgs` admit, and
///   hypotheses of the unit type at every code are refused at `δ`, each in
///   `surface-corpus`'s export cases.
/// - witness: `builtin::tests::the_hypotheses_map_and_eliminator_read_their_roles_first_5160`
#[spec(ensures: |ret| ret.is_ok() || matches!(ret, Err(Departure::Reads(_) | Departure::Answer(_))))]
fn induction(
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
    let fields = held(Builtin::IrArgs)?;
    let mapping = role == Builtin::IrMap;
    let hypotheses = if mapping {
        held(Builtin::IrHypotheses)?
    }
    else {
        holder
    };
    // The map takes the function `g` past the predicate, one binder more.
    let extra = u32::from(mapping);
    let body = arena.value_constant(holder);
    let fields = arena.value_constant(fields);
    let var = |arena: &mut TermArena, index: u32| arena.value_variable(DeBruijnIndex::from(index));
    // `force head a₀ … aₙ`.
    let call = |arena: &mut TermArena, head: ValueId, arguments: &[ValueId]| {
        let forced = arena.computation_force(head);
        arguments.iter().fold(forced, |applied, &argument| {
            arena.computation_application(applied, argument)
        })
    };
    // The value that `read` returns at `argument`, where a value stands.
    let returned = |arena: &mut TermArena, read: ValueId, argument: ValueId| {
        let run = call(arena, read, &[argument]);
        arena.value_returned(run)
    };
    // The constructor `tag` of the signature over the output `output` binders
    // out, its fields the variables at `fields`.
    let code = |arena: &mut TermArena, output: u32, tag: usize, fields: &[u32]| {
        let output = var(arena, output);
        let datatype = arena.value_type_data(signature, alloc::vec![output]);
        let fields = fields.iter().map(|&index| var(arena, index)).collect();
        arena.value_constructor(datatype, ConstructorTag::from(tag), fields)
    };
    let decode = |arena: &mut TermArena, code: ValueId| {
        arena.value_type_element(code, gandr_kernel_strata::Level::zero())
    };
    // The code of `A -> X`, for `A` at `first` and `X` at `over`.
    let arrow = |arena: &mut TermArena, first: u32, over: u32| {
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
    let composite = |arena: &mut TermArena, inner: u32, outer: u32| {
        let point = var(arena, 0);
        let read = var(arena, inner.saturating_add(1));
        let inner = returned(arena, read, point);
        let decoder = var(arena, outer.saturating_add(1));
        let outer = call(arena, decoder, &[inner]);
        let lambda = arena.computation_lambda(outer);
        arena.value_thunk(lambda)
    };
    // `t ∘ h` as a term writes it: `λ z. w ← h z; t w`.
    let sequenced = |arena: &mut TermArena, inner: u32, outer: u32| {
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
    let asked = |arena: &mut TermArena, decoded: bool| {
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
        arena.value_type_data(pairs, alloc::vec![first, family])
    };
    // The pair type of `H`'s answer at `δ`, `shift` binders in: `Pair((z : A)
    // -> P(h(z)), λ k. H(O, f(t ∘ h), X, t, P, r))`, the hypothesis at each
    // point of the field before those of the rest.
    let hypothesised = |arena: &mut TermArena, shift: u32| {
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
        arena.value_type_data(pairs, alloc::vec![first, family])
    };
    // The holder's parameters before its argument, `shift` binders in, the
    // code `code` in place.
    let parameters = |arena: &mut TermArena, code: ValueId, (shift, past): (u32, u32)| {
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
    // ι, under the parameters and `e` 0.
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
        (left, right)
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
        (left, right)
    };
    let equations = [iota, step(1, false), step(2, true)];
    let unfoldings = holding(entries, defined);
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

/// Compare `defined`, the body of the holder of the eliminator role at
/// `holder`, with the canonical eliminator by its answer at the family's one
/// constructor.
///
/// # Specification
/// - requires: `arena` holds `defined` and every entry's nodes; the holder
///   takes the position `holder`, after the last entry.
/// - ensures: `Ok(())` exactly when, under rigid variables for `O`, `S`, `P`,
///   the step `s` and the field `x`, the holder at `intro(x)` converts with `w
///   ← M(O, S, ⌜IR(O, S)⌝, λ m. el(O, S, m), P, λ n. elim(O, S, P, s, n), x);
///   s(x, w)`. Only the holder unfolds, and every entry before it stays rigid.
///   Every value of the family is `intro(x)` for some `x`, so the holder
///   answers as the canonical eliminator at every value.
/// - fails: [`Departure::Reads`] for an unheld role the canonical form reads,
///   then [`Departure::Answer`] at the one constructor.
/// - panics: none.
///
/// # Errors
/// As `- fails:`.
///
/// # Adequacy
/// - hypothesis: L3 — the eliminator reads the family before any other role.
///   `std.ir`'s `elim` admits, and an eliminator that calls itself on its own
///   value is refused at the constructor, each in `surface-corpus`'s export
///   cases.
/// - witness: `builtin::tests::the_hypotheses_map_and_eliminator_read_their_roles_first_5160`
#[spec(ensures: |ret| ret.is_ok() || matches!(ret, Err(Departure::Reads(_) | Departure::Answer(_))))]
fn eliminator(
    arena: &mut TermArena,
    entries: &Entries,
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
    let family = held(Builtin::IrFamily)?;
    let decoder = held(Builtin::IrDecoder)?;
    let map = held(Builtin::IrMap)?;
    let var = |arena: &mut TermArena, index: u32| arena.value_variable(DeBruijnIndex::from(index));
    // `force head a₀ … aₙ`.
    let call = |arena: &mut TermArena, head: ValueId, arguments: &[ValueId]| {
        let forced = arena.computation_force(head);
        arguments.iter().fold(forced, |applied, &argument| {
            arena.computation_application(applied, argument)
        })
    };
    // `IR(O, S)`, under `O` 4 and `S` 3.
    let own = |arena: &mut TermArena| {
        let (output, signature) = (var(arena, 4), var(arena, 3));
        arena.value_type_data(family, alloc::vec![output, signature])
    };
    let body = arena.value_constant(holder);
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
    // Only the holder unfolds, as in the checker: each side calls the map's
    // holder by its name, and a conversion that unfolds the map at the open
    // signature `S` meets the eliminator again in each `δ` arm.
    let unfoldings = alone(entries, defined);
    let verdict = crate::replay::convert_unfolding(
        arena,
        &unfoldings,
        ReplaySides::Computations(left, right),
        ReplayBudget::DEFAULT,
    );
    if verdict != KernelVerdict::Convertible {
        return Err(Departure::Answer(ConstructorTag::from(0_usize)));
    }
    Ok(())
}

/// The unfoldings a holder's answers convert under: each entry's definition
/// unfolds to its body, and the holder unfolds to `defined`.
///
/// # Specification
/// trivial.
fn holding(
    entries: &Entries,
    defined: ValueId,
) -> Unfoldings
{
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
    Unfoldings::new(bodies)
        .presenting(crate::presented::Presentations::of(entries))
        .identifying(entries)
}

/// The unfoldings under which only the holder unfolds, to `defined`: every
/// entry before it stays rigid.
///
/// # Specification
/// trivial.
fn alone(
    entries: &Entries,
    defined: ValueId,
) -> Unfoldings
{
    let mut bodies: Vec<Unfoldable> = entries.iter().map(|_entry| Unfoldable::Opaque).collect();
    bodies.push(Unfoldable::Body(defined));
    Unfoldings::new(bodies)
        .presenting(crate::presented::Presentations::of(entries))
        .identifying(entries)
}

#[cfg(test)]
mod tests;
