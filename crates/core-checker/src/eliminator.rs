//! The eliminator a recursive data declaration derives, per motive.
//!
//! For a declaration `T` at admission position `p` with parameters `P̄`,
//! constructors `c_i` over fields `F̄_i`, and a motive `C` under the
//! parameters and one scrutinee binder, the fold writes
//!
//! ```text
//! elim_T[C] : U (Π p̄ : P̄. U M_1 → … → U M_n → Π (x : T p̄). C)
//! elim_T[C] = thunk (λp̄. λm̄. fix_SD rec. λx. case x [C] of
//!               { c_i ↦ λf̄. (force m_i) f̄ h̄ })
//! M_i       = Π f̄ : F̄_i. U H_1 → … → U H_r → C[c_i f̄ / x]
//! ```
//!
//! with one hypothesis per recursive field, in field order: a direct field
//! `f : T p̄` has `H = C[f / x]` and `h = thunk ((force rec) f)`; a function
//! field `f : U (Π ȳ. F (T p̄))` has `H = Π ȳ. C` and
//! `h = thunk (λȳ. t ← (force f) ȳ; (force rec) t)`, which needs a motive
//! that does not name the scrutinee. The fold is untrusted: the eliminator is
//! an ordinary declaration the checker judges and the kernel readmits, its
//! fixpoint typed by stages in both.
//!
//! A function field's hypothesis ranges over the function's results, where no
//! scrutinee is in scope, so a motive naming its scrutinee at such a
//! declaration is `DerivationRefusal::DependentMotiveAtFunctionField`. The
//! eliminator is stated over an explicit motive (`McBride`, *Elimination with a
//! Motive*, TYPES 2000, doi:10.1007/3-540-45842-5_13) and written over the
//! guarded fixpoint (Giménez, *Structural recursive definitions in type
//! theory*, ICALP 1998, doi:10.1007/BFb0055070).
//!
//! # Definitions by eliminator
//!
//! A definition by eliminator is an application `force (elim_T[C]) p̄ m̄ x`.
//! `length`, `append` and `map` over `List A`, and `plus` over Nat, each:
//!
//! - check, and normalise through `gandr-core-nbe` to the expected numeral or
//!   list;
//! - readmit through the kernel with an empty axiom audit;
//! - export to the same bytes on every run;
//! - carry a conversion whose trace the kernel replays, both the convertible
//!   and the apart verdict.
//!
//! A Tree with a function field derives its eliminator too, and a depth defined
//! through it checks, readmits and normalises.
//!
//! # Decision
//!
//! **Choice.** The eliminator is derived source over the kernel's one fixpoint,
//! with the motive explicit, rather than a checker-native recursor former.
//! **Alternatives.** A native recursor needs a kernel rule per signature.
//! Compiling pattern-matching definitions to case trees belongs to the
//! lowering, which this fold serves rather than replaces. **Reversal.** A
//! derivation the descent replay cannot follow, such as a nested occurrence's
//! hypothesis through another family's eliminator, needs a generalised descent
//! rule first.
//!
//! Witnesses:
//! `tests::recursive_data::recursive_blocks_are_admitted_in_both_checkers`,
//! `tests::recursive_data::derived_eliminators_are_admitted_and_readmitted`,
//! `tests::recursive_data::definitions_by_eliminator_normalise`,
//! `tests::recursive_data::the_kernel_replays_a_conversion_through_a_definition_by_eliminator`
//! and `tests::recursive_data::the_export_is_deterministic`.

use alloc::vec::Vec;

use anodized::spec;
use gandr_core_term::Binders;
use gandr_core_term::CompType;
use gandr_core_term::CompTypeId;
use gandr_core_term::ComputationId;
use gandr_core_term::CoreArena;
use gandr_core_term::DataSignature;
use gandr_core_term::ValueId;
use gandr_core_term::ValueType;
use gandr_core_term::ValueTypeId;
use gandr_core_term::Zone;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::ConstructorTag;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::FieldPosition;
use gandr_kernel_term::FixpointEvidence;
use gandr_kernel_term::OccurrenceSite;
use quenchant_shape::shape::Maybe;

/// Why the fold derives no eliminator.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum DerivationRefusal
{
    /// The motive names its scrutinee, and a function field's hypothesis
    /// ranges over the function's results, where no scrutinee is in scope.
    DependentMotiveAtFunctionField(OccurrenceSite),
    /// A binder count passes the representable ceiling.
    BinderCeiling,
}

/// A derived eliminator: the declaration the fold writes.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Eliminator
{
    /// Its declared type, `U (Π p̄. U M̄ → Π (x : T p̄). C)`.
    declared: ValueTypeId,
    /// Its body, a thunk of the abstracted fixpoint.
    body: ValueId,
}

impl Eliminator
{
    /// The declared type.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn declared(&self) -> ValueTypeId
    {
        self.declared
    }

    /// The body.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn body(&self) -> ValueId
    {
        self.body
    }
}

/// How a field names its own family.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum FieldShape
{
    /// It does not.
    Plain,
    /// It is the family, `T p̄`.
    Direct,
    /// It is a thunked function into the family, `U (Π ȳ. F (T p̄))`.
    Function(CompTypeId),
}

/// The number of binders `items` opens, one per item, checked against the
/// ceiling.
///
/// # Specification
/// trivial.
fn count<T>(items: &[T]) -> Result<Binders, DerivationRefusal>
{
    u32::try_from(items.len())
        .map(Binders::from)
        .map_err(|_cause| DerivationRefusal::BinderCeiling)
}

/// The sum of two binder counts, checked against the ceiling.
///
/// # Specification
/// trivial.
fn plus(
    left: Binders,
    right: Binders,
) -> Result<Binders, DerivationRefusal>
{
    u32::from(left)
        .checked_add(u32::from(right))
        .map(Binders::from)
        .ok_or(DerivationRefusal::BinderCeiling)
}

/// `left` binders less `right`, refused below none.
///
/// # Specification
/// trivial.
fn minus(
    left: Binders,
    right: Binders,
) -> Result<Binders, DerivationRefusal>
{
    u32::from(left)
        .checked_sub(u32::from(right))
        .map(Binders::from)
        .ok_or(DerivationRefusal::BinderCeiling)
}

/// The intuitionistic variable bound `distance` binders out.
///
/// # Specification
/// trivial.
fn variable(
    arena: &mut CoreArena,
    distance: Binders,
) -> ValueId
{
    arena.value_variable(
        Zone::Intuitionistic,
        DeBruijnIndex::from(u32::from(distance)),
    )
}

/// The variables of the innermost `binders` binders, outermost first.
///
/// # Specification
/// trivial.
fn variables(
    arena: &mut CoreArena,
    binders: Binders,
) -> Vec<ValueId>
{
    (0 .. u32::from(binders))
        .rev()
        .map(|distance| variable(arena, Binders::from(distance)))
        .collect()
}

/// The shape of one field: how, if at all, it names its family.
///
/// # Specification
/// - requires: `field` is scoped under the declaration's parameters, and the
///   declaration passed the occurrence walk, so a field names the family only
///   in the two admitted forms.
/// - ensures: `Direct` for the family itself, `Function` with the thunked
///   computation type for a thunked function into the family, `Plain` for any
///   other field.
/// - panics: none.
///
/// # Termination
/// - reason: the `while let` loop descends one function codomain per turn, not
///   recursion.
/// - measure: the arena position of the codomain.
///
/// # Adequacy
/// - hypothesis: L3 — `List A`'s element and tail and `Tree`'s function field
///   take the three shapes; a shape misread is a derived eliminator the checker
///   refuses, never one it accepts.
/// - witness: `tests::recursive_data::derived_eliminators_are_admitted_and_readmitted`
/// - witness: `tests::recursive_data::a_function_field_into_another_type_takes_no_hypothesis`
#[spec(ensures: |ret| (ret == FieldShape::Direct)
    == matches!(arena.value_type(field), Some(&ValueType::Data { declaration, .. }) if declaration == position)
    && match ret {
        | FieldShape::Function(chain) => matches!(arena.value_type(field), Some(&ValueType::Thunk(held)) if held == chain),
        | FieldShape::Plain | FieldShape::Direct => true,
    })]
fn shape(
    arena: &CoreArena,
    position: ConstantIndex,
    field: ValueTypeId,
) -> FieldShape
{
    let names = |result: ValueTypeId| matches!(arena.value_type(result), Some(&ValueType::Data { declaration, .. }) if declaration == position);
    if names(field) {
        return FieldShape::Direct;
    }
    let Some(&ValueType::Thunk(chain)) = arena.value_type(field)
    else {
        return FieldShape::Plain;
    };
    let mut focus = chain;
    while let Some(&(CompType::Arrow { codomain, .. } | CompType::Pi { codomain, .. })) =
        arena.comp_type(focus)
    {
        focus = codomain;
    }
    match arena.comp_type(focus) {
        Some(&CompType::Returner { result, .. }) if focus != chain && names(result) => {
            FieldShape::Function(chain)
        },
        Some(
            &(CompType::Returner { .. }
            | CompType::With(..)
            | CompType::Arrow { .. }
            | CompType::Pi { .. }
            | CompType::Element { .. }
            | CompType::Unknown),
        )
        | None => FieldShape::Plain,
    }
}

/// A function field's hypothesis type, `Π ȳ. C`, under the parameters and
/// `fields` field binders.
///
/// # Specification
/// - requires: `chain` is the field's thunked computation type, scoped under
///   the parameters and the fields before it, `from` binders short of all
///   `fields`; `closed` is the motive strengthened past its scrutinee.
/// - ensures: the chain's domains, shifted past the fields from the field on,
///   ending in the motive shifted past every field and the chain's own
///   dependent binders.
/// - panics: none.
///
/// # Termination
/// - reason: two loops over the chain's codomains and its collected domains,
///   not recursion.
/// - measure: the chain's length.
///
/// # Adequacy
/// - hypothesis: L3 — `Tree`'s `Nat → F Tree` field has the hypothesis `Nat →
///   C`, and a W-type's function field after its index code reads that code.
/// - witness: `tests::recursive_data::derived_eliminators_are_admitted_and_readmitted`
#[spec(ensures: |ret| ret.as_ref().is_err() || ret.as_ref().is_ok_and(|id| arena.comp_type(*id).is_some()))]
fn function_hypothesis(
    arena: &mut CoreArena,
    chain: CompTypeId,
    closed: CompTypeId,
    (fields, from): (Binders, Binders),
) -> Result<CompTypeId, DerivationRefusal>
{
    let shifted = gandr_core_term::shift_comp_type(arena, chain, from);
    let mut domains: Vec<(ValueTypeId, CompBinding)> = Vec::new();
    let mut focus = shifted;
    let mut dependent = Binders::NONE;
    loop {
        match arena.comp_type(focus) {
            Some(&CompType::Arrow { domain, codomain }) => {
                domains.push((domain, CompBinding::Closed));
                focus = codomain;
            },
            Some(&CompType::Pi { domain, codomain }) => {
                domains.push((domain, CompBinding::Binds));
                dependent = plus(dependent, Binders::ONE)?;
                focus = codomain;
            },
            Some(&CompType::Returner { .. }) => break,
            Some(&(CompType::With(..) | CompType::Element { .. } | CompType::Unknown)) | None => {
                return Err(DerivationRefusal::BinderCeiling);
            },
        }
    }
    let past = plus(fields, dependent)?;
    let mut rebuilt = gandr_core_term::shift_comp_type(arena, closed, past);
    for &(domain, binding) in domains.iter().rev() {
        rebuilt = match binding {
            CompBinding::Closed => arena.comp_type_arrow(domain, rebuilt),
            CompBinding::Binds => arena.comp_type_pi(domain, rebuilt),
        };
    }
    Ok(rebuilt)
}

/// Whether a function type's codomain stands under its domain's binder.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum CompBinding
{
    /// A dependent arrow.
    Binds,
    /// A plain arrow.
    Closed,
}

/// The number of domains a thunked function field's chain takes.
///
/// # Specification
/// trivial.
fn arity(
    arena: &CoreArena,
    chain: CompTypeId,
) -> Result<Binders, DerivationRefusal>
{
    let mut focus = chain;
    let mut domains = Binders::NONE;
    while let Some(&(CompType::Arrow { codomain, .. } | CompType::Pi { codomain, .. })) =
        arena.comp_type(focus)
    {
        domains = plus(domains, Binders::ONE)?;
        focus = codomain;
    }
    Ok(domains)
}

/// Derive the eliminator of the data declaration at `position` for
/// `motive`.
///
/// # Specification
/// - requires: `signature` is the admitted signature at `position`, and
///   `motive` a computation type scoped under its parameters and one scrutinee
///   binder of `T p̄`.
/// - ensures: the declared type and body of `elim_T[motive]` as the module
///   documentation states, minted into `arena`; the fixpoint carries structural
///   evidence.
/// - provides: the derived constant a definition by eliminator applies to its
///   parameters, its methods and its target. It is a declaration like any
///   other: the checker judges it, the kernel readmits it, and both type its
///   recursion by stages.
/// - fails: a dependent motive with a function field, or a binder count past
///   the ceiling.
/// - panics: none.
///
/// # Errors
/// [`DerivationRefusal`] naming the reason.
///
/// # Adequacy
/// - hypothesis: L3 — `Nat`, `List A` and `Tree` derive eliminators at closed
///   and dependent motives that the checker accepts and the kernel readmits
///   with an empty audit, and a dependent motive over `Tree`'s function field
///   is refused by name.
/// - witness: `tests::recursive_data::derived_eliminators_are_admitted_and_readmitted`
#[spec(ensures: |ret| ret.as_ref().is_err() || ret.as_ref().is_ok_and(|derived| arena.value_type(derived.declared).is_some() && arena.value(derived.body).is_some()))]
#[inline]
pub fn derive(
    arena: &mut CoreArena,
    position: ConstantIndex,
    signature: &DataSignature,
    motive: CompTypeId,
) -> Result<Eliminator, DerivationRefusal>
{
    let parameters = count(signature.parameters())?;
    let methods = count(signature.constructors())?;
    let two = plus(Binders::ONE, Binders::ONE)?;
    let arguments = variables(arena, parameters);
    let family = arena.value_type_data(position, arguments);
    let mut shapes: Vec<Vec<FieldShape>> = Vec::new();
    let closed = gandr_core_term::strengthen_comp_type(arena, motive);
    for (tag, fields) in signature.constructors().iter().enumerate() {
        let mut row = Vec::new();
        for (field, &root) in fields.iter().enumerate() {
            let site = OccurrenceSite::Field {
                tag: ConstructorTag::from(tag),
                field: FieldPosition::from(field),
            };
            let found = shape(arena, position, root);
            if matches!(found, FieldShape::Function(_)) && matches!(closed, Maybe::Absent(_)) {
                return Err(DerivationRefusal::DependentMotiveAtFunctionField(site));
            }
            row.push(found);
        }
        shapes.push(row);
    }
    // The method types, each under the parameters.
    let mut method_types = Vec::new();
    for ((tag, fields), row) in signature.constructors().iter().enumerate().zip(&shapes) {
        let width = count(fields)?;
        let shifted_family = gandr_core_term::shift_value_type(arena, family, width);
        let values = variables(arena, width);
        let constructor =
            arena.value_constructor(shifted_family, ConstructorTag::from(tag), values);
        let lifted = gandr_core_term::shift_comp_type_under(arena, motive, Binders::ONE, width);
        let mut ty = gandr_core_term::instantiate_comp_type(arena, lifted, constructor);
        // Each field's distance from the innermost field binder.
        let mut after = Binders::NONE;
        for found in row.iter().rev() {
            let distance = after;
            after = plus(after, Binders::ONE)?;
            let hypothesis = match *found {
                FieldShape::Plain => continue,
                FieldShape::Direct => {
                    let at = variable(arena, distance);
                    gandr_core_term::instantiate_comp_type(arena, lifted, at)
                },
                // The field and those after it stand between its own scope and
                // the hypothesis's.
                FieldShape::Function(chain) => match closed {
                    Maybe::Present(motive) => {
                        function_hypothesis(arena, chain, motive, (width, after))?
                    },
                    Maybe::Absent(_) => return Err(DerivationRefusal::BinderCeiling),
                },
            };
            let suspended = arena.value_type_thunk(hypothesis);
            ty = arena.comp_type_arrow(suspended, ty);
        }
        // Each field is formed under the fields before it, as its binder in
        // the telescope sees them.
        for &root in fields.iter().rev() {
            ty = arena.comp_type_pi(root, ty);
        }
        method_types.push(ty);
    }
    // The classifier.
    let mut classifier = arena.comp_type_pi(family, motive);
    for &method in method_types.iter().rev() {
        let suspended = arena.value_type_thunk(method);
        classifier = arena.comp_type_arrow(suspended, classifier);
    }
    for &parameter in signature.parameters().iter().rev() {
        classifier = arena.comp_type_pi(parameter, classifier);
    }
    let declared = arena.value_type_thunk(classifier);
    // The body: under the parameters, the methods, `rec` and `x`.
    let scoped_motive =
        gandr_core_term::shift_comp_type_under(arena, motive, Binders::ONE, plus(methods, two)?);
    let mut branches: Vec<ComputationId> = Vec::new();
    let mut preceding = Binders::NONE;
    for (fields, row) in signature.constructors().iter().zip(&shapes) {
        let width = count(fields)?;
        // The handler `m_i`, past the fields, `x`, `rec` and every later
        // method.
        let handler = plus(width, two)
            .and_then(|base| plus(base, methods))
            .and_then(|past| minus(past, Binders::ONE))
            .and_then(|last| minus(last, preceding))?;
        preceding = plus(preceding, Binders::ONE)?;
        let handler = variable(arena, handler);
        let mut applied = arena.computation_force(handler);
        let mut hypotheses = Vec::new();
        let mut remaining = width;
        for found in row {
            remaining = minus(remaining, Binders::ONE)?;
            let distance = remaining;
            let at = variable(arena, distance);
            applied = arena.computation_application(applied, at);
            let hypothesis = match *found {
                FieldShape::Plain => continue,
                FieldShape::Direct => {
                    let recursive = variable(arena, plus(width, Binders::ONE)?);
                    let forced = arena.computation_force(recursive);
                    let call = arena.computation_application(forced, at);
                    arena.value_thunk(call)
                },
                FieldShape::Function(chain) => {
                    let domains = arity(arena, chain)?;
                    let field_under = variable(arena, plus(distance, domains)?);
                    let mut run = arena.computation_force(field_under);
                    for point in (0 .. u32::from(domains)).rev() {
                        let argument = variable(arena, Binders::from(point));
                        run = arena.computation_application(run, argument);
                    }
                    let recursive = variable(arena, plus(plus(width, domains)?, two)?);
                    let forced = arena.computation_force(recursive);
                    let result = variable(arena, Binders::NONE);
                    let call = arena.computation_application(forced, result);
                    let mut body = arena.computation_bind(run, call);
                    for _point in 0 .. u32::from(domains) {
                        body = arena.computation_lambda(body);
                    }
                    arena.value_thunk(body)
                },
            };
            hypotheses.push(hypothesis);
        }
        for hypothesis in hypotheses {
            applied = arena.computation_application(applied, hypothesis);
        }
        let mut branch = applied;
        for _field in 0 .. u32::from(width) {
            branch = arena.computation_lambda(branch);
        }
        branches.push(branch);
    }
    let argument = variable(arena, Binders::NONE);
    let case = arena.computation_data_case(argument, scoped_motive, branches);
    let over_argument = arena.computation_lambda(case);
    let mut body = arena.computation_fixpoint(over_argument, FixpointEvidence::StructuralDescent);
    for _abstraction in 0 .. u32::from(plus(methods, parameters)?) {
        body = arena.computation_lambda(body);
    }
    Ok(Eliminator {
        declared,
        body: arena.value_thunk(body),
    })
}
