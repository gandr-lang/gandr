//! The capability rules: `Cap E` is a context hypothesis carrying the
//! authority `E`.
//!
//! The leaves — the authority as a set of (interface, operation) grant atoms,
//! the region a capability lives for and its grade — are `gandr-core-term`'s
//! `effect::capability`. This module states the five rules the judgement runs
//! over them, and holds the pieces of those rules that read no machine state.
//!
//! # The rules
//!
//! ```text
//!                Γ ⊢ v ⇒ Cap_ρ E    E′ ⊆ E    ρ outlives ρ′
//!   Attenuate   ───────────────────────────────────────────
//!                Γ ⊢ v ⇐ Cap_ρ′ E′
//!
//!                Γ ⊢ c ⇒ Cap_ρ E    op : A → B ∈ I    (I, op) ∈ E    Γ ⊢ v ⇐ A
//!   Exercise    ────────────────────────────────────────────────────────────────
//!                Γ ⊢ c.op v ⇒ F^⟨I⟩ B
//!
//!                Γ, c : Cap_ρ ⟨I⟩ ⊢ M ⇐ F^⟨I | ε⟩ A    ρ ∉ (A, ε)
//!                Γ, x : A ⊢ N ⇐ F^ε A    Γ, p : A_op, k : U(F^ε B_op → F^ε A) ⊢ N_op ⇐ F^ε A
//!   Scope       ──────────────────────────────────────────────────────────────────────────
//!                Γ ⊢ scope c : I in M with { return x ↦ N; op p k ↦ N_op } ⇐ F^ε A
//! ```
//!
//! - **Introduction at the entry.** A declaration with a signature and no body
//!   whose type is a held capability is a hypothesis the host supplies; the
//!   ledger owes it like every hole. Under a grant, [`CheckingContext::grant`],
//!   one claiming authority the grant does not hold is
//!   [`CheckRefusal::CapabilityUngranted`].
//! - **No forgery.** No term former introduces `Cap`. A value checked at a
//!   capability type that is neither a capability hypothesis nor a hole is
//!   [`CheckRefusal::CapabilityForged`], whether it synthesised another type or
//!   is a checking form such as a thunk or a tuple.
//! - **Attenuate** is subsumption, decided by conversion: authority narrows by
//!   inclusion on grant atoms and a region may only shorten. Widening is
//!   [`CheckRefusal::CapabilityAmplified`]; a region ending before the one
//!   expected is [`CheckRefusal::CapabilityEscaped`].
//! - **Exercise** synthesises. An operation the authority does not grant is
//!   [`CheckRefusal::CapabilityOutsideAuthority`]; a value of another type in
//!   capability position is a shape mismatch wanting a capability.
//! - **Scope** checks, as a deep handler does, and introduces its capability in
//!   the region one deeper than every scope around it. Its answer may not
//!   mention that region or a deeper one: [`CheckRefusal::CapabilityEscaped`]
//!   at the scope.
//!
//! # Decisions
//!
//! - **The exercise's row is the interface.** The result row of `c.op v` names
//!   the interface `I` the operation belongs to, whole, rather than the
//!   capability's authority. A row entry is a whole interface, and a handler
//!   discharges one by name; a restricted entry would never equal the
//!   interface's own entry at a handler or a row inclusion. Authority is
//!   checked at the exercise, against the capability's type, and the row only
//!   records which handler answers. Reversal: rows whose entries are grant
//!   atoms, when a handler may discharge part of an interface.
//! - **Regions are depths, and escape is refused twice.** A scope's region is
//!   its nesting depth, so no region is ever named and two sibling scopes share
//!   one depth without meeting. The capability escapes through a value boundary
//!   — returned, passed, stored — only by subsumption to a region it does not
//!   outlive, which conversion refuses; the side condition `ρ ∉ (A, ε)` refuses
//!   an answer type that mentions the region outright. The alternative, a
//!   region variable per scope and region polymorphism, is the second-class
//!   capabilities of Brachthäuser, Schuster and Ostermann (_Effects as
//!   capabilities: effect handlers and lightweight effect polymorphism_, OOPSLA
//!   2020). Reversal: when a function must accept a capability of its caller's
//!   scope, which a held parameter type refuses.
//! - **A scoped capability is exercised where it was introduced.** Every
//!   source-spelled `Cap` is held, so a scoped capability cannot be passed to a
//!   function or stored in a declaration: it is used lexically, within its
//!   scope's subject. That is the region rule, not a separate restriction.
//! - **One handler per interface.** Rows are keyed by interface, so a scope
//!   over `I` answers every operation of `I` its subject requests, including
//!   one exercised through an outer capability of `I`. The authority check
//!   still runs against the outer capability, so this narrows who answers an
//!   operation, never what may be requested. Reversal: rows tagged by region,
//!   so a request names the scope that answers it.
//! - **Durable only.** A consumable capability is refused at formation by
//!   [`CheckRefusal::CapabilityConsumable`]: the linear zone it belongs in
//!   admits no binder, so checking it as durable would let it be exercised
//!   twice. Revocation is the end of the region; nothing revokes a capability
//!   mid-run.
//! - **Nothing persists.** The kernel admits no effectful former, so the bridge
//!   refuses a capability type, an exercise and a scope by name, as it refuses
//!   a request and a handler. Authority is decided here, completely, and an
//!   exercise carries no evidence beyond the operation it names. Reversal: when
//!   the kernel admits effectful computations.

use alloc::collections::BTreeSet;

use anodized::spec;
use gandr_core_term::CompType;
use gandr_core_term::CompTypeId;
use gandr_core_term::ComputationId;
use gandr_core_term::CoreArena;
use gandr_core_term::Value;
use gandr_core_term::ValueId;
use gandr_core_term::ValueType;
use gandr_core_term::ValueTypeId;
use gandr_core_term::effect::EffectRow;
use gandr_core_term::effect::EffectSig;
use gandr_core_term::effect::OperationName;
use gandr_core_term::effect::RowInclusion;
use gandr_core_term::effect::capability::Region;
use gandr_core_term::effect::host::AuthorityError;
use gandr_core_term::effect::host::HostSignatures;
use gandr_kernel_term::ConstantIndex;

use crate::context::CheckingContext;
use crate::formation::FormedValueType;
use crate::refusal::CheckRefusal;
use crate::refusal::CoreNode;
use crate::refusal::ExpectedShape;
use crate::refusal::TermNode;
use crate::refusal::TypeNode;
use crate::view::ValueTypeView;
use crate::view::value_type_view;

/// The authority the host grants a module's held capabilities at the
/// checker's entry.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Grants
{
    /// No grant is named: every held capability is a hypothesis the ledger
    /// owes.
    Unbounded,
    /// Every held capability's authority falls within this one.
    Within(EffectRow),
}

/// The host operations a run grants, by name: what a driver states before
/// any arena holds the types those operations carry.
///
/// # Specification
/// - ensures: every operation a grant names is one the host declares, checked
///   when the grant is formed; [`HostGrant::grants`] mints it into a module's
///   own arena as the [`Grants`] its checking context is bounded by.
///
/// # Adequacy
/// - hypothesis: L3 — a grant of host operations bounds a held capability
///   within it and refuses one beyond it; an undeclared operation is refused
///   when the grant is formed; the unbounded grant bounds nothing.
/// - witness: `capability::tests::a_named_grant_bounds_the_held_capabilities`
#[derive(Clone, Debug, Eq, PartialEq)]
#[repr(transparent)]
pub struct HostGrant(Named);

/// What a [`HostGrant`] names.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Eq, PartialEq)]
enum Named
{
    /// No grant: [`Grants::Unbounded`].
    Unbounded,
    /// Exactly these host operations, each declared by the host.
    Within(BTreeSet<OperationName>),
}

impl HostGrant
{
    /// No grant: every held capability is a hypothesis the ledger owes.
    pub const UNBOUNDED: Self = Self(Named::Unbounded);

    /// The grant of exactly `operations`, each the host's.
    ///
    /// # Specification
    /// - ensures: a grant naming the operations, a repeated one once.
    /// - fails: an operation no host interface offers.
    /// - panics: none.
    ///
    /// # Errors
    /// [`AuthorityError::Undeclared`] for the first operation the host does
    /// not declare; [`AuthorityError::Conflict`] never, for the host's own
    /// table.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`HostGrant`].
    /// - witness: `capability::tests::a_named_grant_bounds_the_held_capabilities`
    #[spec(ensures: |ret| !matches!(ret, Ok(Self(Named::Unbounded))))]
    #[inline]
    pub fn within<'name, Operations>(operations: Operations) -> Result<Self, AuthorityError>
    where
        Operations: IntoIterator<Item = &'name OperationName>,
    {
        let named: BTreeSet<OperationName> = operations.into_iter().cloned().collect();
        let host = HostSignatures::new(&mut CoreArena::new()).map_err(AuthorityError::Conflict)?;
        let _authority = host.authority(&named)?;
        Ok(Self(Named::Within(named)))
    }

    /// The grant as a checking context's bound, minted into `arena`.
    ///
    /// # Specification
    /// - ensures: no bound for the unbounded grant, minting nothing; otherwise
    ///   the authority granting exactly the named operations over the host's
    ///   interfaces minted into `arena`.
    /// - fails: never: the names were checked against this table when the grant
    ///   was formed, and a table that refused them here would grant nothing,
    ///   closing the bound rather than opening it.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`HostGrant`].
    /// - witness: `capability::tests::a_named_grant_bounds_the_held_capabilities`
    #[spec(ensures: |ret| matches!(ret, Grants::Unbounded) == matches!(self.0, Named::Unbounded))]
    #[inline]
    #[must_use]
    pub fn grants(
        &self,
        arena: &mut CoreArena,
    ) -> Grants
    {
        let Named::Within(ref named) = self.0
        else {
            return Grants::Unbounded;
        };
        let authority = match HostSignatures::new(arena) {
            | Ok(host) => match host.authority(named) {
                | Ok(authority) => authority,
                | Err(_refused) => EffectRow::EMPTY,
            },
            | Err(_conflict) => EffectRow::EMPTY,
        };
        Grants::Within(authority)
    }
}

/// Whether a type mentions a region.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Reach
{
    /// No capability in the type lives in the region or a deeper one.
    Clear,
    /// A capability in the type lives in the region or a deeper one.
    Mentions,
}

/// Decide whether the capability `capability`, of type `classifier` whose weak
/// head is `head`, grants the operation `operation` of `signature` that the
/// exercise `at` requests.
///
/// # Specification
/// - requires: `operation` is an operation of `signature`.
/// - ensures: success when `head` is a capability whose authority grants the
///   operation with the interface's own payload and reply types, and when
///   `head` is the unknown type, which grants every operation.
/// - fails: [`CheckRefusal::CapabilityOutsideAuthority`] for a capability that
///   does not grant it; [`CheckRefusal::ShapeMismatch`] at `capability`,
///   wanting [`ExpectedShape::Capability`], for a type of another former;
///   [`CheckRefusal::UnknownOperation`] for an operation outside `signature`.
/// - panics: none.
///
/// # Errors
/// - [`CheckRefusal`] — as above.
///
/// # Adequacy
/// - hypothesis: L3 — a granted operation, one the authority withholds and a
///   string in capability position, each asserted as the exact answer.
/// - witness: `capability::tests::an_operation_is_exercised_only_within_the_authority`
#[spec(ensures: |ret| match ret {
    | Err(CheckRefusal::CapabilityOutsideAuthority { at: named, capability: found }) => named == at && found == classifier,
    | Err(CheckRefusal::ShapeMismatch { at: named, wanted, .. }) => named == TermNode::Value(capability) && wanted == ExpectedShape::Capability,
    | Ok(()) | Err(_) => true,
})]
pub fn authorise(
    arena: &CoreArena,
    at: ComputationId,
    capability: ValueId,
    classifier: ValueTypeId,
    head: ValueTypeId,
    signature: &EffectSig,
    operation: &OperationName,
) -> Result<(), CheckRefusal>
{
    match value_type_view(arena, head)? {
        | ValueTypeView::Capability { authority, .. } => {
            let requested = signature
                .restrict([operation])
                .map_err(|_unknown| CheckRefusal::UnknownOperation { at })?;
            match EffectRow::singleton(requested).grants_within(authority, arena) {
                | RowInclusion::Included => Ok(()),
                | RowInclusion::Excluded => Err(CheckRefusal::CapabilityOutsideAuthority {
                    at,
                    capability: classifier,
                }),
            }
        },
        | ValueTypeView::Unknown => Ok(()),
        | ValueTypeView::PathUniverse(..)
        | ValueTypeView::Path { .. }
        | ValueTypeView::Data { .. }
        | ValueTypeView::Record(_)
        | ValueTypeView::Sum(..)
        | ValueTypeView::List(_)
        | ValueTypeView::Stack { .. }
        | ValueTypeView::Integer
        | ValueTypeView::String
        | ValueTypeView::Unit
        | ValueTypeView::Thunk(_)
        | ValueTypeView::Universe { .. }
        | ValueTypeView::Lift { .. }
        | ValueTypeView::Element { .. }
        | ValueTypeView::Product(..)
        | ValueTypeView::StaticPi { .. }
        | ValueTypeView::Session(_)
        | ValueTypeView::Abstract(_) => Err(CheckRefusal::ShapeMismatch {
            at: TermNode::Value(capability),
            wanted: ExpectedShape::Capability,
            found: TypeNode::Value(classifier),
        }),
    }
}

/// Whether the computation type `root` mentions the region `region` or one
/// nested in it: the scope rule's side condition `ρ ∉ (A, ε)`.
///
/// # Specification
/// - ensures: [`Reach::Mentions`] when a capability type reachable through
///   `root`'s type formers lives in [`Region::Scoped`] at `region`'s depth or
///   deeper; [`Reach::Clear`] otherwise, and always for [`Region::Held`]. A
///   data type's quoted arguments are read; a code is not decoded.
/// - fails: [`CheckRefusal::DanglingNode`] for a reachable type that does not
///   resolve.
/// - panics: none.
///
/// # Errors
/// - [`CheckRefusal`] — as above.
///
/// # Adequacy
/// - hypothesis: L3 — an answer returning the scope's own capability, one whose
///   row carries it, and one returning a held capability, each asserted as
///   refused or checked.
/// - witness: `capability::tests::a_scoped_capability_never_leaves_its_scope`
#[spec(ensures: |ret| region != Region::Held || matches!(ret, Ok(Reach::Clear)))]
pub fn reaches(
    arena: &CoreArena,
    root: CompTypeId,
    region: Region,
) -> Result<Reach, CheckRefusal>
{
    let Region::Scoped(floor) = region
    else {
        return Ok(Reach::Clear);
    };
    let mut pending = alloc::vec![TypeNode::Computation(root)];
    while let Some(node) = pending.pop() {
        let dangling = CheckRefusal::DanglingNode {
            node: CoreNode::Type(node),
        };
        match node {
            | TypeNode::Value(at) => match *arena.value_type(at).ok_or(dangling)? {
                | ValueType::Capability {
                    region: Region::Scoped(depth),
                    ..
                } if depth >= floor => return Ok(Reach::Mentions),
                | ValueType::Capability { ref authority, .. } => {
                    pending.extend(authority.types().map(TypeNode::Value));
                },
                | ValueType::Data { ref arguments, .. } => {
                    pending.extend(arguments.iter().filter_map(|&argument| {
                        match arena.value(argument) {
                            | Some(&Value::Quote(quoted)) => Some(TypeNode::Value(quoted)),
                            | Some(&Value::QuoteComputation(quoted)) => {
                                Some(TypeNode::Computation(quoted))
                            },
                            | Some(_) | None => None,
                        }
                    }));
                },
                | ValueType::Record(ref fields) => {
                    pending.extend(fields.values().copied().map(TypeNode::Value));
                },
                | ValueType::Product(ref components) | ValueType::Sum(ref components) => {
                    pending.extend(components.iter().copied().map(TypeNode::Value));
                },
                | ValueType::List(inner)
                | ValueType::Lift { inner, .. }
                | ValueType::Path { carrier: inner, .. } => pending.push(TypeNode::Value(inner)),
                | ValueType::Thunk(body) => pending.push(TypeNode::Computation(body)),
                | ValueType::StaticPi { domain, codomain } => {
                    pending.extend([TypeNode::Value(domain), TypeNode::Value(codomain)]);
                },
                | ValueType::Stack { input, output } => {
                    pending.extend([TypeNode::Computation(input), TypeNode::Computation(output)]);
                },
                | ValueType::Session(ref session) => {
                    pending.extend(session.payloads().iter().copied().map(TypeNode::Value));
                },
                | ValueType::PathUniverse(..)
                | ValueType::Base(_)
                | ValueType::Universe { .. }
                | ValueType::Element { .. }
                | ValueType::Abstract(_)
                | ValueType::Unknown => {},
            },
            | TypeNode::Computation(at) => match *arena.comp_type(at).ok_or(dangling)? {
                | CompType::Returner {
                    result,
                    ref effects,
                } => {
                    pending.push(TypeNode::Value(result));
                    pending.extend(effects.types().map(TypeNode::Value));
                },
                | CompType::Arrow { domain, codomain } | CompType::Pi { domain, codomain } => {
                    pending.extend([TypeNode::Value(domain), TypeNode::Computation(codomain)]);
                },
                | CompType::With(left, right) => {
                    pending.extend([TypeNode::Computation(left), TypeNode::Computation(right)]);
                },
                | CompType::Element { .. } | CompType::Unknown => {},
            },
        }
    }
    Ok(Reach::Clear)
}

/// Admit the declaration `constant`, owed at `declared`, as a capability the
/// host holds, when it is one: the introduction at the checker's entry.
///
/// # Specification
/// - ensures: success for a type that is no held capability at its weak head,
///   and for every type when the context names no grant.
/// - fails: [`CheckRefusal::CapabilityUngranted`] for a held capability whose
///   authority does not fall within the context's grant; the weak head's
///   refusal when it does not unfold.
/// - panics: none.
///
/// # Errors
/// - [`CheckRefusal`] — as above.
///
/// # Adequacy
/// - hypothesis: L3 — a held capability within the grant, one beyond it, and
///   both with no grant, each asserted as owed or refused.
/// - witness: `capability::tests::a_held_capability_enters_only_within_the_grant`
#[spec(ensures: |ret| match ret {
    | Err(CheckRefusal::CapabilityUngranted { constant: named, declared: ty }) => named == constant && ty == declared.id(),
    | Ok(()) | Err(_) => true,
})]
pub fn held(
    context: &mut CheckingContext<'_>,
    constant: ConstantIndex,
    declared: FormedValueType,
) -> Result<(), CheckRefusal>
{
    if *context.grants() == Grants::Unbounded {
        return Ok(());
    }
    let head = context.whnf_value_type(declared.id())?;
    let Grants::Within(ref grants) = *context.grants()
    else {
        return Ok(());
    };
    if let ValueTypeView::Capability {
        authority,
        region: Region::Held,
        ..
    } = value_type_view(context.arena(), head)?
        && authority.grants_within(grants, context.arena()) == RowInclusion::Excluded
    {
        return Err(CheckRefusal::CapabilityUngranted {
            constant,
            declared: declared.id(),
        });
    }
    Ok(())
}

#[cfg(test)]
mod tests
{
    use alloc::sync::Arc;

    use gandr_core_term::CompType;
    use gandr_core_term::CoreArena;
    use gandr_core_term::ValueTypeId;
    use gandr_core_term::Zone;
    use gandr_core_term::control::EffectClause;
    use gandr_core_term::effect::EffectRow;
    use gandr_core_term::effect::OperationName;
    use gandr_core_term::effect::RowInclusion;
    use gandr_core_term::effect::capability::CapabilityGrade;
    use gandr_core_term::effect::capability::Region;
    use gandr_core_term::effect::capability::RegionDepth;
    use gandr_core_term::effect::host::AuthorityError;
    use gandr_core_term::effect::host::HostSignatures;
    use gandr_core_term::hole::HoleId;
    use gandr_kernel_term::BaseType;
    use gandr_kernel_term::ConstantIndex;
    use gandr_kernel_term::DeBruijnIndex;
    use quenchant_shape::shape::Maybe;

    use super::Grants;
    use super::HostGrant;
    use crate::CheckBudget;
    use crate::CheckRefusal;
    use crate::CheckingContext;
    use crate::CheckingForm;
    use crate::Declaration;
    use crate::ExpectedShape;
    use crate::OriginToken;
    use crate::TermNode;
    use crate::TypeNode;
    use crate::Verdict;
    use crate::body;
    use crate::check_comp;
    use crate::check_module;
    use crate::check_value;
    use crate::fixture::integer_literal;
    use crate::fixture::text_literal;
    use crate::form_comp_type;
    use crate::form_value_type;
    use crate::synthesise_comp;

    /// The host filesystem restricted to `names`, as an authority.
    ///
    /// # Specification
    /// trivial.
    fn files(
        host: &HostSignatures,
        names: &[OperationName],
    ) -> EffectRow
    {
        EffectRow::authority(&[host.fs.restrict(names).unwrap()]).unwrap()
    }

    /// Check the innermost variable, bound at `hypothesis`, against
    /// `expected`.
    ///
    /// # Specification
    /// trivial.
    fn passed(
        arena: &mut CoreArena,
        hypothesis: ValueTypeId,
        expected: ValueTypeId,
    ) -> Result<(), CheckRefusal>
    {
        let variable = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
        let mut context = CheckingContext::new(arena, CheckBudget::DEFAULT);
        context.binders().open(Zone::Intuitionistic, hypothesis);
        let expected = form_value_type(&mut context, expected)?;
        check_value(&mut context, variable, expected).map(|_checked| ())
    }

    #[test]
    fn attenuation_narrows_and_never_widens()
    {
        let mut arena = CoreArena::new();
        let host = HostSignatures::new(&mut arena).unwrap();
        let durable = CapabilityGrade::Durable;
        let both = arena.value_type_capability(
            files(&host, &["read".into(), "write".into()]),
            durable,
            Region::Held,
        );
        let reads =
            arena.value_type_capability(files(&host, &["read".into()]), durable, Region::Held);
        let writes =
            arena.value_type_capability(files(&host, &["write".into()]), durable, Region::Held);
        let outer_depth = Region::Scoped(RegionDepth::from(1_u32));
        let scoped_reads =
            arena.value_type_capability(files(&host, &["read".into()]), durable, outer_depth);
        let inner_reads = arena.value_type_capability(
            files(&host, &["read".into()]),
            durable,
            Region::Scoped(RegionDepth::from(2_u32)),
        );
        assert_eq!(
            passed(&mut arena, both, reads),
            Ok(()),
            "{{read, write}} narrows to {{read}}"
        );
        assert_eq!(
            passed(&mut arena, both, both),
            Ok(()),
            "a capability stands at its own type"
        );
        assert!(
            matches!(
                passed(&mut arena, reads, both),
                Err(CheckRefusal::CapabilityAmplified(_))
            ),
            "{{read}} never widens to {{read, write}}"
        );
        assert!(
            matches!(
                passed(&mut arena, reads, writes),
                Err(CheckRefusal::CapabilityAmplified(_))
            ),
            "{{read}} never becomes {{write}}"
        );
        assert_eq!(
            passed(&mut arena, reads, scoped_reads),
            Ok(()),
            "a held capability stands where a scoped one is expected"
        );
        assert_eq!(
            passed(&mut arena, scoped_reads, inner_reads),
            Ok(()),
            "an outer scope's capability stands in an inner scope"
        );
        for (shorter, longer) in [(scoped_reads, reads), (inner_reads, scoped_reads)] {
            assert!(
                matches!(
                    passed(&mut arena, shorter, longer),
                    Err(CheckRefusal::CapabilityEscaped {
                        at: TermNode::Value(_),
                        found: TypeNode::Value(_)
                    })
                ),
                "a capability never outlives its region"
            );
        }
    }

    #[test]
    fn a_consumable_capability_is_refused_by_name()
    {
        let mut arena = CoreArena::new();
        let host = HostSignatures::new(&mut arena).unwrap();
        let consumable = arena.value_type_capability(
            files(&host, &["write".into()]),
            CapabilityGrade::Consumable,
            Region::Held,
        );
        let returns = arena.comp_type_returner(consumable);
        let suspended = arena.value_type_thunk(returns);
        let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        for ty in [consumable, suspended] {
            assert_eq!(
                form_value_type(&mut context, ty),
                Err(CheckRefusal::CapabilityConsumable(consumable)),
                "the linear zone admits no binder, so a consumable capability never forms"
            );
        }
    }

    #[test]
    fn no_term_forges_a_capability()
    {
        let mut arena = CoreArena::new();
        let host = HostSignatures::new(&mut arena).unwrap();
        let cap = arena.value_type_capability(
            files(&host, &["read".into()]),
            CapabilityGrade::Durable,
            Region::Held,
        );
        let integer = arena.value_type_base(BaseType::Integer);
        let string = arena.value_type_base(BaseType::String);
        let zero = arena.value_literal(integer_literal());
        let returned = arena.computation_return(zero);
        let thunk = arena.value_thunk(returned);
        let pair = arena.value_tuple(&[zero, zero]);
        let hole = arena.value_hole(HoleId::from(0_u32));
        let variable = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
        let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        context.binders().open(Zone::Intuitionistic, string);
        let formed = form_value_type(&mut context, cap).unwrap();
        for term in [zero, thunk, pair, variable] {
            assert_eq!(
                check_value(&mut context, term, formed).map(|_checked| ()),
                Err(CheckRefusal::CapabilityForged {
                    at: term,
                    expected: cap
                }),
                "only a capability hypothesis stands at a capability type"
            );
        }
        assert_eq!(
            check_value(&mut context, hole, formed).map(|_checked| ()),
            Ok(()),
            "a hole owes the capability rather than forging it"
        );
        let integer = form_value_type(&mut context, integer).unwrap();
        assert!(
            matches!(
                check_value(&mut context, thunk, integer),
                Err(CheckRefusal::ShapeMismatch {
                    wanted: ExpectedShape::Thunk,
                    ..
                })
            ),
            "a thunk at another type keeps its shape mismatch"
        );
    }

    #[test]
    fn an_operation_is_exercised_only_within_the_authority()
    {
        let mut arena = CoreArena::new();
        let host = HostSignatures::new(&mut arena).unwrap();
        let cap = arena.value_type_capability(
            files(&host, &["read".into()]),
            CapabilityGrade::Durable,
            Region::Held,
        );
        let string = arena.value_type_base(BaseType::String);
        let path = arena.value_literal(text_literal());
        let unit = arena.value_unit();
        let contents = arena.value_tuple(&[path, path]);
        let variable = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
        let read = arena.computation_exercise(variable, host.fs.clone(), "read".into(), path);
        let write = arena.computation_exercise(variable, host.fs.clone(), "write".into(), contents);
        let missing = arena.computation_exercise(variable, host.fs.clone(), "missing".into(), path);
        let wrong = arena.computation_exercise(variable, host.fs.clone(), "read".into(), unit);
        let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        context.binders().open(Zone::Intuitionistic, cap);
        let inferred = synthesise_comp(&mut context, read).unwrap().produced().id();
        let Maybe::Present(&gandr_core_term::effect::EffectOp { reply, .. }) =
            host.fs.operation(&"read".into())
        else {
            panic!("the filesystem reads");
        };
        assert_eq!(
            context.arena().comp_type(inferred),
            Some(&CompType::Returner {
                result: reply,
                effects: EffectRow::singleton(host.fs)
            }),
            "a granted read returns its reply, its row the whole interface"
        );
        assert!(
            matches!(
                synthesise_comp(&mut context, write),
                Err(CheckRefusal::CapabilityOutsideAuthority { at, .. }) if at == write
            ),
            "a read capability grants no write"
        );
        assert_eq!(
            synthesise_comp(&mut context, missing).map(|_synthesised| ()),
            Err(CheckRefusal::UnknownOperation { at: missing })
        );
        assert!(
            matches!(
                synthesise_comp(&mut context, wrong),
                Err(CheckRefusal::TypeMismatch(_))
            ),
            "the payload checks against the operation's payload type"
        );
        let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        context.binders().open(Zone::Intuitionistic, string);
        assert!(
            matches!(
                synthesise_comp(&mut context, read),
                Err(CheckRefusal::ShapeMismatch {
                    at: TermNode::Value(at),
                    wanted: ExpectedShape::Capability,
                    ..
                }) if at == variable
            ),
            "a string is exercised as nothing"
        );
    }

    /// One clause per operation of the process interface, each answering
    /// `body`.
    ///
    /// # Specification
    /// trivial.
    fn exits(body: gandr_core_term::ComputationId) -> Arc<[EffectClause]>
    {
        [EffectClause {
            operation: "exit".into(),
            body,
        }]
        .into()
    }

    #[test]
    fn a_scope_handles_the_capability_it_introduces()
    {
        let mut arena = CoreArena::new();
        let host = HostSignatures::new(&mut arena).unwrap();
        let unit_type = arena.value_type_unit();
        let answer = arena.comp_type_returner(unit_type);
        let zero = arena.value_literal(integer_literal());
        let unit = arena.value_unit();
        let bound = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
        let exit = arena.computation_exercise(bound, host.proc.clone(), "exit".into(), zero);
        let returned = arena.computation_return(unit);
        let passes = arena.computation_return(bound);
        let scope = arena.computation_scope(host.proc.clone(), exit, passes, exits(returned));
        let integer_return = arena.computation_return(zero);
        let wrong_return =
            arena.computation_scope(host.proc.clone(), exit, integer_return, exits(returned));
        let uncovered = arena.computation_scope(host.proc, exit, passes, [].into());
        let other_process =
            gandr_core_term::effect::EffectSig::new(gandr_core_term::effect::host::PROC.into(), [
                gandr_core_term::effect::EffectOp {
                    name: "quit".into(),
                    payload: unit_type,
                    reply: unit_type,
                },
            ])
            .unwrap();
        let conflicting =
            arena.comp_type_returner_with_effects(unit_type, EffectRow::singleton(other_process));
        let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        let answer = form_comp_type(&mut context, answer).unwrap();
        let conflicting = form_comp_type(&mut context, conflicting).unwrap();
        check_comp(&mut context, scope, answer)
            .expect("the subject exercises the capability its scope introduces");
        assert_eq!(
            context.binders().depth(Zone::Intuitionistic),
            gandr_core_term::BinderDepth::from(0_usize),
            "the scope closes every binder it opened"
        );
        assert!(
            matches!(
                check_comp(&mut context, wrong_return, answer),
                Err(CheckRefusal::TypeMismatch(_))
            ),
            "the return clause delivers the answer"
        );
        assert_eq!(
            check_comp(&mut context, uncovered, answer).map(|_checked| ()),
            Err(CheckRefusal::HandlerCoverage { at: uncovered })
        );
        assert_eq!(
            synthesise_comp(&mut context, scope).map(|_synthesised| ()),
            Err(CheckRefusal::NotSynthesisable {
                form: CheckingForm::Scope(scope)
            })
        );
        assert!(
            matches!(
                check_comp(&mut context, scope, conflicting),
                Err(CheckRefusal::EffectSignatureConflict { at, first, .. })
                    if at == scope && first == conflicting.id()
            ),
            "an answer row giving the interface's name other operations conflicts"
        );
    }

    #[test]
    fn a_scoped_capability_never_leaves_its_scope()
    {
        let mut arena = CoreArena::new();
        let host = HostSignatures::new(&mut arena).unwrap();
        let process = EffectRow::singleton(host.proc.clone());
        let durable = CapabilityGrade::Durable;
        let unit_type = arena.value_type_unit();
        let held = arena.value_type_capability(process.clone(), durable, Region::Held);
        let outer = arena.value_type_capability(
            process.clone(),
            durable,
            Region::Scoped(RegionDepth::from(1_u32)),
        );
        let returns_held = arena.comp_type_returner(held);
        let returns_outer = arena.comp_type_returner(outer);
        let pure = arena.comp_type_returner(unit_type);
        let requests = arena.comp_type_returner_with_effects(unit_type, process);
        let takes_outer = arena.comp_type_arrow(outer, requests);
        let consumer = arena.value_type_thunk(takes_outer);
        let unit = arena.value_unit();
        let returned = arena.computation_return(unit);
        let [zeroth, first, second] = [0_u32, 1, 2]
            .map(|index| arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(index)));
        let passes = arena.computation_return(zeroth);
        let leaks = arena.computation_scope(host.proc.clone(), passes, passes, exits(passes));
        let mentions =
            arena.computation_scope(host.proc.clone(), returned, returned, exits(returned));
        let consume = |arena: &mut CoreArena, argument| {
            let head = arena.computation_force(second);
            let applied = arena.computation_application(head, argument);
            let inner =
                arena.computation_scope(host.proc.clone(), applied, passes, exits(returned));
            arena.computation_scope(host.proc.clone(), inner, returned, exits(returned))
        };
        let outer_passed = consume(&mut arena, first);
        let inner_passed = consume(&mut arena, zeroth);
        let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        let returns_held = form_comp_type(&mut context, returns_held).unwrap();
        assert!(
            matches!(
                check_comp(&mut context, leaks, returns_held),
                Err(CheckRefusal::CapabilityEscaped {
                    at: TermNode::Value(at),
                    ..
                }) if at == zeroth
            ),
            "the scope's capability never passes where a held one is promised"
        );
        let returns_outer = form_comp_type(&mut context, returns_outer).unwrap();
        assert_eq!(
            check_comp(&mut context, mentions, returns_outer).map(|_checked| ()),
            Err(CheckRefusal::CapabilityEscaped {
                at: TermNode::Computation(mentions),
                found: TypeNode::Computation(returns_outer.id())
            }),
            "an answer naming the scope's region is refused at the scope"
        );
        context.binders().open(Zone::Intuitionistic, consumer);
        let pure = form_comp_type(&mut context, pure).unwrap();
        check_comp(&mut context, outer_passed, pure)
            .expect("the outer scope's capability stands in the inner scope");
        assert!(
            matches!(
                check_comp(&mut context, inner_passed, pure),
                Err(CheckRefusal::CapabilityEscaped {
                    at: TermNode::Value(at),
                    ..
                }) if at == zeroth
            ),
            "the inner scope's capability lives one region deeper"
        );
    }

    #[test]
    fn a_held_capability_enters_only_within_the_grant()
    {
        let mut arena = CoreArena::new();
        let host = HostSignatures::new(&mut arena).unwrap();
        let durable = CapabilityGrade::Durable;
        let both = arena.value_type_capability(
            files(&host, &["read".into(), "write".into()]),
            durable,
            Region::Held,
        );
        let reads =
            arena.value_type_capability(files(&host, &["read".into()]), durable, Region::Held);
        let integer = arena.value_type_base(BaseType::Integer);
        let module: alloc::vec::Vec<Declaration> = [both, reads, integer]
            .into_iter()
            .enumerate()
            .map(|(position, declared)| {
                Declaration::new(
                    ConstantIndex::from(position),
                    Maybe::Present(declared),
                    Maybe::Absent(body::Absent::Hole),
                    OriginToken::from(position),
                )
            })
            .collect();
        let verdicts = |arena: &mut CoreArena, grants: Grants| {
            let mut context = CheckingContext::new(arena, CheckBudget::DEFAULT);
            context.grant(grants);
            let report = check_module(&mut context, &module);
            report
                .judged()
                .iter()
                .map(|judged| matches!(judged.verdict(), Verdict::Owed(_)))
                .collect::<alloc::vec::Vec<_>>()
        };
        assert_eq!(
            verdicts(&mut arena, Grants::Unbounded),
            [true, true, true],
            "with no grant every held capability is owed"
        );
        let all = files(&host, &["read".into(), "write".into()]);
        assert_eq!(verdicts(&mut arena, Grants::Within(all)), [
            true, true, true
        ]);
        let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        context.grant(Grants::Within(files(&host, &["read".into()])));
        let report = check_module(&mut context, &module);
        assert_eq!(
            report.judged()[0].verdict(),
            Verdict::Refused(CheckRefusal::CapabilityUngranted {
                constant: ConstantIndex::from(0_usize),
                declared: both
            }),
            "a held capability beyond the grant is refused by name"
        );
        assert!(
            report.judged()[1 ..]
                .iter()
                .all(|judged| matches!(judged.verdict(), Verdict::Owed(_))),
            "a capability within the grant, and a hole of another type, are owed"
        );
    }

    #[test]
    fn a_named_grant_bounds_the_held_capabilities()
    {
        let [read, write, send] = ["read", "write", "send"].map(OperationName::from);
        assert_eq!(
            HostGrant::within([&read, &send]),
            Err(AuthorityError::Undeclared(send)),
            "an operation the host does not declare is refused when the grant is formed"
        );
        let reads = HostGrant::within([&read, &read]).expect("the host declares read");
        let mut arena = CoreArena::new();
        assert_eq!(HostGrant::UNBOUNDED.grants(&mut arena), Grants::Unbounded);
        let Grants::Within(granted) = reads.grants(&mut arena)
        else {
            panic!("a named grant bounds");
        };
        let host = HostSignatures::new(&mut arena).unwrap();
        let both = files(&host, &[read.clone(), write.clone()]);
        assert_eq!(
            files(&host, core::slice::from_ref(&read)).grants_within(&granted, &arena),
            RowInclusion::Included,
            "the grant holds read"
        );
        assert_eq!(
            both.grants_within(&granted, &arena),
            RowInclusion::Excluded,
            "and not write"
        );
        let written = HostGrant::within([&write, &read]).expect("the host declares both");
        let Grants::Within(granted) = written.grants(&mut arena)
        else {
            panic!("a named grant bounds");
        };
        assert_eq!(both.grants_within(&granted, &arena), RowInclusion::Included);
    }
}
