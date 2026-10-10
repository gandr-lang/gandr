//! Generated closed, well-typed core terms.
//!
//! A term is generated against a type, in a context of typed variables, by an
//! explicit work stack driven from a seed: every computation former — return,
//! lambda, force, application, bind and case — and every value former but the
//! lift is reachable, variables are drawn from the context at their own type,
//! and the fuel bounds the depth. Types come from a fixed menu, interned so
//! two equal types share an id. Shrinking reduces the fuel, so a failure
//! shrinks toward a smaller term over the same draws.
//!
//! Well-typed closed terms of this fragment have no recursion and so always
//! terminate, which is what lets a differential compare two evaluators on
//! them without a divergence verdict.

use alloc::vec::Vec;

use anodized::spec;
use gandr_core_term::ComputationId;
use gandr_core_term::CoreArena;
use gandr_core_term::ValueId;
use gandr_core_term::Zone;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::IntegerLiteral;
use gandr_kernel_term::Literal;
use gandr_kernel_term::Magnitude;
use gandr_kernel_term::Side;
use gandr_kernel_term::Sign;
use proptest::prelude::*;

/// An integer's spelling in a hand-built case.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
pub struct Integer(pub i32);

/// The integer literal value `n` in `core`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: a fresh integer literal with exactly the signed input's value,
///   including the asymmetric negative endpoint.
/// - provides: numeric fixtures without signed-magnitude overflow.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — zero, both signs and both i32 endpoints are compared to
///   explicit sign and digit expectations. These distinguish signed
///   absolute-value overflow, sign loss and incorrect zero handling.
/// - witness: `tests::generate::integer_payloads_cover_both_signed_extremes`
#[spec(ensures: |ret| match core.value(ret) {
    | Some(&gandr_core_term::Value::Literal(Literal::Integer(ref integer))) => {
        let digits: &str = integer.magnitude().as_ref();
        digits.parse::<u32>().ok() == Some(value.0.unsigned_abs())
            && (integer.sign() == Sign::Negative) == (value.0 < 0_i32)
    },
    | _ => false,
})]
pub fn integer(
    core: &mut CoreArena,
    value: Integer,
) -> ValueId
{
    let sign = if value.0 < 0_i32 {
        Sign::Negative
    }
    else {
        Sign::NonNegative
    };
    let digits = Magnitude::from_decimal_text(alloc::format!("{}", value.0.unsigned_abs()))
        .expect("decimal digits");
    core.value_literal(Literal::Integer(IntegerLiteral::new(sign, digits)))
}

/// A generated term and the arena it lives in.
#[derive(Clone, Debug)]
pub struct Generated
{
    /// The arena holding the term.
    pub core: CoreArena,
    /// The term's root.
    pub root: GeneratedRoot,
}

/// The root of a generated term.
#[derive(Clone, Copy, Debug)]
pub enum GeneratedRoot
{
    /// A closed computation.
    Computation(ComputationId),
    /// A closed value.
    Value(ValueId),
}

/// The seed a generation draws from.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
struct Seed(u64);

/// How many more formers deep a generation may go.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Fuel(u32);

impl Fuel
{
    /// The fuel a child gets.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: one less unit of fuel, saturating at zero.
    /// - provides: a non-wrapping structural generation budget.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — zero, one and the counter maximum distinguish
    ///   underflow, failure to consume fuel and a wrong decrement. Typed
    ///   zero-fuel generation exercises the introduction-only frontier.
    /// - witness: `tests::generate::fuel_and_draws_respect_empty_and_full_bounds`
    /// - witness: `tests::generate::typed_builders_preserve_product_sum_and_function_roles`
    #[spec(ensures: |ret| ret.0 == self.0.saturating_sub(1))]
    const fn child(self) -> Self
    {
        Self(self.0.saturating_sub(1))
    }
}

/// How many options a draw chooses among.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
struct Options(usize);

/// The option a draw chose.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Choice(usize);

/// A `SplitMix64` stream.
#[derive(Clone, Copy, Debug)]
#[repr(transparent)]
struct Draws
{
    /// The stream's state.
    state: u64,
}

impl Draws
{
    /// Draw one option out of `options`, or the first when there is none.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a choice below options when nonzero, or zero otherwise.
    /// - provides: bounded choices without division by zero.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — empty, singleton, small and maximum option counts
    ///   over zero and maximum seeds distinguish division by zero, invalid
    ///   remainders and overflow. No distribution, internal stream state or
    ///   particular seed-to-choice table is promised.
    /// - witness: `tests::generate::fuel_and_draws_respect_empty_and_full_bounds`
    #[spec(ensures: |ret| if options.0 == 0 { ret.0 == 0 } else { ret.0 < options.0 })]
    fn pick(
        &mut self,
        options: Options,
    ) -> Choice
    {
        self.state = self.state.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut mixed = self.state;
        mixed = (mixed ^ (mixed >> 30_u32)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        mixed = (mixed ^ (mixed >> 27_u32)).wrapping_mul(0x94D0_49BB_1331_11EB);
        mixed ^= mixed >> 31_u32;
        let bound = u64::try_from(options.0.max(1)).unwrap_or(u64::MAX);
        Choice(usize::try_from(mixed.checked_rem(bound).unwrap_or(0)).unwrap_or(0))
    }
}

/// The id of an interned type.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct TyId(usize);

/// A value or computation type.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Ty
{
    /// `1`.
    Unit,
    /// The integer atom.
    Integer,
    /// `A × B`.
    Product(TyId, TyId),
    /// `A + B`.
    Sum(TyId, TyId),
    /// `U C`.
    Thunk(TyId),
    /// `F A`.
    Returner(TyId),
    /// `A → C`.
    Arrow(TyId, TyId),
}

/// The address of one context binding.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
struct BindingId(usize);

/// A context: the innermost binding, or none.
#[derive(Clone, Copy, Debug)]
enum Scope
{
    /// Nothing is bound.
    Empty,
    /// The innermost binding.
    At(BindingId),
}

/// One pending unit of generation.
#[derive(Clone, Copy, Debug)]
enum Task
{
    /// Generate a value of a type in a scope.
    Value(TyId, Scope, Fuel),
    /// Generate a computation of a type in a scope.
    Computation(TyId, Scope, Fuel),
    /// Pop two values and build their pair.
    Pair,
    /// Pop a value and build its injection.
    Injection(Side),
    /// Pop a computation and build its thunk.
    Thunk,
    /// Pop a value and build its return.
    Return,
    /// Pop a value and build its force.
    Force,
    /// Pop an argument value and a head computation and build the
    /// application.
    Application,
    /// Pop a computation and build its lambda.
    Lambda,
    /// Pop a body and a head computation and build the bind.
    Bind,
    /// Pop two branch computations and a scrutinee value and build the case.
    Case,
}

/// The state of one generation.
struct Generator
{
    /// The draws.
    draws: Draws,
    /// The interned types.
    types: Vec<Ty>,
    /// The context bindings: a type and the binding it extends.
    bindings: Vec<(TyId, Scope)>,
    /// The arena built into.
    core: CoreArena,
    /// The pending work.
    tasks: Vec<Task>,
    /// Built values awaiting their parent.
    values: Vec<ValueId>,
    /// Built computations awaiting their parent.
    computations: Vec<ComputationId>,
}

impl Generator
{
    /// A generator over a seed.
    ///
    /// # Specification
    /// trivial.
    fn new(seed: Seed) -> Self
    {
        Self {
            draws: Draws { state: seed.0 },
            types: Vec::new(),
            bindings: Vec::new(),
            core: CoreArena::new(),
            tasks: Vec::new(),
            values: Vec::new(),
            computations: Vec::new(),
        }
    }

    /// Intern a type.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the first equal interned type's id, reusing an existing entry
    ///   or appending this type without changing prior ids.
    /// - provides: stable type identity for scope lookup.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — repeated and distinct types retain their identities
    ///   while differently typed and shadowed scope bindings select only their
    ///   own variables. This distinguishes duplicate interning, merged types
    ///   and changed ids.
    /// - witness: `tests::generate::interning_and_shadowed_scopes_preserve_distinct_types`
    #[spec(
        captures: [found = self.types.iter().position(|&known| known == ty), count = self.types.len()],
        ensures: |ret| self.types.get(ret.0) == Some(&ty) && ret.0 == found.unwrap_or(count)
            && Some(self.types.len()) == count.checked_add(usize::from(found.is_none())),
    )]
    fn intern(
        &mut self,
        ty: Ty,
    ) -> TyId
    {
        if let Some(found) = self.types.iter().position(|&known| known == ty) {
            return TyId(found);
        }
        self.types.push(ty);
        TyId(self.types.len().saturating_sub(1))
    }

    /// The type an id names.
    ///
    /// # Specification
    /// - requires: id names an interned type.
    /// - ensures: that exact type, without changing the generator.
    /// - provides: checked type-table access during generation.
    /// - panics: on an id this generator did not intern.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — two distinct interned types and an absent id
    ///   distinguish wrong-slot lookup and failure to reject a missing type;
    ///   the generated machine suite exercises the valid lookup domain.
    /// - witness: `tests::generate::interning_and_shadowed_scopes_preserve_distinct_types`
    /// - witness: `tests::differential::l_machine_is_total_and_deterministic`
    #[spec(requires: self.types.get(id.0).is_some(), ensures: |ret| self.types.get(id.0) == Some(&ret))]
    fn ty(
        &self,
        id: TyId,
    ) -> Ty
    {
        *self.types.get(id.0).expect("an interned type")
    }

    /// A value type from the menu.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: an interned value-sort type with recorded immediate children.
    /// - provides: a supported value type for term generation.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — generated computations focus as closed, well-formed
    ///   commands and halt; product and sum fixtures independently distinguish
    ///   value fields from computation fields. L2 compares the generated
    ///   machine readings with normalization by evaluation. Evidence is bounded
    ///   to the strategy domain, not a general typechecker proof.
    /// - witness: `tests::generate::typed_builders_preserve_product_sum_and_function_roles`
    /// - witness: `tests::focus_properties::focusing_is_total_on_generated_computations`
    /// - witness: `tests::differential::l_machine_is_total_and_deterministic`
    /// - witness: `tests::differential::the_l_machine_agrees_with_normalisation_by_evaluation`
    #[spec(ensures: |ret| match self.types.get(ret.0) {
        | Some(&Ty::Unit | &Ty::Integer) => true,
        | Some(&Ty::Product(first, second) | &Ty::Sum(first, second)) => self.types.get(first.0).is_some() && self.types.get(second.0).is_some(),
        | Some(&Ty::Thunk(body)) => self.types.get(body.0).is_some_and(|known| matches!(*known, Ty::Returner(_) | Ty::Arrow(_, _))),
        | _ => false,
    })]
    fn value_type(&mut self) -> TyId
    {
        let unit = self.intern(Ty::Unit);
        let integer = self.intern(Ty::Integer);
        match self.draws.pick(Options(6)) {
            | Choice(0) => unit,
            | Choice(1) => integer,
            | Choice(2) => self.intern(Ty::Product(integer, unit)),
            | Choice(3) => self.intern(Ty::Sum(unit, integer)),
            | Choice(4) => {
                let returner = self.intern(Ty::Returner(integer));
                self.intern(Ty::Thunk(returner))
            },
            | _ => {
                let returner = self.intern(Ty::Returner(integer));
                let arrow = self.intern(Ty::Arrow(integer, returner));
                self.intern(Ty::Thunk(arrow))
            },
        }
    }

    /// A computation type from the menu.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: an interned returner or arrow with recorded immediate
    ///   children.
    /// - provides: a supported computation type for term generation.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — generated roots focus as closed commands and halt;
    ///   zero-fuel function fixtures distinguish domain and result roles. L2
    ///   compares generated readings against the independent normalizer. This
    ///   covers the bounded strategy domain, not arbitrary type graphs or a
    ///   proof of the generator distribution.
    /// - witness: `tests::generate::typed_builders_preserve_product_sum_and_function_roles`
    /// - witness: `tests::focus_properties::focusing_is_total_on_generated_computations`
    /// - witness: `tests::differential::l_machine_is_total_and_deterministic`
    /// - witness: `tests::differential::the_l_machine_agrees_with_normalisation_by_evaluation`
    #[spec(ensures: |ret| match self.types.get(ret.0) {
        | Some(&Ty::Returner(value)) => self.types.get(value.0).is_some(),
        | Some(&Ty::Arrow(domain, codomain)) => self.types.get(domain.0).is_some()
            && self.types.get(codomain.0).is_some_and(|known| matches!(*known, Ty::Returner(_) | Ty::Arrow(_, _))),
        | _ => false,
    })]
    fn computation_type(&mut self) -> TyId
    {
        let value = self.value_type();
        match self.draws.pick(Options(3)) {
            | Choice(0) => self.intern(Ty::Returner(value)),
            | Choice(1) => {
                let domain = self.value_type();
                let returner = self.intern(Ty::Returner(value));
                self.intern(Ty::Arrow(domain, returner))
            },
            | _ => {
                let returner = self.intern(Ty::Returner(value));
                let inner = self.intern(Ty::Arrow(value, returner));
                let domain = self.value_type();
                self.intern(Ty::Arrow(domain, inner))
            },
        }
    }

    /// The scope extended by one binding.
    ///
    /// # Specification
    /// - requires: ty is recorded; scope is empty or already recorded.
    /// - ensures: a fresh binding of ty whose outer link is scope, without
    ///   changing the meaning of an earlier binding.
    /// - provides: persistent scope extension for a binder.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — interleaved types, shadowing and a retained outer
    ///   scope have exact de Bruijn selections. This distinguishes lost outer
    ///   links, overwritten bindings and mistaken binder types.
    /// - witness: `tests::generate::interning_and_shadowed_scopes_preserve_distinct_types`
    /// - witness: `tests::generate::typed_builders_preserve_product_sum_and_function_roles`
    #[spec(
        requires: self.types.get(ty.0).is_some() && match scope { Scope::Empty => true, Scope::At(BindingId(at)) => self.bindings.get(at).is_some() },
        captures: [count = self.bindings.len()],
        ensures: |ret| match ret {
            | Scope::Empty => false,
            | Scope::At(BindingId(at)) => at == count && Some(self.bindings.len()) == count.checked_add(1)
                && self.bindings.get(at).is_some_and(|&(bound, outer)| bound == ty && match (scope, outer) {
                    | (Scope::Empty, Scope::Empty) => true,
                    | (Scope::At(BindingId(first)), Scope::At(BindingId(second))) => first == second,
                    | _ => false,
                }),
        },
    )]
    fn extend(
        &mut self,
        scope: Scope,
        ty: TyId,
    ) -> Scope
    {
        self.bindings.push((ty, scope));
        Scope::At(BindingId(self.bindings.len().saturating_sub(1)))
    }

    /// The de Bruijn indices of every binding of `ty` in `scope`.
    ///
    /// # Specification
    /// - requires: bindings point only to earlier bindings, and scope is empty
    ///   or recorded in this table.
    /// - ensures: all matching bindings' de Bruijn indices, from innermost
    ///   outward, with distance saturating at the index ceiling.
    /// - provides: scope selection that preserves gaps and shadowed bindings.
    /// - panics: on an unrecorded binding.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — empty scopes, interleaved types, shadowing, absent
    ///   types and a retained outer scope have exact index lists. These
    ///   distinguish skipped distance increments, a lost outer link and
    ///   stopping after the first match. Saturation at an unallocatable scope
    ///   depth is outside this finite witness.
    /// - witness: `tests::generate::interning_and_shadowed_scopes_preserve_distinct_types`
    #[spec(
        requires: (match scope { Scope::Empty => true, Scope::At(BindingId(at)) => self.bindings.get(at).is_some() })
            && self.bindings.iter().enumerate().all(|(at, &(_, outer))| match outer { Scope::Empty => true, Scope::At(BindingId(parent)) => parent < at }),
        ensures: |ref ret| ret.windows(2).all(|pair| match pair {
            | &[first, second] => first < second || (u32::from(first) == u32::MAX && first == second),
            | _ => false,
        }) && match scope {
            | Scope::Empty => ret.is_empty(),
            | Scope::At(BindingId(at)) => self.bindings.get(at).is_some_and(|&(bound, _)|
                (ret.first().copied() == Some(DeBruijnIndex::from(0_u32))) == (bound == ty)),
        },
    )]
    fn variables_of(
        &self,
        scope: Scope,
        ty: TyId,
    ) -> Vec<DeBruijnIndex>
    {
        let mut found = Vec::new();
        let mut cursor = scope;
        let mut distance = 0_u32;
        while let Scope::At(BindingId(at)) = cursor {
            let &(bound, outer) = self.bindings.get(at).expect("a recorded binding");
            if bound == ty {
                found.push(DeBruijnIndex::from(distance));
            }
            distance = distance.saturating_add(1);
            cursor = outer;
        }
        found
    }

    /// Generate one value node, or schedule its children.
    ///
    /// # Specification
    /// - requires: ty is a well-founded value-sort type and scope is a valid
    ///   backward-linked binding chain.
    /// - ensures: one immediate value or pending work for its children and
    ///   constructor, leaving the computation-result stack unchanged.
    /// - provides: typed value generation over explicit work and result stacks.
    /// - panics: on a violated type or scope invariant.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — zero-fuel products, sums and function domains
    ///   preserve their distinct field roles; generated roots focus as closed
    ///   commands and halt. L2 compares their machine readings with
    ///   normalization by evaluation. The observations cover bounded generated
    ///   terms, not every seed and depth or general type soundness.
    /// - witness: `tests::generate::typed_builders_preserve_product_sum_and_function_roles`
    /// - witness: `tests::focus_properties::focusing_is_total_on_generated_computations`
    /// - witness: `tests::differential::l_machine_is_total_and_deterministic`
    /// - witness: `tests::differential::the_l_machine_agrees_with_normalisation_by_evaluation`
    #[spec(
        requires: self.types.get(ty.0).is_some_and(|known| matches!(*known, Ty::Unit | Ty::Integer | Ty::Product(_, _) | Ty::Sum(_, _) | Ty::Thunk(_)))
            && match scope { Scope::Empty => true, Scope::At(BindingId(at)) => self.bindings.get(at).is_some() },
        captures: [values = self.values.len(), computations = self.computations.len(), pending = self.tasks.len()],
        ensures: |_| self.computations.len() == computations
            && ((Some(self.values.len()) == values.checked_add(1) && self.tasks.len() == pending)
                || (self.values.len() == values && self.tasks.len() > pending))
            && self.values.get(values..).is_some_and(|added| added.iter().all(|&id| self.core.value(id).is_some()))
            && self.tasks.get(pending).is_none_or(|task| matches!(*task, Task::Pair | Task::Injection(_) | Task::Thunk)),
    )]
    fn value(
        &mut self,
        ty: TyId,
        scope: Scope,
        fuel: Fuel,
    )
    {
        let variables = self.variables_of(scope, ty);
        if !variables.is_empty() && self.draws.pick(Options(3)) == Choice(0) {
            let Choice(at) = self.draws.pick(Options(variables.len()));
            let index = *variables.get(at).expect("a drawn variable");
            let variable = self.core.value_variable(Zone::Intuitionistic, index);
            self.values.push(variable);
            return;
        }
        match self.ty(ty) {
            | Ty::Unit => {
                let unit = self.core.value_unit();
                self.values.push(unit);
            },
            | Ty::Integer => {
                let Choice(magnitude) = self.draws.pick(Options(100));
                let sign = if magnitude > 0 && self.draws.pick(Options(4)) == Choice(0) {
                    Sign::Negative
                }
                else {
                    Sign::NonNegative
                };
                let digits = Magnitude::from_decimal_text(alloc::format!("{magnitude}"))
                    .expect("decimal digits");
                let literal = self
                    .core
                    .value_literal(Literal::Integer(IntegerLiteral::new(sign, digits)));
                self.values.push(literal);
            },
            | Ty::Product(first, second) => {
                self.tasks.push(Task::Pair);
                self.tasks.push(Task::Value(second, scope, fuel.child()));
                self.tasks.push(Task::Value(first, scope, fuel.child()));
            },
            | Ty::Sum(left, right) => {
                let (side, summand) = if self.draws.pick(Options(2)) == Choice(0) {
                    (Side::Left, left)
                }
                else {
                    (Side::Right, right)
                };
                self.tasks.push(Task::Injection(side));
                self.tasks.push(Task::Value(summand, scope, fuel.child()));
            },
            | Ty::Thunk(computation) => {
                self.tasks.push(Task::Thunk);
                self.tasks
                    .push(Task::Computation(computation, scope, fuel.child()));
            },
            | Ty::Returner(_) | Ty::Arrow(..) => {
                panic!("a value is generated at a value type")
            },
        }
    }

    /// Generate one computation node, or schedule its children.
    ///
    /// # Specification
    /// - requires: ty is a well-founded computation-sort type and scope is a
    ///   valid backward-linked binding chain.
    /// - ensures: scheduled work builds a computation of ty without changing
    ///   either result stack or the core; zero fuel uses only introductions.
    /// - provides: finite, typed expansion over explicit pending work.
    /// - panics: on a violated type or scope invariant.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — zero-fuel functions preserve domain and result roles;
    ///   generated computations focus as closed commands and halt. L2 compares
    ///   their readings with normalization by evaluation, challenging wrong
    ///   operand roles, binder scope and failure to make progress. Fuel zero
    ///   and the bounded strategy are observed, not unbounded expansion.
    /// - witness: `tests::generate::typed_builders_preserve_product_sum_and_function_roles`
    /// - witness: `tests::focus_properties::focusing_is_total_on_generated_computations`
    /// - witness: `tests::differential::l_machine_is_total_and_deterministic`
    /// - witness: `tests::differential::the_l_machine_agrees_with_normalisation_by_evaluation`
    #[spec(
        requires: self.types.get(ty.0).is_some_and(|known| matches!(*known, Ty::Returner(_) | Ty::Arrow(_, _)))
            && match scope { Scope::Empty => true, Scope::At(BindingId(at)) => self.bindings.get(at).is_some() },
        captures: [values = self.values.len(), computations = self.computations.len(), pending = self.tasks.len(), core = self.core.watermark()],
        ensures: |_| self.values.len() == values && self.computations.len() == computations && self.core.watermark() == core
            && self.tasks.get(pending).is_some_and(|task| if fuel.0 == 0 {
                matches!((self.types.get(ty.0), task), (Some(&Ty::Returner(_)), &Task::Return) | (Some(&Ty::Arrow(_, _)), &Task::Lambda))
            } else { matches!(*task, Task::Return | Task::Lambda | Task::Force | Task::Application | Task::Bind | Task::Case) }),
    )]
    fn computation(
        &mut self,
        ty: TyId,
        scope: Scope,
        fuel: Fuel,
    )
    {
        let child = fuel.child();
        let former = if fuel == Fuel(0) {
            Choice(0)
        }
        else {
            self.draws.pick(Options(5))
        };
        match former {
            | Choice(1) => {
                let thunk = self.intern(Ty::Thunk(ty));
                self.tasks.push(Task::Force);
                self.tasks.push(Task::Value(thunk, scope, child));
            },
            | Choice(2) => {
                let domain = self.value_type();
                let function = self.intern(Ty::Arrow(domain, ty));
                self.tasks.push(Task::Application);
                self.tasks.push(Task::Value(domain, scope, child));
                self.tasks.push(Task::Computation(function, scope, child));
            },
            | Choice(3) => {
                let bound = self.value_type();
                let head = self.intern(Ty::Returner(bound));
                let inner = self.extend(scope, bound);
                self.tasks.push(Task::Bind);
                self.tasks.push(Task::Computation(ty, inner, child));
                self.tasks.push(Task::Computation(head, scope, child));
            },
            | Choice(4) => {
                let left = self.value_type();
                let right = self.value_type();
                let sum = self.intern(Ty::Sum(left, right));
                let on_left = self.extend(scope, left);
                let on_right = self.extend(scope, right);
                self.tasks.push(Task::Case);
                self.tasks.push(Task::Computation(ty, on_right, child));
                self.tasks.push(Task::Computation(ty, on_left, child));
                self.tasks.push(Task::Value(sum, scope, child));
            },
            | _ => match self.ty(ty) {
                | Ty::Returner(value) => {
                    self.tasks.push(Task::Return);
                    self.tasks.push(Task::Value(value, scope, child));
                },
                | Ty::Arrow(domain, codomain) => {
                    let inner = self.extend(scope, domain);
                    self.tasks.push(Task::Lambda);
                    self.tasks.push(Task::Computation(codomain, inner, child));
                },
                | Ty::Unit | Ty::Integer | Ty::Product(..) | Ty::Sum(..) | Ty::Thunk(_) => {
                    panic!("a computation is generated at a computation type")
                },
            },
        }
    }

    /// Run every pending task.
    ///
    /// # Specification
    /// - requires: pending type and scope roots obey the generator invariants.
    /// - ensures: no pending work remains; result counts equal the ordered
    ///   stack effects of the initial work, and every result resolves in core.
    /// - provides: child-before-parent construction without recursive descent.
    /// - panics: when a builder has too few operands or a scheduled type or
    ///   scope violates its invariant.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — typed zero-fuel products, sums and functions
    ///   distinguish reversed operands and incorrect result-stack selection;
    ///   generated commands are closed and halt. L2 compares their observable
    ///   readings with normalization by evaluation. The stack-effect predicate
    ///   also rejects lost work or result cardinality within this domain.
    /// - witness: `tests::generate::typed_builders_preserve_product_sum_and_function_roles`
    /// - witness: `tests::focus_properties::focusing_is_total_on_generated_computations`
    /// - witness: `tests::differential::l_machine_is_total_and_deterministic`
    /// - witness: `tests::differential::the_l_machine_agrees_with_normalisation_by_evaluation`
    #[spec(
        captures: [shape = self.tasks.iter().rev().try_fold((self.values.len(), self.computations.len()), |(values, computations), task| match *task {
            | Task::Value(_, _, _) => values.checked_add(1).map(|count| (count, computations)),
            | Task::Computation(_, _, _) => computations.checked_add(1).map(|count| (values, count)),
            | Task::Pair => values.checked_sub(2).map(|count| (count.saturating_add(1), computations)),
            | Task::Injection(_) => values.checked_sub(1).map(|_| (values, computations)),
            | Task::Thunk => Some((values.checked_add(1)?, computations.checked_sub(1)?)),
            | Task::Return | Task::Force => Some((values.checked_sub(1)?, computations.checked_add(1)?)),
            | Task::Application => values.checked_sub(1).filter(|_| computations > 0).map(|count| (count, computations)),
            | Task::Lambda => computations.checked_sub(1).map(|_| (values, computations)),
            | Task::Bind => computations.checked_sub(2).map(|count| (values, count.saturating_add(1))),
            | Task::Case => Some((values.checked_sub(1)?, computations.checked_sub(2)?.saturating_add(1))),
        })],
        ensures: |_| self.tasks.is_empty() && shape == Some((self.values.len(), self.computations.len()))
            && self.values.iter().all(|&id| self.core.value(id).is_some())
            && self.computations.iter().all(|&id| self.core.computation(id).is_some()),
    )]
    fn drive(&mut self)
    {
        while let Some(task) = self.tasks.pop() {
            match task {
                | Task::Value(ty, scope, fuel) => self.value(ty, scope, fuel),
                | Task::Computation(ty, scope, fuel) => self.computation(ty, scope, fuel),
                | Task::Pair => {
                    let second = self.values.pop().expect("an operand");
                    let first = self.values.pop().expect("an operand");
                    let pair = self.core.value_pair(first, second);
                    self.values.push(pair);
                },
                | Task::Injection(side) => {
                    let body = self.values.pop().expect("an operand");
                    let injection = self.core.value_injection(side, body);
                    self.values.push(injection);
                },
                | Task::Thunk => {
                    let body = self.computations.pop().expect("an operand");
                    let thunk = self.core.value_thunk(body);
                    self.values.push(thunk);
                },
                | Task::Return => {
                    let value = self.values.pop().expect("an operand");
                    let returned = self.core.computation_return(value);
                    self.computations.push(returned);
                },
                | Task::Force => {
                    let value = self.values.pop().expect("an operand");
                    let forced = self.core.computation_force(value);
                    self.computations.push(forced);
                },
                | Task::Application => {
                    let argument = self.values.pop().expect("an operand");
                    let head = self.computations.pop().expect("an operand");
                    let applied = self.core.computation_application(head, argument);
                    self.computations.push(applied);
                },
                | Task::Lambda => {
                    let body = self.computations.pop().expect("an operand");
                    let lambda = self.core.computation_lambda(body);
                    self.computations.push(lambda);
                },
                | Task::Bind => {
                    let body = self.computations.pop().expect("an operand");
                    let head = self.computations.pop().expect("an operand");
                    let bound = self.core.computation_bind(head, body);
                    self.computations.push(bound);
                },
                | Task::Case => {
                    let on_right = self.computations.pop().expect("an operand");
                    let on_left = self.computations.pop().expect("an operand");
                    let scrutinee = self.values.pop().expect("an operand");
                    let cased = self.core.computation_case(scrutinee, on_left, on_right);
                    self.computations.push(cased);
                },
            }
        }
    }
}

/// A closed, well-typed computation over a seed and a fuel.
///
/// # Specification
/// - requires: nothing.
/// - ensures: a resolvable closed computation of a supported generated type.
/// - provides: a fixture for the supplied seed and fuel.
/// - panics: on a violated generation invariant.
///
/// # Adequacy
/// - hypothesis: L3 — generated computations focus as closed, well-formed
///   commands and halt; L2 compares their machine readings with normalization
///   by evaluation. Zero-fuel typed fixtures challenge the introduction
///   boundary. Evidence uses the bounded strategy domain, not every seed and
///   fuel or a general type-soundness proof.
/// - witness: `tests::generate::typed_builders_preserve_product_sum_and_function_roles`
/// - witness: `tests::focus_properties::focusing_is_total_on_generated_computations`
/// - witness: `tests::differential::l_machine_is_total_and_deterministic`
/// - witness: `tests::differential::the_l_machine_agrees_with_normalisation_by_evaluation`
#[spec(ensures: |ref ret| match ret.root {
    | GeneratedRoot::Computation(root) => ret.core.computation(root).is_some(),
    | GeneratedRoot::Value(_) => false,
})]
fn computation(
    seed: Seed,
    fuel: Fuel,
) -> Generated
{
    let mut generator = Generator::new(seed);
    let ty = generator.computation_type();
    generator
        .tasks
        .push(Task::Computation(ty, Scope::Empty, fuel));
    generator.drive();
    let root = generator.computations.pop().expect("the root computation");
    Generated {
        core: generator.core,
        root: GeneratedRoot::Computation(root),
    }
}

/// A closed, well-typed value over a seed and a fuel.
///
/// # Specification
/// - requires: nothing.
/// - ensures: a resolvable closed value of a supported generated type.
/// - provides: a fixture for the supplied seed and fuel.
/// - panics: on a violated generation invariant.
///
/// # Adequacy
/// - hypothesis: L3 — zero-fuel products, sums and functions have their
///   distinct type roles, and generated values retain their structure through
///   focusing and decoding. The finite constructor oracle is independent of
///   that round trip; neither observation proves arbitrary type soundness or
///   covers every seed and depth.
/// - witness: `tests::generate::typed_builders_preserve_product_sum_and_function_roles`
/// - witness: `tests::focus_properties::unfocusing_inverts_focusing_on_generated_values`
#[spec(ensures: |ref ret| match ret.root {
    | GeneratedRoot::Value(root) => ret.core.value(root).is_some(),
    | GeneratedRoot::Computation(_) => false,
})]
fn value(
    seed: Seed,
    fuel: Fuel,
) -> Generated
{
    let mut generator = Generator::new(seed);
    let ty = generator.value_type();
    generator.tasks.push(Task::Value(ty, Scope::Empty, fuel));
    generator.drive();
    let root = generator.values.pop().expect("the root value");
    Generated {
        core: generator.core,
        root: GeneratedRoot::Value(root),
    }
}

/// Closed, well-typed computations.
///
/// # Specification
/// trivial.
pub fn computations() -> impl Strategy<Value = Generated>
{
    (any::<u64>(), 0_u32 ..= 5_u32).prop_map(|(seed, fuel)| computation(Seed(seed), Fuel(fuel)))
}

/// Closed, well-typed values.
///
/// # Specification
/// trivial.
pub fn values() -> impl Strategy<Value = Generated>
{
    (any::<u64>(), 0_u32 ..= 5_u32).prop_map(|(seed, fuel)| value(Seed(seed), Fuel(fuel)))
}

/// The asymmetric signed endpoint is encoded without overflowing its magnitude.
#[test]
fn integer_payloads_cover_both_signed_extremes()
{
    use gandr_core_term::Value;

    let mut core = CoreArena::new();
    for (input, sign, digits) in [
        (i32::MIN, Sign::Negative, "2147483648"),
        (0_i32, Sign::NonNegative, "0"),
        (i32::MAX, Sign::NonNegative, "2147483647"),
    ] {
        let id = integer(&mut core, Integer(input));
        let Some(&Value::Literal(Literal::Integer(ref value))) = core.value(id)
        else {
            panic!("an integer literal");
        };
        assert_eq!(sign, value.sign());
        let actual: &str = value.magnitude().as_ref();
        assert_eq!(digits, actual);
    }
}

/// Empty choices do not divide by zero, selected indices stay bounded, and
/// fuel cannot underflow.
#[test]
fn fuel_and_draws_respect_empty_and_full_bounds()
{
    for (input, expected) in [(0_u32, 0_u32), (1, 0), (u32::MAX, 0xFFFF_FFFE_u32)] {
        assert_eq!(Fuel(expected), Fuel(input).child());
    }
    for seed in [0_u64, u64::MAX] {
        let mut draws = Draws { state: seed };
        for options in [0_usize, 1, 7, usize::MAX] {
            let Choice(choice) = draws.pick(Options(options));
            if options == 0 {
                assert_eq!(0, choice);
            }
            else {
                assert!(choice < options);
            }
        }
    }
}

/// Persistent scopes retain skipped and shadowed binders without merging their
/// types.
#[test]
fn interning_and_shadowed_scopes_preserve_distinct_types()
{
    let mut generator = Generator::new(Seed(0));
    let unit = generator.intern(Ty::Unit);
    let integer = generator.intern(Ty::Integer);
    assert_ne!(unit, integer);
    assert_eq!(unit, generator.intern(Ty::Unit));
    let pair = generator.intern(Ty::Product(integer, unit));
    assert_eq!(pair, generator.intern(Ty::Product(integer, unit)));
    assert_eq!(Ty::Unit, generator.ty(unit));
    assert_eq!(Ty::Integer, generator.ty(integer));
    assert_eq!(Ty::Product(integer, unit), generator.ty(pair));
    assert!(std::panic::catch_unwind(|| generator.ty(TyId(usize::MAX))).is_err());
    let outer = generator.extend(Scope::Empty, integer);
    let middle = generator.extend(outer, unit);
    let shadow = generator.extend(middle, integer);
    let inner = generator.extend(shadow, unit);
    assert_eq!(
        [DeBruijnIndex::from(1_u32), DeBruijnIndex::from(3_u32)].as_slice(),
        generator.variables_of(inner, integer).as_slice()
    );
    assert_eq!(
        [DeBruijnIndex::from(0_u32), DeBruijnIndex::from(2_u32)].as_slice(),
        generator.variables_of(inner, unit).as_slice()
    );
    assert_eq!(
        [DeBruijnIndex::from(0_u32)].as_slice(),
        generator.variables_of(outer, integer).as_slice()
    );
    assert!(generator.variables_of(outer, unit).is_empty());
    assert!(generator.variables_of(inner, pair).is_empty());
    assert!(generator.variables_of(inner, TyId(usize::MAX)).is_empty());
    assert!(generator.variables_of(Scope::Empty, integer).is_empty());
}

/// The zero-fuel frontier respects product fields, sum labels and a function's
/// binder type.
#[test]
fn typed_builders_preserve_product_sum_and_function_roles()
{
    use gandr_core_term::Computation;
    use gandr_core_term::Value;

    for seed in (0_u64 .. 32_u64).chain([u64::MAX]) {
        let mut generator = Generator::new(Seed(seed));
        let unit = generator.intern(Ty::Unit);
        let integer = generator.intern(Ty::Integer);
        let product = generator.intern(Ty::Product(integer, unit));
        generator
            .tasks
            .push(Task::Value(product, Scope::Empty, Fuel(0)));
        generator.drive();
        let pair = generator.values.pop().expect("one generated value");
        let Some(&Value::Pair(first, second)) = generator.core.value(pair)
        else {
            panic!("a product introduction");
        };
        assert!(matches!(
            generator.core.value(first),
            Some(&Value::Literal(Literal::Integer(_)))
        ));
        assert_eq!(Some(&Value::Unit), generator.core.value(second));
        let sum = generator.intern(Ty::Sum(unit, integer));
        generator
            .tasks
            .push(Task::Value(sum, Scope::Empty, Fuel(0)));
        generator.drive();
        let injection = generator.values.pop().expect("one generated value");
        let Some(&Value::Injection(side, body)) = generator.core.value(injection)
        else {
            panic!("a sum introduction");
        };
        match side {
            | Side::Left => assert_eq!(Some(&Value::Unit), generator.core.value(body)),
            | Side::Right => assert!(matches!(
                generator.core.value(body),
                Some(&Value::Literal(Literal::Integer(_)))
            )),
        }
        let returned = generator.intern(Ty::Returner(integer));
        let arrow = generator.intern(Ty::Arrow(unit, returned));
        generator
            .tasks
            .push(Task::Computation(arrow, Scope::Empty, Fuel(0)));
        generator.drive();
        let function = generator
            .computations
            .pop()
            .expect("one generated computation");
        let Some(&Computation::Lambda(body)) = generator.core.computation(function)
        else {
            panic!("a function introduction");
        };
        let Some(&Computation::Return(value)) = generator.core.computation(body)
        else {
            panic!("a return introduction");
        };
        assert!(matches!(
            generator.core.value(value),
            Some(&Value::Literal(Literal::Integer(_)))
        ));
    }
}
