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
    /// trivial.
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
    /// trivial.
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
    /// trivial.
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
    /// - panics: on an id this generator did not intern.
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
    /// trivial.
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
    /// trivial.
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
    /// trivial.
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
    /// trivial.
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
    /// trivial.
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
    /// trivial.
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
    /// - panics: when a builder finds no operand, which the scheduling rules
    ///   out.
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
/// trivial.
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
/// trivial.
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
