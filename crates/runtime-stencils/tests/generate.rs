//! A deterministic generator of closed, well-typed positive-core programs.

use gandr_core_term::ComponentCount;
use gandr_core_term::ComputationId;
use gandr_core_term::CoreArena;
use gandr_core_term::ValueId;
use gandr_core_term::Zone;
use gandr_kernel_term::Side;

use crate::support::Integer;
use crate::support::integer;

/// A deterministic generator of closed, well-typed positive-core programs:
/// returns, binds, sum cases and tuple splits over integers, the unit, pairs
/// and injections.
///
/// A program is planned top down and built bottom up over an explicit task
/// stack, children before parents as the core arena requires. The budget
/// counts computation formers; types are drawn small, so a program grows
/// with its budget and not with its types.
pub struct Generator
{
    /// The xorshift state.
    state: u64,
    /// The type table: the integers at [`INT`], the unit at [`UNIT`].
    types: Vec<Type>,
    /// The scope chains: each binder's type and the scope it extends.
    scopes: Vec<(Entry, Option<Scope>)>,
}

/// An entry of the generator's type table.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Entry(usize);

/// The integers' entry.
const INT: Entry = Entry(0);

/// The unit's entry.
const UNIT: Entry = Entry(1);

/// An entry of the generator's scope chains.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
struct Scope(usize);

/// Computation formers left to spend.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
struct Budget(usize);

/// A random draw, or the count it stays below.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Draw(usize);

/// A variable's de Bruijn index.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
struct Index(u32);

/// A type, in the generator's table.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Type
{
    /// The integers.
    Int,
    /// The unit.
    Unit,
    /// A pair of two table entries.
    Pair(Entry, Entry),
    /// A sum of two table entries.
    Sum(Entry, Entry),
}

/// One step of the plan.
#[derive(Clone, Copy, Debug)]
enum Task
{
    /// Plan a computation of a type under a scope with a budget.
    Computation(Entry, Option<Scope>, Budget),
    /// Plan a value of a type under a scope.
    Value(Entry, Option<Scope>),
    /// Build a return of the value on top.
    Return,
    /// Build a bind of the two computations on top.
    Bind,
    /// Build a two-armed case of the value and two computations on top.
    Case,
    /// Build a two-component split of the value and the computation on top.
    Split,
    /// Build a pair of the two values on top.
    Pair,
    /// Build an injection of the value on top.
    Inject(Side),
}

/// A built node.
#[derive(Clone, Copy, Debug)]
enum Built
{
    /// A computation.
    Computation(ComputationId),
    /// A value.
    Value(ValueId),
}

/// A seed and a budget: one generated program.
#[derive(Clone, Copy, Debug)]
pub struct Shape
{
    /// The random stream's seed.
    pub seed: u64,
    /// The computation formers to spend.
    pub budget: usize,
}

impl Generator
{
    /// The program `shape` names, in `core`.
    ///
    /// # Specification
    /// - ensures: a closed computation of the positive core.
    /// - executable: none — closure and typing are the checker's to decide; the
    ///   suite focuses and runs every program, which an open one fails.
    ///
    /// # Adequacy
    /// - hypothesis: L1 — every generated program focuses and runs on both
    ///   tiers; an open one declines at its lowering, which fails the suite.
    /// - witness: `tests::agreement::the_generated_programs_agree_on_both_executors`
    pub fn program(
        shape: Shape,
        core: &mut CoreArena,
    ) -> ComputationId
    {
        let mut generator = Self {
            state: shape.seed | 1,
            types: vec![Type::Int, Type::Unit],
            scopes: Vec::new(),
        };
        let ty = generator.ty();
        let mut tasks = vec![Task::Computation(ty, None, Budget(shape.budget))];
        let mut built: Vec<Built> = Vec::new();
        let computation = |built: &mut Vec<Built>| match built.pop() {
            Some(Built::Computation(id)) => id,
            other => panic!("a computation was built, not {other:?}"),
        };
        let value = |built: &mut Vec<Built>| match built.pop() {
            Some(Built::Value(id)) => id,
            other => panic!("a value was built, not {other:?}"),
        };
        while let Some(task) = tasks.pop() {
            match task {
                Task::Computation(ty, scope, budget) => {
                    generator.plan_computation(&mut tasks, ty, scope, budget);
                },
                Task::Value(ty, scope) => {
                    generator.plan_value(core, &mut tasks, &mut built, ty, scope);
                },
                Task::Return => {
                    let returned = value(&mut built);
                    built.push(Built::Computation(core.computation_return(returned)));
                },
                Task::Bind => {
                    let body = computation(&mut built);
                    let bound = computation(&mut built);
                    built.push(Built::Computation(core.computation_bind(bound, body)));
                },
                Task::Case => {
                    let right = computation(&mut built);
                    let left = computation(&mut built);
                    let scrutinee = value(&mut built);
                    built.push(Built::Computation(
                        core.computation_case(scrutinee, &[left, right]),
                    ));
                },
                Task::Split => {
                    let body = computation(&mut built);
                    let scrutinee = value(&mut built);
                    built.push(Built::Computation(core.computation_split(
                        scrutinee,
                        ComponentCount::from(2_usize),
                        body,
                    )));
                },
                Task::Pair => {
                    let second = value(&mut built);
                    let first = value(&mut built);
                    built.push(Built::Value(core.value_tuple(&[first, second])));
                },
                Task::Inject(side) => {
                    let body = value(&mut built);
                    built.push(Built::Value(core.value_injection(side.into(), body)));
                },
            }
        }
        computation(&mut built)
    }

    /// A random draw below `bound`, from the next xorshift word.
    ///
    /// # Specification
    /// trivial.
    fn below(
        &mut self,
        bound: Draw,
    ) -> Draw
    {
        self.state ^= self.state.wrapping_shl(13);
        self.state ^= self.state.wrapping_shr(7);
        self.state ^= self.state.wrapping_shl(17);
        let word = usize::try_from(self.state).expect("a 64-bit host");
        Draw(word.checked_rem(bound.0).unwrap_or(0))
    }

    /// The integers or the unit, at random.
    ///
    /// # Specification
    /// trivial.
    fn base(&mut self) -> Entry
    {
        if self.below(Draw(2)) == Draw(0) {
            INT
        }
        else {
            UNIT
        }
    }

    /// Add `ty` to the table, answering its entry.
    ///
    /// # Specification
    /// trivial.
    fn table(
        &mut self,
        ty: Type,
    ) -> Entry
    {
        self.types.push(ty);
        Entry(self.types.len().saturating_sub(1))
    }

    /// A small random type.
    ///
    /// # Specification
    /// trivial.
    fn ty(&mut self) -> Entry
    {
        match self.below(Draw(6)).0 {
            0 | 1 => INT,
            2 => UNIT,
            3 => {
                let second = self.base();
                self.table(Type::Pair(INT, second))
            },
            4 => self.table(Type::Sum(INT, INT)),
            _ => self.table(Type::Sum(INT, UNIT)),
        }
    }

    /// `scope` extended with a binder of `ty`: the new scope's entry.
    ///
    /// # Specification
    /// trivial.
    fn bind(
        &mut self,
        scope: Option<Scope>,
        ty: Entry,
    ) -> Scope
    {
        self.scopes.push((ty, scope));
        Scope(self.scopes.len().saturating_sub(1))
    }

    /// The de Bruijn index of a binder of `ty` in `scope`, the nearest of a
    /// random few.
    ///
    /// # Specification
    /// trivial.
    fn variable(
        &mut self,
        scope: Option<Scope>,
        ty: Entry,
    ) -> Option<Index>
    {
        let mut cursor = scope;
        let mut index = 0_u32;
        let mut found = None;
        while let Some(at) = cursor {
            let (bound, parent) = self.scopes[at.0];
            if self.types[bound.0] == self.types[ty.0] {
                found = Some(Index(index));
                if self.below(Draw(2)) == Draw(0) {
                    break;
                }
            }
            index = index.saturating_add(1);
            cursor = parent;
        }
        found
    }

    /// Plan one computation former.
    ///
    /// # Specification
    /// trivial.
    fn plan_computation(
        &mut self,
        tasks: &mut Vec<Task>,
        ty: Entry,
        scope: Option<Scope>,
        budget: Budget,
    )
    {
        let Some(rest) = budget.0.checked_sub(1).filter(|&rest| rest > 0)
        else {
            tasks.push(Task::Return);
            tasks.push(Task::Value(ty, scope));
            return;
        };
        match self.below(Draw(3)).0 {
            0 => {
                let bound = self.ty();
                let left = self.below(Draw(rest)).0.saturating_add(1);
                let inner = Some(self.bind(scope, bound));
                tasks.push(Task::Bind);
                tasks.push(Task::Computation(
                    ty,
                    inner,
                    Budget(rest.saturating_sub(left).max(1)),
                ));
                tasks.push(Task::Computation(bound, scope, Budget(left)));
            },
            1 => {
                let right_type = self.base();
                let sum = self.table(Type::Sum(INT, right_type));
                let left = Some(self.bind(scope, INT));
                let right = Some(self.bind(scope, right_type));
                let half = Budget(rest.checked_div(2).unwrap_or(0).max(1));
                tasks.push(Task::Case);
                tasks.push(Task::Computation(ty, right, half));
                tasks.push(Task::Computation(ty, left, half));
                tasks.push(Task::Value(sum, scope));
            },
            _ => {
                let first = self.ty();
                let second = self.ty();
                let pair = self.table(Type::Pair(first, second));
                let inner = Some(self.bind(scope, first));
                let inner = Some(self.bind(inner, second));
                tasks.push(Task::Split);
                tasks.push(Task::Computation(ty, inner, Budget(rest)));
                tasks.push(Task::Value(pair, scope));
            },
        }
    }

    /// Plan one value, or build it at once when it is a leaf.
    ///
    /// # Specification
    /// trivial.
    fn plan_value(
        &mut self,
        core: &mut CoreArena,
        tasks: &mut Vec<Task>,
        built: &mut Vec<Built>,
        ty: Entry,
        scope: Option<Scope>,
    )
    {
        if self.below(Draw(3)) != Draw(0)
            && let Some(index) = self.variable(scope, ty)
        {
            built.push(Built::Value(
                core.value_variable(Zone::Intuitionistic, index.0.into()),
            ));
            return;
        }
        match self.types[ty.0] {
            Type::Int => {
                let drawn = i64::try_from(self.below(Draw(2000)).0).expect("below 2000");
                built.push(Built::Value(integer(
                    core,
                    Integer(drawn.saturating_sub(1000)),
                )));
            },
            Type::Unit => built.push(Built::Value(core.value_unit())),
            Type::Pair(first, second) => {
                tasks.push(Task::Pair);
                tasks.push(Task::Value(second, scope));
                tasks.push(Task::Value(first, scope));
            },
            Type::Sum(left, right) => {
                if self.below(Draw(2)) == Draw(0) {
                    tasks.push(Task::Inject(Side::Left));
                    tasks.push(Task::Value(left, scope));
                }
                else {
                    tasks.push(Task::Inject(Side::Right));
                    tasks.push(Task::Value(right, scope));
                }
            },
        }
    }
}
