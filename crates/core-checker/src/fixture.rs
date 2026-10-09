//! Test fixtures: literals, dangling ids, a seeded signature table, and the
//! recipes the property witnesses generate types and terms from.
//!
//! A recipe is a flat list of steps, each naming earlier entries by position,
//! so a generated tree is built by one forward pass and read by one explicit
//! stack: no fixture recurses, whatever depth a recipe reaches.

use alloc::string::String;
use alloc::vec;
use alloc::vec::Vec;

use gandr_core_term::CompType;
use gandr_core_term::CompTypeId;
use gandr_core_term::ComputationId;
use gandr_core_term::CoreArena;
use gandr_core_term::ValueId;
use gandr_core_term::ValueType;
use gandr_core_term::ValueTypeId;
use gandr_core_term::Zone;
use gandr_kernel_term::BaseType;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::FractionDigits;
use gandr_kernel_term::IntegerLiteral;
use gandr_kernel_term::Literal;
use gandr_kernel_term::Magnitude;
use gandr_kernel_term::NumericLiteral;
use gandr_kernel_term::Sign;
use gandr_kernel_term::StringLiteral;
use proptest::prelude::Just;
use proptest::prelude::Strategy;
use proptest::prop_oneof;

use crate::context::CheckingContext;
use crate::formation::form_value_type;

/// The integer literal `0`.
///
/// # Specification
/// trivial.
pub fn integer_literal() -> Literal
{
    Literal::Integer(IntegerLiteral::new(Sign::NonNegative, Magnitude::zero()))
}

/// The empty string literal.
///
/// # Specification
/// trivial.
pub fn text_literal() -> Literal
{
    Literal::Text(StringLiteral::new(String::new()))
}

/// The numeric literal `0`.
///
/// # Specification
/// trivial.
pub fn numeric_literal() -> Literal
{
    Literal::Numeric(NumericLiteral::new(
        Sign::NonNegative,
        Magnitude::zero(),
        FractionDigits::none(),
    ))
}

/// A value-type id past the end of any arena holding fewer than sixteen
/// value types.
///
/// # Specification
/// trivial.
pub fn dangling_value_type() -> ValueTypeId
{
    let mut scratch = CoreArena::new();
    let mut last = scratch.value_type_unit();
    for _ in 0_u8 .. 16_u8 {
        last = scratch.value_type_unit();
    }
    last
}

/// A value id past the end of any arena holding fewer than sixteen values.
///
/// # Specification
/// trivial.
pub fn dangling_value() -> ValueId
{
    let mut scratch = CoreArena::new();
    let mut last = scratch.value_unit();
    for _ in 0_u8 .. 16_u8 {
        last = scratch.value_unit();
    }
    last
}

/// Admit constants `0..` in order, each supplying the type at its position in
/// `types`.
///
/// # Specification
/// trivial.
pub fn seed(
    context: &mut CheckingContext<'_>,
    types: &[ValueTypeId],
)
{
    for (position, &declared) in types.iter().enumerate() {
        let constant = ConstantIndex::from(position);
        let formed = form_value_type(context, declared).expect("a seeded type is formed");
        context.admit(constant).expect("seeded constants ascend");
        context.record(constant, formed);
    }
}

/// A position in a recipe's pool, counted round past the pool's end.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
pub struct Position(usize);

impl Position
{
    /// The same position, counted round within `pool`.
    ///
    /// # Specification
    /// trivial.
    fn within<Pooled>(
        self,
        pool: &[Pooled],
    ) -> Self
    {
        Self(
            self.0
                .checked_rem(pool.len())
                .expect("pools are seeded non-empty"),
        )
    }
}

/// The entry at `position` of `pool`, counting round past its end.
///
/// # Specification
/// trivial.
fn pick<Pooled>(
    pool: &[Pooled],
    position: Position,
) -> Pooled
where
    Pooled: Copy,
{
    pool[position.within(pool).0]
}

/// Every entry of `pool` once, starting at `position` and counting round past
/// its end.
///
/// # Specification
/// trivial.
fn rotated<Pooled>(
    pool: &[Pooled],
    position: Position,
) -> impl Iterator<Item = Pooled> + '_
where
    Pooled: Copy,
{
    pool.iter()
        .copied()
        .cycle()
        .skip(position.within(pool).0)
        .take(pool.len())
}

/// One step of a type recipe; positions are taken modulo the pool's length.
#[derive(Clone, Copy, Debug)]
pub enum TypeStep
{
    /// Push the integer atom.
    Integer,
    /// Push the string atom.
    String,
    /// Push the unit type.
    Unit,
    /// Push `U C` of the computation type at the position.
    Thunk(Position),
    /// Push `F A` of the value type at the position.
    Returner(Position),
    /// Push `A → C` of the value type and computation type at the positions.
    Arrow(Position, Position),
}

/// A value-type node, its children resolved to pool positions.
#[derive(Clone, Copy, Debug)]
enum ValueShape
{
    /// The integer atom.
    Integer,
    /// The string atom.
    String,
    /// The unit type.
    Unit,
    /// A thunk type of the computation type at the position.
    Thunk(Position),
}

/// A computation-type node, its children resolved to pool positions.
#[derive(Clone, Copy, Debug)]
enum CompShape
{
    /// A returner of the value type at the position.
    Returner(Position),
    /// An arrow of the value type and computation type at the positions.
    Arrow(Position, Position),
}

/// A resolved pool entry.
#[derive(Clone, Copy, Debug)]
enum Entry
{
    /// A value type.
    Value(ValueShape),
    /// A computation type.
    Comp(CompShape),
}

/// One token of a type's preorder spelling, which determines the tree.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Token
{
    /// The integer atom.
    Integer,
    /// The string atom.
    String,
    /// The unit type.
    Unit,
    /// A thunk type; one child follows.
    Thunk,
    /// A returner; one child follows.
    Returner,
    /// An arrow; the domain, then the codomain, follow.
    Arrow,
}

/// A generated pair of a value type and a computation type over the
/// fragment's formers.
#[repr(transparent)]
#[derive(Clone, Debug)]
pub struct TypeRecipe
{
    /// The steps after the seeds `Integer` and `F Integer`.
    steps: Vec<TypeStep>,
}

impl TypeRecipe
{
    /// The pool the steps resolve to, seeds first.
    ///
    /// # Specification
    /// trivial.
    fn resolve(&self) -> Vec<Entry>
    {
        let mut values = Vec::from([ValueShape::Integer]);
        let mut comps = Vec::from([CompShape::Returner(Position(0))]);
        let mut entries = Vec::from([
            Entry::Value(ValueShape::Integer),
            Entry::Comp(CompShape::Returner(Position(0))),
        ]);
        for &step in &self.steps {
            let entry = match step {
                | TypeStep::Integer => Entry::Value(ValueShape::Integer),
                | TypeStep::String => Entry::Value(ValueShape::String),
                | TypeStep::Unit => Entry::Value(ValueShape::Unit),
                | TypeStep::Thunk(body) => Entry::Value(ValueShape::Thunk(body.within(&comps))),
                | TypeStep::Returner(result) => {
                    Entry::Comp(CompShape::Returner(result.within(&values)))
                },
                | TypeStep::Arrow(domain, codomain) => Entry::Comp(CompShape::Arrow(
                    domain.within(&values),
                    codomain.within(&comps),
                )),
            };
            match entry {
                | Entry::Value(shape) => values.push(shape),
                | Entry::Comp(shape) => comps.push(shape),
            }
            entries.push(entry);
        }
        entries
    }

    /// Mint the recipe into `arena` at fresh ids; the last value type and the
    /// last computation type pushed.
    ///
    /// # Specification
    /// trivial.
    pub fn build_both(
        &self,
        arena: &mut CoreArena,
    ) -> (ValueTypeId, CompTypeId)
    {
        let mut values: Vec<ValueTypeId> = Vec::new();
        let mut comps: Vec<CompTypeId> = Vec::new();
        for entry in self.resolve() {
            match entry {
                | Entry::Value(shape) => values.push(match shape {
                    | ValueShape::Integer => arena.value_type_base(BaseType::Integer),
                    | ValueShape::String => arena.value_type_base(BaseType::String),
                    | ValueShape::Unit => arena.value_type_unit(),
                    | ValueShape::Thunk(body) => arena.value_type_thunk(comps[body.0]),
                }),
                | Entry::Comp(shape) => comps.push(match shape {
                    | CompShape::Returner(result) => arena.comp_type_returner(values[result.0]),
                    | CompShape::Arrow(domain, codomain) => {
                        arena.comp_type_arrow(values[domain.0], comps[codomain.0])
                    },
                }),
            }
        }
        (*values.last().unwrap(), *comps.last().unwrap())
    }

    /// Mint the recipe into `arena` at fresh ids; the last value type pushed.
    ///
    /// # Specification
    /// trivial.
    pub fn build(
        &self,
        arena: &mut CoreArena,
    ) -> ValueTypeId
    {
        self.build_both(arena).0
    }

    /// The preorder spelling of the last value type pushed.
    ///
    /// # Specification
    /// trivial.
    pub fn shape(&self) -> Vec<Token>
    {
        let entries = self.resolve();
        let mut value_entries = Vec::new();
        let mut comp_entries = Vec::new();
        for entry in entries {
            match entry {
                | Entry::Value(shape) => value_entries.push(shape),
                | Entry::Comp(shape) => comp_entries.push(shape),
            }
        }
        let mut tokens = Vec::new();
        let mut pending = Vec::from([Entry::Value(*value_entries.last().unwrap())]);
        while let Some(entry) = pending.pop() {
            match entry {
                | Entry::Value(ValueShape::Integer) => tokens.push(Token::Integer),
                | Entry::Value(ValueShape::String) => tokens.push(Token::String),
                | Entry::Value(ValueShape::Unit) => tokens.push(Token::Unit),
                | Entry::Value(ValueShape::Thunk(body)) => {
                    tokens.push(Token::Thunk);
                    pending.push(Entry::Comp(comp_entries[body.0]));
                },
                | Entry::Comp(CompShape::Returner(result)) => {
                    tokens.push(Token::Returner);
                    pending.push(Entry::Value(value_entries[result.0]));
                },
                | Entry::Comp(CompShape::Arrow(domain, codomain)) => {
                    tokens.push(Token::Arrow);
                    pending.push(Entry::Comp(comp_entries[codomain.0]));
                    pending.push(Entry::Value(value_entries[domain.0]));
                },
            }
        }
        tokens
    }
}

/// Type recipes of up to ten steps.
///
/// # Specification
/// trivial.
pub fn type_recipe() -> impl Strategy<Value = TypeRecipe>
{
    let step = prop_oneof![
        Just(TypeStep::Integer),
        Just(TypeStep::String),
        Just(TypeStep::Unit),
        (0_usize .. 8).prop_map(|body| TypeStep::Thunk(Position(body))),
        (0_usize .. 8).prop_map(|result| TypeStep::Returner(Position(result))),
        (0_usize .. 8, 0_usize .. 8)
            .prop_map(|(domain, codomain)| TypeStep::Arrow(Position(domain), Position(codomain))),
    ];
    proptest::collection::vec(step, 0 .. 10).prop_map(|steps| TypeRecipe { steps })
}

/// One step of a free term recipe; positions are taken modulo the pool's
/// length.
#[derive(Clone, Copy, Debug)]
pub enum TermStep
{
    /// Push an intuitionistic variable of index `0..3`.
    Variable(u8),
    /// Push the constant at position `0..6`.
    Constant(u8),
    /// Push the unit value.
    Unit,
    /// Push an integer literal.
    Integer,
    /// Push a string literal.
    Text,
    /// Push a numeric literal.
    Numeric,
    /// Push a thunk of the computation at the position.
    Thunk(Position),
    /// Push a force of the value at the position.
    Force(Position),
    /// Push the application of the computation to the value at the positions.
    Apply(Position, Position),
    /// Push a lambda over the computation at the position.
    Lambda(Position),
    /// Push a return of the value at the position.
    Return(Position),
}

/// A generated pool of terms over the fragment's formers, unconstrained by
/// type.
#[repr(transparent)]
#[derive(Clone, Debug)]
pub struct TermRecipe
{
    /// The steps after the seeds `()` and `return ()`.
    steps: Vec<TermStep>,
}

/// The terms a recipe minted, in the order pushed.
#[derive(Clone, Debug)]
pub struct Terms
{
    /// The values.
    pub values: Vec<ValueId>,
    /// The computations.
    pub comps: Vec<ComputationId>,
}

impl TermRecipe
{
    /// Mint every term of the recipe into `arena`.
    ///
    /// # Specification
    /// trivial.
    pub fn build(
        &self,
        arena: &mut CoreArena,
    ) -> Terms
    {
        let unit = arena.value_unit();
        let returned = arena.computation_return(unit);
        let mut terms = Terms {
            values: Vec::from([unit]),
            comps: Vec::from([returned]),
        };
        for &step in &self.steps {
            let value = |position: Position| pick(&terms.values, position);
            let comp = |position: Position| pick(&terms.comps, position);
            match step {
                | TermStep::Variable(index) => {
                    let index = DeBruijnIndex::from(u32::from(index % 3));
                    terms
                        .values
                        .push(arena.value_variable(Zone::Intuitionistic, index));
                },
                | TermStep::Constant(position) => {
                    let constant = ConstantIndex::from(usize::from(position % 6));
                    terms.values.push(arena.value_constant(constant));
                },
                | TermStep::Unit => terms.values.push(arena.value_unit()),
                | TermStep::Integer => terms.values.push(arena.value_literal(integer_literal())),
                | TermStep::Text => terms.values.push(arena.value_literal(text_literal())),
                | TermStep::Numeric => terms.values.push(arena.value_literal(numeric_literal())),
                | TermStep::Thunk(body) => {
                    let body = comp(body);
                    terms.values.push(arena.value_thunk(body));
                },
                | TermStep::Force(forced) => {
                    let forced = value(forced);
                    terms.comps.push(arena.computation_force(forced));
                },
                | TermStep::Apply(head, argument) => {
                    let (head, argument) = (comp(head), value(argument));
                    terms
                        .comps
                        .push(arena.computation_application(head, argument));
                },
                | TermStep::Lambda(body) => {
                    let body = comp(body);
                    terms.comps.push(arena.computation_lambda(body));
                },
                | TermStep::Return(returned) => {
                    let returned = value(returned);
                    terms.comps.push(arena.computation_return(returned));
                },
            }
        }
        terms
    }
}

/// Free term recipes of up to sixteen steps.
///
/// # Specification
/// trivial.
pub fn term_recipe() -> impl Strategy<Value = TermRecipe>
{
    let step = prop_oneof![
        (0_u8 .. 3).prop_map(TermStep::Variable),
        (0_u8 .. 6).prop_map(TermStep::Constant),
        Just(TermStep::Unit),
        Just(TermStep::Integer),
        Just(TermStep::Text),
        Just(TermStep::Numeric),
        (0_usize .. 16).prop_map(|body| TermStep::Thunk(Position(body))),
        (0_usize .. 16).prop_map(|forced| TermStep::Force(Position(forced))),
        (0_usize .. 16, 0_usize .. 16)
            .prop_map(|(head, argument)| TermStep::Apply(Position(head), Position(argument))),
        (0_usize .. 16).prop_map(|body| TermStep::Lambda(Position(body))),
        (0_usize .. 16).prop_map(|returned| TermStep::Return(Position(returned))),
    ];
    proptest::collection::vec(step, 0 .. 16).prop_map(|steps| TermRecipe { steps })
}

/// Whether a term's former synthesises or checks.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Mode
{
    /// The former synthesises.
    Synthesising,
    /// The former checks.
    Checking,
}

/// One step of a well-typed recipe; positions are taken modulo the pool's
/// length, and a step whose premise the chosen entry does not meet pushes
/// nothing.
#[derive(Clone, Copy, Debug)]
pub enum TypedStep
{
    /// Push an integer literal.
    Integer,
    /// Push a string literal.
    Text,
    /// Push the unit value.
    Unit,
    /// Push a fresh constant declared at the type of the value at the
    /// position.
    Constant(Position),
    /// Push a thunk of the computation at the position.
    Thunk(Position),
    /// Push a return of the value at the position.
    Return(Position),
    /// Push a force of the first synthesising value of thunk type from the
    /// position on.
    Force(Position),
    /// Push the application of the first computation of arrow type from the
    /// position on to a fresh constant of its domain; a checking head is
    /// reached through the force of a fresh constant of its thunk type, which
    /// is pushed too.
    Apply(Position),
    /// Push a fresh constant declared at the thunk type of the computation at
    /// the position.
    Suspend(Position),
    /// Push a lambda over the closed computation at the first position, its
    /// binder typed by the value at the second.
    Lambda(Position, Position),
    /// Push the identity lambda at the type of the value at the position.
    Identity(Position),
}

/// A generated pool of well-typed closed terms, each with its type and mode,
/// and the constants they read.
#[repr(transparent)]
#[derive(Clone, Debug)]
pub struct TypedRecipe
{
    /// The steps after the seeds `()` and `return ()`.
    steps: Vec<TypedStep>,
}

/// The terms a well-typed recipe minted, each with its type and mode, and the
/// type of every constant they read, by position.
#[derive(Clone, Debug)]
pub struct TypedTerms
{
    /// The values.
    pub values: Vec<(ValueId, ValueTypeId, Mode)>,
    /// The computations.
    pub comps: Vec<(ComputationId, CompTypeId, Mode)>,
    /// The constants' types.
    pub constants: Vec<ValueTypeId>,
}

impl TypedRecipe
{
    /// Mint every term of the recipe into `arena`.
    ///
    /// # Specification
    /// trivial.
    pub fn build(
        &self,
        arena: &mut CoreArena,
    ) -> TypedTerms
    {
        let unit_type = arena.value_type_unit();
        let unit = arena.value_unit();
        let returned = arena.computation_return(unit);
        let returns_unit = arena.comp_type_returner(unit_type);
        let mut terms = TypedTerms {
            values: Vec::from([(unit, unit_type, Mode::Synthesising)]),
            comps: Vec::from([(returned, returns_unit, Mode::Checking)]),
            constants: Vec::new(),
        };
        for &step in &self.steps {
            let value = |position: Position| pick(&terms.values, position);
            let comp = |position: Position| pick(&terms.comps, position);
            match step {
                | TypedStep::Integer => {
                    let literal = arena.value_literal(integer_literal());
                    let atom = arena.value_type_base(BaseType::Integer);
                    terms.values.push((literal, atom, Mode::Synthesising));
                },
                | TypedStep::Text => {
                    let literal = arena.value_literal(text_literal());
                    let atom = arena.value_type_base(BaseType::String);
                    terms.values.push((literal, atom, Mode::Synthesising));
                },
                | TypedStep::Unit => {
                    let unit = arena.value_unit();
                    let unit_type = arena.value_type_unit();
                    terms.values.push((unit, unit_type, Mode::Synthesising));
                },
                | TypedStep::Constant(source) => {
                    let (_, declared, _) = value(source);
                    let constant = arena.value_constant(ConstantIndex::from(terms.constants.len()));
                    terms.constants.push(declared);
                    terms.values.push((constant, declared, Mode::Synthesising));
                },
                | TypedStep::Thunk(body) => {
                    let (body, body_type, _) = comp(body);
                    let thunk = arena.value_thunk(body);
                    let thunk_type = arena.value_type_thunk(body_type);
                    terms.values.push((thunk, thunk_type, Mode::Checking));
                },
                | TypedStep::Return(returned) => {
                    let (returned, result, _) = value(returned);
                    let term = arena.computation_return(returned);
                    let returner = arena.comp_type_returner(result);
                    terms.comps.push((term, returner, Mode::Checking));
                },
                | TypedStep::Force(start) => {
                    let found =
                        rotated(&terms.values, start).find_map(|(forced, forced_type, mode)| {
                            match arena.value_type(forced_type) {
                                | Some(&ValueType::Thunk(body_type))
                                    if mode == Mode::Synthesising =>
                                {
                                    Some((forced, body_type))
                                },
                                | _ => None,
                            }
                        });
                    if let Some((forced, body_type)) = found {
                        let term = arena.computation_force(forced);
                        terms.comps.push((term, body_type, Mode::Synthesising));
                    }
                },
                | TypedStep::Apply(start) => {
                    let found =
                        rotated(&terms.comps, start).find_map(
                            |(head, head_type, mode)| match arena.comp_type(head_type) {
                                | Some(&CompType::Arrow { domain, codomain }) => {
                                    Some((head, head_type, mode, domain, codomain))
                                },
                                | _ => None,
                            },
                        );
                    if let Some((head, head_type, mode, domain, codomain)) = found {
                        let head = match mode {
                            | Mode::Synthesising => head,
                            | Mode::Checking => {
                                let declared = arena.value_type_thunk(head_type);
                                let suspended = arena
                                    .value_constant(ConstantIndex::from(terms.constants.len()));
                                terms.constants.push(declared);
                                terms.values.push((suspended, declared, Mode::Synthesising));
                                let forced = arena.computation_force(suspended);
                                terms.comps.push((forced, head_type, Mode::Synthesising));
                                forced
                            },
                        };
                        let argument =
                            arena.value_constant(ConstantIndex::from(terms.constants.len()));
                        terms.constants.push(domain);
                        let term = arena.computation_application(head, argument);
                        terms.comps.push((term, codomain, Mode::Synthesising));
                    }
                },
                | TypedStep::Suspend(body) => {
                    let (_, body_type, _) = comp(body);
                    let declared = arena.value_type_thunk(body_type);
                    let constant = arena.value_constant(ConstantIndex::from(terms.constants.len()));
                    terms.constants.push(declared);
                    terms.values.push((constant, declared, Mode::Synthesising));
                },
                | TypedStep::Lambda(body, domain) => {
                    let (body, body_type, _) = comp(body);
                    let (_, domain, _) = value(domain);
                    let term = arena.computation_lambda(body);
                    let arrow = arena.comp_type_arrow(domain, body_type);
                    terms.comps.push((term, arrow, Mode::Checking));
                },
                | TypedStep::Identity(domain) => {
                    let (_, domain, _) = value(domain);
                    let bound =
                        arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
                    let returned = arena.computation_return(bound);
                    let term = arena.computation_lambda(returned);
                    let returner = arena.comp_type_returner(domain);
                    let arrow = arena.comp_type_arrow(domain, returner);
                    terms.comps.push((term, arrow, Mode::Checking));
                },
            }
        }
        terms
    }
}

/// Well-typed recipes of up to twenty steps.
///
/// # Specification
/// trivial.
pub fn typed_recipe() -> impl Strategy<Value = TypedRecipe>
{
    let step = prop_oneof![
        Just(TypedStep::Integer),
        Just(TypedStep::Text),
        Just(TypedStep::Unit),
        (0_usize .. 16).prop_map(|source| TypedStep::Constant(Position(source))),
        (0_usize .. 16).prop_map(|body| TypedStep::Thunk(Position(body))),
        (0_usize .. 16).prop_map(|returned| TypedStep::Return(Position(returned))),
        (0_usize .. 16).prop_map(|start| TypedStep::Force(Position(start))),
        (0_usize .. 16).prop_map(|start| TypedStep::Apply(Position(start))),
        (0_usize .. 16).prop_map(|body| TypedStep::Suspend(Position(body))),
        (0_usize .. 16, 0_usize .. 16)
            .prop_map(|(body, domain)| TypedStep::Lambda(Position(body), Position(domain))),
        (0_usize .. 16).prop_map(|domain| TypedStep::Identity(Position(domain))),
    ];
    proptest::collection::vec(step, 0 .. 20).prop_map(|steps| TypedRecipe { steps })
}

/// One of the value atoms a generated function's types are built from.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum AtomType
{
    /// The integer atom.
    Integer,
    /// The string atom.
    String,
    /// The unit type.
    Unit,
}

impl AtomType
{
    /// The atom's type, minted into `arena`.
    ///
    /// # Specification
    /// trivial.
    fn mint(
        self,
        arena: &mut CoreArena,
    ) -> ValueTypeId
    {
        match self {
            | Self::Integer => arena.value_type_base(BaseType::Integer),
            | Self::String => arena.value_type_base(BaseType::String),
            | Self::Unit => arena.value_type_unit(),
        }
    }

    /// A closed value of the atom, minted into `arena`.
    ///
    /// # Specification
    /// trivial.
    fn inhabitant(
        self,
        arena: &mut CoreArena,
    ) -> ValueId
    {
        match self {
            | Self::Integer => arena.value_literal(integer_literal()),
            | Self::String => arena.value_literal(text_literal()),
            | Self::Unit => arena.value_unit(),
        }
    }
}

/// Whether a generated function is well typed.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Typing
{
    /// The value the body returns has the result type.
    WellTyped,
    /// The value the body returns has another type.
    IllTyped,
}

/// A generated function definition in the shape a lowering mints for a
/// function tail: `U (A1 -> … -> An -> F B)` declared, and
/// `thunk (λ … λ. run x1 <- force k1 ; … ; return v)` defined.
#[derive(Clone, Debug)]
pub struct FunctionRecipe
{
    /// Each parameter's type, outermost first.
    parameters: Vec<AtomType>,
    /// Each statement's returned type; the statement forces a fresh owed
    /// constant of `U (F T)`.
    statements: Vec<AtomType>,
    /// The result type.
    result: AtomType,
    /// The binder the body returns, counted round the binders in scope, or an
    /// inhabitant of the result when none is; chosen without regard to its
    /// type, so a recipe may be ill typed.
    returned: Position,
}

/// What a function recipe minted beside the constants it owes.
#[derive(Clone, Copy, Debug)]
pub struct FunctionTerms
{
    /// `U (A1 -> … -> An -> F B)`.
    pub declared: ValueTypeId,
    /// The thunked lambda chain over the statements.
    pub body: ValueId,
}

impl FunctionRecipe
{
    /// The types of the binders in scope at the body's last computation,
    /// outermost first.
    ///
    /// # Specification
    /// trivial.
    fn scope(&self) -> Vec<AtomType>
    {
        self.parameters
            .iter()
            .chain(&self.statements)
            .copied()
            .collect()
    }

    /// Whether the function the recipe mints is well typed.
    ///
    /// # Specification
    /// trivial.
    pub fn typing(&self) -> Typing
    {
        let scope = self.scope();
        let returned = match scope.len() {
            | 0 => self.result,
            | _ => pick(&scope, self.returned),
        };
        if returned == self.result {
            Typing::WellTyped
        }
        else {
            Typing::IllTyped
        }
    }

    /// Mint the function into `arena`, declaring each constant its statements
    /// force at the end of `constants`.
    ///
    /// # Specification
    /// trivial.
    pub fn build(
        &self,
        arena: &mut CoreArena,
        constants: &mut Vec<ValueTypeId>,
    ) -> FunctionTerms
    {
        let scope = self.scope();
        let returned = match scope.len().checked_sub(1) {
            | None => self.result.inhabitant(arena),
            | Some(innermost) => {
                let Position(chosen) = self.returned.within(&scope);
                let index = innermost
                    .checked_sub(chosen)
                    .expect("the choice is in scope");
                arena.value_variable(
                    Zone::Intuitionistic,
                    DeBruijnIndex::from(u32::try_from(index).expect("a scope fits an index")),
                )
            },
        };
        let mut chain = arena.computation_return(returned);
        let first = constants.len();
        for &bound in &self.statements {
            let atom = bound.mint(arena);
            let returner = arena.comp_type_returner(atom);
            constants.push(arena.value_type_thunk(returner));
        }
        for offset in (0 .. self.statements.len()).rev() {
            let position = first
                .checked_add(offset)
                .expect("a module fits its constants");
            let forced = arena.value_constant(ConstantIndex::from(position));
            let bound = arena.computation_force(forced);
            chain = arena.computation_bind(bound, chain);
        }
        for _ in &self.parameters {
            chain = arena.computation_lambda(chain);
        }
        let body = arena.value_thunk(chain);
        let result = self.result.mint(arena);
        let mut declared = arena.comp_type_returner(result);
        for &parameter in self.parameters.iter().rev() {
            let domain = parameter.mint(arena);
            declared = arena.comp_type_arrow(domain, declared);
        }
        FunctionTerms {
            declared: arena.value_type_thunk(declared),
            body,
        }
    }
}

/// Function recipes of up to three parameters and two statements.
///
/// # Specification
/// trivial.
pub fn function_recipe() -> impl Strategy<Value = FunctionRecipe>
{
    let atom = || {
        prop_oneof![
            Just(AtomType::Integer),
            Just(AtomType::String),
            Just(AtomType::Unit)
        ]
    };
    (
        proptest::collection::vec(atom(), 0 .. 4),
        proptest::collection::vec(atom(), 0 .. 3),
        atom(),
        0_usize .. 8,
    )
        .prop_map(
            |(parameters, statements, result, returned)| FunctionRecipe {
                parameters,
                statements,
                result,
                returned: Position(returned),
            },
        )
}
