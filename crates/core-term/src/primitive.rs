//! The native prelude: one table for names, signatures and exact evaluation.
//!
//! # Native prelude
//!
//! `primitive::PRELUDE` is the single table of native names, operator
//! spellings, ordered argument classifiers, result classifiers and evaluation
//! instructions. Recognition seeds these rows; the checker reads their
//! signatures; the sequent machine calls their evaluator. Native function
//! values are closed, typed thunks of ordinary curried lambdas, so partial
//! application uses the closure machine rather than a second calling
//! convention.
//!
//! | Family | Names | Types |
//! | ------ | ----- | ----- |
//! | Integer arithmetic | `add`, `sub`, `mul`, `int.div`, `int.mod`, `neg` | Integer operands and result |
//! | Integer comparison | `eq`, `ne`, `lt`, `le`, `gt`, `ge` | Integer operands, boolean result |
//! | Boolean logic | `and`, `or`, `bool.not` | Boolean operands and result |
//! | Text | `string.append` | String operands and result |
//! | Integer combinators | `prim.id`, `prim.const` | Integer operands and result |
//! | Floating-point arithmetic | `float64.add`, `float64.sub`, `float64.mul`, `float64.div`, `float64.neg`, `float64.exp` | Float64 operands and result |
//! | Floating-point comparison | `float64.eq`, `float64.ne`, `float64.lt`, `float64.le`, `float64.gt`, `float64.ge` | Float64 operands, boolean result |
//! | Conversion | `float64.from_integer`, `float64.round` | Integer to Float64, Float64 to Integer |
//!
//! Booleans are `Unit + Unit`, with the left injection true. Division truncates
//! toward zero; remainder has the dividend's sign. Division and remainder by
//! zero return `PrimitiveError::DivisionByZero`, not a host panic. Arity and
//! classifier errors stay distinct. Integer arithmetic preserves the literal
//! vocabulary's unbounded magnitude, including values wider than a machine
//! integer.
//!
//! Floating-point rows are IEEE 754 binary64 under round-to-nearest, ties to
//! even: division by zero is an infinity or a NaN, not an error, and the
//! comparisons are IEEE's, so a NaN equals nothing, itself included.
//! `float64.from_integer` rounds the exact integer to the nearest binary64
//! value; `float64.round` rounds to the nearest integer, ties to even, and
//! refuses an infinity or a NaN as [`PrimitiveError::NotFinite`]. Every result
//! NaN is the one canonical NaN the literal holds.
//!
//! **Choice.** `libm`, with defaults off, supplies `exp` and the rounding: its
//! soft implementation runs alike on every platform, so a run's floating-point
//! answer is the same wherever it runs, and it works in `no_std`. The host's
//! `f64::exp` calls the platform's C library, whose last bit differs across
//! platforms, and `no_std` lacks it; a hand-written series would be a second,
//! unmaintained math library. Revisit if a correctly rounded `exp` is needed
//! (the `core-math` family) or if `libm` loses its maintenance in the Rust
//! project.
//!
//! **Choice.** `num-bigint`, with defaults off, supplies exact arithmetic in
//! `no_std + alloc`. The maintained pure-Rust implementation avoids
//! hand-written arithmetic and a native build dependency. Fixed-width `bnum`
//! cannot implement the literal contract; `rug` brings GMP; `malachite` brings
//! a larger arithmetic surface and LGPL licensing. Revisit if measured
//! arithmetic workloads justify a different backend without changing integer
//! semantics. Native operands borrow decimal payloads until arithmetic requires
//! conversion, and text operands their contents until an append writes one
//! result.
//!
//! Native execution belongs to the sequent runtime. The pure normalizer reports
//! `EvalFault::NativePrimitive` rather than inventing a native reduction rule.
//! Persistence records the table name and ordered operands, never a function
//! pointer or process-local address.
//!
//! Witnesses: `primitive::tests::exact_arithmetic_and_errors`,
//! `primitive::tests::comparisons_and_booleans` and
//! `primitive::tests::table_signatures_and_currying_agree`.
//!
//! # Native runtime assumptions
//!
//! Native values synthesize their thunked curried signatures from the native
//! table, `PRELUDE`. Saturated operations check each argument against that same
//! row and synthesize its result returner.
//!
//! The kernel remains pure: it gains neither primitive syntax nor an arithmetic
//! evaluator. The checker bridge admits each distinct native row present in the
//! core arena as a named opaque axiom of its table signature, before the source
//! module's declarations. Erasure turns a native value into that constant and a
//! saturated operation into ordinary force and application nodes. Export
//! retains these named assumptions, and a declaration's kernel audit reports
//! the native constants it depends on. Kernel admission verifies types; it does
//! not certify the host arithmetic implementation or introduce arithmetic
//! equations into conversion. No unchecked admission is used.
//!
//! **Choice.** Explicit, auditable runtime assumptions rather than silently
//! skipping kernel admission or adding host arithmetic to the trusted kernel.
//! Revisit when a certified arithmetic implementation can replace an opaque
//! signature while preserving the runtime contract. The checker witness
//! `bridge::tests::native_operations_cross_as_audited_assumptions` checks the
//! exported axiom, reference remapping and audit.

use alloc::string::String;
use core::cmp::Ordering;
use core::fmt;
use core::ops::Add as _;
use core::ops::Mul as _;
use core::ops::Neg as _;
use core::ops::Rem as _;
use core::ops::Sub as _;

use anodized::spec;
use gandr_kernel_term::BaseType;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::Float64Literal;
use gandr_kernel_term::IntegerLiteral;
use gandr_kernel_term::Literal;
use gandr_kernel_term::Magnitude;
use gandr_kernel_term::Side;
use gandr_kernel_term::Sign;
use gandr_kernel_term::StringLiteral;
use num_bigint::BigInt;

use crate::CompTypeId;
use crate::CoreArena;
use crate::ValueId;
use crate::ValueTypeId;
use crate::Zone;

/// The bounded argument list of a native operation, without heap allocation.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Arguments<Id = ValueId>
{
    /// One operand.
    Unary(Id),
    /// Two operands in source order.
    Binary([Id; 2]),
}

impl<Id> core::ops::Deref for Arguments<Id>
{
    type Target = [Id];
    /// Borrow the ordered arguments.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn deref(&self) -> &Self::Target
    {
        match *self {
            Self::Unary(ref value) => core::slice::from_ref(value),
            Self::Binary(ref values) => values,
        }
    }
}

impl<Id> core::ops::DerefMut for Arguments<Id>
{
    /// Borrow the ordered arguments for an arena rewrite.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn deref_mut(&mut self) -> &mut Self::Target
    {
        match *self {
            Self::Unary(ref mut value) => core::slice::from_mut(value),
            Self::Binary(ref mut values) => values,
        }
    }
}

/// A native operand or result classifier.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum PrimitiveType
{
    /// An exact, unbounded signed integer.
    Integer,
    /// The canonical boolean sum `Unit + Unit`, true on the left.
    Boolean,
    /// A string of Unicode scalar values.
    Text,
    /// An IEEE 754 binary64 floating-point number.
    Float64,
}

impl PrimitiveType
{
    /// Mint this classifier in the receiving arena.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn mint(
        self,
        arena: &mut CoreArena,
    ) -> ValueTypeId
    {
        match self {
            Self::Integer => arena.value_type_base(BaseType::Integer),
            Self::Boolean => {
                let unit = arena.value_type_unit();
                arena.value_type_sum(&[unit, unit])
            },
            Self::Text => arena.value_type_base(BaseType::String),
            Self::Float64 => arena.value_type_base(BaseType::Float64),
        }
    }
}

/// The operator spelling, or a callable name without operator syntax.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Operator
{
    /// Called by its prelude name only.
    Named,
    /// A prefix operator.
    Prefix(&'static str),
    /// An infix operator.
    Infix(&'static str),
}

/// The first-order instruction evaluated by a native table row.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
enum Operation
{
    /// Return the first integer argument.
    First,
    /// Addition.
    Add,
    /// Subtraction.
    Sub,
    /// Multiplication.
    Mul,
    /// Truncating division.
    Div,
    /// Remainder with the dividend's sign.
    Mod,
    /// Arithmetic negation.
    Neg,
    /// Integer equality.
    Eq,
    /// Integer inequality.
    Ne,
    /// Strict ascending comparison.
    Lt,
    /// Ascending comparison including equality.
    Le,
    /// Strict descending comparison.
    Gt,
    /// Descending comparison including equality.
    Ge,
    /// Boolean conjunction.
    And,
    /// Boolean disjunction.
    Or,
    /// Boolean negation.
    Not,
    /// The first string followed by the second.
    Append,
    /// The natural exponential.
    Exp,
    /// An integer converted to the nearest floating-point number.
    FromInteger,
    /// A floating-point number rounded to the nearest integer, ties to even.
    Round,
}

/// A table-owned native primitive. Callers cannot manufacture a mismatched row.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Primitive(&'static Definition);

/// The immutable metadata and instruction shared by every occurrence of a row.
#[derive(Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct Definition
{
    /// The callable spelling, qualified when it belongs to a module.
    name: &'static str,
    /// Its operator syntax, when one exists.
    operator: Operator,
    /// The ordered argument classifiers.
    arguments: &'static [PrimitiveType],
    /// The returned classifier.
    result: PrimitiveType,
    /// The instruction selected by this row.
    operation: Operation,
}

/// The single native prelude table, including its operator spellings.
pub const PRELUDE: &[Primitive] = &[
    Primitive(&Definition {
        name: "prim.id",
        operator: Operator::Named,
        arguments: &[PrimitiveType::Integer],
        result: PrimitiveType::Integer,
        operation: Operation::First,
    }),
    Primitive(&Definition {
        name: "prim.const",
        operator: Operator::Named,
        arguments: &[PrimitiveType::Integer, PrimitiveType::Integer],
        result: PrimitiveType::Integer,
        operation: Operation::First,
    }),
    Primitive(&Definition {
        name: "add",
        operator: Operator::Infix("+"),
        arguments: &[PrimitiveType::Integer, PrimitiveType::Integer],
        result: PrimitiveType::Integer,
        operation: Operation::Add,
    }),
    Primitive(&Definition {
        name: "sub",
        operator: Operator::Infix("-"),
        arguments: &[PrimitiveType::Integer, PrimitiveType::Integer],
        result: PrimitiveType::Integer,
        operation: Operation::Sub,
    }),
    Primitive(&Definition {
        name: "mul",
        operator: Operator::Infix("*"),
        arguments: &[PrimitiveType::Integer, PrimitiveType::Integer],
        result: PrimitiveType::Integer,
        operation: Operation::Mul,
    }),
    Primitive(&Definition {
        name: "int.div",
        operator: Operator::Named,
        arguments: &[PrimitiveType::Integer, PrimitiveType::Integer],
        result: PrimitiveType::Integer,
        operation: Operation::Div,
    }),
    Primitive(&Definition {
        name: "int.mod",
        operator: Operator::Named,
        arguments: &[PrimitiveType::Integer, PrimitiveType::Integer],
        result: PrimitiveType::Integer,
        operation: Operation::Mod,
    }),
    Primitive(&Definition {
        name: "neg",
        operator: Operator::Prefix("-"),
        arguments: &[PrimitiveType::Integer],
        result: PrimitiveType::Integer,
        operation: Operation::Neg,
    }),
    Primitive(&Definition {
        name: "eq",
        operator: Operator::Infix("=="),
        arguments: &[PrimitiveType::Integer, PrimitiveType::Integer],
        result: PrimitiveType::Boolean,
        operation: Operation::Eq,
    }),
    Primitive(&Definition {
        name: "ne",
        operator: Operator::Infix("!="),
        arguments: &[PrimitiveType::Integer, PrimitiveType::Integer],
        result: PrimitiveType::Boolean,
        operation: Operation::Ne,
    }),
    Primitive(&Definition {
        name: "lt",
        operator: Operator::Infix("<"),
        arguments: &[PrimitiveType::Integer, PrimitiveType::Integer],
        result: PrimitiveType::Boolean,
        operation: Operation::Lt,
    }),
    Primitive(&Definition {
        name: "le",
        operator: Operator::Infix("<="),
        arguments: &[PrimitiveType::Integer, PrimitiveType::Integer],
        result: PrimitiveType::Boolean,
        operation: Operation::Le,
    }),
    Primitive(&Definition {
        name: "gt",
        operator: Operator::Infix(">"),
        arguments: &[PrimitiveType::Integer, PrimitiveType::Integer],
        result: PrimitiveType::Boolean,
        operation: Operation::Gt,
    }),
    Primitive(&Definition {
        name: "ge",
        operator: Operator::Infix(">="),
        arguments: &[PrimitiveType::Integer, PrimitiveType::Integer],
        result: PrimitiveType::Boolean,
        operation: Operation::Ge,
    }),
    Primitive(&Definition {
        name: "and",
        operator: Operator::Infix("&&"),
        arguments: &[PrimitiveType::Boolean, PrimitiveType::Boolean],
        result: PrimitiveType::Boolean,
        operation: Operation::And,
    }),
    Primitive(&Definition {
        name: "or",
        operator: Operator::Infix("||"),
        arguments: &[PrimitiveType::Boolean, PrimitiveType::Boolean],
        result: PrimitiveType::Boolean,
        operation: Operation::Or,
    }),
    Primitive(&Definition {
        name: "bool.not",
        operator: Operator::Named,
        arguments: &[PrimitiveType::Boolean],
        result: PrimitiveType::Boolean,
        operation: Operation::Not,
    }),
    Primitive(&Definition {
        name: "string.append",
        operator: Operator::Named,
        arguments: &[PrimitiveType::Text, PrimitiveType::Text],
        result: PrimitiveType::Text,
        operation: Operation::Append,
    }),
    Primitive(&Definition {
        name: "float64.add",
        operator: Operator::Named,
        arguments: &[PrimitiveType::Float64, PrimitiveType::Float64],
        result: PrimitiveType::Float64,
        operation: Operation::Add,
    }),
    Primitive(&Definition {
        name: "float64.sub",
        operator: Operator::Named,
        arguments: &[PrimitiveType::Float64, PrimitiveType::Float64],
        result: PrimitiveType::Float64,
        operation: Operation::Sub,
    }),
    Primitive(&Definition {
        name: "float64.mul",
        operator: Operator::Named,
        arguments: &[PrimitiveType::Float64, PrimitiveType::Float64],
        result: PrimitiveType::Float64,
        operation: Operation::Mul,
    }),
    Primitive(&Definition {
        name: "float64.div",
        operator: Operator::Named,
        arguments: &[PrimitiveType::Float64, PrimitiveType::Float64],
        result: PrimitiveType::Float64,
        operation: Operation::Div,
    }),
    Primitive(&Definition {
        name: "float64.neg",
        operator: Operator::Named,
        arguments: &[PrimitiveType::Float64],
        result: PrimitiveType::Float64,
        operation: Operation::Neg,
    }),
    Primitive(&Definition {
        name: "float64.exp",
        operator: Operator::Named,
        arguments: &[PrimitiveType::Float64],
        result: PrimitiveType::Float64,
        operation: Operation::Exp,
    }),
    Primitive(&Definition {
        name: "float64.eq",
        operator: Operator::Named,
        arguments: &[PrimitiveType::Float64, PrimitiveType::Float64],
        result: PrimitiveType::Boolean,
        operation: Operation::Eq,
    }),
    Primitive(&Definition {
        name: "float64.ne",
        operator: Operator::Named,
        arguments: &[PrimitiveType::Float64, PrimitiveType::Float64],
        result: PrimitiveType::Boolean,
        operation: Operation::Ne,
    }),
    Primitive(&Definition {
        name: "float64.lt",
        operator: Operator::Named,
        arguments: &[PrimitiveType::Float64, PrimitiveType::Float64],
        result: PrimitiveType::Boolean,
        operation: Operation::Lt,
    }),
    Primitive(&Definition {
        name: "float64.le",
        operator: Operator::Named,
        arguments: &[PrimitiveType::Float64, PrimitiveType::Float64],
        result: PrimitiveType::Boolean,
        operation: Operation::Le,
    }),
    Primitive(&Definition {
        name: "float64.gt",
        operator: Operator::Named,
        arguments: &[PrimitiveType::Float64, PrimitiveType::Float64],
        result: PrimitiveType::Boolean,
        operation: Operation::Gt,
    }),
    Primitive(&Definition {
        name: "float64.ge",
        operator: Operator::Named,
        arguments: &[PrimitiveType::Float64, PrimitiveType::Float64],
        result: PrimitiveType::Boolean,
        operation: Operation::Ge,
    }),
    Primitive(&Definition {
        name: "float64.from_integer",
        operator: Operator::Named,
        arguments: &[PrimitiveType::Integer],
        result: PrimitiveType::Float64,
        operation: Operation::FromInteger,
    }),
    Primitive(&Definition {
        name: "float64.round",
        operator: Operator::Named,
        arguments: &[PrimitiveType::Float64],
        result: PrimitiveType::Integer,
        operation: Operation::Round,
    }),
];

/// A native scalar supplied to or returned from the table evaluator.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Scalar<Integer = IntegerLiteral, Text = StringLiteral>
{
    /// An exact integer, in the syntax's canonical decimal representation.
    Integer(Integer),
    /// A boolean's injection side; left is true.
    Boolean(Side),
    /// A string.
    Text(Text),
    /// An IEEE 754 binary64 number, its NaN canonical.
    Float64(Float64Literal),
}

/// Why a native evaluation cannot produce its result.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum PrimitiveError
{
    /// The number of arguments differs from the row's signature.
    Arity,
    /// An argument is not of the row's classifier.
    ArgumentType,
    /// Integer division or remainder was supplied a zero divisor.
    DivisionByZero,
    /// A numeric conversion violated canonical decimal representation.
    InvalidInteger,
    /// A floating-point number with no integer nearest it: an infinity or a
    /// NaN.
    NotFinite,
}

impl fmt::Display for PrimitiveError
{
    /// Render the native failure.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        f.write_str(match *self {
            Self::Arity => "native primitive argument count mismatch",
            Self::ArgumentType => "native primitive argument type mismatch",
            Self::DivisionByZero => "native integer division by zero",
            Self::InvalidInteger => "invalid native integer representation",
            Self::NotFinite => "native floating-point number is not finite",
        })
    }
}

impl core::error::Error for PrimitiveError
{
}

impl Primitive
{
    /// Borrow the qualified prelude spelling.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn name(self) -> PrimitiveName
    {
        PrimitiveName(self.0.name)
    }

    /// The operator spelling this row owns.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn operator(self) -> Operator
    {
        self.0.operator
    }

    /// The ordered argument classifiers.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn arguments(self) -> &'static [PrimitiveType]
    {
        self.0.arguments
    }

    /// The result classifier.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn result(self) -> PrimitiveType
    {
        self.0.result
    }

    /// Mint the curried computation signature described by this row.
    ///
    /// # Specification
    /// - ensures: one arrow per ordered argument, ending in the result's
    ///   returner.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — every row's curried signature has the expected
    ///   argument and result classifiers.
    /// - witness: `primitive::tests::table_signatures_and_currying_agree`
    #[spec(ensures: |ret| arena.comp_type(ret).is_some())]
    #[inline]
    #[must_use]
    pub fn declared_type(
        self,
        arena: &mut CoreArena,
    ) -> CompTypeId
    {
        let result = self.0.result.mint(arena);
        let mut result = arena.comp_type_returner(result);
        for argument in self.0.arguments.iter().rev() {
            let domain = argument.mint(arena);
            result = arena.comp_type_arrow(domain, result);
        }
        result
    }

    /// Mint a thunked curried primitive using ordinary core lambdas.
    ///
    /// # Specification
    /// - ensures: the saturated operation receives arguments left to right,
    ///   including after partial application.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — asymmetric binary arguments distinguish reversed
    ///   binder order.
    /// - witness: `primitive::tests::table_signatures_and_currying_agree`
    #[spec(ensures: |ret| arena.value(ret).is_some())]
    #[inline]
    #[must_use]
    pub fn thunk(
        self,
        arena: &mut CoreArena,
    ) -> ValueId
    {
        let last = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
        let arguments = if self.0.arguments.len() == 1 {
            Arguments::Unary(last)
        }
        else {
            let first = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(1_u32));
            Arguments::Binary([first, last])
        };
        let mut body = arena.computation_primitive(self, arguments);
        for _ in self.0.arguments {
            body = arena.computation_lambda(body);
        }
        arena.value_primitive(self, body)
    }

    /// Evaluate a saturated application on canonical native scalars.
    ///
    /// # Specification
    /// - requires: nothing; unchecked callers receive typed refusals.
    /// - ensures: exact integer arithmetic; division truncates toward zero,
    ///   remainder has the dividend's sign; booleans use left for true; an
    ///   append is the first string's characters followed by the second's;
    ///   floating-point rows are IEEE 754 binary64, ties to even, with `exp`
    ///   from `libm` and every NaN canonical.
    /// - fails: arity before argument classifiers, then zero division; invalid
    ///   decimal conversion is named separately; a floating-point number with
    ///   no nearest integer is not finite.
    /// - panics: none.
    ///
    /// # Errors
    /// [`PrimitiveError`] preserves argument, arity, division and
    /// representation failures, and a floating-point number rounded to an
    /// integer that is not finite.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — asymmetric signed operands, zero divisors, integers
    ///   beyond machine width, every boolean pair and two strings appended in
    ///   both orders distinguish operation and error drift.
    /// - witness: `primitive::tests::exact_arithmetic_and_errors`
    /// - witness: `primitive::tests::comparisons_and_booleans`
    /// - witness: `primitive::tests::an_append_writes_the_first_string_then_the_second`
    /// - witness: `primitive::tests::floating_point_rows_are_ieee_binary64`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |value| value.classifier() == self.0.result))]
    #[inline]
    pub fn evaluate(
        self,
        arguments: &[Scalar<&IntegerLiteral, &StringLiteral>],
    ) -> Result<Scalar, PrimitiveError>
    {
        if arguments.len() != self.0.arguments.len() {
            return Err(PrimitiveError::Arity);
        }
        if arguments
            .iter()
            .zip(self.0.arguments)
            .any(|(value, expected)| value.classifier() != *expected)
        {
            return Err(PrimitiveError::ArgumentType);
        }
        let first = arguments.first().ok_or(PrimitiveError::Arity)?;
        if self.0.operation == Operation::First {
            return Ok(match *first {
                Scalar::Integer(integer) => Scalar::Integer(integer.clone()),
                Scalar::Boolean(side) => Scalar::Boolean(side),
                Scalar::Text(text) => Scalar::Text(text.clone()),
                Scalar::Float64(float) => Scalar::Float64(float),
            });
        }
        // Only `string.append` takes text, the classifiers say: a text
        // operand is its first.
        if let Scalar::Text(left) = *first {
            let Some(&Scalar::Text(right)) = arguments.get(1)
            else {
                return Err(PrimitiveError::ArgumentType);
            };
            let (left, right): (&str, &str) = (left.as_ref(), right.as_ref());
            let mut appended = String::with_capacity(left.len().saturating_add(right.len()));
            appended.push_str(left);
            appended.push_str(right);
            return Ok(Scalar::Text(StringLiteral::new(appended)));
        }
        if let Scalar::Float64(left) = *first {
            return float64(self.0.operation, left, arguments);
        }
        if self.0.operation == Operation::FromInteger {
            let integer = first.integer()?;
            let value = alloc::format!("{integer}")
                .parse::<f64>()
                .map_err(|_invalid_decimal| PrimitiveError::InvalidInteger)?;
            return Ok(Scalar::Float64(Float64Literal::from(value)));
        }
        if let Scalar::Boolean(left) = *first {
            let right = match arguments.get(1) {
                Some(&Scalar::Boolean(side)) => side,
                _ => Side::Right,
            };
            let answer = match self.0.operation {
                Operation::And => left == Side::Left && right == Side::Left,
                Operation::Or => left == Side::Left || right == Side::Left,
                Operation::Not => left != Side::Left,
                Operation::First
                | Operation::Add
                | Operation::Sub
                | Operation::Mul
                | Operation::Div
                | Operation::Mod
                | Operation::Neg
                | Operation::Eq
                | Operation::Ne
                | Operation::Lt
                | Operation::Le
                | Operation::Gt
                | Operation::Ge
                | Operation::Append
                | Operation::Exp
                | Operation::FromInteger
                | Operation::Round => return Err(PrimitiveError::ArgumentType),
            };
            return Ok(Scalar::Boolean(if answer {
                Side::Left
            }
            else {
                Side::Right
            }));
        }
        let left = first.integer()?;
        if self.0.operation == Operation::Neg {
            return scalar(&left.neg());
        }
        let right = arguments.get(1).ok_or(PrimitiveError::Arity)?;
        let right = right.integer()?;
        let answer = match self.0.operation {
            Operation::Add => return scalar(&left.add(right)),
            Operation::Sub => return scalar(&left.sub(right)),
            Operation::Mul => return scalar(&left.mul(right)),
            Operation::Div => {
                let quotient = left
                    .checked_div(&right)
                    .ok_or(PrimitiveError::DivisionByZero)?;
                return scalar(&quotient);
            },
            Operation::Mod => {
                if right == BigInt::ZERO {
                    return Err(PrimitiveError::DivisionByZero);
                }
                return scalar(&left.rem(right));
            },
            Operation::Eq => left == right,
            Operation::Ne => left != right,
            Operation::Lt => left < right,
            Operation::Le => left <= right,
            Operation::Gt => left > right,
            Operation::Ge => left >= right,
            Operation::First
            | Operation::Neg
            | Operation::And
            | Operation::Or
            | Operation::Not
            | Operation::Append
            | Operation::Exp
            | Operation::FromInteger
            | Operation::Round => {
                return Err(PrimitiveError::ArgumentType);
            },
        };
        Ok(Scalar::Boolean(if answer {
            Side::Left
        }
        else {
            Side::Right
        }))
    }
}

/// A borrowed prelude spelling, kept distinct from arbitrary source text.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct PrimitiveName(&'static str);

impl AsRef<str> for PrimitiveName
{
    /// Borrow the spelling.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn as_ref(&self) -> &str
    {
        self.0
    }
}

impl From<PrimitiveName> for &'static str
{
    /// Expose the table's static source spelling.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(name: PrimitiveName) -> Self
    {
        name.0
    }
}

impl<Integer, Text> Scalar<Integer, Text>
{
    /// The native classifier of this scalar.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn classifier(&self) -> PrimitiveType
    {
        match *self {
            Self::Integer(_) => PrimitiveType::Integer,
            Self::Boolean(_) => PrimitiveType::Boolean,
            Self::Text(_) => PrimitiveType::Text,
            Self::Float64(_) => PrimitiveType::Float64,
        }
    }
}

impl<Integer: core::borrow::Borrow<IntegerLiteral>, Text> Scalar<Integer, Text>
{
    /// Convert the canonical integer payload into the arithmetic
    /// representation.
    ///
    /// # Specification
    /// - ensures: preserves magnitude and sign exactly.
    /// - fails: non-integers and invalid decimal representations are
    ///   distinguished.
    /// - panics: none.
    ///
    /// # Errors
    /// [`PrimitiveError::ArgumentType`] or [`PrimitiveError::InvalidInteger`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — negative and beyond-machine-width inputs survive
    ///   arithmetic unchanged where required.
    /// - witness: `primitive::tests::exact_arithmetic_and_errors`
    #[spec(ensures: |ret| ret.is_err() || self.classifier() == PrimitiveType::Integer)]
    fn integer(&self) -> Result<BigInt, PrimitiveError>
    {
        let Self::Integer(ref value) = *self
        else {
            return Err(PrimitiveError::ArgumentType);
        };
        let value = value.borrow();
        let magnitude = value
            .magnitude()
            .as_ref()
            .parse::<BigInt>()
            .map_err(|_invalid_decimal| PrimitiveError::InvalidInteger)?;
        Ok(if value.sign() == Sign::Negative {
            magnitude.neg()
        }
        else {
            magnitude
        })
    }
}

impl Scalar
{
    /// Borrow an operand without cloning its decimal or text payload.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn borrowed(&self) -> Scalar<&IntegerLiteral, &StringLiteral>
    {
        match *self {
            Self::Integer(ref value) => Scalar::Integer(value),
            Self::Boolean(side) => Scalar::Boolean(side),
            Self::Text(ref text) => Scalar::Text(text),
            Self::Float64(float) => Scalar::Float64(float),
        }
    }

    /// Mint a scalar as a core value.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn mint(
        self,
        arena: &mut CoreArena,
    ) -> ValueId
    {
        match self {
            Self::Integer(integer) => arena.value_literal(Literal::Integer(integer)),
            Self::Boolean(side) => {
                let unit = arena.value_unit();
                arena.value_injection(side.into(), unit)
            },
            Self::Text(text) => arena.value_literal(Literal::Text(text)),
            Self::Float64(float) => arena.value_literal(Literal::Float64(float)),
        }
    }
}

/// Convert an arithmetic result back into canonical syntax.
///
/// # Specification
/// - ensures: preserves exact magnitude and canonicalizes zero's sign.
/// - fails: a non-decimal backend representation is refused.
/// - panics: none.
///
/// # Errors
/// [`PrimitiveError::InvalidInteger`] for a malformed backend decimal result.
///
/// # Adequacy
/// - hypothesis: L3 — negative, zero and beyond-machine-width results
///   distinguish sign and truncation errors.
/// - witness: `primitive::tests::exact_arithmetic_and_errors`
#[spec(ensures: |ret| matches!(ret, Ok(Scalar::Integer(_)) | Err(PrimitiveError::InvalidInteger)))]
fn scalar(value: &BigInt) -> Result<Scalar, PrimitiveError>
{
    let sign = if value.sign() == num_bigint::Sign::Minus {
        Sign::Negative
    }
    else {
        Sign::NonNegative
    };
    let magnitude = Magnitude::from_decimal_text(value.magnitude().to_str_radix(10))
        .ok_or(PrimitiveError::InvalidInteger)?;
    Ok(Scalar::Integer(IntegerLiteral::new(sign, magnitude)))
}

/// Evaluate a floating-point row whose first operand is `left` and whose
/// operands are `arguments`.
///
/// # Specification
/// - requires: `operation` belongs to a row whose first classifier is
///   [`PrimitiveType::Float64`].
/// - ensures: IEEE 754 binary64 arithmetic and comparison, round to nearest,
///   ties to even; `exp` is `libm`'s; a rounding is the nearest integer, ties
///   to even; every NaN result is the canonical NaN.
/// - fails: [`PrimitiveError::NotFinite`] when rounding an infinity or a NaN;
///   [`PrimitiveError::ArgumentType`] for a second operand that is no
///   floating-point number, or an operation no floating-point row names.
/// - panics: none.
///
/// # Errors
/// [`PrimitiveError::NotFinite`] or [`PrimitiveError::ArgumentType`].
///
/// # Adequacy
/// - hypothesis: L3 — sums, quotients by zero, a NaN compared with itself,
///   `exp` at zero and at one (`libm`'s double, pinned by its bits), ties
///   rounded to even and an infinity rounded each meet their answer or named
///   refusal.
/// - witness: `primitive::tests::floating_point_rows_are_ieee_binary64`
#[spec(ensures: |ret| ret.is_ok() || matches!(ret, Err(PrimitiveError::NotFinite | PrimitiveError::ArgumentType | PrimitiveError::InvalidInteger)))]
fn float64(
    operation: Operation,
    left: Float64Literal,
    arguments: &[Scalar<&IntegerLiteral, &StringLiteral>],
) -> Result<Scalar, PrimitiveError>
{
    let left = f64::from(left);
    let float = |value: f64| Ok(Scalar::Float64(Float64Literal::from(value)));
    match operation {
        Operation::Neg => return float(-left),
        Operation::Exp => return float(libm::exp(left)),
        Operation::Round => {
            if !left.is_finite() {
                return Err(PrimitiveError::NotFinite);
            }
            let rounded = libm::rint(left);
            let sign = if rounded < 0.0_f64 {
                Sign::Negative
            }
            else {
                Sign::NonNegative
            };
            let magnitude =
                Magnitude::from_decimal_text(alloc::format!("{:.0}", libm::fabs(rounded)))
                    .ok_or(PrimitiveError::InvalidInteger)?;
            return Ok(Scalar::Integer(IntegerLiteral::new(sign, magnitude)));
        },
        Operation::First
        | Operation::Add
        | Operation::Sub
        | Operation::Mul
        | Operation::Div
        | Operation::Mod
        | Operation::Eq
        | Operation::Ne
        | Operation::Lt
        | Operation::Le
        | Operation::Gt
        | Operation::Ge
        | Operation::And
        | Operation::Or
        | Operation::Not
        | Operation::Append
        | Operation::FromInteger => {},
    }
    let Some(&Scalar::Float64(right)) = arguments.get(1)
    else {
        return Err(PrimitiveError::ArgumentType);
    };
    let right = f64::from(right);
    let answer = match operation {
        Operation::Add => return float(left + right),
        Operation::Sub => return float(left - right),
        Operation::Mul => return float(left * right),
        Operation::Div => return float(left / right),
        // IEEE equality: the zeros are equal, and a NaN equals nothing.
        Operation::Eq => left.partial_cmp(&right) == Some(Ordering::Equal),
        Operation::Ne => left.partial_cmp(&right) != Some(Ordering::Equal),
        Operation::Lt => left < right,
        Operation::Le => left <= right,
        Operation::Gt => left > right,
        Operation::Ge => left >= right,
        Operation::First
        | Operation::Mod
        | Operation::Neg
        | Operation::And
        | Operation::Or
        | Operation::Not
        | Operation::Append
        | Operation::Exp
        | Operation::FromInteger
        | Operation::Round => return Err(PrimitiveError::ArgumentType),
    };
    Ok(Scalar::Boolean(if answer {
        Side::Left
    }
    else {
        Side::Right
    }))
}

#[cfg(test)]
mod tests;
