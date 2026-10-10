//! The native prelude: one table for names, signatures and exact evaluation.

use core::fmt;
use core::ops::Add as _;
use core::ops::Mul as _;
use core::ops::Neg as _;
use core::ops::Rem as _;
use core::ops::Sub as _;

use anodized::spec;
use gandr_kernel_term::BaseType;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::IntegerLiteral;
use gandr_kernel_term::Literal;
use gandr_kernel_term::Magnitude;
use gandr_kernel_term::Side;
use gandr_kernel_term::Sign;
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
            | Self::Unary(ref value) => core::slice::from_ref(value),
            | Self::Binary(ref values) => values,
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
            | Self::Unary(ref mut value) => core::slice::from_mut(value),
            | Self::Binary(ref mut values) => values,
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
            | Self::Integer => arena.value_type_base(BaseType::Integer),
            | Self::Boolean => {
                let unit = arena.value_type_unit();
                arena.value_type_sum(unit, unit)
            },
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
];

/// A native scalar supplied to or returned from the table evaluator.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Scalar<Integer = IntegerLiteral>
{
    /// An exact integer, in the syntax's canonical decimal representation.
    Integer(Integer),
    /// A boolean's injection side; left is true.
    Boolean(Side),
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
            | Self::Arity => "native primitive argument count mismatch",
            | Self::ArgumentType => "native primitive argument type mismatch",
            | Self::DivisionByZero => "native integer division by zero",
            | Self::InvalidInteger => "invalid native integer representation",
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
    ///   remainder has the dividend's sign; booleans use left for true.
    /// - fails: arity before argument classifiers, then zero division; invalid
    ///   decimal conversion is named separately.
    /// - panics: none.
    ///
    /// # Errors
    /// [`PrimitiveError`] preserves argument, arity, division and
    /// representation failures.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — asymmetric signed operands, zero divisors, integers
    ///   beyond machine width and every boolean pair distinguish operation and
    ///   error drift.
    /// - witness: `primitive::tests::exact_arithmetic_and_errors`
    /// - witness: `primitive::tests::comparisons_and_booleans`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |value| value.classifier() == self.0.result))]
    #[inline]
    pub fn evaluate(
        self,
        arguments: &[Scalar<&IntegerLiteral>],
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
                | Scalar::Integer(integer) => Scalar::Integer(integer.clone()),
                | Scalar::Boolean(side) => Scalar::Boolean(side),
            });
        }
        if let Scalar::Boolean(left) = *first {
            let right = match arguments.get(1) {
                | Some(&Scalar::Boolean(side)) => side,
                | _ => Side::Right,
            };
            let answer = match self.0.operation {
                | Operation::And => left == Side::Left && right == Side::Left,
                | Operation::Or => left == Side::Left || right == Side::Left,
                | Operation::Not => left != Side::Left,
                | _ => return Err(PrimitiveError::ArgumentType),
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
            | Operation::Add => return scalar(&left.add(right)),
            | Operation::Sub => return scalar(&left.sub(right)),
            | Operation::Mul => return scalar(&left.mul(right)),
            | Operation::Div => {
                let quotient = left
                    .checked_div(&right)
                    .ok_or(PrimitiveError::DivisionByZero)?;
                return scalar(&quotient);
            },
            | Operation::Mod => {
                if right == BigInt::ZERO {
                    return Err(PrimitiveError::DivisionByZero);
                }
                return scalar(&left.rem(right));
            },
            | Operation::Eq => left == right,
            | Operation::Ne => left != right,
            | Operation::Lt => left < right,
            | Operation::Le => left <= right,
            | Operation::Gt => left > right,
            | Operation::Ge => left >= right,
            | Operation::First
            | Operation::Neg
            | Operation::And
            | Operation::Or
            | Operation::Not => return Err(PrimitiveError::ArgumentType),
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

impl<Integer> Scalar<Integer>
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
            | Self::Integer(_) => PrimitiveType::Integer,
            | Self::Boolean(_) => PrimitiveType::Boolean,
        }
    }
}

impl<Integer: core::borrow::Borrow<IntegerLiteral>> Scalar<Integer>
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
    /// Borrow an operand without cloning its decimal payload.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn borrowed(&self) -> Scalar<&IntegerLiteral>
    {
        match *self {
            | Self::Integer(ref value) => Scalar::Integer(value),
            | Self::Boolean(side) => Scalar::Boolean(side),
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
            | Self::Integer(integer) => arena.value_literal(Literal::Integer(integer)),
            | Self::Boolean(side) => {
                let unit = arena.value_unit();
                arena.value_injection(side, unit)
            },
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

#[cfg(test)]
mod tests
{
    use super::*;
    use crate::CompType;
    use crate::Computation;
    use crate::Value;
    use crate::ValueType;
    use crate::rewrite::instantiate_value;

    /// A fixture's signed decimal spelling.
    #[repr(transparent)]
    #[derive(Clone, Copy)]
    struct Digits(&'static str);

    /// Read a fixture's canonical signed integer.
    ///
    /// # Specification
    /// trivial.
    fn integer(digits: Digits) -> Scalar
    {
        let (sign, text) = digits
            .0
            .strip_prefix('-')
            .map_or((Sign::NonNegative, digits.0), |magnitude| {
                (Sign::Negative, magnitude)
            });
        Scalar::Integer(IntegerLiteral::new(
            sign,
            Magnitude::from_decimal_text(text.into()).expect("decimal fixture"),
        ))
    }

    /// Look up a fixture's native function.
    ///
    /// # Specification
    /// trivial.
    fn named(name: PrimitiveName) -> Primitive
    {
        PRELUDE
            .iter()
            .copied()
            .find(|primitive| primitive.name() == name)
            .expect("native fixture name")
    }

    #[test]
    fn exact_arithmetic_and_errors()
    {
        for (name, left, right, expected) in [
            (
                "add",
                "99999999999999999999999999999999999999",
                "1",
                "100000000000000000000000000000000000000",
            ),
            ("sub", "7", "11", "-4"),
            (
                "mul",
                "-100000000000000000000",
                "100000000000000000000",
                "-10000000000000000000000000000000000000000",
            ),
            ("int.div", "-19", "4", "-4"),
            ("int.mod", "-19", "4", "-3"),
            ("prim.const", "23", "45", "23"),
        ] {
            let operands = [integer(Digits(left)), integer(Digits(right))];
            assert_eq!(
                named(PrimitiveName(name)).evaluate(&operands.each_ref().map(Scalar::borrowed)),
                Ok(integer(Digits(expected))),
                "{name}"
            );
        }
        for (name, input, expected) in [("neg", "-7", "7"), ("prim.id", "-8", "-8")] {
            let operand = integer(Digits(input));
            assert_eq!(
                named(PrimitiveName(name)).evaluate(&[operand.borrowed()]),
                Ok(integer(Digits(expected)))
            );
        }
        let zero = integer(Digits("0"));
        let one = integer(Digits("1"));
        assert_eq!(
            named(PrimitiveName("neg")).evaluate(&[zero.borrowed()]),
            Ok(zero.clone())
        );
        for name in ["int.div", "int.mod"] {
            assert_eq!(
                named(PrimitiveName(name)).evaluate(&[one.borrowed(), zero.borrowed()]),
                Err(PrimitiveError::DivisionByZero)
            );
        }
        let add = named(PrimitiveName("add"));
        assert_eq!(add.evaluate(&[]), Err(PrimitiveError::Arity));
        assert_eq!(
            add.evaluate(&[Scalar::Boolean(Side::Left)]),
            Err(PrimitiveError::Arity)
        );
        assert_eq!(
            add.evaluate(&[one.borrowed(), Scalar::Boolean(Side::Left)]),
            Err(PrimitiveError::ArgumentType)
        );
    }

    #[test]
    fn comparisons_and_booleans()
    {
        let less = integer(Digits("-4"));
        let more = integer(Digits("9"));
        for (name, expected) in [
            ("eq", Side::Right),
            ("ne", Side::Left),
            ("lt", Side::Left),
            ("le", Side::Left),
            ("gt", Side::Right),
            ("ge", Side::Right),
        ] {
            assert_eq!(
                named(PrimitiveName(name)).evaluate(&[less.borrowed(), more.borrowed()]),
                Ok(Scalar::Boolean(expected)),
                "{name}"
            );
        }
        for (name, expected) in [
            ("eq", Side::Left),
            ("ne", Side::Right),
            ("lt", Side::Right),
            ("le", Side::Left),
            ("gt", Side::Right),
            ("ge", Side::Left),
        ] {
            assert_eq!(
                named(PrimitiveName(name)).evaluate(&[less.borrowed(), less.borrowed()]),
                Ok(Scalar::Boolean(expected)),
                "{name} equality boundary"
            );
        }
        for (left, right, conjunction, disjunction) in [
            (Side::Left, Side::Left, Side::Left, Side::Left),
            (Side::Left, Side::Right, Side::Right, Side::Left),
            (Side::Right, Side::Left, Side::Right, Side::Left),
            (Side::Right, Side::Right, Side::Right, Side::Right),
        ] {
            let arguments = [Scalar::Boolean(left), Scalar::Boolean(right)];
            assert_eq!(
                named(PrimitiveName("and")).evaluate(&arguments),
                Ok(Scalar::Boolean(conjunction))
            );
            assert_eq!(
                named(PrimitiveName("or")).evaluate(&arguments),
                Ok(Scalar::Boolean(disjunction))
            );
        }
        for (input, expected) in [(Side::Left, Side::Right), (Side::Right, Side::Left)] {
            assert_eq!(
                named(PrimitiveName("bool.not")).evaluate(&[Scalar::Boolean(input)]),
                Ok(Scalar::Boolean(expected))
            );
        }
    }

    #[test]
    fn table_signatures_and_currying_agree()
    {
        let mut arena = CoreArena::new();
        let primitive = named(PrimitiveName("sub"));
        let mut signature = primitive.declared_type(&mut arena);
        let thunk = primitive.thunk(&mut arena);
        let Some(&Value::Primitive { mut body, .. }) = arena.value(thunk)
        else {
            panic!("native thunk");
        };
        for input in ["19", "7"] {
            let Some(&CompType::Arrow { domain, codomain }) = arena.comp_type(signature)
            else {
                panic!("curried arrow");
            };
            assert_eq!(
                arena.value_type(domain),
                Some(&ValueType::Base(BaseType::Integer))
            );
            signature = codomain;
            let Some(&Computation::Lambda(inner)) = arena.computation(body)
            else {
                panic!("curried lambda");
            };
            let wrapper = arena.value_thunk(inner);
            let argument = integer(Digits(input)).mint(&mut arena);
            let applied = instantiate_value(&mut arena, wrapper, argument);
            let Some(&Value::Thunk(inner)) = arena.value(applied)
            else {
                panic!("substituted thunk");
            };
            body = inner;
        }
        let Some(&CompType::Returner(result)) = arena.comp_type(signature)
        else {
            panic!("returner");
        };
        assert_eq!(
            arena.value_type(result),
            Some(&ValueType::Base(BaseType::Integer))
        );
        let Some(&Computation::Primitive {
            primitive,
            arguments: Arguments::Binary(arguments),
        }) = arena.computation(body)
        else {
            panic!("saturated primitive");
        };
        let operands = arguments.map(|argument| match arena.value(argument) {
            | Some(&Value::Literal(Literal::Integer(ref integer))) => Scalar::Integer(integer),
            | _ => panic!("substituted operand"),
        });
        assert_eq!(primitive.evaluate(&operands), Ok(integer(Digits("12"))));
    }
}
