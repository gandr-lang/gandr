//! Fixtures the unit tests share: scratch directories and small programs.

use alloc::format;
use alloc::string::String;
use alloc::vec::Vec;
use std::path::Path;
use std::path::PathBuf;

use gandr_core_checker::CheckBudget;
use gandr_core_checker::Declaration;
use gandr_core_checker::OriginToken;
use gandr_core_checker::body;
use gandr_core_checker::signature;
use gandr_core_term::CoreArena;
use gandr_core_term::ValueId;
use gandr_core_term::ValueTypeId;
use gandr_core_term::Zone;
use gandr_kernel_strata::Level;
use gandr_kernel_strata::LevelConstant;
use gandr_kernel_strata::LevelVar;
use gandr_kernel_strata::LevelVarIndex;
use gandr_kernel_term::BaseType;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::FractionDigits;
use gandr_kernel_term::IntegerLiteral;
use gandr_kernel_term::Literal;
use gandr_kernel_term::Magnitude;
use gandr_kernel_term::NumericLiteral;
use gandr_kernel_term::Side;
use gandr_kernel_term::Sign;
use gandr_kernel_term::StringLiteral;
use quenchant_shape::shape::Maybe;

use crate::checkpoint::Checkpoints;
use crate::checkpoint::check_program;
use crate::region::Item;
use crate::region::ItemKey;
use crate::region::Program;

/// A scratch directory's label, unique among the tests.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
pub struct Label(pub &'static str);

/// An item key of a fixture.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
pub struct Key(pub &'static str);

/// An integer literal's decimal digits.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
pub struct Digits(pub &'static str);

/// How many unrelated nodes an arena holds before a fixture's own, so two
/// builds of one program differ in every id.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
pub struct Noise(pub usize);

/// An item's admission position in a fixture program.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
pub struct Position(pub usize);

/// A directory under the system temporary directory, emptied on creation and
/// removed on drop.
#[repr(transparent)]
#[derive(Debug)]
pub struct Scratch(PathBuf);

impl Scratch
{
    /// The scratch directory of `label` for this process.
    ///
    /// # Specification
    /// trivial.
    pub fn new(label: Label) -> Self
    {
        let path = std::env::temp_dir().join(format!(
            "gandr-core-incremental-{}-{}",
            std::process::id(),
            label.0
        ));
        drop(std::fs::remove_dir_all(&path));
        Self(path)
    }

    /// The directory's path.
    ///
    /// # Specification
    /// trivial.
    pub fn path(&self) -> &Path
    {
        &self.0
    }

    /// The names of the directory's entries, sorted.
    ///
    /// # Specification
    /// trivial.
    pub fn entries(&self) -> Vec<String>
    {
        let mut names: Vec<String> = std::fs::read_dir(&self.0)
            .expect("the scratch directory is readable")
            .map(|entry| {
                entry
                    .expect("a readable entry")
                    .file_name()
                    .to_string_lossy()
                    .into_owned()
            })
            .collect();
        names.sort();
        names
    }
}

impl Drop for Scratch
{
    /// Remove the directory.
    ///
    /// # Specification
    /// trivial.
    fn drop(&mut self)
    {
        drop(std::fs::remove_dir_all(&self.0));
    }
}

/// An arena holding `noise` unrelated nodes of every sort.
///
/// # Specification
/// trivial.
pub fn noisy(noise: Noise) -> CoreArena
{
    let mut arena = CoreArena::new();
    for _ in 0 .. noise.0 {
        let unit = arena.value_unit();
        let returned = arena.computation_return(unit);
        let _thunk = arena.value_thunk(returned);
        let unit_type = arena.value_type_unit();
        let _returner = arena.comp_type_returner(unit_type);
    }
    arena
}

/// The integer literal of `digits`.
///
/// # Specification
/// trivial.
pub fn integer(digits: Digits) -> Literal
{
    Literal::Integer(IntegerLiteral::new(
        Sign::NonNegative,
        Magnitude::from_decimal_text(String::from(digits.0)).expect("decimal digits"),
    ))
}

/// One declaration at `position`.
///
/// # Specification
/// trivial.
pub fn declaration(
    position: Position,
    signature: Maybe<ValueTypeId, signature::Absent>,
    body: Maybe<ValueId, body::Absent>,
) -> Declaration
{
    Declaration::new(
        ConstantIndex::from(position.0),
        signature,
        body,
        OriginToken::from(position.0),
    )
}

/// The program of unsigned items `key = digits`, in order, over `arena`.
///
/// # Specification
/// trivial.
pub fn integers(
    mut arena: CoreArena,
    entries: &[(Key, Digits)],
) -> Program
{
    let items = entries
        .iter()
        .enumerate()
        .map(|(position, &(key, digits))| {
            let literal = arena.value_literal(integer(digits));
            Item::new(
                ItemKey::from(key.0),
                declaration(
                    Position(position),
                    Maybe::Absent(signature::Absent::Unsigned),
                    Maybe::Present(literal),
                ),
            )
        })
        .collect();
    Program::new(arena, items).expect("positions ascend")
}

/// The checkpoints of a batch run over `program`.
///
/// # Specification
/// trivial.
pub fn checked(program: &mut Program) -> Checkpoints
{
    check_program(program, CheckBudget::DEFAULT)
        .expect("the order builds")
        .checkpoints()
        .clone()
}

/// A program holding every former of the core vocabulary and reaching every
/// verdict and refusal the fragment can, with a reader whose support holds a
/// structured type; built after `noise` unrelated nodes.
///
/// # Specification
/// trivial.
pub fn every_former(noise: Noise) -> Program
{
    let mut arena = noisy(noise);
    let unsigned = || Maybe::Absent(signature::Absent::Unsigned);
    let hole = || Maybe::Absent(body::Absent::Hole);
    let mut items: Vec<Item> = Vec::new();
    let mut push = |key: &str, signature, body| {
        let position = items.len();
        items.push(Item::new(
            ItemKey::from(key),
            declaration(Position(position), signature, body),
        ));
    };

    // 0: (Integer × (String + Numeric)) over a pair and an injection: out of
    // the fragment, its content complete.
    let integer_type = arena.value_type_base(BaseType::Integer);
    let string_type = arena.value_type_base(BaseType::String);
    let numeric_type = arena.value_type_base(BaseType::Numeric);
    let sum = arena.value_type_sum(string_type, numeric_type);
    let product = arena.value_type_product(integer_type, sum);
    let negative = arena.value_literal(Literal::Integer(IntegerLiteral::new(
        Sign::Negative,
        Magnitude::from_decimal_text(String::from("7")).expect("decimal digits"),
    )));
    let numeric = arena.value_literal(Literal::Numeric(NumericLiteral::new(
        Sign::NonNegative,
        Magnitude::from_decimal_text(String::from("3")).expect("decimal digits"),
        FractionDigits::from_decimal_text(String::from("25")).expect("decimal digits"),
    )));
    let injected = arena.value_injection(Side::Right, numeric);
    let pair = arena.value_pair(negative, injected);
    push("data", Maybe::Present(product), Maybe::Present(pair));

    // 1: U (Integer → F Integer) checked by λ. return v0.
    let integer_type = arena.value_type_base(BaseType::Integer);
    let returner = arena.comp_type_returner(integer_type);
    let arrow = arena.comp_type_arrow(integer_type, returner);
    let function_type = arena.value_type_thunk(arrow);
    let bound = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let returned = arena.computation_return(bound);
    let lambda = arena.computation_lambda(returned);
    let function = arena.value_thunk(lambda);
    push(
        "function",
        Maybe::Present(function_type),
        Maybe::Present(function),
    );

    // 2: an unsigned thunk of a bind, a force and an application: refused,
    // its content complete.
    let data = arena.value_constant(ConstantIndex::from(0_usize));
    let function_constant = arena.value_constant(ConstantIndex::from(1_usize));
    let returned = arena.computation_return(data);
    let forced = arena.computation_force(function_constant);
    let argument = arena.value_literal(integer(Digits("4")));
    let applied = arena.computation_application(forced, argument);
    let bind = arena.computation_bind(returned, applied);
    let thunk = arena.value_thunk(bind);
    push("sequence", unsigned(), Maybe::Present(thunk));

    // 3: U (Π (x : 1 + 1). F 1) with a case: the dependent former.
    let unit_type = arena.value_type_unit();
    let unit_sum = arena.value_type_sum(unit_type, unit_type);
    let unit_returner = arena.comp_type_returner(unit_type);
    let pi = arena.comp_type_pi(unit_sum, unit_returner);
    let pi_type = arena.value_type_thunk(pi);
    let scrutinee = arena.value_variable(Zone::Linear, DeBruijnIndex::from(0_u32));
    let unit = arena.value_unit();
    let on_left = arena.computation_return(unit);
    let on_right = arena.computation_return(unit);
    let case = arena.computation_case(scrutinee, on_left, on_right);
    let lambda = arena.computation_lambda(case);
    let case_thunk = arena.value_thunk(lambda);
    push("case", Maybe::Present(pi_type), Maybe::Present(case_thunk));

    // 4: a universe at max(3, v0 + 2, v1), owed.
    let level = Level::constant(LevelConstant::from(3_u64))
        .max(
            &Level::var(LevelVar::new(LevelVarIndex::from(0_u32)))
                .succ()
                .and_then(|level| level.succ())
                .expect("small offsets"),
        )
        .max(&Level::var(LevelVar::new(LevelVarIndex::from(1_u32))));
    let universe = arena.value_type_universe(level);
    push("universe", Maybe::Present(universe), hole());

    // 5: a lift of the unit type, by a lifted unit.
    let one = Level::constant(LevelConstant::from(1_u64));
    let unit_type = arena.value_type_unit();
    let lifted_type = arena.value_type_lift(unit_type, one.clone());
    let unit = arena.value_unit();
    let lifted = arena.value_lift(one, unit);
    push("lift", Maybe::Present(lifted_type), Maybe::Present(lifted));

    // 6: El 0 (universe), owed: a type position naming an item.
    let code = arena.value_constant(ConstantIndex::from(4_usize));
    let element = arena.value_type_element(code, Level::zero());
    push("element", Maybe::Present(element), hole());

    // 7: an abstract type named by an item, owed.
    let abstract_type = arena.value_type_abstract(ConstantIndex::from(0_usize));
    push("abstract", Maybe::Present(abstract_type), hole());

    // 8: Integer checked against a string: a mismatch.
    let integer_type = arena.value_type_base(BaseType::Integer);
    let text = arena.value_literal(Literal::Text(StringLiteral::new(String::from("x"))));
    push(
        "mismatch",
        Maybe::Present(integer_type),
        Maybe::Present(text),
    );

    // 9: a constant at no item's position.
    let dangling = arena.value_constant(ConstantIndex::from(99_usize));
    push("unknown", unsigned(), Maybe::Present(dangling));

    // 10: a variable with no binder.
    let free = arena.value_variable(Zone::Linear, DeBruijnIndex::from(2_u32));
    push("unbound", unsigned(), Maybe::Present(free));

    // 11: U (F Integer) checked by forcing a literal: a shape mismatch.
    let integer_type = arena.value_type_base(BaseType::Integer);
    let returner = arena.comp_type_returner(integer_type);
    let thunk_type = arena.value_type_thunk(returner);
    let literal = arena.value_literal(integer(Digits("1")));
    let forced = arena.computation_force(literal);
    let thunk = arena.value_thunk(forced);
    push("shape", Maybe::Present(thunk_type), Maybe::Present(thunk));

    // 12: an unsigned hole.
    push("hole", unsigned(), hole());

    // 13: a reader of item 1, synthesising its thunk type from the table.
    let reader = arena.value_constant(ConstantIndex::from(1_usize));
    push("reader", unsigned(), Maybe::Present(reader));

    // 14: Integer, owed.
    let integer_type = arena.value_type_base(BaseType::Integer);
    push("owed", Maybe::Present(integer_type), hole());

    Program::new(arena, items).expect("positions ascend")
}
