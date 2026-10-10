//! First-order residual readmission for the experimental stage universe.
//!
//! Compilation first replays the producer's stage certificate. The residual
//! grammar is one natural argument, literals and multiplication: no closure,
//! higher-order argument, iterator, quote or splice survives. The ordinary
//! kernel checks its CBPV image over an explicit multiplication signature.

use alloc::collections::BTreeMap;
use alloc::string::ToString as _;
use alloc::vec::Vec;
use core::fmt;

use anodized::spec;
use gandr_kernel_core::CheckedId;
use gandr_kernel_core::Environment;
use gandr_kernel_core::KernelError;
use gandr_kernel_term::BaseType;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::IntegerLiteral;
use gandr_kernel_term::LevelSignature;
use gandr_kernel_term::Literal;
use gandr_kernel_term::Magnitude;
use gandr_kernel_term::Sign;
use gandr_kernel_term::TermArena;
use gandr_kernel_term::ValueId;
use gandr_kernel_term::stage::Arena;
use gandr_kernel_term::stage::Budget;
use gandr_kernel_term::stage::Certificate;
use gandr_kernel_term::stage::Index;
use gandr_kernel_term::stage::Natural;
use gandr_kernel_term::stage::Stage;
use gandr_kernel_term::stage::StageError;
use gandr_kernel_term::stage::Term;
use gandr_kernel_term::stage::Type;
use gandr_kernel_term::stage::TypeId;

/// One register in a closure-free, straight-line residual.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct Register(pub usize);

/// First-order instructions; operands always precede their result.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Instruction
{
    /// The function's sole natural argument.
    Input,
    /// A nonnegative natural literal.
    Natural(Natural),
    /// Natural multiplication, with two earlier registers.
    Multiply(Register, Register),
}

/// A replayed, closed first-order natural function.
///
/// # Specification
/// - ensures: every operand is an earlier register, and the result names an
///   instruction. Only replayed, closed natural functions reach this type.
/// - panics: none.
/// - executable: none — construction is private; compile and execute check the
///   register invariant at their callable boundaries.
///
/// # Adequacy
/// - hypothesis: L1/L2/L3 — replay refusal, captured variables and independent
///   execution of powers distinguish unauthorized or malformed residuals.
/// - witness: `stage::tests::power_is_admitted_and_executed`
/// - witness: `stage::tests::unreplayed_and_open_residuals_are_refused`
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Program
{
    /// Instructions in dependency order.
    instructions: Vec<Instruction>,
    /// The returned register.
    result: Register,
}

/// The checked definition and the explicit primitive signature it may use.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Admitted
{
    /// The residual definition's checked admission.
    pub definition: CheckedId,
    /// The typed, uninterpreted multiplication primitive.
    pub multiplication: CheckedId,
    /// The admitted function body in the destination environment's arena.
    pub body: ValueId,
}

/// A residual readmission failure, retaining the layer that refused it.
#[derive(Debug)]
pub enum ReadmissionError
{
    /// Malformed residual or resource failure.
    Stage(StageError),
    /// Ordinary kernel declaration refusal.
    Kernel(KernelError),
}

impl fmt::Display for ReadmissionError
{
    /// Display the refusing layer's diagnostic.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        match *self {
            | Self::Stage(ref error) => error.fmt(f),
            | Self::Kernel(ref error) => error.fmt(f),
        }
    }
}
impl core::error::Error for ReadmissionError
{
}
impl From<StageError> for ReadmissionError
{
    /// Preserve a staging failure at readmission.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(error: StageError) -> Self
    {
        Self::Stage(error)
    }
}
impl From<KernelError> for ReadmissionError
{
    /// Preserve the ordinary kernel's refusal.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(error: KernelError) -> Self
    {
        Self::Kernel(error)
    }
}

/// Replay a staged result and compile its closed first-order residual.
///
/// # Specification
/// - ensures: returned instructions describe precisely the quoted natural
///   function, with only backward register edges and one permitted variable.
/// - fails: replay errors or `NotResidual` for any other residual grammar.
/// - panics: none.
///
/// # Errors
/// Returns replay, lookup, work errors or `NotResidual`.
///
/// # Adequacy
/// - hypothesis: L2/L3 — power at multiple exponents/inputs, an escaping
///   variable, and a modified certificate distinguish replay and extraction.
/// - witness: `stage::tests::power_is_admitted_and_executed`
/// - witness: `stage::tests::unreplayed_and_open_residuals_are_refused`
#[inline]
#[spec(ensures: |ret| ret.as_ref().ok().is_none_or(|program|
    program.result.0 < program.instructions.len()
    && program.instructions.iter().enumerate().all(|(index, instruction)| match *instruction {
        Instruction::Multiply(left, right) => left.0 < index && right.0 < index,
        _ => true,
    })))]
pub fn compile(
    arena: &mut Arena,
    context: &[TypeId],
    certificate: &Certificate,
    budget: &mut Budget,
) -> Result<Program, StageError>
{
    gandr_kernel_core::stage::replay(arena, context, certificate, budget)?;
    let Term::Quote(lambda) = arena.term(certificate.target)?
    else {
        return Err(StageError::NotResidual);
    };
    let Term::Lambda(domain, root) = arena.term(lambda)?
    else {
        return Err(StageError::NotResidual);
    };
    let Type::Nat(stage @ Stage::Inner(_)) = arena.ty(domain)?
    else {
        return Err(StageError::NotResidual);
    };
    let mut instructions = Vec::new();
    let mut registers = BTreeMap::new();
    let mut pending = Vec::from([(root, false)]);
    while let Some((id, ready)) = pending.pop() {
        budget.spend()?;
        if registers.contains_key(&id) {
            continue;
        }
        let term = arena.term(id)?;
        if !ready && let Term::Multiply(left, right) = term {
            pending.push((id, true));
            pending.push((right, false));
            pending.push((left, false));
            continue;
        }
        let instruction = match term {
            | Term::Variable(Index(0)) => Instruction::Input,
            | Term::Natural(actual, value) if actual == stage => Instruction::Natural(value),
            | Term::Multiply(left, right) => {
                let left = *registers.get(&left).ok_or(StageError::Unbalanced)?;
                let right = *registers.get(&right).ok_or(StageError::Unbalanced)?;
                Instruction::Multiply(left, right)
            },
            | _ => return Err(StageError::NotResidual),
        };
        let register = Register(instructions.len());
        instructions.push(instruction);
        registers.insert(id, register);
    }
    let result = *registers.get(&root).ok_or(StageError::Unbalanced)?;
    Ok(Program {
        instructions,
        result,
    })
}

/// A register's representation during CBPV lowering.
#[derive(Clone, Copy, Debug)]
enum Operand
{
    /// A closed literal.
    Literal(ValueId),
    /// A variable's absolute binder level; zero is the input.
    Local(Index),
}

/// Mint one operand at its current binder distance.
///
/// # Specification
/// - ensures: variable references account for exactly the preceding binds.
/// - fails: invalid register, binder underflow or index-width overflow.
/// - panics: none.
///
/// # Errors
/// Returns `Unbalanced` or `Overflow`.
///
/// # Adequacy
/// - hypothesis: L2 — execution of the admitted CBPV code distinguishes
///   incorrect binder distances from correct first-order evaluation.
/// - witness: `stage::tests::power_is_admitted_and_executed`
/// - witness: `stage::tests::operand_boundaries`
#[spec(ensures: |ret| ret.as_ref().ok().is_none_or(|value|
    match operands.get(register.0).copied() {
        Some(Operand::Literal(literal)) => *value == literal,
        Some(Operand::Local(level)) => match arena.value(*value) {
            Some(&gandr_kernel_term::Value::Variable(index)) =>
                usize::try_from(u32::from(index)).ok() == depth.0.checked_sub(level.0),
            _ => false,
        },
        None => false,
    }))]
fn operand(
    arena: &mut TermArena,
    operands: &[Operand],
    register: Register,
    depth: Index,
) -> Result<ValueId, StageError>
{
    match *operands.get(register.0).ok_or(StageError::Unbalanced)? {
        | Operand::Literal(value) => Ok(value),
        | Operand::Local(level) => {
            let distance = depth.0.checked_sub(level.0).ok_or(StageError::Unbalanced)?;
            let distance = u32::try_from(distance).map_err(|_overflow| StageError::Overflow)?;
            Ok(arena.value_variable(DeBruijnIndex::from(distance)))
        },
    }
}

impl Program
{
    /// Borrow the executable first-order instructions.
    ///
    /// # Specification
    /// trivial.
    #[must_use]
    #[inline]
    pub fn instructions(&self) -> &[Instruction]
    {
        &self.instructions
    }

    /// Execute the residual on finite machine naturals with checked arithmetic.
    ///
    /// # Specification
    /// - requires: the program's private register graph is backward and its
    ///   result register is present.
    /// - ensures: returns the residual's natural result when representable.
    /// - fails: `Overflow` rather than wrapping natural multiplication.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns `Overflow` or `Unbalanced` for an invalid internal register.
    ///
    /// # Adequacy
    /// - hypothesis: L2/L3 — exponentiation over a bounded grid and the machine
    ///   ceiling distinguish arithmetic from wrapping or constants.
    /// - witness: `stage::tests::power_is_admitted_and_executed`
    #[inline]
    #[spec(requires: self.result.0 < self.instructions.len()
        && self.instructions.iter().enumerate().all(|(index, instruction)| match *instruction {
            Instruction::Multiply(left, right) => left.0 < index && right.0 < index,
            _ => true,
        }),
        ensures: |ret| ret.as_ref().ok().is_none_or(|value| match self.instructions.get(self.result.0).copied() {
            Some(Instruction::Input) => *value == input,
            Some(Instruction::Natural(expected)) => *value == expected,
            _ => true,
        }),
    )]
    pub fn execute(
        &self,
        input: Natural,
    ) -> Result<Natural, StageError>
    {
        let mut values: Vec<Natural> = Vec::with_capacity(self.instructions.len());
        for instruction in &self.instructions {
            let value = match *instruction {
                | Instruction::Input => input,
                | Instruction::Natural(value) => value,
                | Instruction::Multiply(left, right) => {
                    let left = values.get(left.0).ok_or(StageError::Unbalanced)?;
                    let right = values.get(right.0).ok_or(StageError::Unbalanced)?;
                    Natural(left.0.checked_mul(right.0).ok_or(StageError::Overflow)?)
                },
            };
            values.push(value);
        }
        values
            .get(self.result.0)
            .copied()
            .ok_or(StageError::Unbalanced)
    }

    /// Admit the CBPV residual over an explicit multiplication signature.
    ///
    /// Naturals use nonnegative integer literals. The kernel treats
    /// multiplication as an uninterpreted, typed primitive; its axiom remains
    /// visible in the definition's audit. No unchecked admission is used.
    ///
    /// # Specification
    /// - ensures: the returned definition was checked by
    ///   `Environment::add_decl` and consists of one top-level lambda and
    ///   first-order primitive calls.
    /// - fails: staging/lowering errors or ordinary kernel refusals; a failure
    ///   after primitive admission leaves that explicit signature in place.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns `ReadmissionError` retaining the failing layer.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the admitted body is independently interpreted and
    ///   compared with exponentiation; audit observes the exact assumption.
    /// - witness: `stage::tests::power_is_admitted_and_executed`
    #[inline]
    #[spec(ensures: |ret| ret.as_ref().ok().is_none_or(|admitted| {
        let audit = environment.audit(admitted.definition);
        audit.unchecked_admissions().is_empty()
            && audit.axioms().iter().all(|axiom| *axiom == admitted.multiplication.position())
    }))]
    pub fn admit(
        &self,
        environment: &mut Environment,
    ) -> Result<Admitted, ReadmissionError>
    {
        let primitive = {
            let mut staging = environment.stage();
            let arena = staging.arena();
            let nat = arena.value_type_base(BaseType::Integer);
            let result = arena.comp_type_returner(nat);
            let unary = arena.comp_type_arrow(nat, result);
            let binary = arena.comp_type_arrow(nat, unary);
            let declared = arena.value_type_thunk(binary);
            staging.axiom(LevelSignature::monomorphic(), declared)
        };
        let multiplication = environment.add_decl(primitive)?;
        let mut staging = environment.stage();
        let arena = staging.arena();
        let primitive = arena.value_constant(multiplication.position());
        let mut operands = Vec::with_capacity(self.instructions.len());
        let mut calls = Vec::new();
        let mut depth = Index(0);
        for instruction in &self.instructions {
            let value = match *instruction {
                | Instruction::Input => Operand::Local(Index(0)),
                | Instruction::Natural(Natural(value)) => {
                    let magnitude = Magnitude::from_decimal_text(value.to_string())
                        .ok_or(StageError::Unbalanced)?;
                    let literal = IntegerLiteral::new(Sign::NonNegative, magnitude);
                    Operand::Literal(arena.value_literal(Literal::Integer(literal)))
                },
                | Instruction::Multiply(left, right) => {
                    let left = operand(arena, &operands, left, depth)?;
                    let right = operand(arena, &operands, right, depth)?;
                    let head = arena.computation_force(primitive);
                    let head = arena.computation_application(head, left);
                    let call = arena.computation_application(head, right);
                    calls.push(call);
                    depth = Index(depth.0.checked_add(1).ok_or(StageError::Overflow)?);
                    Operand::Local(depth)
                },
            };
            operands.push(value);
        }
        let value = operand(arena, &operands, self.result, depth)?;
        let mut body = arena.computation_return(value);
        for call in calls.into_iter().rev() {
            body = arena.computation_bind(call, body);
        }
        let body = arena.computation_lambda(body);
        let body = arena.value_thunk(body);
        let nat = arena.value_type_base(BaseType::Integer);
        let result = arena.comp_type_returner(nat);
        let arrow = arena.comp_type_arrow(nat, result);
        let declared = arena.value_type_thunk(arrow);
        let staged = staging.def(LevelSignature::monomorphic(), declared, body);
        let definition = environment.add_decl(staged)?;
        Ok(Admitted {
            definition,
            multiplication,
            body,
        })
    }
}

#[cfg(test)]
mod tests;
