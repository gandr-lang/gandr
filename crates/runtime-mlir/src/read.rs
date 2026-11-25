//! The read entry of the shim: the text of a machine body and the type of
//! each hole go in, the facts of each operation come out.
//!
//! A machine body is a sequence of operations of the `llvm` dialect with no
//! branch and no terminator. A hole `${name}` names an argument of the body.
//! The shim parses the body inside one function with one argument for each
//! hole, and the verifier of MLIR checks each operation. The answer is text,
//! one line for each fact, and this module reads it into [`Operation`]s. The
//! format is in `cxx/include/gandr_mlir_shim.h`.
//!
//! A diagnostic has the line and the column in the body, from 1. Line 0 is
//! the list of the holes.

use core::fmt;

#[cfg(feature = "full")]
use anodized::spec;

#[cfg(feature = "full")]
use crate::Text;
#[cfg(feature = "full")]
use crate::ffi;

/// One hole of a body: its name, as `${name}` in the body, and its type in
/// the `llvm` dialect, for example `i64`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Hole<'text>
{
    /// The name, an identifier.
    pub name: &'text str,
    /// The type, on one line.
    pub ty: &'text str,
}

/// The source of the value of an operand.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Operand
{
    /// The hole at this index of the list of holes.
    Hole(usize),
    /// A result of an operation before it in the body.
    Result
    {
        /// The index of the operation in the body.
        operation: usize,
        /// The index of the result of that operation.
        index: usize,
    },
}

/// The facts of one operation of a body.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Operation
{
    /// The name with the dialect, for example `llvm.load`.
    pub name: String,
    /// The operands, in order.
    pub operands: Vec<Operand>,
    /// Each attribute, with its inherent properties, as its name and its
    /// text. An enum property is a number: `ordering 4 : i64` is the
    /// `acquire` of `llvm::AtomicOrdering`.
    pub attributes: Vec<(String, String)>,
    /// The type of each result, as text.
    pub results: Vec<String>,
}

/// One diagnostic of the parser or of the verifier.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Diagnostic
{
    /// The line in the body, from 1. Line 0 is the list of the holes.
    pub line: u32,
    /// The column in the line, from 1.
    pub column: u32,
    /// `error`, `warning`, `note` or `remark`.
    pub severity: String,
    /// The message, on one line.
    pub message: String,
}

impl fmt::Display for Diagnostic
{
    /// Write the diagnostic in the form of the shim.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        write!(
            f,
            "{}:{}: {}: {}",
            self.line, self.column, self.severity, self.message
        )
    }
}

/// Why a body has no facts.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ReadError
{
    /// The parser or the verifier refused the body.
    InvalidText(Vec<Diagnostic>),
    /// The answer of the shim does not have the form of the facts or of the
    /// diagnostics. The text is the line that does not.
    Malformed(String),
    /// The shim gave a status that this crate does not know.
    UnknownStatus(i32),
}

impl fmt::Display for ReadError
{
    /// Name the cause, then each diagnostic on its own line.
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
            Self::InvalidText(ref diagnostics) => {
                write!(f, "the body is not valid:")?;
                for diagnostic in diagnostics {
                    write!(f, "\n{diagnostic}")?;
                }
                Ok(())
            },
            Self::Malformed(ref line) => write!(f, "the shim gave a line of no known form: {line}"),
            Self::UnknownStatus(status) => write!(f, "the shim gave the unknown status {status}"),
        }
    }
}

impl core::error::Error for ReadError
{
}

/// Read a machine body into the facts of its operations.
///
/// Each `${name}` in `body` is the hole of that name in `holes`. The verifier
/// of MLIR checks each operation. Each call has its own MLIR context, so
/// calls on more than one thread do not share state.
///
/// # Specification
/// - requires: nothing. No string needs a terminating zero.
/// - ensures: on success one [`Operation`] for each operation of the body, in
///   order, with its operands, its attributes and its result types.
/// - fails: the diagnostics of a refusal, a line of the answer of no known
///   form, or a status that the crate does not know.
/// - panics: none.
/// - intension: one call of the shim, with one MLIR context in the shim.
///
/// # Errors
///
/// - [`ReadError::InvalidText`]: the parser or the verifier refused the body.
///   Each diagnostic has its line and its column in the body.
/// - [`ReadError::Malformed`]: a line of the answer has no known form.
/// - [`ReadError::UnknownStatus`]: the shim gave a status outside its header.
///
/// # Cost
/// - allocation: the facts or the diagnostics of the answer, growth within the
///   answer of the shim
///
/// # Adequacy
/// - hypothesis: L3 — a load, a store, an atomic load and an inline assembly
///   body each give their facts, and an atomic load with no alignment gives the
///   diagnostic of the verifier with its line and column.
/// - witness: `read::tests::read_load`
/// - witness: `read::tests::read_store`
/// - witness: `read::tests::read_atomic_load`
/// - witness: `read::tests::read_inline_asm`
/// - witness: `read::tests::read_verifier_refuses`
#[cfg(feature = "full")]
#[inline]
#[spec(ensures: |ref ret| match *ret {
    Err(ReadError::UnknownStatus(status)) => ![ffi::STATUS_OK, ffi::STATUS_INVALID_TEXT].contains(&ffi::Status(status)),
    Ok(_) | Err(ReadError::InvalidText(_) | ReadError::Malformed(_)) => true,
})]
pub fn read(
    body: Text<'_>,
    holes: &[Hole<'_>],
) -> Result<Vec<Operation>, ReadError>
{
    let output = ffi::Output::read(body, holes);
    match output.status() {
        ffi::STATUS_OK => facts(&output),
        ffi::STATUS_INVALID_TEXT => Err(ReadError::InvalidText(diagnostics(&output)?)),
        ffi::Status(status) => Err(ReadError::UnknownStatus(status)),
    }
}

/// The facts of an answer: an `operation` line, then the lines of its
/// operands, its attributes and its results.
///
/// # Specification
/// - ensures: on success one [`Operation`] for each `operation` line, in order.
/// - fails: [`ReadError::Malformed`] with the first line of no known form.
/// - panics: none.
///
/// # Errors
///
/// [`ReadError::Malformed`]: a line has no known form, or a fact comes before
/// the first `operation` line.
///
/// # Cost
/// - allocation: the text of each fact, growth within the answer of the shim
///
/// # Adequacy
/// - hypothesis: L3 — the facts of four bodies equal the facts files of the C++
///   tests, field by field.
/// - witness: `read::tests::read_load`
/// - witness: `read::tests::read_inline_asm`
#[cfg(feature = "full")]
#[spec(ensures: |ref ret| ret.as_ref().map_or(true, |operations| {
    operations.len() == String::from_utf8_lossy(output.as_ref()).lines().filter(|line| line.starts_with("operation ")).count()
}))]
fn facts(output: &ffi::Output) -> Result<Vec<Operation>, ReadError>
{
    let text = String::from_utf8_lossy(output.as_ref());
    let mut operations: Vec<Operation> = Vec::new();
    for line in text.lines() {
        let malformed = || ReadError::Malformed(line.to_owned());
        let (kind, rest) = line.split_once(' ').ok_or_else(malformed)?;
        if kind == "operation" {
            operations.push(Operation {
                name: rest.to_owned(),
                operands: Vec::new(),
                attributes: Vec::new(),
                results: Vec::new(),
            });
            continue;
        }
        let operation = operations.last_mut().ok_or_else(malformed)?;
        match kind {
            "operand" => {
                let operand = if let Some(index) = rest.strip_prefix("hole ") {
                    Operand::Hole(index.parse().map_err(|_error| malformed())?)
                }
                else {
                    let indices = rest.strip_prefix("result ").ok_or_else(malformed)?;
                    let (operation_index, index) = indices.split_once(' ').ok_or_else(malformed)?;
                    Operand::Result {
                        operation: operation_index.parse().map_err(|_error| malformed())?,
                        index: index.parse().map_err(|_error| malformed())?,
                    }
                };
                operation.operands.push(operand);
            },
            "attribute" => {
                let (name, value) = rest.split_once(' ').ok_or_else(malformed)?;
                operation
                    .attributes
                    .push((name.to_owned(), value.to_owned()));
            },
            "result" => operation.results.push(rest.to_owned()),
            _ => return Err(malformed()),
        }
    }
    Ok(operations)
}

/// The diagnostics of an answer: one line
/// `<line>:<column>: <severity>: <message>` each.
///
/// # Specification
/// - ensures: on success one [`Diagnostic`] for each line, in order.
/// - fails: [`ReadError::Malformed`] with the first line of no known form.
/// - panics: none.
///
/// # Errors
///
/// [`ReadError::Malformed`]: a line does not have the form of a diagnostic.
///
/// # Cost
/// - allocation: the text of each diagnostic, error path
///
/// # Adequacy
/// - hypothesis: L3 — the refusal of an atomic load with no alignment gives one
///   error at its line and column.
/// - witness: `read::tests::read_verifier_refuses`
#[cfg(feature = "full")]
#[spec(ensures: |ref ret| ret.as_ref().map_or(true, |found| {
    found.len() == String::from_utf8_lossy(output.as_ref()).lines().count()
}))]
fn diagnostics(output: &ffi::Output) -> Result<Vec<Diagnostic>, ReadError>
{
    String::from_utf8_lossy(output.as_ref())
        .lines()
        .map(|line| {
            let malformed = || ReadError::Malformed(line.to_owned());
            let (place, rest) = line.split_once(": ").ok_or_else(malformed)?;
            let (row, column) = place.split_once(':').ok_or_else(malformed)?;
            let (severity, message) = rest.split_once(": ").ok_or_else(malformed)?;
            Ok(Diagnostic {
                line: row.parse().map_err(|_error| malformed())?,
                column: column.parse().map_err(|_error| malformed())?,
                severity: severity.to_owned(),
                message: message.to_owned(),
            })
        })
        .collect()
}
