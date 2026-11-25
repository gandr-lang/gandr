//! The Rust side of the MLIR shim of `cxx/`: two entries over one C
//! interface.
//!
//! # Items
//!
//! - `compile`: MLIR text in the `llvm` and `gandr` dialects and a target
//!   triple go in. The verifier runs first. The bytes of an object come out, or
//!   the diagnostics of the step that refused the text.
//! - `read`: the text of a machine body and the type of each hole go in. The
//!   verifier runs. The facts of each operation come out, or the diagnostics
//!   with their line and column in the body. The module `read` has the form of
//!   a body.
//!
//! # Boundaries
//!
//! The two entries, `Object`, `Text` and `Triple` exist under the feature
//! `full` alone. The feature builds the shim of `cxx/` and links it.
//! Without the feature the crate holds the types of the answers,
//! [`CompileError`] and the facts of a body, and the build compiles no C++.
//!
//! The `gandr` dialect has one operation for each transition of the machine
//! that the first slice uses. The shim lowers each one to the `llvm` dialect,
//! by the one lowering of `cxx/src/dialect.cpp`.
//!
//! The shim is one shared library with the MLIR and LLVM of the pin inside
//! it. Its C interface is `cxx/include/gandr_mlir_shim.h`, and the module
//! `ffi` declares it again for Rust. The order of the steps is in the
//! documentation of `compile`.
//!
//! The entry is total: a fatal error of LLVM in the translation or in the
//! code generator gives [`CompileError::Codegen`], and the process continues.
//!
//! # References
//!
//! - `vault:01a1f7d8-3d56-7502-b037-3d37c5464b50` — dependency: § mojo-shim,
//!   the boundary of MLIR text, one C entry, and the verifier first; and §
//!   mojo-library-bottom, the check of a machine body by the shim.

#[cfg(feature = "full")]
mod ffi;
mod read;

use core::fmt;

#[cfg(feature = "full")]
use anodized::spec;
pub use read::Diagnostic;
pub use read::Hole;
pub use read::Operand;
pub use read::Operation;
pub use read::ReadError;
#[cfg(feature = "full")]
pub use read::read;

/// An object file from the code generator, in the format of the target.
///
/// # Specification
/// - ensures: the value holds one answer of the shim whose status is
///   `GANDR_MLIR_OK`. Its bytes are the object file of that call.
/// - provides: the bytes, until the drop of the value gives them back to the
///   shim.
/// - panics: none.
/// - executable: none — a type-level block: a data declaration has no body and
///   no call boundary to check.
///
/// # Adequacy
/// - hypothesis: L3 — the object of each backend of the pin starts with the ELF
///   magic, so a value that held another answer is observed.
/// - witness: `shim::tests::object_x86_64`
/// - witness: `shim::tests::object_aarch64`
/// - witness: `shim::tests::object_riscv64`
#[cfg(feature = "full")]
#[repr(transparent)]
pub struct Object
{
    /// The answer of the shim. It holds the bytes of the object.
    output: ffi::Output,
}

#[cfg(feature = "full")]
impl AsRef<[u8]> for Object
{
    /// The bytes of the object file.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn as_ref(&self) -> &[u8]
    {
        self.output.as_ref()
    }
}

/// MLIR text in the `llvm` and `gandr` dialects. It needs no terminating zero.
#[cfg(feature = "full")]
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Text<'text>(&'text str);

#[cfg(feature = "full")]
impl<'text> From<&'text str> for Text<'text>
{
    /// The text as MLIR text.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(text: &'text str) -> Self
    {
        Self(text)
    }
}

/// A target triple, for example `x86_64-unknown-linux-gnu`. It needs no
/// terminating zero.
#[cfg(feature = "full")]
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Triple<'triple>(&'triple str);

#[cfg(feature = "full")]
impl<'triple> From<&'triple str> for Triple<'triple>
{
    /// The text as a target triple.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(triple: &'triple str) -> Self
    {
        Self(triple)
    }
}

#[cfg(feature = "full")]
impl fmt::Debug for Object
{
    /// Write the count of the bytes, and not the bytes.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        f.debug_struct("Object")
            .field("len", &self.as_ref().len())
            .finish()
    }
}

/// The step that refused a call, with the text of its diagnostics.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CompileError
{
    /// The parser or the verifier refused the text.
    InvalidText(String),
    /// LLVM knows no target for the triple.
    UnknownTarget(String),
    /// The translation to LLVM IR or the code generator failed.
    Codegen(String),
    /// The shim gave a status that this crate does not know.
    UnknownStatus(i32),
}

impl fmt::Display for CompileError
{
    /// Name the step that refused the call, then its diagnostics.
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
            Self::InvalidText(ref text) => write!(f, "the text is not valid MLIR:\n{text}"),
            Self::UnknownTarget(ref text) => write!(f, "the target is not known: {text}"),
            Self::Codegen(ref text) => write!(f, "the code generator failed: {text}"),
            Self::UnknownStatus(status) => write!(f, "the shim gave the unknown status {status}"),
        }
    }
}

impl core::error::Error for CompileError
{
}

/// Compile MLIR text for one target.
///
/// The steps run in this order, and the first step that fails gives the
/// error:
///
/// 1. The parser reads `text`, and the verifier checks each operation. The shim
///    lowers each operation of the `gandr` dialect to the `llvm` dialect, and
///    the verifier checks the module again.
/// 2. LLVM looks up the target of `triple`, for example
///    `x86_64-unknown-linux-gnu`.
/// 3. The text goes to LLVM IR.
/// 4. The code generator writes a relocatable object.
///
/// Each call has its own MLIR context, so calls on more than one thread do
/// not share state.
///
/// # Specification
/// - requires: nothing. Neither string needs a terminating zero.
/// - ensures: on success the bytes of a relocatable object of the target of
///   `triple` for the module of `text`. A fatal error of LLVM in step 3 or 4
///   gives an error, and the process continues.
/// - provides: an [`Object`], which owns the bytes.
/// - fails: the first step that fails gives its variant of [`CompileError`],
///   with the text of its diagnostics. A status that the crate does not know
///   gives [`CompileError::UnknownStatus`], and never a known status.
/// - panics: none.
/// - intension: one call of the shim, with one MLIR context and one LLVM
///   context in the shim, and one copy of the diagnostics into a `String` on a
///   refusal.
///
/// # Errors
///
/// - [`CompileError::InvalidText`]: the parser, the verifier or the lowering of
///   the `gandr` dialect refused `text`.
/// - [`CompileError::UnknownTarget`]: LLVM has no target for `triple`.
/// - [`CompileError::Codegen`]: the translation or the code generator failed,
///   also with a fatal error of LLVM.
/// - [`CompileError::UnknownStatus`]: the shim gave a status outside its
///   header.
///
/// # Cost
/// - allocation: the diagnostics of a refusal in one `String`, error path
///
/// # Adequacy
/// - hypothesis: L3 — each step is reached by one input that fails only that
///   step, asserted by its exact variant and a phrase of its diagnostic: a
///   wrong return type for step 1, an unknown triple for step 2, `tailcc` on
///   riscv64 for step 4. Each backend, each operation of the minimal core and
///   each transition of the `gandr` dialect gives an ELF object, and a
///   transition with a wrong type is refused in step 1. A call after a fatal
///   error and calls on eight threads give objects.
/// - witness: `shim::tests::object_x86_64`
/// - witness: `shim::tests::object_aarch64`
/// - witness: `shim::tests::object_riscv64`
/// - witness: `shim::tests::verifier_refuses`
/// - witness: `shim::tests::unknown_target`
/// - witness: `shim::tests::operation_integers`
/// - witness: `shim::tests::operation_load_store`
/// - witness: `shim::tests::operation_atomic`
/// - witness: `shim::tests::operation_inline_asm`
/// - witness: `shim::tests::convention_tailcc_x86_64`
/// - witness: `shim::tests::convention_preserve_none`
/// - witness: `shim::tests::calls_on_threads`
/// - witness: `shim::tests::convention_tailcc_riscv64_refused`
/// - witness: `shim::tests::dialect_transitions`
/// - witness: `shim::tests::dialect_return_wrong_type`
/// - witness: `shim::tests::dialect_call_wrong_operand`
/// - witness: `shim::tests::dialect_jump_wrong_result`
#[cfg(feature = "full")]
#[inline]
#[spec(ensures: |ref ret| match *ret {
    Err(CompileError::UnknownStatus(status)) => ![
        ffi::STATUS_OK,
        ffi::STATUS_INVALID_TEXT,
        ffi::STATUS_UNKNOWN_TARGET,
        ffi::STATUS_COMPILE_ERROR,
    ]
    .contains(&ffi::Status(status)),
    Ok(_) | Err(CompileError::InvalidText(_) | CompileError::UnknownTarget(_) | CompileError::Codegen(_)) => true,
})]
pub fn compile(
    text: Text<'_>,
    triple: Triple<'_>,
) -> Result<Object, CompileError>
{
    let output = ffi::Output::compile(text, triple);
    let diagnostics = || String::from_utf8_lossy(output.as_ref()).into_owned();
    match output.status() {
        ffi::STATUS_OK => Ok(Object { output }),
        ffi::STATUS_INVALID_TEXT => Err(CompileError::InvalidText(diagnostics())),
        ffi::STATUS_UNKNOWN_TARGET => Err(CompileError::UnknownTarget(diagnostics())),
        ffi::STATUS_COMPILE_ERROR => Err(CompileError::Codegen(diagnostics())),
        ffi::Status(status) => Err(CompileError::UnknownStatus(status)),
    }
}
