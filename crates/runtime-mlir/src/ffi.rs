//! The C interface of `cxx/include/gandr_mlir_shim.h`, declared for Rust, and
//! the owner of one answer of the shim.

use core::ffi::c_int;
use core::ffi::c_void;
use core::slice;

use anodized::spec;

use crate::Hole;
use crate::Text;
use crate::Triple;

/// A status of the shim, `gandr_mlir_status` of the header. A C enum has the
/// size of `int` on each target of the pin.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Status(pub c_int);

/// A count of bytes, `size_t` of the header.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
struct ByteCount(usize);

/// `GANDR_MLIR_OK`: the bytes are an object file.
pub const STATUS_OK: Status = Status(0);
/// `GANDR_MLIR_INVALID_TEXT`: the bytes are the diagnostics of the parser or
/// of the verifier.
pub const STATUS_INVALID_TEXT: Status = Status(1);
/// `GANDR_MLIR_UNKNOWN_TARGET`: the bytes tell why the target is not known.
pub const STATUS_UNKNOWN_TARGET: Status = Status(2);
/// `GANDR_MLIR_COMPILE_ERROR`: the bytes are the error of the translation or
/// of the code generator.
pub const STATUS_COMPILE_ERROR: Status = Status(3);

/// `gandr_mlir_output`.
///
/// # Specification
/// - ensures: the layout is the layout of `gandr_mlir_output` of the header:
///   the status, the pointer, the count, in that order, with the C rules.
/// - provides: the answer of one call, as the shim wrote it.
/// - panics: none.
/// - executable: none — a type-level block: a foreign declaration has no body
///   and no call boundary to check.
///
/// # Adequacy
/// - hypothesis: L3 — a wrong layout reads a wrong status or a wrong count.
///   Each status of the header and an object of each backend are read back.
/// - witness: `shim::tests::object_x86_64`
/// - witness: `shim::tests::verifier_refuses`
/// - witness: `shim::tests::unknown_target`
/// - witness: `shim::tests::convention_tailcc_riscv64_refused`
#[repr(C)]
struct RawOutput
{
    /// `gandr_mlir_status`.
    status: Status,
    /// The bytes, from `malloc` of the shim, or null when `len` is zero.
    bytes: *mut u8,
    /// The count of the bytes.
    len: usize,
}

/// `gandr_mlir_hole`: the name and the type of one hole, each with its
/// length.
///
/// # Specification
/// - ensures: the layout is the layout of `gandr_mlir_hole` of the header: the
///   name, its count, the type, its count, in that order, with the C rules.
/// - provides: the borrowed bytes of one hole, for one call of the shim.
/// - panics: none.
/// - executable: none — a type-level block: a foreign declaration has no body
///   and no call boundary to check.
///
/// # Adequacy
/// - hypothesis: L3 — a wrong layout gives the shim a wrong type of a hole, and
///   the verifier refuses the body.
/// - witness: `read::tests::read_load`
/// - witness: `read::tests::read_store`
#[repr(C)]
struct RawHole
{
    /// The bytes of the name.
    name: *const c_void,
    /// The count of the bytes of the name.
    name_len: ByteCount,
    /// The bytes of the type.
    ty: *const c_void,
    /// The count of the bytes of the type.
    ty_len: ByteCount,
}

/// The three entries of `cxx/include/gandr_mlir_shim.h`.
///
/// # Safety
/// - unsafe invariants: each signature matches its declaration in the header:
///   `const char *` as a pointer to `c_void`, `size_t` as a transparent
///   `usize`, the status as a transparent `int`, and the output and the hole
///   with the C layout.
#[expect(
    unused_doc_comments,
    reason = "the policy lint reads the safety section of this block; rustdoc renders none on an extern block"
)]
unsafe extern "C" {
    /// `gandr_mlir_compile`. Neither input needs a terminating zero.
    ///
    /// # Specification
    /// - requires: `text` is valid for `text_len` bytes and `triple` for
    ///   `triple_len` bytes, for the whole call.
    /// - ensures: the answer of the four steps of the shim. The shim owns the
    ///   bytes of the answer until `gandr_mlir_output_free`.
    /// - provides: one [`RawOutput`].
    /// - panics: none. A fatal error of LLVM in the translation or in the code
    ///   generator gives the status `GANDR_MLIR_COMPILE_ERROR`.
    /// - unsafe invariants: the two pointer and length pairs.
    /// - executable: none — a type-level block: a foreign declaration has no
    ///   body and no call boundary to check.
    ///
    /// # Safety
    ///
    /// Each pointer is valid for its length for the whole call.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — each status of the header comes back for its input,
    ///   and a call after a fatal error gives an object.
    /// - witness: `shim::tests::verifier_refuses`
    /// - witness: `shim::tests::unknown_target`
    /// - witness: `shim::tests::convention_tailcc_riscv64_refused`
    fn gandr_mlir_compile(
        text: *const c_void,
        text_len: ByteCount,
        triple: *const c_void,
        triple_len: ByteCount,
    ) -> RawOutput;
    /// `gandr_mlir_read`. No input needs a terminating zero.
    ///
    /// # Specification
    /// - requires: `body` is valid for `body_len` bytes, `holes` for
    ///   `hole_count` holes, and each name and type of a hole for its count,
    ///   for the whole call.
    /// - ensures: the facts of the body, or the diagnostics of the parser or
    ///   the verifier. The shim owns the bytes of the answer until
    ///   `gandr_mlir_output_free`.
    /// - provides: one [`RawOutput`].
    /// - panics: none.
    /// - unsafe invariants: the pointer and length pairs of the body, of the
    ///   holes and of each hole.
    /// - executable: none — a type-level block: a foreign declaration has no
    ///   body and no call boundary to check.
    ///
    /// # Safety
    ///
    /// Each pointer is valid for its length for the whole call.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a load gives its facts, and a body that the verifier
    ///   refuses gives its diagnostic with its line and column.
    /// - witness: `read::tests::read_load`
    /// - witness: `read::tests::read_verifier_refuses`
    fn gandr_mlir_read(
        body: *const c_void,
        body_len: ByteCount,
        holes: *const RawHole,
        hole_count: ByteCount,
    ) -> RawOutput;
    /// `gandr_mlir_output_free`. It accepts an output with null bytes.
    ///
    /// # Specification
    /// - requires: `output` points to an answer of `gandr_mlir_compile` that no
    ///   earlier call released.
    /// - ensures: the bytes go back to the shim, and the output holds null
    ///   bytes and a zero count.
    /// - panics: none.
    /// - unsafe invariants: `output` is valid for a write.
    /// - executable: none — a type-level block: a foreign declaration has no
    ///   body and no call boundary to check.
    ///
    /// # Safety
    ///
    /// `output` points to an answer of the shim, released at most one time.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — eight threads and a call after a fatal error each
    ///   release their answers, and the process stays sound.
    /// - witness: `shim::tests::calls_on_threads`
    /// - witness: `shim::tests::convention_tailcc_riscv64_refused`
    fn gandr_mlir_output_free(output: *mut RawOutput);
}

/// One answer of the shim. The drop gives its bytes back to the shim.
///
/// # Specification
/// - ensures: the value holds one answer of `gandr_mlir_compile`, which only
///   the drop releases.
/// - panics: none.
/// - executable: none — a type-level block: a data declaration has no body and
///   no call boundary to check.
#[repr(transparent)]
pub struct Output
{
    /// The answer as the shim gave it. Only the drop releases it.
    raw: RawOutput,
}

/// An answer moves between threads.
///
/// # Safety
/// - unsafe invariants: the bytes come from `malloc` of the shim and belong to
///   one value alone, and `gandr_mlir_output_free` is safe on any thread.
///
/// # Specification
/// trivial.
// SAFETY: as above.
unsafe impl Send for RawOutput
{
}

/// An answer is shared between threads.
///
/// # Safety
/// - unsafe invariants: a shared reference only reads the bytes.
///
/// # Specification
/// trivial.
// SAFETY: as above.
unsafe impl Sync for RawOutput
{
}

impl Output
{
    /// Call `gandr_mlir_compile` on the two strings.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the answer of the shim for `text` and `triple`.
    /// - provides: the owner of that answer.
    /// - panics: none.
    /// - intension: one foreign call.
    /// - executable: none — unwitnessable provenance: the answer is the outcome
    ///   of the shim, and the call holds nothing to check it against.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — each status of the header comes back for its input,
    ///   from more than one thread.
    /// - witness: `shim::tests::verifier_refuses`
    /// - witness: `shim::tests::calls_on_threads`
    pub fn compile(
        text: Text<'_>,
        triple: Triple<'_>,
    ) -> Self
    {
        // SAFETY: each pointer is valid for its length for the whole call, and
        // the shim reads no byte past that length.
        let raw = unsafe {
            gandr_mlir_compile(
                text.0.as_ptr().cast::<c_void>(),
                ByteCount(text.0.len()),
                triple.0.as_ptr().cast::<c_void>(),
                ByteCount(triple.0.len()),
            )
        };
        Self { raw }
    }

    /// Call `gandr_mlir_read` on a body and its holes.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the answer of the shim for `body` and `holes`.
    /// - provides: the owner of that answer.
    /// - panics: none.
    /// - intension: one foreign call, with the holes in the C layout.
    /// - executable: none — unwitnessable provenance: the answer is the outcome
    ///   of the shim, and the call holds nothing to check it against.
    ///
    /// # Cost
    /// - allocation: one `Vec` of the holes in the C layout, setup
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the facts of a body come back for its holes, and a
    ///   refusal comes back with its diagnostic.
    /// - witness: `read::tests::read_store`
    /// - witness: `read::tests::read_verifier_refuses`
    pub fn read(
        body: Text<'_>,
        holes: &[Hole<'_>],
    ) -> Self
    {
        let raw_holes: Vec<RawHole> = holes
            .iter()
            .map(|hole| RawHole {
                name: hole.name.as_ptr().cast::<c_void>(),
                name_len: ByteCount(hole.name.len()),
                ty: hole.ty.as_ptr().cast::<c_void>(),
                ty_len: ByteCount(hole.ty.len()),
            })
            .collect();
        // SAFETY: each pointer is valid for its length for the whole call:
        // `body`, and the strings of `holes`, which `raw_holes` borrows and
        // which outlive the call. The shim reads no byte past a length.
        let raw = unsafe {
            gandr_mlir_read(
                body.0.as_ptr().cast::<c_void>(),
                ByteCount(body.0.len()),
                raw_holes.as_ptr(),
                ByteCount(raw_holes.len()),
            )
        };
        Self { raw }
    }

    /// The status of the call.
    ///
    /// # Specification
    /// trivial.
    pub const fn status(&self) -> Status
    {
        self.raw.status
    }
}

impl AsRef<[u8]> for Output
{
    /// The bytes of the answer.
    ///
    /// # Specification
    /// - ensures: the `len` bytes at the pointer of the answer, or no byte when
    ///   the pointer is null.
    /// - panics: none.
    /// - intension: no copy. The slice borrows the block of the shim.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an object starts with the ELF magic, and a diagnostic
    ///   holds the phrase of its step.
    /// - witness: `shim::tests::object_x86_64`
    /// - witness: `shim::tests::verifier_refuses`
    #[spec(ensures: |ret| ret.len() == if self.raw.bytes.is_null() { 0 } else { self.raw.len })]
    fn as_ref(&self) -> &[u8]
    {
        if self.raw.bytes.is_null() {
            return &[];
        }
        // SAFETY: the shim gave `len` bytes at a non-null `bytes`. They stay
        // until the drop of `self`, and the borrow of `self` ends before it.
        unsafe { slice::from_raw_parts(self.raw.bytes, self.raw.len) }
    }
}

impl Drop for Output
{
    /// Give the bytes back to the shim.
    ///
    /// # Specification
    /// - ensures: `gandr_mlir_output_free` runs one time on the answer.
    /// - panics: none.
    /// - executable: none — unwitnessable provenance: the release is an effect
    ///   in the shim, and the drop holds nothing to check it against.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — eight threads and a call after a fatal error each
    ///   drop their answers, and the process stays sound.
    /// - witness: `shim::tests::calls_on_threads`
    /// - witness: `shim::tests::convention_tailcc_riscv64_refused`
    fn drop(&mut self)
    {
        // SAFETY: `raw` came from `gandr_mlir_compile` and is released one
        // time, here.
        unsafe {
            gandr_mlir_output_free(&raw mut self.raw);
        }
    }
}
