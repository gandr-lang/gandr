//! The stencil table the build script generated from the stencil object, and
//! the shape of one entry.

use gandr_runtime_stencils::StencilId;

/// A byte offset inside one stencil's code.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Offset(pub usize);

/// A relocation's explicit addend, which the compiler folds a constant
/// offset of the operand into (an immediate's bias of one among them).
///
/// # Specification
/// trivial.
#[cfg(any(target_arch = "x86_64", test))]
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct Addend(pub i64);

/// How a hole is patched: the relocation kinds the stencil object uses.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum HoleKind
{
    /// arm64 `BRANCH26`: a `b` to a continuation, ±128 MiB.
    #[cfg(target_arch = "aarch64")]
    Branch26,
    /// arm64 `GOT_LOAD_PAGE21`: the `adrp` of an operand's GOT load.
    #[cfg(target_arch = "aarch64")]
    Page21,
    /// arm64 `GOT_LOAD_PAGEOFF12`: the `ldr` of an operand's GOT load.
    #[cfg(target_arch = "aarch64")]
    PageOff12,
    /// x86-64 `PLT32` or `PC32`: a 32-bit field holding `S + A - P`.
    #[cfg(target_arch = "x86_64")]
    Relative32(Addend),
    /// x86-64 `32`: a 32-bit field holding `S + A`, zero-extended.
    #[cfg(target_arch = "x86_64")]
    Absolute32(Addend),
    /// x86-64 `32S`: a 32-bit field holding `S + A`, sign-extended.
    #[cfg(target_arch = "x86_64")]
    Absolute32Signed(Addend),
}

/// The symbol a hole names.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum HoleSymbol
{
    /// The continuation that follows in the lowered order.
    Next,
    /// The other continuation of a two-way stencil.
    Alt,
    /// The heap exit.
    HeapExhausted,
    /// The frame exit.
    FramesExhausted,
    /// The fuel exit.
    FuelExhausted,
    /// The first operand.
    A,
    /// The second operand.
    B,
}

/// One relocation inside a stencil.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Hole
{
    /// The patched field's or instruction's offset from the stencil's start.
    pub offset: Offset,
    /// How to patch it.
    pub kind: HoleKind,
    /// What it names.
    pub symbol: HoleSymbol,
}

/// One stencil's code.
///
/// # Specification
/// trivial.
#[derive(Debug)]
pub struct StencilCode
{
    /// The machine code, holes unpatched.
    pub bytes: &'static [u8],
    /// The holes, by offset.
    pub holes: &'static [Hole],
    /// The bytes of the trailing branch to `hole_next` a copy drops when its
    /// continuation is the next copy; zero when the stencil ends otherwise.
    pub tail: Offset,
}

include!(concat!(env!("OUT_DIR"), "/stencils.rs"));
