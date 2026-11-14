//! The packed write of a whole batch on the ring of the IO layer, which
//! the module `ring` measures. The ring stands on Linux on x86-64, aarch64
//! and riscv64 alone, so on any other target the bench runs nothing.

#[cfg(all(
    target_os = "linux",
    any(
        target_arch = "aarch64",
        target_arch = "riscv64",
        target_arch = "x86_64"
    )
))]
#[path = "batch/ring.rs"]
mod ring;

/// Run the bench of the ring.
///
/// # Specification
/// trivial.
#[cfg(all(
    target_os = "linux",
    any(
        target_arch = "aarch64",
        target_arch = "riscv64",
        target_arch = "x86_64"
    )
))]
fn main()
{
    ring::main();
}

/// Run nothing: the target holds no ring.
///
/// # Specification
/// trivial.
#[cfg(not(all(
    target_os = "linux",
    any(
        target_arch = "aarch64",
        target_arch = "riscv64",
        target_arch = "x86_64"
    )
)))]
fn main()
{
}
