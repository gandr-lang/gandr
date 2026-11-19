//! The stencils' witnesses, one module per area.
//!
//! One target rather than one per area, so a witness path names the area it
//! belongs to (`tests::agreement::…`) instead of a file.

extern crate alloc;

#[cfg(test)]
mod accumulate;
#[cfg(test)]
mod agreement;
#[cfg(test)]
mod count;
#[cfg(test)]
mod exits;
#[cfg(test)]
mod generate;
#[cfg(test)]
mod image;
#[cfg(test)]
mod layout;
#[cfg(test)]
#[cfg(any(
    all(
        target_os = "linux",
        any(
            target_arch = "x86_64",
            target_arch = "aarch64",
            target_arch = "riscv64"
        )
    ),
    all(target_os = "macos", target_arch = "aarch64")
))]
mod machine;
#[cfg(test)]
mod support;
