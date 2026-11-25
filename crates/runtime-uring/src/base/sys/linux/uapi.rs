//! The kernel's UAPI: the declarations that the build script makes for each
//! architecture, and the three calls of the ring over them.

#[cfg_attr(target_arch = "aarch64", path = "uapi/arch/aarch64.rs")]
#[cfg_attr(target_arch = "arm", path = "uapi/arch/arm.rs")]
#[cfg_attr(target_arch = "loongarch64", path = "uapi/arch/loongarch64.rs")]
#[cfg_attr(target_arch = "powerpc64", path = "uapi/arch/powerpc64.rs")]
#[cfg_attr(target_arch = "riscv64", path = "uapi/arch/riscv64.rs")]
#[cfg_attr(target_arch = "s390x", path = "uapi/arch/s390x.rs")]
#[cfg_attr(target_arch = "x86", path = "uapi/arch/x86.rs")]
#[cfg_attr(target_arch = "x86_64", path = "uapi/arch/x86_64.rs")]
pub mod arch;

pub mod io_uring;
