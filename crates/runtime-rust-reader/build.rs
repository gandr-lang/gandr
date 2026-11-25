//! The reader finds rustc's driver library where its toolchain keeps it, so
//! it runs as a plain process with no variable of the library path.

use std::env;
use std::io;
use std::process::Command;

/// Gives the binary a run path to the `lib` directory of the toolchain that
/// builds it.
///
/// # Errors
/// An I/O error when `RUSTC` is unset or the compiler does not print its
/// sysroot.
fn main() -> io::Result<()>
{
    println!("cargo::rerun-if-env-changed=RUSTC");
    let rustc = env::var_os("RUSTC").ok_or_else(|| io::Error::other("Cargo sets RUSTC"))?;
    let output = Command::new(&rustc).args(["--print", "sysroot"]).output()?;
    let sysroot = String::from_utf8(output.stdout).map_err(io::Error::other)?;
    let sysroot = sysroot.trim();
    if sysroot.is_empty() {
        return Err(io::Error::other("`rustc --print sysroot` prints a path"));
    }
    println!("cargo::rustc-link-arg-bins=-Wl,-rpath,{sysroot}/lib");
    Ok(())
}
