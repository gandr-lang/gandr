//! The build and the link of the shim. Under the feature `full`, the script
//! builds the library of `cxx/` with `CMake` against the MLIR toolchain that
//! `GANDR_MLIR_TOOLCHAIN` names, installs it into the output directory of the
//! crate, and tells rustc where it is. Without the feature it builds nothing
//! and links nothing.

use std::env;
use std::ffi::OsString;
use std::io;
use std::io::Write as _;
use std::path::Path;
use std::path::PathBuf;
use std::process::Command;

/// The variable that names the root of the unpacked MLIR toolchain.
const TOOLCHAIN: &str = "GANDR_MLIR_TOOLCHAIN";

/// The release of LLVM of the pin. `cxx/CMakeLists.txt` refuses a toolchain
/// of another release.
const PIN: &str = "23.1.6";

/// Build the shim and tell Cargo where it is, when the feature `full` is on.
///
/// # Specification
/// - requires: nothing.
/// - ensures: without the feature, no directive but the reruns. With it, the
///   library `libgandr_mlir_shim.so` of `cxx/` is in `lib` below the output
///   directory, and the link directives of the shim are on standard output: the
///   search path, the library, the rpath and the metadata `lib`.
/// - provides: the link of the shim for the crate, its tests and its consumers.
/// - fails: under the feature, when `GANDR_MLIR_TOOLCHAIN` is not set, when a
///   step of `CMake` fails, or when a write to standard output fails.
/// - panics: none.
/// - executable: none — a build script, whose only observer is Cargo.
///
/// # Errors
///
/// As the failure clause states.
///
/// # Cost
/// - allocation: the paths, the commands and the directives, setup
///
/// # Adequacy
/// - hypothesis: L2 — each test of the crate under the feature links and loads
///   the shim through these directives.
/// - witness: `shim::tests::object_x86_64`
fn main() -> Result<(), String>
{
    let mut out = io::stdout().lock();
    let mut say = |line: &str| writeln!(out, "{line}").map_err(|error| error.to_string());
    say("cargo::rerun-if-changed=build.rs")?;
    say("cargo::rerun-if-changed=cxx")?;
    say(&format!("cargo::rerun-if-env-changed={TOOLCHAIN}"))?;
    if env::var_os("CARGO_FEATURE_FULL").is_none() {
        return Ok(());
    }
    let toolchain = PathBuf::from(env::var_os(TOOLCHAIN).ok_or_else(|| {
        format!("the feature `full` builds the shim, and {TOOLCHAIN} names no MLIR toolchain")
    })?);
    let manifest =
        PathBuf::from(env::var_os("CARGO_MANIFEST_DIR").ok_or("Cargo sets no CARGO_MANIFEST_DIR")?);
    let output = PathBuf::from(env::var_os("OUT_DIR").ok_or("Cargo sets no OUT_DIR")?);
    let build = output.join("build");
    let shim = output.join("shim");
    let mut configure = Command::new("cmake");
    let _configure = configure
        .arg("-S")
        .arg(manifest.join("cxx"))
        .arg("-B")
        .arg(&build)
        .arg("-DCMAKE_BUILD_TYPE=Release")
        .arg(define("CMAKE_INSTALL_PREFIX", &shim))
        .arg(define("MLIR_DIR", &toolchain.join("lib/cmake/mlir")))
        .arg(format!("-DGANDR_MLIR_VERSION={PIN}"));
    run(&mut configure)?;
    let mut compile = Command::new("cmake");
    let _compile = compile.arg("--build").arg(&build).arg("--parallel");
    if let Some(jobs) = env::var_os("NUM_JOBS") {
        let _jobs = compile.arg(jobs);
    }
    run(&mut compile)?;
    let mut install = Command::new("cmake");
    let _install = install.arg("--install").arg(&build);
    run(&mut install)?;
    let lib = shim.join("lib");
    say(&format!(
        "cargo::rustc-link-search=native={}",
        lib.display()
    ))?;
    say("cargo::rustc-link-lib=dylib=gandr_mlir_shim")?;
    // The tests of this crate find the library at run time through this path.
    say(&format!(
        "cargo::rustc-link-arg=-Wl,-rpath,{}",
        lib.display()
    ))?;
    // A consumer reads the directory as `DEP_GANDR_MLIR_SHIM_LIB`, for its own
    // rpath.
    say(&format!("cargo::metadata=lib={}", lib.display()))
}

/// The `CMake` definition `-D<name>=<path>`.
///
/// # Specification
/// trivial.
fn define(
    name: &str,
    path: &Path,
) -> OsString
{
    let mut definition = OsString::from(format!("-D{name}="));
    definition.push(path.as_os_str());
    definition
}

/// Run `command` to its end, with its output on the output of the script.
///
/// # Specification
/// - ensures: the command ran and exited with the status 0.
/// - fails: the command did not start, or it exited with another status.
/// - panics: none.
/// - executable: none — a build script, whose only observer is Cargo.
///
/// # Errors
///
/// The text names the program and the status.
///
/// # Cost
/// - allocation: the text of a failure, error path
fn run(command: &mut Command) -> Result<(), String>
{
    let status = command.status().map_err(|error| {
        format!(
            "{} does not start: {error}",
            command.get_program().display()
        )
    })?;
    if status.success() {
        Ok(())
    }
    else {
        Err(format!("{command:?} failed: {status}"))
    }
}
