//! The choice of the `llc` that the block compiler runs, read from the file
//! that the build script reads.

use std::ffi::OsStr;
use std::ffi::OsString;
use std::path::PathBuf;

#[path = "../build-llc.rs"]
mod choice;

use choice::Stated;

/// A sysroot that no test reads: a run of it is a fault of the choice.
///
/// # Specification
/// trivial.
#[derive(Debug, Eq, PartialEq)]
struct Unread;

/// A stated path is the build's path whole, and the sysroot does not run. So
/// a cross build names the runner's `llc`, never the building host's.
#[test]
fn a_stated_path_is_kept_whole_8133()
{
    let answer = choice::llc(
        Stated::Path(OsString::from("/tmp/gandr-riscv64-llc")),
        OsStr::new("x86_64-unknown-linux-gnu"),
        || Err(Unread),
    );
    assert_eq!(Ok(PathBuf::from("/tmp/gandr-riscv64-llc")), answer);
}

/// With no stated path, the build takes the `llc` under the host's directory
/// of the sysroot.
#[test]
fn an_unstated_path_is_the_llc_of_the_host_sysroot_8133()
{
    let answer = choice::llc(
        Stated::Unstated,
        OsStr::new("riscv64gc-unknown-linux-gnu"),
        || Ok::<_, Unread>(PathBuf::from("/opt/toolchain")),
    );
    assert_eq!(
        Ok(PathBuf::from(
            "/opt/toolchain/lib/rustlib/riscv64gc-unknown-linux-gnu/bin/llc"
        )),
        answer
    );
}

/// With no stated path, a sysroot that does not read gives its own error.
#[test]
fn an_unread_sysroot_gives_its_error_8133()
{
    let answer = choice::llc(
        Stated::Unstated,
        OsStr::new("riscv64gc-unknown-linux-gnu"),
        || Err(Unread),
    );
    assert_eq!(Err(Unread), answer);
}
