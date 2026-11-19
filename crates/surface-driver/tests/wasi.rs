//! The driver's build for WASI (#7402). Crossterm, the backend of the
//! terminal view, has no WASI port, so an edge to it breaks the build of the
//! `wasm32-wasip3` driver.
//!
//! The rule is checked against the resolver's own answer for the target, so
//! an edge that arrives transitively fails it too.

use std::process::Command;

/// The terminal backend that has no WASI port.
const TERMINAL_BACKEND: &str = "crossterm";

#[test]
fn the_wasi_driver_takes_no_terminal_backend_7402()
{
    let output = Command::new(std::env::var_os("CARGO").expect("cargo names itself to the test"))
        .arg("tree")
        .arg("--manifest-path")
        .arg(concat!(env!("CARGO_MANIFEST_DIR"), "/../../Cargo.toml"))
        .args(["--offline", "--locked", "--package", env!("CARGO_PKG_NAME")])
        .args([
            "--target",
            "wasm32-wasip3",
            "--edges",
            "normal,build",
            "--invert",
            TERMINAL_BACKEND,
        ])
        .output()
        .expect("cargo runs");
    assert!(
        output.status.success(),
        "cargo resolves the driver's tree for WASI: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    let paths = String::from_utf8(output.stdout).expect("cargo prints UTF-8");
    assert!(
        paths.trim().is_empty(),
        "the wasm32-wasip3 driver reaches {TERMINAL_BACKEND}, which has no WASI port, through:\n{paths}"
    );
}
