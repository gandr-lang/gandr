use std::path::Path;
use std::process::Command;
use std::process::Output;

/// Run the binary with `arguments` at the workspace `root`, with the target
/// directory `target`.
///
/// # Specification
/// trivial.
fn run(
    root: &Path,
    arguments: &[&str],
    target: &Path,
) -> Output
{
    Command::new(env!("CARGO_BIN_EXE_twin-census"))
        .args(arguments)
        .arg("--root")
        .arg(root)
        .env("CARGO_TARGET_DIR", target)
        .output()
        .expect("the binary runs")
}

/// The census of the fixture workspace: the emitter depends on `near`, and
/// the emitter has one generic public function and one in the export
/// fragment.
const FIXTURE: &str = "# Twin census

A twin is a function of a crate that gandr source states. A crate is under the emitter when `gandr-runtime-emitter` depends on it by a normal or a build dependency, directly or through other crates. A twin of such a crate runs as an object, and not as a record that the runtime loads.

An item is generic when it has a type parameter or a trait bound. An entry under the C convention carries neither, so a generic item has no twin without a wrapper. The column counts the public functions, methods, types, traits and type aliases of the crate's library that are generic.

An export carries a function that is not generic, whose operands are fixed-width integers or addresses, and whose result is one of the two. A fixed-width integer is `u8` to `u64`, `i8` to `i64`, `usize` or `isize`. An address is a reference or a raw pointer to a sized type. The column gives the count of such public functions and methods, of the count of all, and its share.

`twin-census` prints this text from `cargo metadata` and from the JSON that rustdoc writes for each library.

| Crate | Under the emitter | Generic items | Export fragment |
| ----- | ----------------- | ------------- | --------------- |
| `near` | yes | 0 | 0 of 0 |
| `runtime-emitter` | the emitter | 1 | 1 of 2 (50 %) |

Crates under the emitter: 1 of 2.

Generic public items: 1.

Public functions in the export fragment: 1 of 2 (50 %).
";

/// The binary prints the census of the fixture workspace, and `--cost` names
/// each part of the run on standard error.
#[test]
fn the_census_of_the_fixture_is_its_text()
{
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/workspace");
    let target = Path::new(env!("CARGO_TARGET_TMPDIR")).join("twin-census-fixture");
    let output = run(&root, &["--cost"], &target);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(output.status.success(), "the census is printed: {stderr}");
    assert_eq!(
        String::from_utf8_lossy(&output.stdout),
        FIXTURE,
        "the census is the fixture's"
    );
    assert!(
        stderr.contains("twin-census: cargo metadata: 1 call, ")
            && stderr.contains("twin-census: read rustdoc: 2 calls, "),
        "the cost names each part: {stderr}"
    );
}

/// A root with no workspace exits one, and standard error has the message of
/// cargo.
#[test]
fn a_root_with_no_workspace_exits_one()
{
    let target = Path::new(env!("CARGO_TARGET_TMPDIR")).join("twin-census-none");
    let output = run(Path::new(env!("CARGO_TARGET_TMPDIR")), &[], &target);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(
        output.status.code(),
        Some(1_i32),
        "a fault exits one: {stderr}"
    );
    assert!(
        stderr.starts_with("twin-census: `cargo metadata` failed: "),
        "the refusal names the command: {stderr}"
    );
    assert!(output.stdout.is_empty(), "no census is printed");
}
