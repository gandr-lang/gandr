//! `gandr run` of the exact reals exemplar: the host admits the plan of the
//! square root of two and prints the two ends of an enclosure of it.

use std::path::Path;
use std::process::Command;

/// #5700: `gandr run` of the square root of two prints the two ends of an
/// enclosure no wider than `2^-64`, each spelled `<mantissa>p<exponent>`,
/// and exits 0. The upper end less the lower end is `1 / 2^64`, and the
/// lower end is `1.41421356237309504…`.
#[test]
fn gandr_run_encloses_the_square_root_of_two_5700()
{
    let exemplar =
        Path::new(env!("CARGO_MANIFEST_DIR")).join("../../corpus/model/reals/sqrt-two.gandr");
    let unconfigured = std::env::temp_dir().join("gandr-driver-unconfigured");
    let ran = Command::new(env!("CARGO_BIN_EXE_gandr"))
        .arg("run")
        .arg(&exemplar)
        .env("XDG_CONFIG_HOME", &unconfigured)
        .output()
        .expect("the run starts");
    assert_eq!(
        (ran.status.code(), String::from_utf8_lossy(&ran.stdout)),
        (
            Some(0_i32),
            "3260954456333195553p-61 26087635650665564425p-64\n".into()
        ),
        "the run prints the enclosure: {}",
        String::from_utf8_lossy(&ran.stderr)
    );
}
