//! `gandr run` of the exact reals exemplars: the host admits the plan of the
//! square root of two and prints the two ends of an enclosure of it, and its
//! machines decide comparisons, stop by name, and resume from a checkpoint.

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

/// #5703: `gandr run` of the three comparison exemplars prints each verdict
/// by name and exits 0. `sqrt 2 < 3/2` holds. The two boundary comparisons
/// end `exhausted` and `suspended` at each budget, never `fails`. A machine
/// restored from its checkpoint after one quantum holds with the work of an
/// uninterrupted one.
#[test]
fn gandr_run_decides_comparisons_5703()
{
    let reals = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../corpus/model/reals");
    let unconfigured = std::env::temp_dir().join("gandr-driver-unconfigured");
    for (exemplar, printed) in [
        ("comparison.gandr", "holds\n"),
        (
            "boundary.gandr",
            "exhausted exhausted exhausted\nsuspended suspended suspended\n",
        ),
        ("resume.gandr", "exhausted\nholds\nthe same work\n"),
    ] {
        let ran = Command::new(env!("CARGO_BIN_EXE_gandr"))
            .arg("run")
            .arg(reals.join(exemplar))
            .env("XDG_CONFIG_HOME", &unconfigured)
            .output()
            .expect("the run starts");
        assert_eq!(
            (ran.status.code(), String::from_utf8_lossy(&ran.stdout)),
            (Some(0_i32), printed.into()),
            "{exemplar} prints its verdicts: {}",
            String::from_utf8_lossy(&ran.stderr)
        );
    }
}
