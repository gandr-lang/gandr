//! `gandr run` of the randomness exemplar: the host draws from the entropy
//! source of the operating system, and the run exits with the sum of two
//! draws of two bits.

use std::path::Path;
use std::process::Command;

/// #5707: `gandr run` of the draws exemplar exits with the sum of two draws
/// of two bits, from 0 to 6. It prints nothing, and it writes nothing on
/// standard error.
#[test]
fn gandr_run_sums_two_draws_of_two_bits_5707()
{
    let exemplar =
        Path::new(env!("CARGO_MANIFEST_DIR")).join("../../corpus/model/probability/draws.gandr");
    let ran = Command::new(env!("CARGO_BIN_EXE_gandr"))
        .arg("run")
        .arg(&exemplar)
        .env(
            "XDG_CONFIG_HOME",
            std::env::temp_dir().join("gandr-driver-unconfigured"),
        )
        .output()
        .expect("the run starts");
    let stderr = String::from_utf8_lossy(&ran.stderr);
    assert!(
        ran.status
            .code()
            .is_some_and(|sum| (0_i32 ..= 6_i32).contains(&sum)),
        "the run exits with a sum from 0 to 6: {:?}, {stderr}",
        ran.status
    );
    assert_eq!(
        (String::from_utf8_lossy(&ran.stdout), stderr),
        (String::new().into(), String::new().into()),
        "the run prints nothing, and writes nothing on standard error"
    );
}
