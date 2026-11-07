//! `gandr run` of the exact reals exemplars: the host admits the plan of the
//! square root of two and prints the two ends of an enclosure of it, its
//! machines decide comparisons, stop by name, and resume from a checkpoint,
//! and it encloses reals that read π, the cosine, the sine and an angle. The
//! machines decide the two bounded quantifiers, and every exemplar of the
//! exact reals runs to its end. The host refuses each pathological plan and
//! checkpoint of stage C by its check, and `gandr check` refuses a capability
//! that claims an operation past its grant. The profile that the
//! configuration names sets the quotas of a run.

use std::path::Path;
use std::path::PathBuf;
use std::process::Command;
use std::process::Output;

use crate::cli::Scratch;
use crate::cli::Text;

/// The root of the repository, where the driver runs so that the paths it
/// names stay relative.
///
/// # Specification
/// trivial.
fn repository() -> PathBuf
{
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../..")
}

/// `gandr run` of `source`, a path from the root of the repository, with no
/// configuration.
///
/// # Specification
/// trivial.
fn run(source: &Path) -> Output
{
    Command::new(env!("CARGO_BIN_EXE_gandr"))
        .arg("run")
        .arg(source)
        .current_dir(repository())
        .env(
            "XDG_CONFIG_HOME",
            std::env::temp_dir().join("gandr-driver-unconfigured"),
        )
        .output()
        .expect("the run starts")
}

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
/// end `exhausted`, or `suspended` at the checker's quota, never `fails`. A
/// machine restored from its checkpoint after one quantum holds with the work
/// of an uninterrupted one.
#[test]
fn gandr_run_decides_comparisons_5703()
{
    let reals = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../corpus/model/reals");
    let unconfigured = std::env::temp_dir().join("gandr-driver-unconfigured");
    for (exemplar, printed) in [
        ("comparison.gandr", "holds\n"),
        (
            "boundary.gandr",
            "exhausted exhausted exhausted\nexhausted exhausted suspended\n",
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

/// #5786: `gandr run` of the trigonometry exemplar decides that
/// `cos (π/4)` and `sin (π/4)` each lie between `0.7071` and `0.7072`. It
/// then prints the two ends of an enclosure of the Euler angle `β₁` for
/// `α₁ = 1`, `α₂ = 1` and `α₃ = 1/2`, and exits 0. The two ends are
/// `0.43052850328517242567…` and `0.43052850328517242704…`, and `β₁` is
/// `0.43052850328517242635…`.
#[test]
fn gandr_run_decides_and_encloses_through_the_builtins_5786()
{
    let exemplar =
        Path::new(env!("CARGO_MANIFEST_DIR")).join("../../corpus/model/reals/trigonometry.gandr");
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
            "holds holds holds holds\n586005032499230016071096543046997561923p-130 \
             586005032499230017944185075441990931755p-130\n"
                .into()
        ),
        "the run prints the verdicts and the enclosure: {}",
        String::from_utf8_lossy(&ran.stderr)
    );
}

/// #5705: `gandr run` of the two quantifier exemplars prints `holds` and
/// exits 0. The overt existential `∃ x ∈ [1, 2] (3 < x · x)` holds by a
/// witness, and the compact universal `∀ x ∈ [0, 1] (x · x < 2)` holds by a
/// cover. The checker replays each certificate before the host replies.
#[test]
fn gandr_run_decides_the_bounded_quantifiers_5705()
{
    for exemplar in ["exists.gandr", "forall.gandr"] {
        let ran = run(&Path::new("corpus/model/reals").join(exemplar));
        assert_eq!(
            (
                ran.status.code(),
                String::from_utf8_lossy(&ran.stdout),
                String::from_utf8_lossy(&ran.stderr)
            ),
            (Some(0_i32), "holds\n".into(), "".into()),
            "{exemplar} prints its verdict"
        );
    }
}

/// #5705: `gandr run` of each pathological source of stage C exits 1 with
/// two lines on standard error and nothing on standard output. The host
/// writes the first line: the operation, then the site and the check that
/// refuse the plan or the checkpoint. The driver then names the source and
/// the operation where `main` is stuck. The forged cut law, the binder
/// outside its scope and the universal without compactness fail at `admit`,
/// and the checkpoint with false evidence fails at `restore`.
#[test]
fn gandr_run_refuses_each_pathological_case_by_its_check_5705()
{
    for (source, refusal) in [
        (
            "forged-cut-law.gandr",
            "std.reals.Eff.admit: the plan is refused at node 10: the evidence table does \
             not register a reference",
        ),
        (
            "unscoped-binder.gandr",
            "std.reals.Eff.admit: the plan is refused at node 1: a bound variable reaches \
             past its binders",
        ),
        (
            "missing-compactness.gandr",
            "std.reals.Eff.admit: the plan is refused at node 5: a quantifier's evidence \
             differs from the evidence of its interval domain",
        ),
        (
            "false-checkpoint.gandr",
            "std.reals.Eff.restore: the checkpoint is refused: the steps of an obligation \
             of the checkpoint do not replay: a point does not lie in the lower cut at step 0",
        ),
    ] {
        let path = Path::new("corpus/pathological/reals").join(source);
        let ran = run(&path);
        let stderr = String::from_utf8_lossy(&ran.stderr);
        let lines: Vec<&str> = stderr.lines().collect();
        assert_eq!(
            (
                ran.status.code(),
                ran.stdout.is_empty(),
                lines.first().copied()
            ),
            (Some(1_i32), true, Some(refusal)),
            "{source}: the host names the check first: {stderr}"
        );
        let stuck = format!(
            "gandr: {}: `main` stuck: operation at command ",
            path.display()
        );
        assert!(
            lines.len() == 2
                && lines.get(1).is_some_and(
                    |line| line.starts_with(&stuck) && line.ends_with(" has no handler")
                ),
            "{source}: the driver names where `main` is stuck: {stderr}"
        );
    }
}

/// #5705: `gandr check --grant admit` of a declaration whose capability
/// claims `admit` and `decide` exits 1. The refusal is
/// `CapabilityUngranted`, and it names the claimed capability with `decide`
/// in it. A grant of both operations refuses no capability.
#[test]
fn gandr_check_refuses_a_capability_past_its_grant_5705()
{
    let scratch = Scratch::new(Path::new("reals-grant-5705"));
    let source = scratch.file(
        Path::new("held.gandr"),
        Text::from("def reals : Cap {admit, decide} ;\n"),
    );
    let check = |grant: &str| {
        Command::new(env!("CARGO_BIN_EXE_gandr"))
            .arg("check")
            .arg("--grant")
            .arg(grant)
            .arg(&source)
            .env(
                "XDG_CONFIG_HOME",
                std::env::temp_dir().join("gandr-driver-unconfigured"),
            )
            .output()
            .expect("the check starts")
    };
    let narrow = check("admit");
    let report = String::from_utf8_lossy(&narrow.stdout);
    assert_eq!(narrow.status.code(), Some(1_i32), "{report}");
    assert!(
        report.contains(
            "error[CapabilityUngranted]: this capability claims authority the host did not grant"
        ) && report.contains("authority the host did not grant: found `Cap {admit, decide}`"),
        "a capability that claims `decide` past the grant is refused by name: {report}"
    );
    let wide = check("admit,decide");
    assert!(
        !String::from_utf8_lossy(&wide.stdout).contains("CapabilityUngranted"),
        "a grant of both operations refuses no capability: {}",
        String::from_utf8_lossy(&wide.stdout)
    );
}

/// A source that encloses the square root of two no wider than `2^-300`.
const FINE: &str = "import std.io;\nimport std.reals;\nimport std.string (concat);\n\ndef main() -> [std.reals.Eff, std.io.Console.Eff] Integer =\n  let held = std.reals.admit \"4758525001000b0000000000000001000000000200000000000000000000000012000000000100000005000000000000000002010000000100000000000000011203000000040000001402000000050000001201000000000000001204000000030000001307000000080000000800010000000001000000000000000100010100000001000000000000000100060000000900000000000000\"\n  let *{lower, upper} = std.reals.enclose held 300\n  std.io.Console.print (concat lower (concat \" \" upper))\n  0\n";

/// #5704: `[reals] profile` in the configuration of the driver sets the
/// quotas of a run. With no configuration, and under `default`, an enclosure
/// no wider than `2^-300` prints its two ends. Under `bounded` the finest
/// precision is `2^-256`. So the host declines that enclosure, and the run
/// exits 1 with the cause on standard error. The existential still holds
/// under `bounded`. A name that is no profile stops the driver with exit 2
/// before the run starts, and the fault names the file and each profile.
#[test]
fn a_configured_profile_bounds_the_run_5704()
{
    let scratch = Scratch::new(Path::new("reals-profile-5704"));
    let source = scratch.file(Path::new("fine.gandr"), Text::from(FINE));
    let home = |profile: &str| {
        let file = scratch.file(
            &Path::new(profile).join("gandr/config.toml"),
            Text::from(format!("[reals]\nprofile = \"{profile}\"\n").as_str()),
        );
        file.parent()
            .and_then(Path::parent)
            .expect("a configuration home")
            .to_path_buf()
    };
    let run_under = |home: &Path, source: &Path| {
        Command::new(env!("CARGO_BIN_EXE_gandr"))
            .arg("run")
            .arg(source)
            .current_dir(repository())
            .env("XDG_CONFIG_HOME", home)
            .output()
            .expect("the run starts")
    };
    let unconfigured = run(&source);
    let ends = String::from_utf8_lossy(&unconfigured.stdout).into_owned();
    assert_eq!(
        unconfigured.status.code(),
        Some(0_i32),
        "{}",
        String::from_utf8_lossy(&unconfigured.stderr)
    );
    assert_eq!(ends.split_whitespace().count(), 2, "two ends: {ends}");
    let standard = run_under(&home("default"), &source);
    assert_eq!(
        (
            standard.status.code(),
            String::from_utf8_lossy(&standard.stdout)
        ),
        (Some(0_i32), ends.as_str().into()),
        "`default` takes the quotas of a run with no configuration"
    );
    let bounded = home("bounded");
    let refused = run_under(&bounded, &source);
    let stderr = String::from_utf8_lossy(&refused.stderr);
    assert_eq!(
        (
            refused.status.code(),
            String::from_utf8_lossy(&refused.stdout),
            stderr.lines().next()
        ),
        (
            Some(1_i32),
            "".into(),
            Some("std.reals.Eff.enclose: the precision is not from 0 to 256")
        ),
        "{stderr}"
    );
    let searched = run_under(&bounded, Path::new("corpus/model/reals/exists.gandr"));
    assert_eq!(
        (
            searched.status.code(),
            String::from_utf8_lossy(&searched.stdout)
        ),
        (Some(0_i32), "holds\n".into()),
        "{}",
        String::from_utf8_lossy(&searched.stderr)
    );
    let unknown = home("fast");
    let stopped = run_under(&unknown, &source);
    assert_eq!(
        (
            stopped.status.code(),
            String::from_utf8_lossy(&stopped.stdout),
            String::from_utf8_lossy(&stopped.stderr)
        ),
        (
            Some(2_i32),
            "".into(),
            format!(
                "gandr: {}: `reals.profile` is `fast`; it names `default` or `bounded`\n",
                unknown.join("gandr/config.toml").display()
            )
            .into()
        )
    );
}

/// #5705: the gate of stage C. `gandr run` of every exemplar of the exact
/// reals exits 0 and writes nothing on standard error. An exemplar is a
/// source of `corpus/model/reals/` that declares `main`, so the base source
/// of shared declarations is not run. The host admits each plan, and each
/// machine certifies or stops with a named outcome.
#[test]
fn every_exact_reals_exemplar_runs_to_its_end_5705()
{
    let directory = Path::new("corpus/model/reals");
    let mut sources: Vec<PathBuf> = std::fs::read_dir(repository().join(directory))
        .expect("the exemplars are read")
        .map(|entry| entry.expect("an entry is read").file_name())
        .filter(|name| {
            Path::new(name)
                .extension()
                .is_some_and(|extension| extension == "gandr")
        })
        .map(|name| directory.join(name))
        .filter(|source| {
            std::fs::read_to_string(repository().join(source))
                .expect("a source is read")
                .lines()
                .any(|line| line.starts_with("def main("))
        })
        .collect();
    sources.sort();
    assert!(
        sources.len() >= 7,
        "the exemplars of stages A to C: {sources:?}"
    );
    for source in &sources {
        let ran = run(source);
        assert_eq!(
            (ran.status.code(), String::from_utf8_lossy(&ran.stderr)),
            (Some(0_i32), "".into()),
            "{}: the run ends, and the host declines nothing: {}",
            source.display(),
            String::from_utf8_lossy(&ran.stdout)
        );
    }
}
