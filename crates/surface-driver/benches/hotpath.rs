//! The `gandr` series of the benchmark report: fixed workloads run once each
//! under the hotpath profiler. Each workload's function states what it runs
//! and what its block measures, and `main` runs them in order.
//!
//! Each language-server workload serves its session on the bench's thread,
//! and a client on a thread of its own speaks to it over pipes
//! (`lsp`). A workload's block runs on the client's thread, so it
//! counts the client's allocations alone. The server's allocations are
//! counted under its own functions, `recheck::judge_laid` among them.
//!
//! A walk and a staging run serial. `--jobs <n>` after the `--` of the
//! `cargo bench` line runs them on `n` threads, as the scaling account does at
//! each width of its curve (`mise run bench:scaling`).
//!
//! # Items
//!
//! | Block | Workload |
//! | ----- | -------- |
//! | `closure check` | [`closure_check`] |
//! | `stage readmission` | [`stage_readmission`] |
//! | `rule completion` | [`rule_completion`] |
//! | `component walk` | [`component_walk`] |
//! | `component floor` | [`component_floor`] |
//! | `prelude resolve` | [`prelude_resolve`] |
//! | `many candidates` | [`many_candidates`] |
//! | `many outputs` | [`many_outputs`] |
//! | `winding lengths` | [`winding_lengths`] |
//! | `negation lengths` | [`negation_lengths`] |
//! | `lsp first keystroke`, `lsp keystroke` | [`lsp_keystrokes`] |
//! | `lsp burst` | [`lsp_burst`] |
//! | `lsp comment edit` | [`lsp_comment_edit`] |
//! | `distinct definitions, serial`, `distinct definitions, two jobs` | [`distinct_definitions`] |
//!
//! # Dependencies
//!
//! Built with `--features hotpath`, which turns on the profiler in every
//! measured crate, counts allocations through the profiler's global
//! allocator, and links the upload client. The run prints the report on exit;
//! `mise run ci:hotpath` runs it three times in GitHub Actions and uploads it
//! as `gandr`, as `gandr-timing` and as `gandr-bytes`, and hotpath Cloud
//! compares a pull request's reports with its base's and comments when one
//! changed. The `gandr-bytes` run measures allocations in bytes, and Cloud
//! checks the budgets of `hotpath/gandr-bytes-policy.toml` on each report.
//!
//! Cloud gives a pull request a per-function comparison of time and
//! allocations against its base, with no baseline storage of our own.
//! Allocation counts are exact for a fixed workload, so `gandr`
//! (`hotpath/gandr-policy.toml`) judges them at 2% in every crate. Wall-clock
//! time on a shared runner is not exact, so `gandr-timing`
//! (`hotpath/gandr-timing-policy.toml`) judges the average of functions called
//! at least 20 times at 7.5%, only in the crates a change reaches.

#![expect(
    clippy::expect_used,
    clippy::panic,
    reason = "a measurement binary: a workload that cannot start ends the run"
)]

#[path = "shared/lsp.rs"]
mod lsp;
#[path = "shared/support.rs"]
mod support;

use core::fmt::Write as _;
use core::num::NonZeroUsize;
use std::path::Path;
use std::path::PathBuf;

use gandr_surface_dispatcher::Invocation;
use gandr_surface_dispatcher::Outcome;
use gandr_surface_dispatcher::Pool;
use gandr_surface_dispatcher::ProgramSpec;
use gandr_surface_dispatcher::Threads;
use gandr_surface_dispatcher::Width;
use lsp::live;
use support::check;
use support::check_at;
use support::corpus;
use support::width;

/// The source the closure check and the keystroke run on: the largest model
/// source's closure.
const SOURCE: &str = "../../corpus/model/desc/lc/model-record.gandr";

/// The staged programs whose certificates the kernel readmits.
const PROGRAMS: [&str; 2] = ["pow:0..8", "double:0..8"];

/// How many keystrokes the burst sends, one character erased by each.
const BURST: usize = 8;

/// The sources whose rule blocks complete: the group laws, a block whose pairs
/// part at a non-value, and a block refused because its completion never ends.
const COMPLETION: [&str; 3] = [
    "../../corpus/model/identity/group-laws.gandr",
    "../../corpus/model/desc/rules-completed.gandr",
    "../../corpus/pathological/desc/rules-never-complete.gandr",
];

/// The directory the component walk checks: twenty-one sources in seventeen
/// components, each laid after the prelude. A component whose first source is
/// a `std` module settles under the strict root and the rest under the fixture
/// root, so the walk judges the prelude once under each.
const COMPONENTS: &str = "../../corpus/model/control";

/// The component the prelude resolve checks: `==` and `<` at the integers and
/// the strings, and `==` at a point through a derived member.
const RESOLVE: &str = "../../corpus/model/modules/prelude-resolve.gandr";

/// The source the many candidates check: sixteen models of one theory, each
/// forced at one of sixteen calls in one body.
const MANY: &str = "../../corpus/model/modules/model-resolution-many.gandr";

/// The source the many outputs check: division with remainder, an operation
/// of two outputs, and a run that binds both outputs of its call.
const MANY_OUTPUTS: &str = "../../corpus/model/desc/many-out-op.gandr";

/// The source the winding lengths check: three loop words, each wound by a
/// run.
const WINDING: &str = "../../corpus/model/identity/winding-lengths.gandr";

/// The source the negation lengths check: three negation composites, each
/// transported along by a run.
const NEGATION: &str = "../../corpus/model/identity/negation-lengths.gandr";

/// How many one-definition components the component floor checks.
const FLOOR: usize = 64;

/// How many distinct plain definitions each of the two sources of the
/// distinct definitions holds.
const DISTINCT: usize = 5_000;

/// The path of [`SOURCE`] from the driver's manifest directory.
///
/// # Specification
/// trivial.
fn source() -> PathBuf
{
    corpus(Path::new(SOURCE))
}

/// Check the closure of [`SOURCE`], as `gandr check` of the largest model
/// source and its imports does. The block measures the checker's
/// per-declaration judgement and the kernel bridge's readmission.
///
/// # Specification
/// trivial.
fn closure_check()
{
    check(vec![source()]);
}

/// Check the [`COMPLETION`] sources, every rule block decided and completed.
/// The block measures each rule block's decision, and the completion's
/// overlap queries and normalization.
///
/// # Specification
/// trivial.
fn rule_completion()
{
    check(
        COMPLETION
            .iter()
            .map(|relative| corpus(Path::new(relative)))
            .collect(),
    );
}

/// Check every source under [`COMPONENTS`], component by component. The
/// block measures the prelude's lowering and judgement, once per walk, and
/// each component's own.
///
/// # Specification
/// trivial.
fn component_walk()
{
    check(vec![corpus(Path::new(COMPONENTS))]);
}

/// Check [`RESOLVE`], every comparison resolved through the prelude. The
/// block measures the prelude's lowering and judgement (`lower_closure`,
/// `judge_closure`), the candidates a model slot collects
/// (`Lowerer::model_candidates`), each candidate's packing, an include's among
/// them (`Lowerer::packed_structure`), the include's reduct maps
/// (`Lowerer::mint_reducts`), the checker's trial of each candidate
/// (`Deferrals::resolve`) and the derived equality (`Lowerer::mint_generics`).
///
/// # Specification
/// trivial.
fn prelude_resolve()
{
    check(vec![corpus(Path::new(RESOLVE))]);
}

/// Check [`MANY`], each of its sixteen slots trying every candidate. The block
/// measures each candidate's trial against the one solver store all sixteen
/// slots share (`tried`), and the slots' resolution (`Deferrals::resolve`).
///
/// # Specification
/// trivial.
fn many_candidates()
{
    check(vec![corpus(Path::new(MANY))]);
}

/// Check [`MANY_OUTPUTS`]: its operation of two outputs, its rules and its
/// run. The block measures the operation's lowering, the kernel's link of its
/// rules to its body, and the run of the call, which returns both outputs with
/// no product.
///
/// # Specification
/// trivial.
fn many_outputs()
{
    check(vec![corpus(Path::new(MANY_OUTPUTS))]);
}

/// Check [`WINDING`]: the loop words of 100, 10³ and 10⁵ letters, each built,
/// wound and forced by a run, as cctt's `tests/bench/s1.cctt` winds them. The
/// block measures the run machine's reduction of each word, and the checker's
/// and the kernel's judgement of the source.
///
/// # Specification
/// trivial.
fn winding_lengths()
{
    check(vec![corpus(Path::new(WINDING))]);
}

/// Check [`NEGATION`]: the transport of `true` along composites of 101,
/// 10³ + 1 and 10⁵ + 1 negation paths, each built and transported along by a
/// run, as cctt's `tests/bench/negPath.cctt` transports it. The block measures
/// the run machine's application of each path's map, and the checker's and the
/// kernel's judgement of the source.
///
/// # Specification
/// trivial.
fn negation_lengths()
{
    check(vec![corpus(Path::new(NEGATION))]);
}

/// Check [`FLOOR`] components of one definition each, written under a
/// directory of their own: each component's cost is what it pays for the
/// prelude its judgement reuses. The block measures that cost: the
/// component's lowering resumed onto the prelude's (`lower_onto_closure`), its
/// program continued from the prelude's (`Program::after`) and its readmission
/// resumed from the prelude's record (`Crossed::resume`).
///
/// # Specification
/// trivial.
fn component_floor()
{
    let directory =
        std::env::temp_dir().join(format!("gandr-hotpath-floor-{}", std::process::id()));
    std::fs::create_dir_all(&directory).expect("the floor's directory is created");
    for component in 0 .. FLOOR {
        std::fs::write(
            directory.join(format!("floor{component}.gandr")),
            format!("def floor{component} = {component} ;\n"),
        )
        .expect("a floor component is written");
    }
    check(vec![directory.clone()]);
    std::fs::remove_dir_all(&directory).expect("the floor's directory is removed");
}

/// Check two sources of [`DISTINCT`] distinct plain definitions each, written
/// under a directory of their own: first on one thread, then at two jobs, or
/// at the series' width when it is wider. A commit beside an open check
/// costs what a commit beside none costs, so the wider block allocates what
/// the serial one allocates; a copy of a structure that an open check shares
/// shows as the difference. The serial block measures each declaration's
/// check and commit, the cost that the wider run must match. The wider block
/// runs under the policy that the driver installs for its width, and measures
/// each commit beside an open check.
///
/// # Specification
/// trivial.
fn distinct_definitions()
{
    let directory =
        std::env::temp_dir().join(format!("gandr-hotpath-distinct-{}", std::process::id()));
    std::fs::create_dir_all(&directory)
        .expect("the directory of the distinct definitions is created");
    for (source, first) in [(1_usize, 0_usize), (2, DISTINCT)] {
        let text = (first .. first.saturating_add(DISTINCT)).fold(
            String::new(),
            |mut text, definition| {
                let _written = writeln!(
                    text,
                    "/// One more definition.\ndef p{definition} : Integer = {definition};"
                );
                text
            },
        );
        std::fs::write(directory.join(format!("p{source}.gandr")), text)
            .expect("a source of distinct definitions is written");
    }
    let wide = if width().threads() == Threads::ONE {
        Width::Threads(Threads::from(NonZeroUsize::MIN.saturating_add(1)))
    }
    else {
        width()
    };
    hotpath::measure_block!(
        "distinct definitions, serial",
        check_at(vec![directory.clone()], Width::SERIAL)
    );
    hotpath::measure_block!(
        "distinct definitions, two jobs",
        check_at(vec![directory.clone()], wide)
    );
    std::fs::remove_dir_all(&directory)
        .expect("the directory of the distinct definitions is removed");
}

/// Stage [`PROGRAMS`] and readmit every certificate they produce, as
/// `gandr stage pow:0..8 double:0..8` does. The block measures the kernel's
/// readmission of each staged certificate.
///
/// # Specification
/// trivial.
fn stage_readmission()
{
    let programs = PROGRAMS
        .iter()
        .map(|spelled| spelled.parse::<ProgramSpec>().expect("a staged program"))
        .collect();
    let Outcome::Stage(staging) = gandr_surface_dispatcher::dispatch(Invocation::Stage {
        programs,
        width: width(),
    })
    else {
        panic!("stage dispatches a staging");
    };
    let pool = Pool::new(staging.width());
    let run = staging.run(&pool).expect("the staging runs");
    core::hint::black_box(run.digest());
}

/// Open [`SOURCE`] in a language-server session and wait for the open's
/// judgement. Erase its middle line, timed as the first keystroke, then the
/// line after it, timed as a keystroke with the closure warm. The first block
/// measures the server's first recheck, which also builds the closure's
/// lowering and judgement once. The second measures the server's recheck with
/// the closure warm, the cost each later keystroke pays.
///
/// # Specification
/// trivial.
fn lsp_keystrokes()
{
    let text = std::fs::read_to_string(source()).expect("the model source reads");
    let lines: Vec<&str> = text.lines().collect();
    let middle = lines.len().checked_div(2).unwrap_or_default();
    let (before, after) = lines
        .split_at_checked(middle)
        .expect("the middle line is a line of the source");
    // The source with the middle line and the `skipped - 1` lines after it left
    // out.
    let kept = |skipped: usize| {
        before
            .iter()
            .chain(after.iter().skip(skipped))
            .copied()
            .collect::<Vec<&str>>()
            .join("\n")
    };
    let first = kept(1);
    let second = kept(2);
    live(&source(), text, move |client| {
        hotpath::measure_block!("lsp first keystroke", client.change(&[first]))?;
        hotpath::measure_block!("lsp keystroke", client.change(&[second]))
    })
    .expect("the session serves its keystrokes");
}

/// Open [`SOURCE`] in a language-server session and wait for the open's
/// judgement. Erase the last [`BURST`] characters of its middle line one
/// keystroke at a time, every keystroke a content change of one notification,
/// timed as one burst. The block measures the server's recheck, once per
/// burst.
///
/// # Specification
/// trivial.
fn lsp_burst()
{
    let text = std::fs::read_to_string(source()).expect("the model source reads");
    let lines: Vec<&str> = text.lines().collect();
    let erased_at = lines.len().checked_div(2).unwrap_or_default();
    let edits: Vec<String> = (1 ..= BURST)
        .map(|erased| {
            lines
                .iter()
                .enumerate()
                .map(|(at, line)| {
                    if at == erased_at {
                        let kept = line.chars().count().saturating_sub(erased);
                        line.chars().take(kept).collect()
                    }
                    else {
                        String::from(*line)
                    }
                })
                .collect::<Vec<String>>()
                .join("\n")
        })
        .collect();
    live(&source(), text, move |client| {
        hotpath::measure_block!("lsp burst", client.change(&edits))
    })
    .expect("the session serves its burst");
}

/// Open the group laws in a language-server session and wait for the open's
/// judgement. Add a comment line before their first, outside the rule block,
/// timed as one change. The block measures the server's recheck and each rule
/// block's decision, which no change of the block's own text asks for.
///
/// # Specification
/// trivial.
fn lsp_comment_edit()
{
    let laws = corpus(Path::new(COMPLETION[0]));
    let text = std::fs::read_to_string(&laws).expect("the group laws read");
    let edited = format!("// Edited.\n{text}");
    live(&laws, text, move |client| {
        hotpath::measure_block!("lsp comment edit", client.change(&[edited]))
    })
    .expect("the session serves its comment edit");
}

/// Run each workload once under its own measured block. A language-server
/// workload times its changes alone, each under its own block.
///
/// # Specification
/// trivial.
#[hotpath::main]
fn main()
{
    hotpath::measure_block!("closure check", closure_check());
    hotpath::measure_block!("stage readmission", stage_readmission());
    hotpath::measure_block!("rule completion", rule_completion());
    hotpath::measure_block!("component walk", component_walk());
    hotpath::measure_block!("component floor", component_floor());
    hotpath::measure_block!("prelude resolve", prelude_resolve());
    hotpath::measure_block!("many candidates", many_candidates());
    hotpath::measure_block!("many outputs", many_outputs());
    hotpath::measure_block!("winding lengths", winding_lengths());
    hotpath::measure_block!("negation lengths", negation_lengths());
    lsp_keystrokes();
    lsp_burst();
    lsp_comment_edit();
    // Last: its wider check installs the driver's policy for the process, so
    // each workload after it would run under that policy.
    distinct_definitions();
}
