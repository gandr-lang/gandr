//! The `gandr` series of the benchmark report: fixed workloads run once each
//! under the hotpath profiler.
//!
//! | Workload | What it runs | Measured functions |
//! | -------- | ------------ | ------------------ |
//! | `closure check` | `gandr check` of the largest model source and its imports | the checker's per-declaration judgement and the kernel bridge's readmission |
//! | `stage readmission` | `gandr stage pow:0..8 double:0..8` | the kernel's readmission of each staged certificate |
//! | `rule completion` | `gandr check` of the corpus's completion sources: the group laws, a completed block, and a block whose completion never ends | each rule block's decision, and the completion's overlap queries and normalization |
//! | `component walk` | `gandr check` of a directory of twenty sources in sixteen components, each laid after the prelude | the prelude's lowering and judgement, once per walk, and each component's own |
//! | `component floor` | `gandr check` of a directory of sixty-four components of one definition each, every one laid after the prelude | what each component pays to reuse the prelude's judgement: its lowering resumed onto the prelude's (`lower_onto_closure`), its program continued from the prelude's (`Program::after`) and its readmission resumed from the prelude's record (`Crossed::resume`) |
//! | `prelude resolve` | `gandr check` of one component whose `==` and `<` resolve at the integers, the strings and a point whose `Eq` member is derived | the prelude's lowering and judgement (`lower_closure`, `judge_closure`), the candidates a model slot collects (`Lowerer::model_candidates`), each candidate's packing, an include's among them (`Lowerer::packed_structure`), the include's reduct maps (`Lowerer::mint_reducts`), the checker's trial of each candidate (`Deferrals::resolve`) and the derived equality (`Lowerer::mint_generics`) |
//! | `many candidates` | `gandr check` of one body calling a function sixteen times, each call leaving out a model implicit sixteen modules in scope answer | each candidate's trial against the one solver store all sixteen slots share (`tried`), and the slots' resolution (`Deferrals::resolve`) |
//! | `lsp first keystroke` | a language-server session that opens the same source, waits for the open's judgement, then erases one line; only the change is timed | the server's first recheck, which also builds the closure's lowering and judgement once |
//! | `lsp keystroke` | the same session after its first keystroke, erasing the next line; only this change is timed | the server's recheck with the closure warm, the cost each later keystroke pays |
//! | `lsp burst` | a session that opens the same source, waits for the open's judgement, then erases the end of its middle line one character per change, every change sent in one write; only the burst is timed | the server's recheck, once per burst |
//! | `lsp comment edit` | a session that opens the group laws, waits for the open's judgement, then adds a comment line before their first, outside the rule block; only the change is timed | the server's recheck and each rule block's decision, which no change of the block's own text asks for |
//!
//! Each language-server workload serves its session on the bench's thread,
//! and a client on a thread of its own speaks to it over pipes
//! (`lsp`). A workload's block runs on the client's thread, so it
//! counts the client's allocations alone. The server's allocations are
//! counted under its own functions, `recheck::judge_laid` among them.
//!
//! Built with `--features hotpath`, which turns on the profiler in every
//! measured crate, counts allocations through the profiler's global
//! allocator, and links the upload client. The run prints the report on exit;
//! `mise run ci:hotpath` runs it twice in GitHub Actions and uploads it as
//! `gandr` and as `gandr-timing`, and hotpath Cloud compares a pull request's
//! reports with its base's and comments when one changed.
//!
//! # Decision
//!
//! hotpath 0.28 was chosen for its CI comparison service: a pull request gets
//! a per-function comparison of time and allocations against its base, with
//! no baseline storage of our own. Allocation counts are exact for a fixed
//! workload, so `gandr` (`hotpath/gandr-policy.toml`) judges them at 2% in
//! every crate; wall-clock time on a shared runner is not, so `gandr-timing`
//! (`hotpath/gandr-timing-policy.toml`) judges the average of functions called
//! at least 20 times at 7.5%, only in the crates a change reaches.
//! Rejected: criterion and divan time a closure in isolation and keep their
//! baselines on the machine that ran them; iai-callgrind counts instructions
//! exactly but needs valgrind and gives no per-function allocation view. The
//! choice reverses if the comparison service stops answering, or if
//! instruction counts prove the better regression signal for the same lane
//! cost.

#![expect(
    clippy::expect_used,
    clippy::panic,
    reason = "a measurement binary: a workload that cannot start ends the run"
)]

#[path = "shared/lsp.rs"]
mod lsp;
mod support;

use std::path::PathBuf;

use gandr_surface_dispatcher::Invocation;
use gandr_surface_dispatcher::Outcome;
use gandr_surface_dispatcher::Pool;
use gandr_surface_dispatcher::ProgramSpec;
use gandr_surface_dispatcher::Width;
use lsp::live;
use support::check;
use support::corpus;

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

/// The directory the component walk checks: twenty sources, three of which
/// import siblings, in sixteen components, each laid after the prelude.
const COMPONENTS: &str = "../../corpus/model/control";

/// The component the prelude resolve checks: `==` and `<` at the integers and
/// the strings, and `==` at a point through a derived member.
const RESOLVE: &str = "../../corpus/model/modules/prelude-resolve.gandr";

/// The source the many candidates check: sixteen models of one theory, each
/// forced at one of sixteen calls in one body.
const MANY: &str = "../../corpus/model/modules/model-resolution-many.gandr";

/// How many one-definition components the component floor checks.
const FLOOR: usize = 64;

/// The path of [`SOURCE`] from the driver's manifest directory.
///
/// # Specification
/// trivial.
fn source() -> PathBuf
{
    corpus(SOURCE)
}

/// Check the closure of [`SOURCE`].
///
/// # Specification
/// trivial.
fn closure_check()
{
    check(vec![source()]);
}

/// Check the [`COMPLETION`] sources, every rule block decided and completed.
///
/// # Specification
/// trivial.
fn rule_completion()
{
    check(COMPLETION.iter().map(|relative| corpus(relative)).collect());
}

/// Check every source under [`COMPONENTS`], component by component.
///
/// # Specification
/// trivial.
fn component_walk()
{
    check(vec![corpus(COMPONENTS)]);
}

/// Check [`RESOLVE`], every comparison resolved through the prelude.
///
/// # Specification
/// trivial.
fn prelude_resolve()
{
    check(vec![corpus(RESOLVE)]);
}

/// Check [`MANY`], each of its sixteen slots trying every candidate.
///
/// # Specification
/// trivial.
fn many_candidates()
{
    check(vec![corpus(MANY)]);
}

/// Check [`FLOOR`] components of one definition each, written under a
/// directory of their own: each component's cost is what it pays for the
/// prelude its judgement reuses.
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

/// Stage [`PROGRAMS`] and readmit every certificate they produce.
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
        width: Width::SERIAL,
    })
    else {
        panic!("stage dispatches a staging");
    };
    let pool = Pool::new(staging.width());
    let run = staging.run(&pool).expect("the staging runs");
    core::hint::black_box(run.digest());
}

/// `text` with the lines at `left_out` left out.
///
/// # Specification
/// trivial.
fn erased(
    text: &str,
    left_out: &[usize],
) -> String
{
    text.lines()
        .enumerate()
        .filter(|&(at, _)| !left_out.contains(&at))
        .map(|(_, line)| line)
        .collect::<Vec<&str>>()
        .join("\n")
}

/// Open [`SOURCE`] in a language-server session and wait for the open's
/// judgement. Erase its middle line, timed as the first keystroke, then the
/// line after it, timed as a keystroke with the closure warm.
///
/// # Specification
/// trivial.
fn lsp_keystrokes()
{
    let text = std::fs::read_to_string(source()).expect("the model source reads");
    let middle = text.lines().count().checked_div(2).unwrap_or_default();
    let first = erased(&text, &[middle]);
    let second = erased(&text, &[middle, middle.saturating_add(1)]);
    live(&source(), text, move |client| {
        hotpath::measure_block!("lsp first keystroke", client.change(&[first]))?;
        hotpath::measure_block!("lsp keystroke", client.change(&[second]))
    })
    .expect("the session serves its keystrokes");
}

/// Open [`SOURCE`] in a language-server session and wait for the open's
/// judgement. Erase the last [`BURST`] characters of its middle line one
/// keystroke at a time, every change sent in one write, timed as one burst.
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
/// timed as one change.
///
/// # Specification
/// trivial.
fn lsp_comment_edit()
{
    let laws = corpus(COMPLETION[0]);
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
    lsp_keystrokes();
    lsp_burst();
    lsp_comment_edit();
}
