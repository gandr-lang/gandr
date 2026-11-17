//! The specification facade: a specified function runs its body in its own
//! frame, so its specification costs no call of its own.

use alloc::string::ToString as _;
use std::backtrace::Backtrace;
use std::backtrace::BacktraceStatus;

use anodized::spec;
use gandr_surface_syntax::NodeCount;
use gandr_surface_syntax::NodeIndex;
use gandr_surface_syntax::SourceText;

use crate::common::GRAMMAR;

/// The backtrace taken inside a specified body, after it reads every node of
/// `text`'s tree, as a lookup in the edit loop does.
///
/// # Specification
/// - requires: nothing.
/// - ensures: a captured backtrace, or the platform's unsupported one; never a
///   disabled one, since the capture is forced.
/// - fails: never.
/// - panics: when `text` does not parse.
///
/// # Adequacy
/// - hypothesis: L3 — the witness reads the frames of the one call.
/// - witness: `tests::specification::a_specified_body_runs_in_no_helper_frame_4507`
#[spec(ensures: |ret| ret.0.status() != BacktraceStatus::Disabled)]
#[inline(never)]
fn read_then_captured(text: SourceText<'_>) -> (Backtrace, NodeCount)
{
    let parsed = gandr_surface_parser::parse(&GRAMMAR, text).expect("the text parses");
    let tree = parsed.tree();
    let read = tree
        .positions()
        .filter(|&position: &NodeIndex| tree.node(position).is_some())
        .count();
    (Backtrace::force_capture(), NodeCount::from(read))
}

/// #4507: at the size-optimised profile every specified function ran its body
/// behind a call into the specification backend's `eval_once`, and a small
/// lookup paid that call on every read. The backend now inlines its helpers:
/// a backtrace taken inside a specified body shows the function's own frame
/// and no frame of the backend.
///
/// A build with line tables prints an inlined frame under its own name too, so
/// only a build without them, the test profile's, reads the call frames alone.
#[test]
fn a_specified_body_runs_in_no_helper_frame_4507()
{
    let (trace, read) = read_then_captured(SourceText::from("def answer : Integer = 42\n"));
    assert!(usize::from(read) > 0, "the tree holds nodes");
    let trace = trace.to_string();
    let own = trace
        .lines()
        .skip_while(|line| !line.contains("read_then_captured"))
        .nth(1)
        .unwrap_or_default();
    if own.trim_start().starts_with("at ") && own.contains("specification.rs") {
        return;
    }
    assert!(
        trace.contains("read_then_captured"),
        "the specified function keeps its frame:\n{trace}"
    );
    assert!(
        !trace.contains("anodized::__::"),
        "no frame of the specification backend:\n{trace}"
    );
}
