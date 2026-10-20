//! Every corpus run through a described operation, held against the engine's
//! certified normal form of the call it runs.
//!
//! A block's rules are read twice: the operation route compiles them to the
//! first-match decision tree the machine runs, and the cell layer rewrites a
//! call to its normal form, the path certified by replaying it. The lowering
//! admits a block only when the two readings coincide on every term; this is
//! the differential witness that they do on the corpus's own calls, under
//! whichever specification mode the suite runs in.
//!
//! The differential, in a `cfg(test)` module so the crate's lint wall reads
//! it as test code rather than as shipping code.

use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use std::path::PathBuf;

use anodized::spec;
use gandr_surface_corpus::CorpusRoot;
use gandr_surface_corpus::Outcome;
use gandr_surface_corpus::Runner as _;
use gandr_surface_corpus::Stated;
use gandr_surface_dispatcher::Composed;
use gandr_surface_dispatcher::HostGrant;
use gandr_surface_dispatcher::Lowered;
use gandr_surface_dispatcher::LoweringCount;
use gandr_surface_dispatcher::judge_module;
use gandr_surface_dispatcher::lower_source;
use gandr_surface_grammar::built_in;
use gandr_surface_lowering::coincide::CallText;
use gandr_surface_syntax::SourceFragment;
use gandr_surface_syntax::SourceText;
use quenchant_shape::shape::Maybe;

/// Every corpus source under the strict and fixture roots, the pending
/// set aside: a pending source is not yet read whole.
///
/// # Specification
/// - requires: the corpus directories list and read.
/// - ensures: every `.gandr` file below either root with no `pending` directory
///   on its path, once each, in path order.
/// - panics: if a directory does not list.
///
/// # Adequacy
/// - hypothesis: L3 — the differential reaches the described sources of both
///   roots; a walk that missed a root reads no run through a described
///   operation and fails the non-vacuity assertion.
/// - witness: `tests::coincide::every_run_through_a_described_operation_is_its_calls_normal_form`
#[spec(ensures: |ref ret| ret.iter().all(|path|
        path.extension().is_some_and(|extension| extension == "gandr")))]
fn sources() -> BTreeSet<PathBuf>
{
    let corpus = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../surface-corpus");
    let mut directories = vec![corpus.join("strict"), corpus.join("fixture")];
    let mut found = BTreeSet::new();
    while let Some(directory) = directories.pop() {
        for entry in std::fs::read_dir(&directory).expect("the directory lists") {
            let path = entry.expect("the entry reads").path();
            if path.is_dir() {
                if !path.ends_with("pending") {
                    directories.push(path);
                }
            }
            else if path
                .extension()
                .is_some_and(|extension| extension == "gandr")
            {
                let _new = found.insert(path);
            }
        }
    }
    found
}

/// The body of the thunk `name` is defined as in `text`: the bytes between
/// `def name = thunk {` and the brace that closes it.
///
/// # Specification
/// - ensures: absent when `text` defines no thunk of that name; otherwise the
///   text inside its braces, nested braces kept.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — as the differential: a body cut short reads no call and
///   the run is reported as no direct call.
/// - witness: `tests::coincide::every_run_through_a_described_operation_is_its_calls_normal_form`
#[spec(ensures: |ret| ret.as_deref().is_none_or(|body| text.as_ref().contains(body)))]
fn thunk_body(
    text: SourceText<'_>,
    name: SourceFragment<'_>,
) -> Option<String>
{
    let opening = format!("def {name} = thunk {{");
    let text: &str = text.as_ref();
    let start = text.find(&opening)?.saturating_add(opening.len());
    let rest = text.get(start ..)?;
    let mut depth = 0_usize;
    for (offset, character) in rest.char_indices() {
        match character {
            '{' => depth = depth.saturating_add(1),
            '}' if depth == 0 => return rest.get(.. offset).map(String::from),
            '}' => depth = depth.saturating_sub(1),
            _ => {},
        }
    }
    None
}

/// The call a thunk's body is, when the body is one call delivered
/// unchanged: `become f(…)`, `f(…)`, or `run p <- f(…); return p`.
///
/// # Specification
/// - ensures: present only for a body of one of the three shapes, the call an
///   identifier applied to one balanced argument list, with white space between
///   tokens collapsed.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the corpus's direct calls read, every shape among them; a
///   body that does more than deliver its call reads none and fails the
///   differential by name.
/// - witness: `tests::coincide::every_run_through_a_described_operation_is_its_calls_normal_form`
#[spec(ensures: |ret| ret.as_deref().is_none_or(|call| call.ends_with(')')))]
fn direct_call(body: SourceFragment<'_>) -> Option<String>
{
    let spaced = body
        .as_ref()
        .split_whitespace()
        .collect::<Vec<_>>()
        .join(" ");
    let spaced = spaced.trim_end_matches(';').trim_end();
    let call = if let Some(call) = spaced.strip_prefix("become ") {
        call
    }
    else if let Some(bound) = spaced.strip_prefix("run ") {
        let (pattern, rest) = bound.split_once(" <- ")?;
        let (call, returned) = rest.split_once("; return ")?;
        if returned.trim_end_matches(';').trim() != pattern {
            return None;
        }
        call
    }
    else {
        spaced
    };
    let (head, arguments) = call.split_once('(')?;
    let identifier = !head.is_empty()
        && head
            .chars()
            .all(|character| character.is_alphanumeric() || character == '_');
    let mut depth = 1_usize;
    let mut closed = None;
    for (offset, character) in arguments.char_indices() {
        match character {
            '(' => depth = depth.saturating_add(1),
            ')' => {
                depth = depth.saturating_sub(1);
                if depth == 0 {
                    closed = Some(offset);
                    break;
                }
            },
            _ => {},
        }
    }
    (identifier && closed == Some(arguments.len().saturating_sub(1))).then(|| String::from(call))
}

#[test]
fn every_run_through_a_described_operation_is_its_calls_normal_form()
{
    let grammar = built_in().expect("the built-in grammar builds");
    let mut lowerings = LoweringCount::default();
    let mut compared = 0_usize;
    let mut operations: Vec<String> = Vec::new();
    let mut needle = String::new();
    for path in sources() {
        let text = std::fs::read_to_string(&path).expect("the source reads");
        let shown = path.display();
        let Lowered::Module { module, arena } =
            lower_source(&grammar, SourceText::from(text.as_str()), &mut lowerings)
                .unwrap_or_else(|fault| panic!("{shown}: {fault}"))
                .into_lowered()
        else {
            continue;
        };
        // A presentation's operations are interpreted by its models and
        // run nowhere; only a family's operations have runs to compare.
        operations.clear();
        operations.extend(
            module
                .descriptions()
                .declarations
                .iter()
                .filter(|described| matches!(described.presentation, Maybe::Absent(_)))
                .flat_map(|described| described.description.opers.iter())
                .map(|operation| String::from(operation.name.as_ref())),
        );
        if operations.is_empty() {
            continue;
        }
        let mut calls = Vec::new();
        for declaration in module.declarations() {
            let name = declaration.name();
            let Some(body) = thunk_body(
                SourceText::from(text.as_str()),
                SourceFragment::from(name.as_ref()),
            )
            else {
                continue;
            };
            let named = operations.iter().find(|operation| {
                needle.clear();
                for part in [operation.as_str(), "("] {
                    needle.push_str(part);
                }
                body.contains(needle.as_str())
            });
            let Some(operation) = named
            else {
                continue;
            };
            let call = direct_call(SourceFragment::from(body.as_str())).unwrap_or_else(|| {
                panic!(
                    "{shown}: `{name}` runs through `{operation}` but is no direct call; the \
                         differential reads a run whose body is the call it delivers"
                )
            });
            let member = module
                .declarations()
                .iter()
                .find(|member| {
                    let name = member.name();
                    call.strip_prefix(AsRef::<str>::as_ref(&name))
                        .is_some_and(|rest| rest.starts_with('('))
                })
                .unwrap_or_else(|| panic!("{shown}: `{call}` names no declaration"));
            let normal = module
                .normal_form(member, CallText::from(call.as_str()))
                .unwrap_or_else(|fault| panic!("{shown}: `{call}`: {fault}"));
            calls.push((
                declaration.constant(),
                name.to_string(),
                call,
                normal.spelling(),
            ));
        }
        let Composed::Settled {
            report,
            mut program,
            ..
        } = judge_module(
            CorpusRoot::Fixture,
            (module, SourceText::from(text.as_str())),
            arena,
            &HostGrant::UNBOUNDED,
        )
        .unwrap_or_else(|fault| panic!("{shown}: {fault}"))
        else {
            panic!("{shown}: the module was refused whole");
        };
        let mut declared = BTreeMap::new();
        for declaration in report.declarations() {
            let _first = declared
                .entry(declaration.constant())
                .or_insert(declaration);
        }
        for (constant, name, call, engine) in calls {
            let runs = declared.get(&constant).is_some_and(|declaration| {
                matches!(declaration.stated(), Stated::Verdict(Outcome::Runs(_)))
            });
            if !runs {
                continue;
            }
            let machine = program.run(constant);
            assert_eq!(
                machine.as_ref(),
                engine,
                "{shown}: `{name}` runs `{call}` to {machine} on the machine; the engine \
                     reads {engine}"
            );
            compared = compared.saturating_add(1);
        }
    }
    assert!(
        compared > 0_usize,
        "the corpus holds a run through a described operation: {compared}"
    );
}
