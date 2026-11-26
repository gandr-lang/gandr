//! The rendered refusals of the corpus's refusing sources, as the writer of
//! the outputs crate gives them. The store of outputs holds each text, and a
//! landing compares it with the text of its base.
//!
//! The cases, in a `cfg(test)` module so the crate's lint wall reads them as
//! test code rather than as shipping code.

use std::path::Path;
use std::path::PathBuf;

use gandr_workflow_outputs::refusals::REFUSING;
use gandr_workflow_outputs::refusals::rendered;

/// The checkout's root, as the walk reaches it.
///
/// # Specification
/// trivial.
fn repository() -> PathBuf
{
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .canonicalize()
        .expect("the checkout's root resolves")
}

/// Every refusing source's rendered refusals are a text that two checkouts
/// share: it names no path of the checkout, and its last line ends. A text
/// that named the checkout would differ between two hosts, and the store
/// would hold a change that no source made.
#[test]
fn every_refusing_source_renders_a_text_that_names_no_checkout()
{
    let repository = repository();
    let roots = REFUSING
        .iter()
        .map(|directory| repository.join("corpus").join(directory))
        .collect();
    let refusals = rendered(&repository, roots).expect("every refusing source reads");
    assert!(
        !refusals.is_empty(),
        "the refusing sources print their refusals"
    );
    let checkout = repository.display().to_string();
    let named: Vec<&PathBuf> = refusals
        .iter()
        .filter(|&(_, text)| text.contains(&checkout))
        .map(|(source, _)| source)
        .collect();
    assert!(
        named.is_empty(),
        "refusals that name the checkout: {named:?}"
    );
    let open: Vec<&PathBuf> = refusals
        .iter()
        .filter(|&(_, text)| !text.ends_with('\n'))
        .map(|(source, _)| source)
        .collect();
    assert!(
        open.is_empty(),
        "refusals whose last line does not end: {open:?}"
    );
}

/// The cyclic circuit's refusal names its port. The walk reads that source
/// alone, as a refusal of one source reads nothing beside it.
#[test]
fn cyclic_circuit_wiring_names_its_port_5805()
{
    let source = "pathological/circuit/circuit-cyclic-wiring.gandr";
    let repository = repository();
    let refusals = rendered(&repository, vec![repository.join("corpus").join(source)])
        .expect("the cyclic circuit fixture reads");
    let rendered = refusals
        .get(Path::new(source))
        .expect("the cyclic circuit fixture is refused");
    assert!(
        rendered.contains("port `z`"),
        "the cyclic circuit refusal names its port: {rendered}"
    );
}
