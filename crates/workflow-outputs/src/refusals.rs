//! The refusals of a refusing corpus source: each diagnostic that
//! `gandr check` prints for it, plain, at the verbosity of a user.
//!
//! A refusal reads more than its source: the standard library, and the other
//! members of a package. So one walk gives the refusals of each source of a
//! checkout, and the input of the kind is the corpus with the library.

use alloc::collections::BTreeMap;
use core::convert::Infallible;
use core::fmt;
use core::ops::ControlFlow;
use std::path::Path;
use std::path::PathBuf;

use gandr_surface_diagnostics::Verbosity;
use gandr_surface_dispatcher::Goals;
use gandr_surface_dispatcher::Pool;
use gandr_surface_dispatcher::Refusals;
use gandr_surface_dispatcher::Step;
use gandr_surface_dispatcher::Verb;
use gandr_surface_dispatcher::Walk;
use gandr_surface_dispatcher::Width;
use gandr_surface_dispatcher::entries;
use gandr_surface_evaluate::Evaluator;
use gandr_surface_render_terminal::RenderStyle;
use gandr_surface_render_terminal::render;

/// The directories below `corpus/` whose sources state refusals: the
/// pathological twins, and one exemplar for each refusal name.
pub const REFUSING: [&str; 2] = ["pathological", "ledger/diagnostics"];

/// Why the refusals of a checkout could not be written: the walk could not
/// read these paths.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RefusalsError
{
    /// Each path that the walk could not read.
    pub faults: Vec<PathBuf>,
}

impl fmt::Display for RefusalsError
{
    /// Writes one line with the count of the paths and the first one.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        write!(f, "the walk cannot read {} paths", self.faults.len())?;
        self.faults.first().map_or(Ok(()), |first| {
            write!(f, "; the first is {}", first.display())
        })
    }
}

/// A refusal is an error value, so a caller can return it.
impl core::error::Error for RefusalsError
{
}

/// The refusals of each source below `roots`, by the path of the source
/// below `corpus/` of the checkout `repository`.
///
/// Each root is a directory or a source below `corpus/`. The text of a
/// source is each of its diagnostics as `gandr check` prints an unexpected
/// one: plain, at the verbosity of a user, in the order of the source, with
/// a blank line between two. The text names a file by its path below
/// `repository`. A source that prints nothing has no entry.
///
/// # Specification
/// trivial.
///
/// # Errors
/// [`RefusalsError`] when the walk cannot read a path.
///
/// # Adequacy
/// - hypothesis: L3 — the refusal of a circuit with a cycle names the port of
///   the cycle, and no text names the checkout.
/// - witness: `refusals::tests::a_cyclic_circuit_names_its_port`
#[inline]
pub fn rendered(
    repository: &Path,
    roots: Vec<PathBuf>,
) -> Result<BTreeMap<PathBuf, String>, RefusalsError>
{
    let corpus = repository.join("corpus");
    let prefix = format!("{}/", repository.display());
    let mut rendered = BTreeMap::new();
    let mut faults = Vec::new();
    let ControlFlow::Continue(_report) = Walk::new(roots).visit::<Evaluator, _, _>(
        &Pool::new(Width::PerformanceCores),
        |step| -> ControlFlow<Infallible> {
            match step {
                Step::Source { path, .. } => {
                    let mut text = String::new();
                    for diagnostic in entries::<Evaluator>(&step, Verb::Check(Goals::Gated))
                        .refusals(Refusals::Every)
                    {
                        if !text.is_empty() {
                            text.push('\n');
                        }
                        text.push_str(
                            render(&diagnostic, RenderStyle::Plain, Verbosity::User).as_ref(),
                        );
                        text.push('\n');
                    }
                    if !text.is_empty() {
                        match path.strip_prefix(&corpus) {
                            Ok(relative) => {
                                let _previous = rendered
                                    .insert(relative.to_path_buf(), text.replace(&prefix, ""));
                            },
                            Err(_) => faults.push(path.to_path_buf()),
                        }
                    }
                },
                Step::Fault { path, .. } => faults.push(path.to_path_buf()),
            }
            ControlFlow::Continue(())
        },
    );
    if faults.is_empty() {
        Ok(rendered)
    }
    else {
        Err(RefusalsError { faults })
    }
}

#[cfg(test)]
mod tests
{
    use std::path::Path;

    use super::rendered;

    /// The refusal of the circuit with a cycle names the port of the cycle.
    /// The walk reads that source alone, and its text does not name the
    /// checkout.
    #[test]
    fn a_cyclic_circuit_names_its_port()
    {
        let source = "pathological/circuit/circuit-cyclic-wiring.gandr";
        let repository = Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../..")
            .canonicalize()
            .expect("the root of the checkout resolves");
        let refusals = rendered(&repository, vec![repository.join("corpus").join(source)])
            .expect("the walk reads the source");
        let text = refusals
            .get(Path::new(source))
            .expect("the circuit with a cycle is refused");
        assert!(
            text.contains("port `z`"),
            "the refusal names its port: {text}"
        );
        let checkout = repository.display().to_string();
        assert!(
            !text.contains(&checkout),
            "the refusal does not name the checkout: {text}"
        );
    }
}
