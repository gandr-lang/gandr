//! How the lowering holds each path composite a source writes: the
//! transports it returns as values, and the composites of flows.
//!
//! The printer reads a returned transport that a derived path operation
//! builds as that operation, `Path.step p q`, `Path.back p` or `Path.ap f p`,
//! in both forms (#5206). So both forms fold such a transport into its
//! operation, and neither form unfolds an operation into its transport. A
//! transport standing as a computation, a body's last step, stays as written,
//! and so does a composite of flows, which the core holds as written.

use alloc::vec::Vec;

use gandr_core_term::Computation;
use gandr_core_term::CoreArena;
use gandr_core_term::Value;
use gandr_surface_lowering::LoweredModule;
use gandr_surface_syntax::ByteOffset;
use gandr_surface_syntax::ByteSpan;

/// How the lowering holds a composite the source writes.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Standing
{
    /// A transport returned as a value: the printer writes it as the
    /// operation it derives, `Path.step p q`.
    Returned,
    /// A transport otherwise, a body's last step among them: the printer
    /// writes it as written.
    Run,
    /// A composite of flows, which the core holds as written: both forms
    /// write it as written.
    Flows,
}

/// How the lowering holds each path composite the source writes, by the
/// composite's span in the source.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Composites
{
    /// The spans of the transports, written or derived, the lowering returns
    /// as values: those the printer writes as the operation they derive. A
    /// transport standing as a computation, a body's last step, it writes as
    /// written.
    returned: Vec<ByteSpan>,
    /// The spans of the flow composites, which the core holds as written.
    flows: Vec<ByteSpan>,
}

impl Composites
{
    /// How `module`, lowered into `arena`, holds the path composites of the
    /// formatted source that starts at `base` in the unit's text: the span
    /// of each transport it returns as a value, and of each composite of
    /// flows, in the source's own offsets.
    ///
    /// # Specification
    /// trivial.
    pub fn of(
        module: &LoweredModule<'_>,
        arena: &CoreArena,
        base: ByteOffset,
    ) -> Self
    {
        let mut returned = Vec::new();
        let mut flows = Vec::new();
        for &(id, origin) in module.origins().values() {
            let Some(span) = within(origin.span(), base)
            else {
                continue;
            };
            match arena.value(id) {
                Some(&Value::Returned(transport))
                    if matches!(
                        arena.computation(transport),
                        Some(&Computation::PathTransport { .. })
                    ) =>
                {
                    returned.push(span);
                },
                Some(&Value::Then(..)) => flows.push(span),
                Some(_) | None => {},
            }
        }
        Self { returned, flows }
    }

    /// How the lowering holds the composite spanning exactly `span`.
    ///
    /// # Specification
    /// trivial.
    pub fn standing(
        &self,
        span: ByteSpan,
    ) -> Standing
    {
        if self.flows.contains(&span) {
            return Standing::Flows;
        }
        let returned = self.returned.contains(&span);
        if returned {
            Standing::Returned
        }
        else {
            Standing::Run
        }
    }
}

/// `span`, of a unit's text, as a span of the source starting at `base` in
/// it; none when it starts before the source.
///
/// # Specification
/// trivial.
pub fn within(
    span: ByteSpan,
    base: ByteOffset,
) -> Option<ByteSpan>
{
    let start = usize::from(span.start()).checked_sub(usize::from(base))?;
    let end = usize::from(span.end()).checked_sub(usize::from(base))?;
    ByteSpan::new(ByteOffset::from(start), ByteOffset::from(end)).ok()
}
