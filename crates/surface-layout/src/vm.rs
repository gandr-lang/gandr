//! The first-order render machine.
//!
//! The winning plan executes with an explicit heap stack of plan identities.
//! No choiceless document tree, candidate string, closure, or input-scaled
//! recursion is materialized.

use alloc::string::String;
use alloc::vec::Vec;

use quenchant_shape::shape::Maybe;

use crate::arena::DocArena;
use crate::error::RenderAllocationSite;
use crate::error::RenderArithmetic;
use crate::error::RenderError;
use crate::error::RenderInvariant;
use crate::limits::RenderMeter;
use crate::measure::PhysicalLineEnding;
use crate::plan::PlanArena;
use crate::plan::PlanId;
use crate::plan::PlanNode;
use crate::render::RenderedText;
use crate::units::OutputBytes;
use crate::units::PeakVmStack;

/// The bytes a layout-owned line of indentation emits after its ending, one
/// run of spaces at a time.
const SPACES: &str = "                                                                ";

/// Fallible output storage with an exact cumulative byte projection.
#[derive(Debug)]
pub(crate) struct OutputBuffer
{
    /// The reserved output bytes.
    text: String,
    /// Bytes appended so far.
    bytes: OutputBytes,
}

impl OutputBuffer
{
    /// Reserves exactly the selected measure's output size once.
    ///
    /// # Specification
    /// - requires: `capacity` is the checked output size of the selected plan.
    /// - ensures: the buffer has one exact fallible reservation before appends.
    /// - provides: output storage that cannot grow during machine execution.
    /// - fails: returns `AllocationFailed` when the output reservation fails,
    ///   or `ArithmeticOverflow` when the capacity cannot be represented.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns a typed render allocation or arithmetic error.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — one selected output size gets one exact fallible
    ///   reservation before any fragment append.
    /// - witness: `algebra::tests::render_text_and_layout_metadata_are_exact`
    /// - witness: `algebra::tests::render_limits_fail_without_partial_output`
    pub(crate) fn try_new(capacity: OutputBytes) -> Result<Self, RenderError>
    {
        let capacity = usize::try_from(u64::from(capacity)).map_err(|_error| {
            RenderError::ArithmeticOverflow {
                operation: RenderArithmetic::OutputBytes,
            }
        })?;
        let mut text = String::new();
        text.try_reserve_exact(capacity)
            .map_err(|_error| RenderError::AllocationFailed {
                site: RenderAllocationSite::Output,
            })?;
        Ok(Self {
            text,
            bytes: OutputBytes::from(0u64),
        })
    }

    /// Converts complete output storage into the public text wrapper.
    ///
    /// # Specification
    /// - requires: the machine has completed without an error.
    /// - ensures: ownership moves without another allocation.
    /// - provides: the exact rendered bytes.
    /// - panics: none.
    pub(crate) fn into_text(self) -> RenderedText
    {
        RenderedText::from(self.text)
    }

    /// Charges and appends one UTF-8 fragment without allowing partial
    /// output.
    ///
    /// # Specification
    /// - requires: `fragment` is one exact output fragment and the buffer has
    ///   been reserved for the selected measure.
    /// - ensures: the output counter advances before the string append.
    /// - provides: one shared append boundary for text, endings, and spaces.
    /// - fails: returns a checked output arithmetic or render-limit error.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns `ArithmeticOverflow` if the local output counter cannot advance,
    /// or the named output limit when the meter refuses the append.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — every concrete fragment advances output accounting
    ///   before its bytes become observable.
    /// - witness: `algebra::tests::render_preserves_verbatim_bytes_and_physical_endings`
    /// - witness: `algebra::tests::render_limits_fail_without_partial_output`
    fn append(
        &mut self,
        meter: &mut RenderMeter,
        fragment: &Fragment<'_>,
    ) -> Result<(), RenderError>
    {
        let amount =
            u64::try_from(fragment.0.len()).map_err(|_error| RenderError::ArithmeticOverflow {
                operation: RenderArithmetic::OutputBytes,
            })?;
        let next =
            u64::from(self.bytes)
                .checked_add(amount)
                .ok_or(RenderError::ArithmeticOverflow {
                    operation: RenderArithmetic::OutputBytes,
                })?;
        meter.charge_output_bytes(OutputBytes::from(amount))?;
        self.bytes = OutputBytes::from(next);
        self.text.push_str(fragment.0);
        Ok(())
    }
}

/// One run of bytes the machine appends.
#[repr(transparent)]
struct Fragment<'bytes>(&'bytes str);

/// Executes one retained plan with a first-order machine stack.
///
/// # Specification
/// - requires: `root` is a live identity in `plans`, and `expected` is the
///   selected measure's checked output byte count.
/// - ensures: every plan identity is popped iteratively, every sequence pushes
///   right then left under the machine-stack ceiling, and output bytes are
///   exact.
/// - provides: complete rendered output with cumulative machine and output
///   charges.
/// - fails: returns an invariant, allocation, arithmetic, or render-limit error
///   without returning partial output.
/// - panics: none.
///
/// # Errors
/// Returns [`RenderError`] at the first refused machine step, stack growth,
/// output append, or counter/measure disagreement.
///
/// # Adequacy
/// - hypothesis: L3 — the surfaces are the left-first sequence order, the
///   complete output of a tainted plan, the stack ceiling checked before any
///   output and the exact byte reconciliation, each asserted on rendered text
///   or a named limit.
/// - witness: `algebra::tests::render_tainted_root_preserves_promise_columns_and_indentation`
/// - witness: `algebra::tests::render_limits_fail_without_partial_output`
/// - witness: `algebra::tests::render_vm_stack_limit_is_checked_before_output`
pub(crate) fn execute(
    arena: &DocArena,
    plans: &PlanArena,
    root: PlanId,
    expected: OutputBytes,
    meter: &mut RenderMeter,
) -> Result<OutputBuffer, RenderError>
{
    let mut buffer = OutputBuffer::try_new(expected)?;
    let mut stack = Vec::new();
    meter.observe_vm_stack(PeakVmStack::from(1u64))?;
    stack
        .try_reserve(1usize)
        .map_err(|_error| RenderError::AllocationFailed {
            site: RenderAllocationSite::VmStack,
        })?;
    stack.push(root);
    while let Some(plan) = stack.pop() {
        meter.charge_vm_step()?;
        let Maybe::Present(node) = plans.get(plan)
        else {
            return Err(RenderError::Invariant {
                invariant: RenderInvariant::PlanIdentity,
            });
        };
        match node {
            | PlanNode::Empty => {},
            | PlanNode::Text(text) => {
                let Maybe::Present(identity) = arena.text_identity(text)
                else {
                    return Err(RenderError::Invariant {
                        invariant: RenderInvariant::DocumentIdentity,
                    });
                };
                buffer.append(meter, &Fragment(identity.as_ref()))?;
            },
            | PlanNode::Verbatim(verbatim) => {
                let Maybe::Present(identity) = arena.verbatim_identity(verbatim)
                else {
                    return Err(RenderError::Invariant {
                        invariant: RenderInvariant::DocumentIdentity,
                    });
                };
                buffer.append(meter, &Fragment(identity.as_ref()))?;
            },
            | PlanNode::Newline {
                indentation,
                ending,
            } => {
                let ending = match ending {
                    | PhysicalLineEnding::Lf => "\n",
                    | PhysicalLineEnding::CrLf => "\r\n",
                };
                buffer.append(meter, &Fragment(ending))?;
                let mut remaining = usize::try_from(u32::from(indentation)).map_err(|_error| {
                    RenderError::ArithmeticOverflow {
                        operation: RenderArithmetic::Indentation,
                    }
                })?;
                while remaining > 0usize {
                    let run = remaining.min(SPACES.len());
                    let Some(spaces) = SPACES.get(.. run)
                    else {
                        return Err(RenderError::ArithmeticOverflow {
                            operation: RenderArithmetic::Indentation,
                        });
                    };
                    buffer.append(meter, &Fragment(spaces))?;
                    remaining = remaining.saturating_sub(run);
                }
            },
            | PlanNode::Seq { left, right } => {
                let next_depth = u64::try_from(stack.len())
                    .ok()
                    .and_then(|depth| depth.checked_add(2u64))
                    .ok_or(RenderError::ArithmeticOverflow {
                        operation: RenderArithmetic::StackDepth,
                    })?;
                meter.observe_vm_stack(PeakVmStack::from(next_depth))?;
                stack
                    .try_reserve(2usize)
                    .map_err(|_error| RenderError::AllocationFailed {
                        site: RenderAllocationSite::VmStack,
                    })?;
                stack.push(right);
                stack.push(left);
            },
        }
    }
    if buffer.bytes != expected {
        return Err(RenderError::Invariant {
            invariant: RenderInvariant::OutputReconciliation,
        });
    }
    Ok(buffer)
}

#[cfg(test)]
mod tests
{
    use crate::error::RenderError;
    use crate::error::RenderLimitKind;
    use crate::limits::RenderLimits;
    use crate::limits::RenderMeter;
    use crate::units::LimitBound;
    use crate::units::MaxVmStack;
    use crate::units::MaxVmSteps;
    use crate::units::PeakVmStack;
    use crate::units::VmStepsUsed;

    /// Machine-step spending refuses the first over-limit step and leaves the
    /// count where it was.
    #[test]
    fn vm_step_limit_is_checked_before_usage_changes()
    {
        let limits = RenderLimits {
            max_vm_steps: MaxVmSteps::from(1u64),
            ..RenderLimits::default()
        };
        let mut meter = RenderMeter::new(limits);
        assert_eq!(meter.charge_vm_step(), Ok(()));
        assert_eq!(meter.usage().vm_steps, VmStepsUsed::from(1u64));
        assert_eq!(
            meter.charge_vm_step(),
            Err(RenderError::LimitExceeded {
                kind: RenderLimitKind::VmSteps,
                limit: LimitBound::from(1u64),
            })
        );
        assert_eq!(meter.usage().vm_steps, VmStepsUsed::from(1u64));
    }

    /// Machine-stack observation refuses the first over-limit depth and leaves
    /// the recorded peak where it was.
    #[test]
    fn vm_stack_limit_is_checked_before_peak_changes()
    {
        let limits = RenderLimits {
            max_vm_stack: MaxVmStack::from(2u64),
            ..RenderLimits::default()
        };
        let mut meter = RenderMeter::new(limits);
        assert_eq!(meter.observe_vm_stack(PeakVmStack::from(2u64)), Ok(()));
        assert_eq!(meter.usage().peak_vm_stack, PeakVmStack::from(2u64));
        assert_eq!(
            meter.observe_vm_stack(PeakVmStack::from(3u64)),
            Err(RenderError::LimitExceeded {
                kind: RenderLimitKind::VmStack,
                limit: LimitBound::from(2u64),
            })
        );
        assert_eq!(meter.usage().peak_vm_stack, PeakVmStack::from(2u64));
    }
}
