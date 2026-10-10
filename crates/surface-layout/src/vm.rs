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
///
/// # Specification
/// - requires: the buffer was reserved for a selected plan and receives metered
///   UTF-8 fragments.
/// - ensures: the stored byte count agrees with the emitted string, and refusal
///   does not publish a partial buffer.
/// - provides: the state represented by this item.
/// - panics: none.
/// - executable: none — this private state carrier has no invocation boundary;
///   reservation, append and execution carry its executable invariants.
///
/// # Adequacy
/// - hypothesis: L3 — Unicode fragments at an exact cumulative byte ceiling,
///   counter overflow, left-first sequences, stale and foreign identities,
///   mismatched selected sizes and VM ceilings expose emitted bytes, typed
///   first errors and meter frames. Dropped fragments, reordered children,
///   charging after append or publishing an unreconciled buffer change those
///   observations. Allocation-capacity overflow is deterministic; allocator
///   exhaustion is not injected.
/// - witness: `vm::tests::append_refusals_preserve_unicode_output_and_meter_state`
/// - witness: `vm::tests::execution_checks_identity_order_and_byte_reconciliation`
/// - witness: `algebra::tests::render_vm_stack_limit_is_checked_before_output`
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
    /// Requests the selected measure's output size in one fallible reservation.
    ///
    /// # Specification
    /// - requires: `capacity` is the checked output size of the selected plan.
    /// - ensures: the empty buffer has at least the requested capacity after
    ///   one fallible exact-reservation request; the allocator may provide
    ///   more.
    /// - provides: output storage that cannot grow during machine execution.
    /// - fails: returns `AllocationFailed` when the output reservation fails,
    ///   or `ArithmeticOverflow` when the capacity cannot be represented.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns a typed render allocation or arithmetic error.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — Unicode fragments at an exact cumulative byte
    ///   ceiling, counter overflow, left-first sequences, stale and foreign
    ///   identities, mismatched selected sizes and VM ceilings expose emitted
    ///   bytes, typed first errors and meter frames. Dropped fragments,
    ///   reordered children, charging after append or publishing an
    ///   unreconciled buffer change those observations. Allocation-capacity
    ///   overflow is deterministic; allocator exhaustion is not injected.
    /// - witness: `vm::tests::append_refusals_preserve_unicode_output_and_meter_state`
    /// - witness: `vm::tests::execution_checks_identity_order_and_byte_reconciliation`
    /// - witness: `algebra::tests::render_vm_stack_limit_is_checked_before_output`
    #[anodized::spec(
        ensures: |ret| match usize::try_from(u64::from(capacity)) { Err(_error) => matches!(ret, Err(RenderError::ArithmeticOverflow { operation: RenderArithmetic::OutputBytes })), Ok(requested) => ret.as_ref().map_or_else(|error| *error == RenderError::AllocationFailed { site: RenderAllocationSite::Output },
            |buffer| buffer.text.is_empty()
                && u64::from(buffer.bytes) == 0
                && buffer.text.capacity() >= requested) }
    )]
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
    ///
    /// # Adequacy
    /// - hypothesis: L3 — Unicode fragments at an exact cumulative byte
    ///   ceiling, counter overflow, left-first sequences, stale and foreign
    ///   identities, mismatched selected sizes and VM ceilings expose emitted
    ///   bytes, typed first errors and meter frames. Dropped fragments,
    ///   reordered children, charging after append or publishing an
    ///   unreconciled buffer change those observations. Allocation-capacity
    ///   overflow is deterministic; allocator exhaustion is not injected.
    /// - witness: `vm::tests::append_refusals_preserve_unicode_output_and_meter_state`
    /// - witness: `vm::tests::execution_checks_identity_order_and_byte_reconciliation`
    /// - witness: `algebra::tests::render_vm_stack_limit_is_checked_before_output`
    #[anodized::spec(
        captures: before = (self.text.as_ptr(), self.text.len()),
        ensures: |ret| ret.as_ptr() == before.0
                && ret.len() == before.1
    )]
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
    /// - hypothesis: L3 — Unicode fragments at an exact cumulative byte
    ///   ceiling, counter overflow, left-first sequences, stale and foreign
    ///   identities, mismatched selected sizes and VM ceilings expose emitted
    ///   bytes, typed first errors and meter frames. Dropped fragments,
    ///   reordered children, charging after append or publishing an
    ///   unreconciled buffer change those observations. Allocation-capacity
    ///   overflow is deterministic; allocator exhaustion is not injected.
    /// - witness: `vm::tests::append_refusals_preserve_unicode_output_and_meter_state`
    /// - witness: `vm::tests::execution_checks_identity_order_and_byte_reconciliation`
    /// - witness: `algebra::tests::render_vm_stack_limit_is_checked_before_output`
    #[anodized::spec(
        captures: before = (self.text.len(), self.text.as_ptr(), self.text.capacity(), self.bytes, meter.usage()),
        ensures: |ret| ret.as_ref().map_or_else(|_error| self.text.len() == before.0
                && self.text.as_ptr() == before.1
                && self.text.capacity() == before.2
                && self.bytes == before.3
                && meter.usage() == before.4,
            |&()| before.0.checked_add(fragment.0.len()) == Some(self.text.len())
                && self.text.ends_with(fragment.0)
                && u64::try_from(self.text.len()) == Ok(u64::from(self.bytes))
                && u64::try_from(fragment.0.len()).ok().and_then(|amount| u64::from(before.3).checked_add(amount)) == Some(u64::from(self.bytes))
                && u64::try_from(fragment.0.len()).ok().and_then(|amount| u64::from(before.4.output_bytes).checked_add(amount)) == Some(u64::from(meter.usage().output_bytes))
                && (self.text.len() > before.2 || (self.text.as_ptr() == before.1
                && self.text.capacity() == before.2)))
    )]
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
/// - hypothesis: L3 — Unicode fragments at an exact cumulative byte ceiling,
///   counter overflow, left-first sequences, stale and foreign identities,
///   mismatched selected sizes and VM ceilings expose emitted bytes, typed
///   first errors and meter frames. Dropped fragments, reordered children,
///   charging after append or publishing an unreconciled buffer change those
///   observations. Allocation-capacity overflow is deterministic; allocator
///   exhaustion is not injected.
/// - witness: `vm::tests::append_refusals_preserve_unicode_output_and_meter_state`
/// - witness: `vm::tests::execution_checks_identity_order_and_byte_reconciliation`
/// - witness: `algebra::tests::render_vm_stack_limit_is_checked_before_output`
#[anodized::spec(
    captures: before = meter.usage(),
    ensures: |ret| ret.as_ref().map_or(true,
        |buffer| buffer.bytes == expected
            && u64::try_from(buffer.text.len()) == Ok(u64::from(expected))
            && u64::from(before.output_bytes).checked_add(u64::from(expected)) == Some(u64::from(meter.usage().output_bytes))
            && u64::from(meter.usage().vm_steps) > u64::from(before.vm_steps))
)]
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

    /// Append failures retain complete prior Unicode bytes and do not spend
    /// refused charges.
    #[test]
    fn append_refusals_preserve_unicode_output_and_meter_state()
    {
        let mut output =
            super::OutputBuffer::try_new(crate::units::OutputBytes::from(6_u64)).expect("buffer");
        let mut meter = RenderMeter::new(RenderLimits {
            max_output_bytes: 6_u64.into(),
            ..RenderLimits::default()
        });
        output
            .append(&mut meter, &super::Fragment("é"))
            .expect("first fragment");
        output
            .append(&mut meter, &super::Fragment("𐐀"))
            .expect("exact ceiling");
        let before = meter.usage();
        assert_eq!(
            output.append(&mut meter, &super::Fragment("\n")),
            Err(RenderError::LimitExceeded {
                kind: RenderLimitKind::OutputBytes,
                limit: LimitBound::from(6_u64)
            })
        );
        assert_eq!(meter.usage(), before);
        assert_eq!(output.into_text(), "é𐐀");
        let mut output = super::OutputBuffer::try_new(crate::units::OutputBytes::from(1_u64))
            .expect("overflow buffer");
        let mut meter = RenderMeter::new(RenderLimits {
            max_output_bytes: u64::MAX.into(),
            ..RenderLimits::default()
        });
        meter
            .charge_output_bytes(crate::units::OutputBytes::from(u64::MAX))
            .expect("prior cumulative output");
        let before = meter.usage();
        assert_eq!(
            output.append(&mut meter, &super::Fragment("a")),
            Err(RenderError::ArithmeticOverflow {
                operation: crate::error::RenderArithmetic::OutputBytes
            })
        );
        assert_eq!(meter.usage(), before);
        assert_eq!(output.into_text(), "");
        let refusal = super::OutputBuffer::try_new(crate::units::OutputBytes::from(u64::MAX));
        if usize::try_from(u64::MAX).is_ok() {
            assert!(matches!(
                refusal,
                Err(RenderError::AllocationFailed {
                    site: crate::error::RenderAllocationSite::Output
                })
            ));
        }
        else {
            assert!(matches!(
                refusal,
                Err(RenderError::ArithmeticOverflow {
                    operation: crate::error::RenderArithmetic::OutputBytes
                })
            ));
        }
    }

    /// Plan order, stale identities and selected-size disagreement are
    /// observable at execution.
    #[test]
    fn execution_checks_identity_order_and_byte_reconciliation()
    {
        let mut build_meter = crate::limits::BuildMeter::new(crate::limits::BuildLimits::default());
        let mut builder = crate::build::DocBuilder::try_new(&mut build_meter).expect("builder");
        let left_doc = builder
            .text(crate::arena::TextSource::from("é"))
            .expect("left text");
        let right_doc = builder
            .text(crate::arena::TextSource::from("𐐀"))
            .expect("right text");
        let arena = builder.finish().expect("arena");
        let super::Maybe::Present(crate::arena::DocNode::Text(left_text)) =
            arena.node(left_doc.node_id())
        else {
            panic!("left identity")
        };
        let super::Maybe::Present(crate::arena::DocNode::Text(right_text)) =
            arena.node(right_doc.node_id())
        else {
            panic!("right identity")
        };
        let mut plan_meter = RenderMeter::new(RenderLimits::default());
        let mut plans = super::PlanArena::new();
        let left = plans
            .alloc(super::PlanNode::Text(left_text), &mut plan_meter)
            .expect("left plan");
        let right = plans
            .alloc(super::PlanNode::Text(right_text), &mut plan_meter)
            .expect("right plan");
        let root = plans
            .alloc_seq(left, right, &mut plan_meter)
            .expect("sequence");
        let mut meter = RenderMeter::new(RenderLimits {
            max_vm_stack: 2_u64.into(),
            ..RenderLimits::default()
        });
        let output = super::execute(
            &arena,
            &plans,
            root,
            crate::units::OutputBytes::from(6_u64),
            &mut meter,
        )
        .expect("execution");
        assert_eq!(output.into_text(), "é𐐀");
        assert_eq!(u64::from(meter.usage().output_bytes), 6);
        assert_eq!(u64::from(meter.usage().vm_steps), 3);
        let mut meter = RenderMeter::new(RenderLimits::default());
        assert!(matches!(
            super::execute(
                &arena,
                &plans,
                root,
                crate::units::OutputBytes::from(7_u64),
                &mut meter
            ),
            Err(RenderError::Invariant {
                invariant: crate::error::RenderInvariant::OutputReconciliation
            })
        ));
        assert_eq!(u64::from(meter.usage().output_bytes), 6);
        let stale = plans
            .alloc(super::PlanNode::Empty, &mut plan_meter)
            .expect("stale subject");
        plans
            .release_one(stale, &mut plan_meter)
            .expect("release subject");
        let mut meter = RenderMeter::new(RenderLimits::default());
        assert!(matches!(
            super::execute(
                &arena,
                &plans,
                stale,
                crate::units::OutputBytes::from(0_u64),
                &mut meter
            ),
            Err(RenderError::Invariant {
                invariant: crate::error::RenderInvariant::PlanIdentity
            })
        ));
        assert_eq!(u64::from(meter.usage().output_bytes), 0);
        let invalid_doc = plans
            .alloc(
                super::PlanNode::Text(crate::arena::TextId::from(u32::MAX)),
                &mut plan_meter,
            )
            .expect("invalid document subject");
        let mut meter = RenderMeter::new(RenderLimits::default());
        assert!(matches!(
            super::execute(
                &arena,
                &plans,
                invalid_doc,
                crate::units::OutputBytes::from(0_u64),
                &mut meter
            ),
            Err(RenderError::Invariant {
                invariant: crate::error::RenderInvariant::DocumentIdentity
            })
        ));
        assert_eq!(u64::from(meter.usage().output_bytes), 0);
        let mut meter = RenderMeter::new(RenderLimits {
            max_vm_steps: 0_u64.into(),
            ..RenderLimits::default()
        });
        assert!(
            matches!(super::execute(&arena, &plans, stale, crate::units::OutputBytes::from(0_u64), &mut meter), Err(RenderError::LimitExceeded { kind: RenderLimitKind::VmSteps, limit }) if u64::from(limit) == 0)
        );
        assert_eq!(u64::from(meter.usage().output_bytes), 0);
    }
}
