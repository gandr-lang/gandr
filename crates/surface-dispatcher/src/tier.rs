//! The emitter as the checker's tier for closed endpoint pairs.
//!
//! Each side of a pair is focused into the command IL beside the
//! definitions admitted so far, run under the process's policy within
//! [`TIER_FUEL`] jumps, and read back; the pair meets when the two readings
//! are one term. The focused definitions persist across the pairs one
//! context offers, each later admission focused once when a pair first needs
//! it.

use alloc::boxed::Box;

use gandr_core_checker::CodeDefinitions;
use gandr_core_checker::tier::ClosedTier;
use gandr_core_checker::tier::Meeting;
use gandr_core_sequent::CommandArena;
use gandr_core_sequent::Definition;
use gandr_core_sequent::Definitions;
use gandr_core_sequent::NodeCount;
use gandr_core_sequent::Outcome;
use gandr_core_sequent::ProducerId;
use gandr_core_sequent::ProducerNode;
use gandr_core_sequent::Provenance;
use gandr_core_sequent::Store;
use gandr_core_sequent::focus_computation;
use gandr_core_sequent::focus_definition;
use gandr_core_sequent::focus_top_value;
use gandr_core_sequent::read_back_value;
use gandr_core_term::CertificateEquality;
use gandr_core_term::CoreArena;
use gandr_core_term::Value;
use gandr_core_term::ValueId;
use gandr_core_term::equal_certificate_syntax;
use gandr_kernel_term::ConstantIndex;
use gandr_runtime_emitter::Fuel;
use gandr_runtime_emitter::RunInputs;
use gandr_runtime_emitter::evaluate;

/// The jumps each side's run may take before the tier leaves the pair to the
/// machine. The machine has a step budget a run past it declines on, and the
/// tier keeps to a fuel well inside it, so a pair the machine would decline
/// is still the machine's to decline: the conversion corpus's closed pairs
/// each run within `2^15` jumps, and the budget fixture's
/// `fib(nineteen())`, which the machine declines, takes more than `2^17`.
const TIER_FUEL: usize = 1_usize << 16_u32;

/// The emitter's tier: the program the definitions admitted so far focus to.
///
/// # Specification
/// trivial.
#[derive(Default)]
pub struct Emitted
{
    /// Every focused definition's and side's commands.
    commands: CommandArena,
    /// The admitted definitions, focused, by admission position.
    definitions: Definitions,
    /// The origins focusing recorded, which no run reads.
    provenance: Provenance,
}

impl Emitted
{
    /// A fresh tier, for one context to own.
    ///
    /// # Specification
    /// trivial.
    pub fn boxed() -> Box<dyn ClosedTier>
    {
        Box::new(Self::default())
    }

    /// Focus every definition `definitions` holds past those focused already.
    /// A position with no body, a body that does not focus, and a body that
    /// steps a native operation are opaque: a run that reaches one sticks
    /// there.
    ///
    /// # Specification
    /// trivial.
    fn extend(
        &mut self,
        core: &CoreArena,
        definitions: &CodeDefinitions,
    )
    {
        let focused = ConstantIndex::from(usize::from(self.definitions.len()));
        for (constant, body) in definitions.definitions_from(focused) {
            while usize::from(self.definitions.len()) < usize::from(constant) {
                let _skipped = self.definitions.push(Definition::Opaque);
            }
            let before = self.commands.producer_count();
            let definition = match focus_definition(
                core,
                body,
                &mut self.commands,
                &mut self.provenance,
                &gandr_core_sequent::Writers::NONE,
            ) {
                Ok(_) if self.native_since(before).is_some() => Definition::Opaque,
                Ok(root) => Definition::Transparent(root),
                Err(_) => Definition::Opaque,
            };
            let _position = self.definitions.push(definition);
        }
    }

    /// The first producer minted at or past `from` that is a native operation.
    /// The kernel reads a native operation as an opaque constant, so a run that
    /// steps one computes past what the kernel's own evaluation repeats, and
    /// the pair is the machine's.
    ///
    /// # Specification
    /// trivial.
    fn native_since(
        &self,
        from: NodeCount,
    ) -> Option<ProducerId>
    {
        (usize::from(from) .. usize::from(self.commands.producer_count()))
            .filter_map(|index| u32::try_from(index).ok().map(ProducerId::from))
            .find(|id| {
                matches!(
                    self.commands.producer(*id),
                    Some(&ProducerNode::Primitive { .. })
                )
            })
    }

    /// Run `side` to its value and read it back into `read`: a returned
    /// computation runs as itself, any other value as its own return. `None`
    /// when it does not focus, steps a native operation, does not halt within
    /// [`TIER_FUEL`], or does not read back.
    ///
    /// # Specification
    /// trivial.
    fn run(
        &mut self,
        core: &CoreArena,
        side: ValueId,
        read: &mut CoreArena,
    ) -> Option<ValueId>
    {
        let before = self.commands.producer_count();
        let root = if let Value::Returned(computation) = *core.value(side)? {
            focus_computation(
                core,
                computation,
                &mut self.commands,
                &mut self.provenance,
                &gandr_core_sequent::Writers::NONE,
            )
        }
        else {
            focus_top_value(
                core,
                side,
                &mut self.commands,
                &mut self.provenance,
                &gandr_core_sequent::Writers::NONE,
            )
        }
        .ok()?;
        if self.native_since(before).is_some() {
            return None;
        }
        let mut store = Store::new();
        let Outcome::Halted(value) = evaluate(
            &self.commands,
            &self.definitions,
            root,
            Fuel::from(TIER_FUEL),
            RunInputs::new(&mut store),
        )
        .ok()?
        else {
            return None;
        };
        read_back_value(&self.commands, &store, value, read).ok()
    }
}

impl ClosedTier for Emitted
{
    /// Run both sides on the emitter and compare their readings.
    ///
    /// # Specification
    /// - requires: as [`ClosedTier::meet`].
    /// - ensures: [`Meeting::Met`] exactly when both sides run within
    ///   [`TIER_FUEL`], stepping no native operation, to values that read back
    ///   as one term.
    /// - panics: none.
    /// - executable: none — the runs are the emitter's.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a closed pair whose sides compute one value meets,
    ///   one whose sides compute two does not, one past the fuel does not, and
    ///   one whose run steps a native operation does not.
    /// - witness: `tier::tests::the_emitter_meets_a_pair_computing_one_value_2282`
    /// - witness: `tier::tests::a_pair_stepping_a_native_operation_is_the_machine_s_2282`
    fn meet(
        &mut self,
        core: &CoreArena,
        definitions: &CodeDefinitions,
        (left, right): (ValueId, ValueId),
    ) -> Meeting
    {
        self.extend(core, definitions);
        let mut read = CoreArena::new();
        match (
            self.run(core, left, &mut read),
            self.run(core, right, &mut read),
        ) {
            (Some(left), Some(right))
                if equal_certificate_syntax(&read, left, right) == CertificateEquality::Equal =>
            {
                Meeting::Met
            },
            _ => Meeting::Unmet,
        }
    }
}

#[cfg(test)]
mod tests;
