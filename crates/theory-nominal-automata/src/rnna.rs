//! Allocation-only regular nondeterministic nominal word automata.

use alloc::collections::BTreeSet;
use alloc::vec::Vec;

use anodized::spec;

use crate::handle::Allocation;
use crate::handle::Arity;
use crate::handle::AutomatonError;
use crate::handle::Configuration;
use crate::handle::Control;
use crate::handle::Degree;
use crate::handle::Register;
use crate::handle::Transfer;
use crate::handle::arity_at;
use crate::handle::validate_initial;
use crate::handle::validate_transfer;

/// The two event shapes in an allocation-only word automaton.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum RnnaRuleKind
{
    /// Read the name held in a source register.
    Free
    {
        /// The source register.
        register: Register,
    },
    /// Allocate a fresh name.
    Allocate,
}
/// One symbolic allocation-only transition.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RnnaRule
{
    /// The source control.
    source: Control,
    /// The event shape.
    kind: RnnaRuleKind,
    /// The target control.
    target: Control,
    /// The target register assignment.
    transfer: Vec<Transfer>,
}
impl RnnaRule
{
    /// Construct a free-name transition.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn free(
        source: Control,
        register: Register,
        target: Control,
        transfer: Vec<Transfer>,
    ) -> Self
    {
        Self {
            source,
            kind: RnnaRuleKind::Free { register },
            target,
            transfer,
        }
    }
    /// Construct an allocating transition.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn allocate(
        source: Control,
        target: Control,
        transfer: Vec<Transfer>,
    ) -> Self
    {
        Self {
            source,
            kind: RnnaRuleKind::Allocate,
            target,
            transfer,
        }
    }
    /// The source control.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn source(&self) -> Control
    {
        self.source
    }

    /// The event shape.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn kind(&self) -> RnnaRuleKind
    {
        self.kind
    }

    /// The target control.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn target(&self) -> Control
    {
        self.target
    }

    /// The target assignment.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn transfer(&self) -> &[Transfer]
    {
        &self.transfer
    }
}
/// A validated allocation-only symbolic word automaton.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Rnna<A>
{
    /// The control arities.
    arities: Vec<Arity>,
    /// The initial configuration.
    initial: Configuration<A>,
    /// The accepting controls.
    finals: BTreeSet<Control>,
    /// The symbolic transitions.
    rules: Vec<RnnaRule>,
}
impl<A: Copy + Ord> Rnna<A>
{
    /// Validate a finite allocation-only handle.
    ///
    /// # Specification
    /// - ensures: every control and register exists, target arities match, and
    ///   transfers preserve partial injectivity and allocation discipline.
    /// - fails: returns the structural automaton error naming the violation.
    /// - panics: none.
    ///
    /// # Errors
    /// Invalid controls, arities, reads, repeated registers and misplaced
    /// allocations.
    ///
    /// # Adequacy
    /// - hypothesis: L3 an allocation/free handle and malformed transfers
    ///   distinguish the two event shapes and structural validation.
    /// - witness: `tests::rnna::construction_accepts_a_well_formed_rnna`
    /// - witness: `tests::rnna::construction_rejects_misplaced_allocated_name`
    /// - witness: `tests::validation::transfers_preserve_partial_injections`
    #[inline]
    #[spec(ensures: |ref result| result.as_ref().map_or(true, |automaton| automaton.arities.get(usize::from(automaton.initial.control())) == Some(&automaton.initial.store().arity())))]
    pub fn new(
        arities: Vec<Arity>,
        initial: Configuration<A>,
        finals: BTreeSet<Control>,
        rules: Vec<RnnaRule>,
    ) -> Result<Self, AutomatonError>
    {
        validate_initial(&arities, &initial)?;
        for control in &finals {
            arity_at(&arities, *control)?;
        }
        for rule in &rules {
            let source_arity = arity_at(&arities, rule.source)?;
            let allocation = match rule.kind {
                | RnnaRuleKind::Free { register } => {
                    if usize::from(register) >= usize::from(source_arity) {
                        return Err(AutomatonError::UnknownRegister {
                            control: rule.source,
                            register,
                        });
                    }
                    Allocation::Forbidden
                },
                | RnnaRuleKind::Allocate => Allocation::Allowed,
            };
            validate_transfer(
                &arities,
                rule.source,
                rule.target,
                &rule.transfer,
                allocation,
            )?;
        }
        Ok(Self {
            arities,
            initial,
            finals,
            rules,
        })
    }
    /// The control arities.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn arities(&self) -> &[Arity]
    {
        &self.arities
    }

    /// The initial configuration.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn initial(&self) -> &Configuration<A>
    {
        &self.initial
    }

    /// The accepting controls.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn finals(&self) -> &BTreeSet<Control>
    {
        &self.finals
    }

    /// The symbolic transitions.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn rules(&self) -> &[RnnaRule]
    {
        &self.rules
    }

    /// The maximum declared register arity.
    ///
    /// # Specification
    /// - ensures: returns the maximum arity across controls.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 the empty initial and occupied successor separate
    ///   maximum from initial arity.
    /// - witness: `tests::rnna::construction_accepts_a_well_formed_rnna`
    #[inline]
    #[must_use]
    #[spec(ensures: |result| self.arities.iter().all(|arity| usize::from(*arity) <= usize::from(result)) && self.arities.iter().any(|arity| usize::from(*arity) == usize::from(result)))]
    pub fn degree(&self) -> Degree
    {
        Degree::from(
            self.arities
                .iter()
                .map(|arity| usize::from(*arity))
                .max()
                .unwrap_or(0),
        )
    }
}
