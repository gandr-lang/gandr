//! Nondeterministic deallocation automata and literal word membership.

use alloc::collections::BTreeSet;
use alloc::vec::Vec;

use anodized::spec;
use quenchant_shape::shape::Maybe;

use crate::handle::Allocation;
use crate::handle::Arity;
use crate::handle::AutomatonError;
use crate::handle::Configuration;
use crate::handle::Control;
use crate::handle::Controls;
use crate::handle::Degree;
use crate::handle::EmptyRegister;
use crate::handle::Freshness;
use crate::handle::Membership;
use crate::handle::Register;
use crate::handle::Transfer;
use crate::handle::arity_at;
use crate::handle::validate_initial;
use crate::handle::validate_transfer;
use crate::letter::Letter;

/// The event shape and register read by a symbolic rule.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum RuleKind
{
    /// Read a remembered name.
    Free
    {
        /// The source register.
        register: Register,
    },
    /// Allocate a fresh name.
    Open,
    /// Erase a remembered name.
    Close
    {
        /// The erased register.
        register: Register,
    },
    /// Allocate and release a fresh name immediately.
    OpenClose,
    /// Erase a register without consuming a letter.
    Drop
    {
        /// The erased register.
        register: Register,
    },
}

/// One orbit of symbolic word transitions.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Rule
{
    /// The source control.
    source: Control,
    /// The event shape.
    kind: RuleKind,
    /// The target control.
    target: Control,
    /// One entry for each target register.
    transfer: Vec<Transfer>,
}
impl Rule
{
    /// Read a remembered name.
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
            kind: RuleKind::Free { register },
            target,
            transfer,
        }
    }
    /// Allocate a fresh name.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn open(
        source: Control,
        target: Control,
        transfer: Vec<Transfer>,
    ) -> Self
    {
        Self {
            source,
            kind: RuleKind::Open,
            target,
            transfer,
        }
    }
    /// Release and erase a remembered name.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn close(
        source: Control,
        register: Register,
        target: Control,
        transfer: Vec<Transfer>,
    ) -> Self
    {
        Self {
            source,
            kind: RuleKind::Close { register },
            target,
            transfer,
        }
    }
    /// Allocate and immediately release a fresh name.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn open_close(
        source: Control,
        target: Control,
        transfer: Vec<Transfer>,
    ) -> Self
    {
        Self {
            source,
            kind: RuleKind::OpenClose,
            target,
            transfer,
        }
    }
    /// Erase a register without consuming a letter.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn forget(
        source: Control,
        register: Register,
        target: Control,
        transfer: Vec<Transfer>,
    ) -> Self
    {
        Self {
            source,
            kind: RuleKind::Drop { register },
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
    pub fn kind(&self) -> RuleKind
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

/// A validated finite register presentation of a deallocation automaton.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Nda<A>
{
    /// Declared register arities in control order.
    arities: Vec<Arity>,
    /// Initial control and assignment.
    initial: Configuration<A>,
    /// Accepting control points.
    finals: BTreeSet<Control>,
    /// Symbolic transitions, including epsilon drops.
    rules: Vec<Rule>,
}
impl<A: Copy + Ord> Nda<A>
{
    /// Validate every control, register transfer and erasure condition.
    ///
    /// # Specification
    /// - ensures: successful handles preserve partial injective stores and
    ///   erase the selected register on both close and drop rules.
    /// - fails: returns the first structural violation as an automaton error.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns an invalid control, arity, register, duplicate transfer,
    /// misplaced allocation or retained erased register.
    ///
    /// # Adequacy
    /// - hypothesis: L3 near-miss handles isolate each validation branch;
    ///   accepted and rejected lifecycle words distinguish register semantics.
    /// - witness: `tests::nda::construction_rejects_invalid_control`
    /// - witness: `tests::nda::construction_rejects_arity_mismatch`
    /// - witness: `tests::nda::construction_rejects_unknown_register`
    /// - witness: `tests::nda::construction_rejects_misplaced_allocated_name`
    /// - witness: `tests::nda::construction_rejects_kept_deallocated_name`
    /// - witness: `tests::validation::transfers_preserve_partial_injections`
    #[inline]
    #[spec(ensures: |ref result| result.as_ref().map_or(true, |automaton| automaton.arities.get(usize::from(automaton.initial.control())) == Some(&automaton.initial.store().arity())))]
    pub fn new(
        arities: Vec<Arity>,
        initial: Configuration<A>,
        finals: BTreeSet<Control>,
        rules: Vec<Rule>,
    ) -> Result<Self, AutomatonError>
    {
        validate_initial(&arities, &initial)?;
        for control in &finals {
            arity_at(&arities, *control)?;
        }
        for rule in &rules {
            let source_arity = arity_at(&arities, rule.source)?;
            match rule.kind {
                | RuleKind::Free { register }
                | RuleKind::Close { register }
                | RuleKind::Drop { register } => {
                    if usize::from(register) >= usize::from(source_arity) {
                        return Err(AutomatonError::UnknownRegister {
                            control: rule.source,
                            register,
                        });
                    }
                    if matches!(rule.kind, RuleKind::Close { .. } | RuleKind::Drop { .. })
                        && rule.transfer.contains(&Transfer::Keep(register))
                    {
                        return Err(AutomatonError::KeptDeallocatedName {
                            control: rule.source,
                            register,
                        });
                    }
                },
                | RuleKind::Open | RuleKind::OpenClose => {},
            }
            let allocation = if rule.kind == RuleKind::Open {
                Allocation::Allowed
            }
            else {
                Allocation::Forbidden
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

    /// The declared arities in control order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn arities(&self) -> &[Arity]
    {
        &self.arities
    }
    /// The number of control points.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn controls(&self) -> Controls
    {
        Controls::from(self.arities.len())
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
    /// The symbolic rules.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn rules(&self) -> &[Rule]
    {
        &self.rules
    }
    /// The maximum register count across controls.
    ///
    /// # Specification
    /// - ensures: returns the maximum declared arity, or zero for an empty
    ///   table.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 a two-control monitor distinguishes maximum from
    ///   initial arity.
    /// - witness: `tests::nda::session_monitor_degree_is_maximum_arity`
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

    /// Decide literal word membership, closing under epsilon drops at each
    /// step.
    ///
    /// # Specification
    /// - ensures: acceptance means a run consumes the whole word and ends at a
    ///   final control; free/close require the selected name, open/open-close
    ///   require freshness, and epsilon drops consume no input.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 lifecycle near-misses separate leaks, unmatched closes,
    ///   unknown actors, capacity and immediate-release freshness; a directed
    ///   name-dropping witness isolates epsilon closure before consumption.
    /// - witness: `tests::nda::session_monitor_accepts_drained_log`
    /// - witness: `tests::nda::session_monitor_rejects_leaked_login`
    /// - witness: `tests::nda::session_monitor_rejects_logout_without_login`
    /// - witness: `tests::nda::session_monitor_rejects_unknown_actor`
    /// - witness: `tests::nda::session_monitor_bounds_concurrent_logins`
    /// - witness: `tests::nda::open_close_allocates_and_immediately_forgets`
    /// - witness: `tests::dropping::name_dropping_closes_language_under_alpha`
    #[inline]
    #[must_use]
    #[spec(ensures: |result| result != Membership::Accepted || !self.finals.is_empty())]
    pub fn accepts(
        &self,
        word: &[Letter<A>],
    ) -> Membership
    {
        let mut frontier = self.close_under_drops(BTreeSet::from([self.initial.clone()]));
        for letter in word {
            let mut next = BTreeSet::new();
            for configuration in &frontier {
                for rule in &self.rules {
                    if rule.source != configuration.control() {
                        continue;
                    }
                    let allocated = match (rule.kind, *letter) {
                        | (RuleKind::Free { register }, Letter::Free(atom))
                        | (RuleKind::Close { register }, Letter::Close(atom)) => {
                            if configuration.store().name(register) != Maybe::Present(atom) {
                                continue;
                            }
                            Maybe::Absent(EmptyRegister::Empty)
                        },
                        | (RuleKind::Open, Letter::Open(atom)) => {
                            if configuration.store().freshness(atom) != Freshness::Fresh {
                                continue;
                            }
                            Maybe::Present(atom)
                        },
                        | (RuleKind::OpenClose, Letter::OpenClose(atom)) => {
                            if configuration.store().freshness(atom) != Freshness::Fresh {
                                continue;
                            }
                            Maybe::Absent(EmptyRegister::Empty)
                        },
                        | _ => continue,
                    };
                    let store = configuration.store().transfer(&rule.transfer, allocated);
                    next.insert(Configuration::new(rule.target, store));
                }
            }
            if next.is_empty() {
                return Membership::Rejected;
            }
            frontier = self.close_under_drops(next);
        }
        if frontier
            .iter()
            .any(|configuration| self.finals.contains(&configuration.control()))
        {
            Membership::Accepted
        }
        else {
            Membership::Rejected
        }
    }

    /// Reach every epsilon successor without revisiting a configuration.
    ///
    /// # Specification
    /// - ensures: retains the seed and closes it under every drop rule.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 a remembered allocation name becomes usable only after
    ///   epsilon erasure, while a cyclic drop relation still terminates.
    /// - witness: `tests::dropping::name_dropping_closes_language_under_alpha`
    /// - witness: `tests::validation::epsilon_cycles_and_nondeterminism_preserve_membership`
    #[spec(ensures: |ref result| result.iter().all(|configuration| self.arities.get(usize::from(configuration.control())) == Some(&configuration.store().arity())))]
    fn close_under_drops(
        &self,
        mut seen: BTreeSet<Configuration<A>>,
    ) -> BTreeSet<Configuration<A>>
    {
        let mut work: Vec<_> = seen.iter().cloned().collect();
        while let Some(configuration) = work.pop() {
            for rule in &self.rules {
                if rule.source != configuration.control()
                    || !matches!(rule.kind, RuleKind::Drop { .. })
                {
                    continue;
                }
                let store = configuration
                    .store()
                    .transfer(&rule.transfer, Maybe::Absent(EmptyRegister::Empty));
                let next = Configuration::new(rule.target, store);
                if seen.insert(next.clone()) {
                    work.push(next);
                }
            }
        }
        seen
    }
}

/// Add one epsilon erasure at each register of each control.
///
/// # Specification
/// - ensures: retains all original transitions, the initial configuration and
///   final controls; each new rule empties one register and retains the rest.
/// - ensures: every originally accepted word remains accepted.
/// - panics: none.
/// - intension: exactly one drop rule is added per declared register.
///
/// # Adequacy
/// - hypothesis: L3 a remembered-name alpha variant requires epsilon erasure;
///   exhaustive bounded words witness enlargement, and exact transfers observe
///   the declared rule-count bound.
/// - witness: `tests::dropping::name_dropping_closes_language_under_alpha`
/// - witness: `tests::dropping::name_dropping_only_enlarges_the_language`
/// - witness: `tests::dropping::name_dropping_adds_one_drop_rule_per_register`
#[inline]
#[must_use]
#[spec(ensures: |ref result| result.arities() == automaton.arities() && result.initial() == automaton.initial() && result.finals() == automaton.finals() && result.rules().starts_with(automaton.rules()))]
pub fn name_dropping<A>(automaton: &Nda<A>) -> Nda<A>
where
    A: Copy + Ord,
{
    let mut result = automaton.clone();
    for (index, arity) in automaton.arities().iter().enumerate() {
        let control = Control::from(index);
        for register in 0 .. usize::from(*arity) {
            let transfer = (0 .. usize::from(*arity))
                .map(|slot| {
                    if slot == register {
                        Transfer::Empty
                    }
                    else {
                        Transfer::Keep(Register::from(slot))
                    }
                })
                .collect();
            result.rules.push(Rule::forget(
                control,
                Register::from(register),
                control,
                transfer,
            ));
        }
    }
    result
}
