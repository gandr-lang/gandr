//! Residual conversion equations, restricted to bare owed code constants, and
//! the collector a value declaration's judgement leaves them in.

use alloc::collections::BTreeSet;
use alloc::vec::Vec;

use anodized::spec;
use gandr_core_term::CompType;
use gandr_core_term::CoreArena;
use gandr_core_term::Value;
use gandr_core_term::ValueType;
use gandr_kernel_term::ConstantIndex;
use quenchant_shape::shape::Maybe;

use crate::TypeNode;

quenchant_shape::reason_enum! {
    /// Why an equation cannot enter the residual fragment.
    mod candidate {
        /// The equation has no bare owed flex head opposite a rigid head.
        #[derive(Clone, Copy, Debug, Eq, PartialEq)]
        pub enum Absent {
            /// Ordinary conversion must decide this equation.
            Rigid,
        }
    }
}

/// One conversion obligation on a bare module hole.
///
/// # Specification
/// - requires: constructed only by the elaboration conversion boundary.
/// - ensures: `hole` was owed when the equation was recorded; `flex` is its
///   decode with no application spine, and `rigid` has a constructor head.
/// - provides: a residual equation, not a unifier or a certificate of
///   emptiness.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — exact equations and blockers separate bare flex–rigid
///   suspension from rigid disagreement and flex–flex comparison.
/// - witness: `elaboration::tests::owed_conversion_suspends`
/// - witness: `elaboration::tests::only_bare_flex_rigid_equations_suspend`
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Equation
{
    /// The module hole whose filling may settle the comparison.
    hole: ConstantIndex,
    /// The stuck decode.
    flex: TypeNode,
    /// The type opposite the decode.
    rigid: TypeNode,
}

impl Equation
{
    /// The owed constant at the flex head.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn hole(&self) -> ConstantIndex
    {
        self.hole
    }

    /// The flex side, a decode of the bare hole.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn flex(&self) -> TypeNode
    {
        self.flex
    }

    /// The constructor-headed side.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn rigid(&self) -> TypeNode
    {
        self.rigid
    }
}

/// Whether a comparison was recorded instead of decided.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Deferred
{
    /// Continue the surrounding conjunction, retaining the equation.
    Yes,
    /// Run ordinary conversion.
    No,
}

/// Whether the running judgement may leave residuals.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub enum Collecting
{
    /// A nominal declaration's formation, or no judgement: every comparison
    /// is decided rigidly.
    #[default]
    Off,
    /// A value declaration's judgement: a bare owed flex–rigid equation is
    /// recorded, and a read of a waiting declaration is a dependency.
    On,
}

/// What one value declaration's judgement left undecided: the equations it
/// recorded and the waiting declarations it read.
///
/// # Specification
/// - requires: taken from the collector once the verdict's run ends.
/// - ensures: the equations in the order the judgement recorded them; the
///   dependencies are the waiting declarations whose types it read.
/// - provides: the input a [`super::Suspension`] is built from.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a residual alone, a waiting read alone and neither
///   separate the three answers of [`Residue::pending`].
/// - witness: `elaboration::tests::owed_conversion_suspends`
/// - witness: `elaboration::tests::dependent_resumption_closes_its_prerequisites`
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Residue
{
    /// The equations recorded.
    pub equations: Vec<Equation>,
    /// The waiting declarations read.
    pub dependencies: BTreeSet<ConstantIndex>,
}

impl Residue
{
    /// Whether the judgement waits: it recorded an equation or read a waiting
    /// declaration.
    ///
    /// # Specification
    /// trivial.
    pub fn pending(&self) -> Deferred
    {
        if self.equations.is_empty() && self.dependencies.is_empty() {
            Deferred::No
        }
        else {
            Deferred::Yes
        }
    }
}

/// The residual collector: the holes a comparison may wait on, the
/// declarations that wait, and what the running judgement left.
///
/// An empty owed set disables suspension, so a context that never judged an
/// owed hole decides every comparison as ordinary checking does.
#[derive(Default)]
pub struct Deferrals
{
    /// The only constants eligible as flex heads: the holes judged owed.
    pub owed: BTreeSet<ConstantIndex>,
    /// The declarations judged suspended; a judgement reading one waits too.
    pub suspended: BTreeSet<ConstantIndex>,
    /// Whether the running judgement collects.
    pub collecting: Collecting,
    /// What the running judgement left.
    pub residue: Residue,
    /// Per-occurrence transport, enabled only for a term-producing run.
    pub emission: super::output::Emission,
}

impl Deferrals
{
    /// Start one declaration's judgement: `collecting` says whether it may
    /// leave residuals; nothing an earlier judgement left is kept.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the residue is empty, the collector is in `collecting`, and a
    ///   recording emission holds no transport; the owed and suspended sets are
    ///   unchanged.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — two suspended declarations judged in turn keep their
    ///   own blockers, and a nominal declaration after an owed hole forms
    ///   rigidly.
    /// - witness: `elaboration::tests::residual_conjunction_does_not_hide_refusal`
    /// - witness: `elaboration::tests::resumptions_commute`
    #[spec(
        captures: [owed = self.owed.len(), suspended = self.suspended.len()],
        ensures: self.collecting == collecting && self.residue.equations.is_empty()
            && self.residue.dependencies.is_empty()
            && self.owed.len() == owed && self.suspended.len() == suspended,
    )]
    pub fn open(
        &mut self,
        collecting: Collecting,
    )
    {
        self.collecting = collecting;
        self.residue = Residue::default();
        self.emission.restart();
    }

    /// Take what the running judgement left, leaving the residue empty.
    ///
    /// # Specification
    /// trivial.
    pub fn take(&mut self) -> Residue
    {
        core::mem::take(&mut self.residue)
    }

    /// Note that the running judgement read `constant`'s type: a dependency
    /// when `constant` waits and the judgement collects.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: `constant` is a dependency exactly when the collector is on
    ///   and `constant` is suspended; nothing else changes.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a reference to a waiting declaration and one to a
    ///   checked declaration separate a dependency from a plain read.
    /// - witness: `elaboration::tests::dependent_resumption_closes_its_prerequisites`
    /// - witness: `elaboration::tests::checked_success_is_stable_without_rejudgement`
    #[spec(
        captures: count = self.residue.dependencies.len(),
        ensures: if self.collecting == Collecting::On && self.suspended.contains(&constant) {
            self.residue.dependencies.contains(&constant)
        } else {
            self.residue.dependencies.len() == count
        },
    )]
    pub fn read(
        &mut self,
        constant: ConstantIndex,
    )
    {
        if self.collecting == Collecting::On && self.suspended.contains(&constant) {
            self.residue.dependencies.insert(constant);
        }
    }

    /// Recognize either orientation of a bare flex–rigid equation.
    ///
    /// # Specification
    /// - requires: the arguments are weak-head types of the same family.
    /// - ensures: returns the first orientation with a bare owed code constant
    ///   and a constructor-headed opposite side; otherwise
    ///   `candidate::Absent::Rigid`.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — reversed orientation, rigid and flex–flex controls in
    ///   both the value and the computation family distinguish the eligibility
    ///   boundary without claiming unification.
    /// - witness: `elaboration::tests::only_bare_flex_rigid_equations_suspend`
    /// - witness: `elaboration::tests::computation_code_decodes_suspend_as_value_ones_do`
    #[spec(ensures: |ret| match ret {
        Maybe::Present(equation) => self.owed.contains(&equation.hole),
        Maybe::Absent(_) => true,
    })]
    fn candidate(
        &self,
        arena: &CoreArena,
        left: TypeNode,
        right: TypeNode,
    ) -> Maybe<Equation, candidate::Absent>
    {
        for (flex, rigid) in [(left, right), (right, left)] {
            let code = match (flex, rigid) {
                (TypeNode::Value(flex), TypeNode::Value(rigid)) => {
                    match (arena.value_type(flex), arena.value_type(rigid)) {
                        (Some(&ValueType::Element { code, .. }), Some(other))
                            if !matches!(*other, ValueType::Element { .. }) =>
                        {
                            code
                        },
                        _ => continue,
                    }
                },
                (TypeNode::Computation(flex), TypeNode::Computation(rigid)) => {
                    match (arena.comp_type(flex), arena.comp_type(rigid)) {
                        (Some(&CompType::Element { code, .. }), Some(other))
                            if !matches!(*other, CompType::Element { .. }) =>
                        {
                            code
                        },
                        _ => continue,
                    }
                },
                _ => continue,
            };
            if let Some(&Value::Constant(hole)) = arena.value(code)
                && self.owed.contains(&hole)
            {
                return Maybe::Present(Equation { hole, flex, rigid });
            }
        }
        Maybe::Absent(candidate::Absent::Rigid)
    }

    /// Accumulate a residual without changing ordinary checking contexts.
    ///
    /// # Specification
    /// - requires: both nodes are weak-head types of the same family.
    /// - ensures: `Yes` records one eligible equation; `No` changes nothing. A
    ///   collector that is off, or has no owed flex head, always answers `No`.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an owed decode suspends a value declaration; a rigid
    ///   decode keeps the rigid mismatch, and a collector that is off defers
    ///   nothing while holes are owed.
    /// - witness: `elaboration::tests::owed_conversion_suspends`
    /// - witness: `elaboration::tests::only_bare_flex_rigid_equations_suspend`
    /// - witness: `elaboration::tests::an_off_collector_never_defers`
    #[spec(
        captures: before = self.residue.equations.len(),
        ensures: |ret| match ret {
            Deferred::Yes => self.residue.equations.len() == before.saturating_add(1),
            Deferred::No => self.residue.equations.len() == before,
        },
    )]
    pub fn defer(
        &mut self,
        arena: &CoreArena,
        left: TypeNode,
        right: TypeNode,
    ) -> Deferred
    {
        if self.collecting == Collecting::Off || self.owed.is_empty() {
            return Deferred::No;
        }
        match self.candidate(arena, left, right) {
            Maybe::Present(equation) => {
                self.residue.equations.push(equation);
                Deferred::Yes
            },
            Maybe::Absent(_) => Deferred::No,
        }
    }
}
