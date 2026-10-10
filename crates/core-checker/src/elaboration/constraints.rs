//! Residual conversion equations, restricted to bare owed code constants.

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

/// The local residual collector; an empty owed set disables suspension.
#[derive(Default)]
pub struct Deferrals
{
    /// The only constants eligible as flex heads.
    pub owed: BTreeSet<ConstantIndex>,
    /// Equations encountered while judging one declaration.
    pub equations: Vec<Equation>,
    /// Per-occurrence transport, enabled only for the elaboration driver.
    pub emission: super::output::Emission,
}

impl Deferrals
{
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
    /// - hypothesis: L3 — reversed orientation, rigid and flex–flex controls
    ///   distinguish the eligibility boundary without claiming unification.
    /// - witness: `elaboration::tests::only_bare_flex_rigid_equations_suspend`
    #[spec(ensures: |ret| match ret {
        | Maybe::Present(equation) => self.owed.contains(&equation.hole),
        | Maybe::Absent(_) => true,
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
                | (TypeNode::Value(flex), TypeNode::Value(rigid)) => {
                    match (arena.value_type(flex), arena.value_type(rigid)) {
                        | (Some(&ValueType::Element { code, .. }), Some(other))
                            if !matches!(*other, ValueType::Element { .. }) =>
                        {
                            code
                        },
                        | _ => continue,
                    }
                },
                | (TypeNode::Computation(flex), TypeNode::Computation(rigid)) => {
                    match (arena.comp_type(flex), arena.comp_type(rigid)) {
                        | (Some(&CompType::Element { code, .. }), Some(other))
                            if !matches!(*other, CompType::Element { .. }) =>
                        {
                            code
                        },
                        | _ => continue,
                    }
                },
                | _ => continue,
            };
            if let Some(&Value::Constant(hole)) = arena.value(code)
                && self.owed.contains(&hole)
            {
                return Maybe::Present(Equation { hole, flex, rigid });
            }
        }
        Maybe::Absent(candidate::Absent::Rigid)
    }
}

impl Deferrals
{
    /// Accumulate a residual without changing ordinary checking contexts.
    ///
    /// # Specification
    /// - requires: both nodes are weak-head types of the same family.
    /// - ensures: `Yes` records one eligible equation; `No` changes nothing.
    ///   Ordinary contexts have no owed flex heads and always return `No`.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an owed decode suspends only through elaboration;
    ///   ordinary checking retains its rigid-hole mismatch.
    /// - witness: `elaboration::tests::owed_conversion_suspends`
    #[spec(ensures: |ret| ret == Deferred::No || !self.equations.is_empty())]
    pub fn defer(
        &mut self,
        arena: &CoreArena,
        left: TypeNode,
        right: TypeNode,
    ) -> Deferred
    {
        if self.owed.is_empty() {
            return Deferred::No;
        }
        let candidate = self.candidate(arena, left, right);
        match candidate {
            | Maybe::Present(equation) => {
                self.equations.push(equation);
                Deferred::Yes
            },
            | Maybe::Absent(_) => Deferred::No,
        }
    }
}
