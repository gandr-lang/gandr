//! A natural literal checked where a type other than `Integer` is expected
//! reads through a model of the prelude's `FromNat` at that type.
//!
//! # The lowering lends the readers, the checker picks one
//!
//! A literal lowers to its primitive integer wherever it stands. Each
//! top-level module whose ascription is the prelude's `Model(FromNat)`, or a
//! model of a theory including it, lends its `fromNat` member to the checker
//! as a reader. The checker crosses a natural literal checked against a type
//! apart from `Integer` by the one reader whose carrier converts with that
//! type, as it crosses a model by a kept reduct. A literal at `Integer`, or
//! where nothing states a type, never meets a reader, so it stays the
//! primitive it is and costs nothing.
//!
//! # The prelude's `FromNat`, by position
//!
//! The theory is read from the prelude's top level, as the binary naturals
//! are ([`super::natural`]). A source's own theory named `FromNat` is another
//! theory, and its models lend nothing; a unit with no prelude, which only a
//! test lays, has no readers.

use alloc::collections::BTreeSet;
use alloc::vec::Vec;

use anodized::spec;
use gandr_kernel_term::ConstantIndex;
use quenchant_shape::shape::Maybe;

use super::Lowerer;
use crate::module::Container;
use crate::module::Stratum;
use crate::module::StructureIndex;
use crate::resolve::SurfaceName;

#[cfg(test)]
mod tests;

impl Lowerer<'_, '_>
{
    /// The `fromNat` member of every top-level module that is a model of the
    /// prelude's `FromNat`, in declaration order: the readers the checker may
    /// cross a natural literal by.
    ///
    /// # Specification
    /// - requires: the mint sweep has run.
    /// - ensures: one admission position per top-level module whose ascription
    ///   names the prelude's `FromNat`, or a theory including it, and whose
    ///   member `fromNat` lowered without a refusal, in declaration order; none
    ///   for a unit with no prelude or a prelude without the theory.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a model of the prelude's theory lends its member, a
    ///   model of a source's own `FromNat` lends none.
    /// - witness: `lower::reader::tests::a_model_of_the_prelude_s_from_nat_lends_its_reader_4528`
    /// - witness: `lower::reader::tests::a_source_s_own_from_nat_lends_no_reader_4528`
    #[spec(ensures: |ret| ret.windows(2).all(|pair| pair.first() != pair.get(1)))]
    pub(super) fn literal_readers(&self) -> Vec<ConstantIndex>
    {
        let Some(prelude) = self.collected.unit.prelude()
        else {
            return Vec::new();
        };
        let Some(&theory) = self
            .collected
            .by_name
            .get(&(Container::TopLevel(prelude), SurfaceName::from("FromNat")))
        else {
            return Vec::new();
        };
        let mut answering = BTreeSet::from([theory]);
        for (&including, reached) in &self.collected.included {
            if reached.iter().any(|&(included, _)| included == theory) {
                let _fresh = answering.insert(including);
            }
        }
        self.collected
            .structures
            .iter()
            .enumerate()
            .filter(|&(_, structure)| {
                matches!(structure.container, Container::TopLevel(_))
                    && matches!(structure.stratum, Stratum::Module)
                    && match structure.model {
                        Maybe::Present(model) => self
                            .collected
                            .model_theories
                            .get(&model)
                            .is_some_and(|slot| answering.contains(slot)),
                        Maybe::Absent(_) => false,
                    }
            })
            .filter_map(|(at, _)| {
                let module = Container::Module(StructureIndex::from(at));
                self.collected
                    .by_name
                    .get(&(module, SurfaceName::from("fromNat")))
                    .and_then(|&slot| self.collected.slots.get(usize::from(slot)))
                    .filter(|declared| matches!(declared.refusal, Maybe::Absent(_)))
                    .map(|declared| declared.constant)
            })
            .collect()
    }
}
