//! Family arities, uniform result heads and symbol attributes.

use alloc::vec::Vec;

use anodized::spec;
use gandr_surface_syntax::ByteSpan;
use gandr_theory_levitation::Attr;
use gandr_theory_levitation::Attrs;
use gandr_theory_levitation::Name;

use super::DescriptionDiagnostic;
use super::DescriptionFault;
use super::FamilyParameter;
use super::Reader;
use super::Run;
use super::Spelling;
use crate::form::Piece;
use crate::form::Placed;

/// The number of term-index positions declared by a family's classifier.
#[repr(transparent)]
#[derive(Clone, Copy)]
pub(super) struct IndexArity(usize);

impl Reader<'_, '_>
{
    /// Count the right-associated index telescope without interpreting its
    /// terms.
    ///
    /// # Specification
    /// - ensures: one index position is counted for each outer classifier
    ///   arrow.
    /// - fails: unreadable classifier syntax retains its source location.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns the shared molded-reader refusal for malformed syntax.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — indexed and unindexed declarations distinguish the
    ///   two arities.
    /// - witness: `description::tests::the_data_corpus_fixture_elaborates_to_its_descriptions`
    #[spec(ensures: |result| result.is_ok() || self.tree.node(at.node).is_some())]
    pub(super) fn index_arity(
        &self,
        at: Placed,
    ) -> Result<IndexArity, DescriptionDiagnostic>
    {
        let mut current = at;
        let mut count = 0_usize;
        loop {
            let pieces = self.pieces(current)?;
            match *pieces.as_slice() {
                [_, Piece::Tile { label, .. }, ref result] if label.as_ref() == "->" => {
                    count = count.saturating_add(1);
                    current = result.placed();
                },
                _ => return Ok(IndexArity(count)),
            }
        }
    }

    /// Require the declared family and its parameter variables in binding
    /// order. Index expressions occupy the remaining positions without
    /// being decoded as types; their semantics belong to the indexed
    /// former.
    ///
    /// # Specification
    /// - ensures: success has the declared head, parameter prefix and total
    ///   arity, and answers the bytes of each argument in written order.
    /// - fails: a foreign, instantiated, reordered or wrong-arity result is
    ///   located at the result rather than at a sibling member.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns `NonUniformResult` when the result violates family uniformity.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — foreign heads, instantiated parameters and unequal
    ///   arities separate the independent uniformity premises; a result
    ///   repeating a parameter by another name is refused.
    /// - witness: `description::tests::an_instantiated_result_head_declines_as_uninferable`
    /// - witness: `description::tests::a_result_head_of_the_wrong_arity_declines`
    /// - witness: `description::tests::a_foreign_result_head_declines`
    /// - witness: `description::tests::a_result_must_repeat_each_parameter_by_its_own_name`
    #[spec(ensures: |result| match result.as_ref() {
        Ok(arguments) => arguments.len() == parameters.len().saturating_add(indices.0),
        Err(diagnostic) => diagnostic.span == at.span,
    })]
    pub(super) fn uniform_result(
        &self,
        at: Placed,
        family: &Name,
        parameters: &[FamilyParameter],
        indices: IndexArity,
    ) -> Result<Vec<ByteSpan>, DescriptionDiagnostic>
    {
        let refusal = || DescriptionDiagnostic {
            span: at.span,
            fault: DescriptionFault::NonUniformResult,
        };
        let pieces = self.pieces(at).map_err(|_diagnostic| refusal())?;
        let mut run = Run::new(&pieces, at.span);
        let head = run.take().map_err(|_diagnostic| refusal())?;
        if self.text(head).0 != family.as_ref() {
            return Err(refusal());
        }
        let expected = parameters.len().saturating_add(indices.0);
        if !run.eat(Spelling("(")).0 {
            return if expected == 0 && run.remaining().is_empty() {
                Ok(Vec::new())
            }
            else {
                Err(refusal())
            };
        }
        let mut arguments = Vec::with_capacity(expected);
        while !run.eat(Spelling(")")).0 {
            let argument = run.take().map_err(|_diagnostic| refusal())?;
            if let Some(parameter) = parameters.get(arguments.len()) {
                let shape = self.pieces(argument).map_err(|_diagnostic| refusal())?;
                if !matches!(shape.as_slice(), [Piece::Tile { label, .. }] if label.as_ref() == "type_variable")
                    || self.text(argument).0 != parameter.name.as_ref()
                {
                    return Err(refusal());
                }
            }
            arguments.push(argument.span);
            if !run.eat(Spelling(",")).0 && !run.at(Spelling(")")).0 {
                return Err(refusal());
            }
        }
        if arguments.len() != expected || !run.remaining().is_empty() {
            return Err(refusal());
        }
        Ok(arguments)
    }

    /// Retain an optional symbol-attribute slot for the description checker.
    /// Reserved metadata is not silently erased before `check_desc` sees it.
    ///
    /// # Specification
    /// - ensures: an absent slot consumes nothing; a present slot keeps its
    ///   markers.
    /// - fails: incomplete delimiters or marker separators are located.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns `Malformed` for an incomplete attribute slot.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a reserved marker distinguishes retained attributes
    ///   from erasure, two markers read through their separator.
    /// - witness: `description::tests::the_declined_metadata_golden_is_declined`
    #[spec(captures: before = run.remaining().len(), ensures: run.remaining().len() <= before)]
    pub(super) fn attrs(
        &self,
        run: &mut Run<'_>,
    ) -> Result<Attrs, DescriptionDiagnostic>
    {
        if !run.eat(Spelling("[")).0 {
            return Ok(Attrs::empty());
        }
        let mut markers = Vec::new();
        while !run.eat(Spelling("]")).0 {
            let at = run.take()?;
            markers.push(Attr::marker(self.text(at).0));
            if !run.eat(Spelling(",")).0 && !run.at(Spelling("]")).0 {
                return Err(run.fault(DescriptionFault::Malformed));
            }
        }
        Ok(Attrs::new(markers))
    }
}

impl Run<'_>
{
    /// Refuse a suffix instead of silently dropping another written member.
    ///
    /// # Specification
    /// - ensures: success is equivalent to complete consumption.
    /// - fails: an unread suffix is a malformed member.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns `Malformed` when syntax remains.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — unseparated members distinguish complete from partial
    ///   consumption.
    /// - witness: `description::sign::tests::unseparated_members_are_declined_rather_than_dropped`
    #[spec(ensures: |result| result.is_ok() == self.remaining().is_empty())]
    pub(super) fn end(&self) -> Result<(), DescriptionDiagnostic>
    {
        if self.remaining().is_empty() {
            Ok(())
        }
        else {
            Err(self.fault(DescriptionFault::Malformed))
        }
    }
}
