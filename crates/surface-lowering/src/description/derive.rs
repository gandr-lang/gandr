//! The statement a `derive` declaration writes, `derive r : l <=> r in T`:
//! the rule's name, its two sides read as terms over the theory's
//! operations, as a theory's own rule reads them, and the theory it holds in.

use alloc::collections::BTreeSet;

use anodized::spec;
use gandr_surface_grammar::Pbg;
use gandr_surface_syntax::SyntaxTree;
use quenchant_shape::shape::Maybe;

use super::DescriptionDiagnostic;
use super::DescriptionFault;
use super::Reader;
use super::Run;
use super::Spelling;
use super::written::WrittenDerived;
use crate::LoweringRefusal;
use crate::form::FormName;
use crate::form::Pieces;
use crate::form::Placed;
use crate::form::read_pieces;

/// What `derive r : l <=> r in T` states: the equation `l = r` between two
/// terms over the operations of the theory `T`, named `r`.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: each side is the free term its written form reads as, a name a
///   variable and an application `f(t, …)` an operation's, kept with where each
///   of its nodes is written.
/// - executable: none — a statement is data the collection reads.
///
/// # Adequacy
/// - hypothesis: L3 — a group's inverse of a product reads as its two sides.
/// - witness: `tests::modules::models::a_derived_rule_reads_the_model_it_quantifies_over`
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct DerivedStatement
{
    /// The rule's name tile.
    pub named: Placed,
    /// The theory's name tile.
    pub theory: Placed,
    /// Where the left side is written.
    pub left: Placed,
    /// Where the right side is written.
    pub right: Placed,
    /// The two sides read, each with its nodes.
    pub sides: WrittenDerived,
}

/// Read the `derive` declaration at `at`.
///
/// # Specification
/// - requires: `at` is a derive declaration of `tree`, molded under `grammar`.
/// - ensures: the name after `derive`; the two sides either side of the face
///   arrow, `<=>` or `==>`, each read as [`Reader::free_term`] reads a rule's
///   side, the right one's applied variables those the left binds; the name
///   after `in`.
/// - fails: the parser's repair of the form, as the repair's refusal; a piece
///   out of place, or a side that is no term, as the description diagnostic
///   locating it.
/// - panics: none.
///
/// # Errors
/// The repair's [`LoweringRefusal::MalformedForm`], or the mold refusals of
/// [`read_pieces`].
///
/// # Adequacy
/// - hypothesis: L3 — a group's inverse of a product reads as its two sides,
///   and a statement its theory keeps apart reads as its sides too.
/// - witness: `tests::modules::models::a_derived_rule_reads_the_model_it_quantifies_over`
/// - witness: `tests::modules::models::a_rule_the_theory_does_not_derive_is_refused`
#[spec(ensures: |ret| ret.as_ref().map_or(true, |read| read.as_ref().map_or(true, |statement| statement.named.span.start() >= at.span.start())))]
pub fn derived_statement<'source>(
    grammar: &Pbg,
    tree: &SyntaxTree<'source>,
    at: Placed,
) -> Result<Result<DerivedStatement, DescriptionDiagnostic>, LoweringRefusal<'source>>
{
    let mut pieces = Pieces::new();
    read_pieces(grammar, tree, at.node, &mut pieces)?;
    if let Maybe::Present(repair) = pieces.repair {
        return Err(repair.refusal(FormName::DERIVE_DECLARATION));
    }
    let reader = Reader { grammar, tree };
    let mut run = Run::new(&pieces.pieces, at.span);
    Ok(reader.derived(&mut run))
}

impl Reader<'_, '_>
{
    /// The statement `run` writes, past nothing.
    ///
    /// # Specification
    /// - requires: `run` stands before the declaration's `derive` tile.
    /// - ensures: as [`derived_statement`].
    /// - fails: a tile out of place, a missing piece, a piece past the theory's
    ///   name, or a side that is no term, located.
    /// - panics: none.
    ///
    /// # Errors
    /// [`DescriptionFault::Malformed`] at the declaration, or the side's own
    /// diagnostic.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`derived_statement`].
    /// - witness: `tests::modules::models::a_derived_rule_reads_the_model_it_quantifies_over`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |statement| statement.named.span.start() < statement.left.span.start() && statement.left.span.start() < statement.right.span.start() && statement.right.span.start() < statement.theory.span.start()))]
    fn derived(
        &self,
        run: &mut Run<'_>,
    ) -> Result<DerivedStatement, DescriptionDiagnostic>
    {
        if !run.eat(Spelling("derive")).0 {
            return Err(run.fault(DescriptionFault::Malformed));
        }
        let named = run.take()?;
        if !run.eat(Spelling(":")).0 {
            return Err(run.fault(DescriptionFault::Malformed));
        }
        let left = run.take()?;
        if !(run.eat(Spelling("<=>")).0 || run.eat(Spelling("==>")).0) {
            return Err(run.fault(DescriptionFault::Malformed));
        }
        let right = run.take()?;
        if !run.eat(Spelling("in")).0 {
            return Err(run.fault(DescriptionFault::Malformed));
        }
        let theory = run.take()?;
        run.end()?;
        let (lhs, left_nodes) = self.free_term(left, &BTreeSet::new())?;
        let (rhs, right_nodes) = self.free_term(right, &lhs.to_node().vars().collect())?;

        Ok(DerivedStatement {
            named,
            theory,
            left,
            right,
            sides: WrittenDerived {
                left: (lhs, left_nodes),
                right: (rhs, right_nodes),
            },
        })
    }
}
