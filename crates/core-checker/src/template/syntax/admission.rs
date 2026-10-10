//! Translate producer graph syntax into the kernel's untrusted proposal.

use gandr_kernel_core::admission::Node as Pattern;
use gandr_kernel_core::admission::Point;
use gandr_kernel_core::admission::Proposal;
use gandr_kernel_term::stage::Child;
use gandr_kernel_term::stage::Step;

use super::Graph;
use super::Head;
use super::Stage;
use super::StageError;
use super::Term;
use super::TermId;
use super::Vec;

impl Graph
{
    /// Export the graph without giving its cached inheritance any authority.
    ///
    /// # Specification
    /// - ensures: preserves every rigid payload, edge, point and predecessor.
    /// - fails: malformed point or child shape.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns `StageError::Unbalanced` or a child-shape refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — kernel inheritance and the complete family replay
    ///   differential distinguish changed edges or payloads.
    /// - witness: `template::tests::compressed_admission_matches_plain_families`
    pub(in crate::template) fn admission_proposal(
        &self,
        equation: Step,
        arms: Vec<Vec<TermId>>,
    ) -> Result<Proposal, StageError>
    {
        let mut nodes = Vec::with_capacity(self.nodes.len());
        for node in &self.nodes {
            let dummy = TermId(0);
            let term = match node.head {
                | Head::Point(point) => {
                    nodes.push(Pattern::Point(Point(usize::from(point))));
                    continue;
                },
                | Head::Predecessor => {
                    let child = node
                        .children
                        .0
                        .first()
                        .copied()
                        .flatten()
                        .ok_or(StageError::Unbalanced)?;
                    let Head::Point(point) = self.node(child)?.head
                    else {
                        return Err(StageError::Unbalanced);
                    };
                    nodes.push(Pattern::Predecessor(Point(usize::from(point))));
                    continue;
                },
                | Head::Variable(index) => Term::Variable(index),
                | Head::OuterNatural(value) => Term::Natural(Stage::Outer, value),
                | Head::InnerNatural(model, value) => Term::Natural(Stage::Inner(model), value),
                | Head::Code(ty) => Term::Code(ty),
                | Head::Lambda(ty) => Term::Lambda(ty, dummy),
                | Head::Apply => Term::Apply(dummy, dummy),
                | Head::Multiply => Term::Multiply(dummy, dummy),
                | Head::Quote => Term::Quote(dummy),
                | Head::Splice => Term::Splice(dummy),
                | Head::Iterate => Term::Iterate(dummy, dummy, dummy),
                | Head::Eliminate(ty) => Term::Eliminate(dummy, ty),
            };
            let children = node
                .children
                .0
                .map(|child| child.map_or(Child::Vacant, |id| Child::Present(TermId(id.0))));
            nodes.push(Pattern::Rigid(term.rebuild(children)?));
        }
        Ok(Proposal {
            classifiers: self.types.values().copied().collect(),
            nodes,
            equation,
            arms,
        })
    }
}
