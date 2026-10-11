//! Translate producer graph syntax into the kernel's untrusted proposal.
//!
//! The emitted proposal is canonical: nodes are numbered in post-order from
//! the source, the target and then every arm in point and guard order,
//! children in slot order, and a classifier takes the next number where a
//! payload first names it, its own components first. Only syntax reachable
//! from those roots and the classifiers it names are emitted. Two graphs that
//! hold equal content for the sides and the arms, listed in one order, emit
//! equal proposals however their coordinates were assigned, so a schema
//! drafted from an earlier run's template and the schema a fresh run emits
//! compare byte for byte.

use anodized::spec;
use gandr_kernel_core::admission::Node as Pattern;
use gandr_kernel_core::admission::Point;
use gandr_kernel_core::admission::Proposal;
use gandr_kernel_term::stage::Child;
use gandr_kernel_term::stage::Rule;
use gandr_kernel_term::stage::Step;

use super::BTreeMap;
use super::Graph;
use super::Head;
use super::Id;
use super::Stage;
use super::StageError;
use super::Term;
use super::TermId;
use super::Type;
use super::TypeId;
use super::Vec;

/// The canonical numbering of one emission in progress.
#[derive(Default)]
struct Emission
{
    /// Emitted pattern nodes, children before parents.
    nodes: Vec<Pattern>,
    /// The canonical coordinate of every emitted graph node.
    nodes_at: BTreeMap<Id, TermId>,
    /// Emitted classifiers, components before the classifiers naming them.
    classifiers: Vec<Type>,
    /// The canonical coordinate of every emitted graph classifier.
    classifiers_at: BTreeMap<TypeId, TypeId>,
}

impl Graph
{
    /// Number one classifier and its components canonically.
    ///
    /// # Specification
    /// - ensures: `root` and every component it names are emitted once, each
    ///   after its components; returns `root`'s canonical coordinate.
    /// - fails: Unbalanced for a classifier this graph does not hold.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns `StageError::Unbalanced`.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the kernel allocates every emitted classifier at its
    ///   own coordinate and refuses a forward or repeated one, so a lost
    ///   component or a duplicate fails schema checking on the corpus.
    /// - witness: `template::tests::compressed_admission_matches_plain_families`
    #[spec(ensures: |output| output.as_ref().ok().is_none_or(|id|
        emission.classifiers_at.get(&root) == Some(id) && id.0 < emission.classifiers.len()))]
    fn emit_classifier(
        &self,
        root: TypeId,
        emission: &mut Emission,
    ) -> Result<TypeId, StageError>
    {
        let mut pending = Vec::from([(root, false)]);
        while let Some((id, ready)) = pending.pop() {
            if emission.classifiers_at.contains_key(&id) {
                continue;
            }
            let ty = *self.types.get(&id).ok_or(StageError::Unbalanced)?;
            if !ready {
                pending.push((id, true));
                match ty {
                    | Type::Arrow(domain, codomain) => {
                        pending.extend([(codomain, false), (domain, false)]);
                    },
                    | Type::Lift(inner) => pending.push((inner, false)),
                    | Type::In(_) | Type::Universe(_) | Type::Nat(_) => {},
                }
                continue;
            }
            let at = |component: TypeId| {
                emission
                    .classifiers_at
                    .get(&component)
                    .copied()
                    .ok_or(StageError::Unbalanced)
            };
            let ty = match ty {
                | Type::Arrow(domain, codomain) => {
                    let domain = at(domain)?;
                    let codomain = at(codomain)?;
                    Type::Arrow(domain, codomain)
                },
                | Type::Lift(inner) => {
                    let inner = at(inner)?;
                    Type::Lift(inner)
                },
                | leaf @ (Type::In(_) | Type::Universe(_) | Type::Nat(_)) => leaf,
            };
            emission
                .classifiers_at
                .insert(id, TypeId(emission.classifiers.len()));
            emission.classifiers.push(ty);
        }
        emission
            .classifiers_at
            .get(&root)
            .copied()
            .ok_or(StageError::Unbalanced)
    }

    /// Emit an equation and its guarded arms as the canonical kernel proposal,
    /// without giving any cached inheritance authority.
    ///
    /// # Specification
    /// - requires: every arm is point-free content of this graph.
    /// - ensures: preserves every rigid payload, edge, point and predecessor
    ///   reachable from the sides and the arms, and the arms in the order
    ///   given; nodes and classifiers are numbered canonically, every child and
    ///   classifier component before its parent, so equal content listed in one
    ///   order emits an equal proposal.
    /// - fails: Unbalanced for a node or classifier this graph does not hold,
    ///   or a predecessor without its point; a child-shape refusal.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns `StageError::Unbalanced` or a child-shape refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — kernel inheritance and the complete family replay
    ///   differential distinguish changed edges or payloads; drafted and fresh
    ///   proposals over the edit-pair corpus compare byte for byte, which an
    ///   order that followed graph coordinates, or kept unreachable syntax or
    ///   classifiers, would break.
    /// - witness: `template::tests::compressed_admission_matches_plain_families`
    /// - witness: `template::tests::drafts_equal_fresh_runs_across_the_edit_traces`
    #[spec(ensures: |ret| ret.as_ref().ok().is_none_or(|proposal|
        proposal.equation.rule == rule
        && proposal.arms.len() == arms.len()
        && proposal.arms.iter().zip(arms).all(|(emitted, given)| emitted.len() == given.len())
        && proposal.nodes.len() <= self.nodes.len()
        && self.types.len() >= proposal.classifiers.len()
        && proposal.nodes.iter().enumerate().all(|(index, node)| match *node {
            Pattern::Rigid(term) => term.children().into_iter().flatten().all(|child| child.0 < index),
            Pattern::Point(point) | Pattern::Predecessor(point) => point.0 < arms.len(),
        })))]
    pub(in crate::template) fn admission_proposal(
        &self,
        sides: [Id; 2],
        rule: Rule,
        arms: &[Vec<Id>],
    ) -> Result<Proposal, StageError>
    {
        let mut emission = Emission::default();
        let mut pending = Vec::new();
        for root in sides.iter().chain(arms.iter().flatten()) {
            pending.push((*root, false));
            while let Some((id, ready)) = pending.pop() {
                if emission.nodes_at.contains_key(&id) {
                    continue;
                }
                let node = self.node(id)?;
                if !ready {
                    pending.push((id, true));
                    pending.extend(
                        node.children
                            .0
                            .iter()
                            .rev()
                            .flatten()
                            .map(|child| (*child, false)),
                    );
                    continue;
                }
                let dummy = TermId(0);
                let term = match node.head {
                    | Head::Point(point) => {
                        emission.nodes_at.insert(id, TermId(emission.nodes.len()));
                        emission
                            .nodes
                            .push(Pattern::Point(Point(usize::from(point))));
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
                        emission.nodes_at.insert(id, TermId(emission.nodes.len()));
                        emission
                            .nodes
                            .push(Pattern::Predecessor(Point(usize::from(point))));
                        continue;
                    },
                    | Head::Variable(index) => Term::Variable(index),
                    | Head::OuterNatural(value) => Term::Natural(Stage::Outer, value),
                    | Head::InnerNatural(model, value) => Term::Natural(Stage::Inner(model), value),
                    | Head::Code(ty) => {
                        let ty = self.emit_classifier(ty, &mut emission)?;
                        Term::Code(ty)
                    },
                    | Head::Lambda(ty) => {
                        let ty = self.emit_classifier(ty, &mut emission)?;
                        Term::Lambda(ty, dummy)
                    },
                    | Head::Apply => Term::Apply(dummy, dummy),
                    | Head::Multiply => Term::Multiply(dummy, dummy),
                    | Head::Quote => Term::Quote(dummy),
                    | Head::Splice => Term::Splice(dummy),
                    | Head::Iterate => Term::Iterate(dummy, dummy, dummy),
                    | Head::Eliminate(ty) => {
                        let ty = self.emit_classifier(ty, &mut emission)?;
                        Term::Eliminate(dummy, ty)
                    },
                };
                let mut children = [Child::Vacant; 3];
                for (child, slot) in node.children.0.iter().zip(&mut children) {
                    if let Some(child) = *child {
                        let at = *emission
                            .nodes_at
                            .get(&child)
                            .ok_or(StageError::Unbalanced)?;
                        *slot = Child::Present(at);
                    }
                }
                let term = term.rebuild(children)?;
                emission.nodes_at.insert(id, TermId(emission.nodes.len()));
                emission.nodes.push(Pattern::Rigid(term));
            }
        }
        let at = |id: &Id| {
            emission
                .nodes_at
                .get(id)
                .copied()
                .ok_or(StageError::Unbalanced)
        };
        let [source, target] = sides;
        let source = at(&source)?;
        let target = at(&target)?;
        let arms = arms
            .iter()
            .map(|point| point.iter().map(at).collect::<Result<Vec<_>, _>>())
            .collect::<Result<Vec<_>, _>>()?;
        Ok(Proposal {
            classifiers: emission.classifiers,
            nodes: emission.nodes,
            equation: Step {
                source,
                target,
                rule,
            },
            arms,
        })
    }
}
