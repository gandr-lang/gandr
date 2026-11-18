//! Saturation: rounds of a read phase that finds every match of every
//! equation, an apply phase that joins each match's two sides, and a rebuild.

use alloc::collections::BTreeSet;
use alloc::vec;
use alloc::vec::Vec;

use gandr_theory_coherent_resolutions::TermHead;
use gandr_theory_coherent_resolutions::TermPlace;

use super::Count;
use super::EGraph;
use super::Equation;
use super::EquationPlace;
use crate::analysis::Analysis;
use crate::error::EGraphError;

/// The limits of a saturation.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct Budget
{
    /// The most rounds it runs.
    pub rounds: Count,
    /// The most nodes the e-graph holds before it stops.
    pub nodes: Count,
}

/// How a saturation stops.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Outcome
{
    /// A round finds no match that the e-graph has not applied: the classes
    /// are closed under the equations.
    Saturated,
    /// The saturation reaches its budget of rounds or of nodes first.
    Exhausted,
}

/// What a saturation does.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct Run
{
    /// The rounds that apply a match.
    pub rounds: Count,
    /// The matches applied.
    pub matches: Count,
    /// How it stops.
    pub outcome: Outcome,
}

/// What a partial match still has to match: a pattern against one node, or
/// against any member of a node's class.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Goal
{
    /// The node itself.
    Node(TermPlace),
    /// Any member of the node's class; a variable takes the node itself.
    Class(TermPlace),
}

/// A partial match: each variable's value so far, and the goals left.
#[derive(Clone, Debug, Default)]
struct Partial
{
    /// The value of each variable, by its place.
    bound: Vec<Option<TermPlace>>,
    /// The pattern nodes left, each with its goal.
    goals: Vec<(TermPlace, Goal)>,
}

impl<A> EGraph<A>
where
    A: Analysis,
{
    /// Saturate the e-graph with its equations within `budget`. Each round
    /// reads every match of every equation, then applies each match that the
    /// e-graph has not applied, then rebuilds. An equation with no variable
    /// matches once, wherever its sides stand; any other equation matches a
    /// held node that its left side meets modulo the classes.
    ///
    /// # Specification
    /// - ensures: a round's matches depend on the classes before the round
    ///   alone, so the order of the equations does not change the classes;
    ///   [`Outcome::Saturated`] exactly when a round finds no new match.
    /// - fails: as [`EGraph::apply`] and [`EGraph::rebuild`] fail.
    /// - panics: none.
    /// - executable: none — the ensures compares two runs, and the call is one.
    /// - intension: the read phase matches each equation at each held node; the
    ///   apply phase joins each match once.
    ///
    /// # Errors
    /// - [`EGraphError`]: as [`EGraph::apply`] or [`EGraph::rebuild`] refuse.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — two orders of one block's equations give one set of
    ///   classes; an equation that grows a term each round reaches its budget;
    ///   a pattern meets a node through the members of a child's class.
    /// - witness: `tests::phases::two_orders_of_the_equations_give_the_same_classes`
    /// - witness: `tests::phases::a_saturation_that_grows_stops_at_its_budget`
    /// - witness: `tests::phases::a_pattern_matches_modulo_the_classes`
    #[inline]
    pub fn saturate(
        &mut self,
        budget: Budget,
    ) -> Result<Run, EGraphError>
    {
        let (mut rounds, mut matches) = (0_usize, 0_usize);
        self.rebuild()?;
        let outcome = loop {
            if rounds >= usize::from(budget.rounds) {
                break Outcome::Exhausted;
            }
            let found = self.read()?;
            if found.is_empty() {
                break Outcome::Saturated;
            }
            rounds = rounds.saturating_add(1);
            matches = matches.saturating_add(found.len());
            for (equation, values) in found {
                let _joined = self.apply(equation, values)?;
            }
            self.rebuild()?;
            if self.nodes > usize::from(budget.nodes) {
                break Outcome::Exhausted;
            }
        };
        Ok(Run {
            rounds: Count::from(rounds),
            matches: Count::from(matches),
            outcome,
        })
    }

    /// Every match of every equation that the e-graph has not applied, each
    /// once, in order. A match binds each variable to the root of a class,
    /// so two matches that differ in members of one class are one; an
    /// instance applied before counts as applied while its values' classes
    /// stay the classes of the match's values.
    ///
    /// # Specification
    /// trivial.
    fn read(&self) -> Result<Vec<(EquationPlace, Vec<TermPlace>)>, EGraphError>
    {
        let mut done = BTreeSet::new();
        for &(equation, ref values) in &self.applied {
            let mut roots = Vec::with_capacity(values.len());
            for &value in values {
                roots.push(self.find(value)?);
            }
            let _new = done.insert((equation, roots));
        }
        let mut found = BTreeSet::new();
        for (index, &equation) in self.equations.iter().enumerate() {
            let place = EquationPlace::from(index);
            if usize::from(equation.variables) == 0 {
                let _new = found.insert((place, Vec::new()));
                continue;
            }
            for node in self.table.issued() {
                if self.leader(node).is_some() {
                    self.matches_at((place, equation), node, &mut found)?;
                }
            }
        }
        Ok(found
            .into_iter()
            .filter(|instance| !done.contains(instance))
            .collect())
    }

    /// Put into `found` each match of the equation's left side at `node`:
    /// the node itself matches the left side's root, and each argument of a
    /// pattern matches any member of the class of the node's argument there.
    ///
    /// # Specification
    /// trivial.
    fn matches_at(
        &self,
        (place, equation): (EquationPlace, Equation),
        node: TermPlace,
        found: &mut BTreeSet<(EquationPlace, Vec<TermPlace>)>,
    ) -> Result<(), EGraphError>
    {
        let mut pending = vec![Partial {
            bound: vec![None; usize::from(equation.variables)],
            goals: vec![(equation.left, Goal::Node(node))],
        }];
        while let Some(mut partial) = pending.pop() {
            let Some((pattern, goal)) = partial.goals.pop()
            else {
                let values: Option<Vec<TermPlace>> = partial.bound.into_iter().collect();
                if let Some(values) = values {
                    let _new = found.insert((place, values));
                }
                continue;
            };
            let wanted = self.table.node(pattern)?;
            match wanted.head {
                TermHead::Var(variable) => {
                    let at = match goal {
                        Goal::Node(at) | Goal::Class(at) => at,
                    };
                    let value = self.root(at)?;
                    match partial.bound.get_mut(usize::from(variable)) {
                        Some(slot @ &mut None) => {
                            *slot = Some(value);
                            pending.push(partial);
                        },
                        Some(&mut Some(bound)) if bound == value => pending.push(partial),
                        Some(&mut Some(_)) | None => {},
                    }
                },
                TermHead::Op(_) => {
                    let candidates: Vec<TermPlace> = match goal {
                        Goal::Node(at) => vec![at],
                        Goal::Class(at) => self.members(at)?.collect(),
                    };
                    for candidate in candidates {
                        let had = self.table.node(candidate)?;
                        if had.head != wanted.head || had.children.len() != wanted.children.len() {
                            continue;
                        }
                        let mut next = partial.clone();
                        next.goals.extend(
                            wanted
                                .children
                                .iter()
                                .zip(&had.children)
                                .map(|(&pattern, &child)| (pattern, Goal::Class(child))),
                        );
                        pending.push(next);
                    }
                },
            }
        }
        Ok(())
    }
}
