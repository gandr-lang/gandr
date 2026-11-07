//! Semidecisions: the obligations of the refinement machine, the evidence
//! that each asks for, and the outcome of each.
//!
//! A semidecision is Sierpiński-valued. It gives finite positive evidence, or
//! it stays undecided for a stated reason. An [`Obligation`] names a node of a
//! validated plan and its [`Demand`], the evidence that it asks for: an
//! enclosure of a real node to a width, or a certificate that an open node
//! holds or fails. The machine works on an obligation one certificate step
//! at a time, so each unit of work adds one step of the certificate that
//! [`crate::certificate::check`] replays. The work of one step is at most two
//! exact squares, or four exact products, of dyadics within the checker's
//! width quota, or the series of one builtin at the precision of its step.
//!
//! An obligation ends in one of five [`Outcome`]s. [`Outcome::Certified`]
//! carries the certificate. [`Outcome::Suspended`] states why the machine
//! cannot go on. The other three outcomes say only why a run stopped while
//! the obligation was live. No outcome states that a proposition is false
//! unless its certificate concludes it: a failure is evidence only when an
//! obligation asks for it and the certificate replays.
//!
//! # Boundaries
//!
//! The machine has rules for constants, registered cuts, strict comparisons of
//! such reals, the lower and upper cuts of a registered cut, and bounded
//! quantifiers over intervals whose body compares polynomials in the bound
//! variable. The search of a quantifier is `crate::bisection`. It also has a
//! rule for a real made of constants, registered cuts, sums, differences,
//! products, π, cosines, sines and angles, and for a strict comparison of two
//! such reals: the compound chain of `crate::compound`. Any other form
//! suspends with [`SuspendReason::NoRule`].

use alloc::vec::Vec;

use anodized::spec;
use num_bigint::BigInt;

use crate::bisection::PieceCount;
use crate::bisection::Search;
use crate::bisection::Turn;
use crate::certificate::Certificate;
use crate::certificate::CertificateCheck;
use crate::certificate::CheckerQuotas;
use crate::certificate::Conclusion;
use crate::certificate::FormatVersion;
use crate::certificate::Side;
use crate::certificate::Step;
use crate::certificate::StepId;
use crate::certificate::replay_prefix;
use crate::compound::Compound;
use crate::dovetail::ResumeError;
use crate::dovetail::Steps;
use crate::dyadic::Dyadic;
use crate::dyadic::Exponent;
use crate::dyadic::Precision;
use crate::dyadic::Rounded;
use crate::dyadic::Rounding;
use crate::interval::Endpoint;
use crate::interval::NumericInterval;
use crate::plan::Node;
use crate::plan::NodeId;
use crate::plan::Open;
use crate::plan::Plan;
use crate::plan::PlanError;
use crate::plan::Real;
use crate::schema::Membership;
use crate::schema::Refinement;
use crate::schema::Split;
use crate::schema::membership;
use crate::schema::radicand;
use crate::validate::ValidatedPlan;

/// What an obligation asks the machine to certify.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Demand
{
    /// An enclosure of a real node no wider than `2^width`.
    Encloses
    {
        /// The power of two that bounds the width of the enclosure.
        width: Exponent,
    },
    /// The open node holds.
    Holds,
    /// The open node fails.
    Fails,
}

/// A typed obligation: a node of a validated plan and the evidence that it
/// asks for.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct Obligation
{
    /// The node.
    node: NodeId,
    /// The evidence asked for.
    demand: Demand,
}

impl Obligation
{
    /// The obligation that asks for `demand` of the node `node` of `plan`.
    ///
    /// # Specification
    /// - ensures: an enclosure names a real node, and a pole names an open
    ///   node.
    /// - fails: refuses a node that the plan does not hold as
    ///   [`PlanError::UnknownNode`], and a node of the other sort as
    ///   [`PlanError::WrongSort`].
    /// - panics: none.
    ///
    /// # Errors
    /// - [`PlanError::UnknownNode`]: no node is at `node`.
    /// - [`PlanError::WrongSort`]: the node's sort does not take the evidence.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — each evidence on a node of its sort, of the other
    ///   sort, of sort domain, and on a position past the plan.
    /// - witness: `tests::dovetail::an_obligation_names_a_node_of_its_sort`
    #[spec(ensures: |ref result| result.as_ref().map_or(true, |obligation| obligation.node == node && obligation.demand == demand))]
    #[inline]
    pub fn new(
        plan: &ValidatedPlan,
        node: NodeId,
        demand: Demand,
    ) -> Result<Self, PlanError>
    {
        let sorted = match (plan.plan().node(node)?, demand) {
            (&Node::Real(_), Demand::Encloses { .. })
            | (&Node::Open(_), Demand::Holds | Demand::Fails) => true,
            (&Node::Real(_), Demand::Holds | Demand::Fails)
            | (&Node::Open(_), Demand::Encloses { .. })
            | (&Node::Domain(_), _) => false,
        };
        if !sorted {
            return Err(PlanError::WrongSort);
        }
        return Ok(Self { node, demand });
    }

    /// The node.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn node(&self) -> NodeId
    {
        return self.node;
    }

    /// The evidence asked for.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn demand(&self) -> Demand
    {
        return self.demand;
    }

    /// Whether `conclusion` is the evidence that the obligation asks for: its
    /// node holds or fails as asked, or an enclosure of its node is no wider
    /// than `2^width`.
    ///
    /// # Specification
    /// - ensures: [`Answer::Answers`] exactly for a conclusion about the
    ///   obligation's node of the kind that its demand asks, and, for an
    ///   enclosure, both ends finite and the exact width at most `2^width`.
    /// - panics: none.
    /// - executable: none — the clause restates the test.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a certificate of each demand, one of another node,
    ///   and one that a narrower quota refuses, through the cache that reads
    ///   each before it stores or gives a certificate.
    /// - witness: `tests::cache::an_entry_that_does_not_replay_leaves_by_name`
    /// - witness: `tests::cache::the_corpus_answers_alike_cached_and_uncached`
    #[inline]
    #[must_use]
    pub fn answered_by(
        &self,
        conclusion: &Conclusion,
    ) -> Answer
    {
        let answers = match (conclusion, self.demand) {
            (&Conclusion::Holds { open }, Demand::Holds)
            | (&Conclusion::Fails { open }, Demand::Fails) => open == self.node,
            (&Conclusion::Encloses { real, ref interval }, Demand::Encloses { width }) => {
                real == self.node
                    && gap(interval)
                        .zip(Dyadic::new(BigInt::from(1_u8), width).ok())
                        .is_some_and(|(gap, target)| gap <= target)
            },
            (
                &(Conclusion::Holds { .. }
                | Conclusion::Fails { .. }
                | Conclusion::Encloses { .. }),
                _,
            ) => false,
        };
        return if answers {
            Answer::Answers
        }
        else {
            Answer::Misses
        };
    }
}

/// Whether a conclusion is the evidence that an obligation asks for.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Answer
{
    /// The conclusion is the evidence asked for.
    Answers,
    /// The conclusion is about another node, of another kind, or wider than
    /// the width asked.
    Misses,
}

/// The exact width of `interval`, or `None` for an infinite end.
///
/// # Specification
/// trivial.
pub(crate) fn gap(interval: &NumericInterval) -> Option<Dyadic>
{
    let (&Endpoint::Finite(ref lower), &Endpoint::Finite(ref upper)) =
        (&interval.lower().endpoint, &interval.upper().endpoint)
    else {
        return None;
    };
    return upper
        .sub(lower, Precision::MAX, Rounding::Ceiling)
        .ok()
        .map(Rounded::into_value);
}

/// Why the machine cannot go on with an obligation.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum SuspendReason
{
    /// The certificate format has no rule for the node's form yet.
    NoRule,
    /// The next step would put the certificate past the checker's quotas.
    Quota,
    /// A step of the certificate would conclude the other pole, so no step
    /// concludes the asked pole. An obligation that asks for the other pole
    /// gets that certificate.
    Opposed,
}

/// The outcome of an obligation at the end of a run.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Outcome<'run>
{
    /// The certificate of the evidence asked for. The checker replays it to
    /// that evidence.
    Certified(&'run Certificate),
    /// The obligation is live, and the run stopped at its limit of rounds. A
    /// later run goes on with it.
    Pending,
    /// The machine cannot go on with the obligation, for the stated reason.
    Suspended(SuspendReason),
    /// The obligation is live, and the run spent its budget.
    Exhausted,
    /// The obligation is live, and the run stopped at a cancellation.
    Cancelled,
}

/// What a unit of work did.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
enum Unit
{
    /// The unit added one step, and the obligation is live.
    Stepped,
    /// The unit added one step, and the obligation settled.
    Concluded,
    /// The obligation settled with no step.
    Stopped,
}

/// The enclosure of one real operand inside a certificate under construction.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
enum Chain
{
    /// A constant, its point stated by one step.
    Constant
    {
        /// The step that states the point.
        step: StepId,
        /// The point.
        value: Dyadic,
    },
    /// A registered cut, refined by halvings.
    Cut
    {
        /// The step that concludes the current enclosure.
        step: StepId,
        /// The current enclosure.
        refinement: Refinement,
    },
}

impl Chain
{
    /// The step that concludes the current enclosure.
    ///
    /// # Specification
    /// trivial.
    const fn step(&self) -> StepId
    {
        return match *self {
            Self::Constant { step, .. } | Self::Cut { step, .. } => step,
        };
    }

    /// The lower end of the current enclosure.
    ///
    /// # Specification
    /// trivial.
    const fn lower(&self) -> &Dyadic
    {
        return match *self {
            Self::Constant { ref value, .. } => value,
            Self::Cut { ref refinement, .. } => refinement.lower(),
        };
    }

    /// The upper end of the current enclosure.
    ///
    /// # Specification
    /// trivial.
    const fn upper(&self) -> &Dyadic
    {
        return match *self {
            Self::Constant { ref value, .. } => value,
            Self::Cut { ref refinement, .. } => refinement.upper(),
        };
    }
}

/// Whether a real has a chain.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
struct Chainable(bool);

/// Whether the real at `node` has a chain: a constant, or a registered cut.
///
/// # Specification
/// trivial.
fn chainable(
    plan: &Plan,
    node: NodeId,
) -> Chainable
{
    return Chainable(match plan.node(node) {
        Ok(&Node::Real(Real::Constant(_))) => true,
        Ok(&Node::Real(Real::Cut(_))) => radicand(plan, node).is_ok(),
        Ok(_) | Err(_) => false,
    });
}

/// Whether a chain serves `obligation`: an enclosure of a chainable real, a
/// comparison of two chainable reals, or a cut at a chainable point. The
/// machine rebuilds such work from its steps, and runs any other work again.
///
/// # Specification
/// trivial.
fn chained(
    plan: &Plan,
    obligation: Obligation,
) -> Chainable
{
    let node = obligation.node;
    return Chainable(match (plan.node(node), obligation.demand) {
        (Ok(&Node::Real(Real::Constant(_) | Real::Cut(_))), Demand::Encloses { .. }) => {
            chainable(plan, node).0
        },
        (Ok(&Node::Open(Open::Less(first, second))), Demand::Holds | Demand::Fails) => {
            chainable(plan, first.node()).0 && chainable(plan, second.node()).0
        },
        (
            Ok(&Node::Open(Open::LowerCut(cut, point) | Open::UpperCut(cut, point))),
            Demand::Holds | Demand::Fails,
        ) => radicand(plan, cut.node()).is_ok() && chainable(plan, point.node()).0,
        (Ok(_) | Err(_), _) => false,
    });
}

/// Where the work on an obligation is.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
enum State
{
    /// No step yet.
    Fresh,
    /// The enclosure of a real node.
    Enclosing(Chain),
    /// The comparison of two real operands.
    Comparing
    {
        /// The comparison.
        less: NodeId,
        /// The first operand, once its first step is written.
        left: Option<Chain>,
        /// The second operand, once its first step is written. Both
        /// operands share the first chain when they are one node.
        right: Option<Chain>,
    },
    /// The membership of a real operand in the lower or the upper cut of a
    /// registered cut.
    Cutting
    {
        /// The lower or the upper cut.
        open: NodeId,
        /// The operand, once its first step is written.
        point: Option<Chain>,
    },
    /// The search of a bounded quantifier's domain.
    Searching(Search),
    /// The compound chain of a real made of builtins, or of a comparison of
    /// two such reals.
    Composing(Compound),
    /// The certificate of the evidence asked for.
    Certified(Certificate),
    /// The reason the machine stopped.
    Suspended(SuspendReason),
}

/// The work on one obligation: the steps of its certificate so far and where
/// the work is.
///
/// # Specification
/// - invariant: the steps form a prefix of a certificate that
///   [`crate::certificate::check`] replays, and each chain names the step that
///   concludes its current enclosure.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub(crate) struct Progress
{
    /// The obligation.
    obligation: Obligation,
    /// The steps written so far.
    steps: Vec<Step>,
    /// Where the work is.
    state: State,
    /// The most pieces that a search of the work holds at once, or zero for
    /// work that searches no domain.
    regions: PieceCount,
    /// The point at which the work splits an enclosure or a piece.
    split: Split,
}

impl Progress
{
    /// The work on `obligation`, with no step yet, that splits as `split`
    /// takes.
    ///
    /// # Specification
    /// trivial.
    pub(crate) const fn new(
        obligation: Obligation,
        split: Split,
    ) -> Self
    {
        return Self {
            obligation,
            steps: Vec::new(),
            state: State::Fresh,
            regions: PieceCount::ZERO,
            split,
        };
    }

    /// The work on `obligation` that `steps` record, as a checkpoint holds it,
    /// that splits as `split` takes.
    ///
    /// # Specification
    /// - ensures: the steps replay as a prefix of a certificate, as
    ///   [`crate::certificate::check`] replays them, within `quotas`, and each
    ///   chain of the work names the step that concludes its current enclosure.
    ///   The work goes on as the work that wrote the steps goes on.
    /// - fails: refuses steps that do not replay with the checker's refusal,
    ///   and steps that the machine does not write for a live obligation as
    ///   [`ResumeError::Steps`]: a chain of another node, a split of an
    ///   enclosure that a later step narrows, or a step that concludes.
    /// - panics: none.
    /// - executable: none — the clause speaks of the work that wrote the steps.
    /// - intension: one replay of the steps, then one walk of them for a chain,
    ///   or one run of the machine to the same steps for any other work.
    ///
    /// # Errors
    /// - [`ResumeError::Replay`]: the steps do not replay.
    /// - [`ResumeError::Steps`]: the machine does not write these steps.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — every checkpoint of a run at every turn resumes to
    ///   the certificates of the run that never stops. L3 — each refusal on its
    ///   smallest trigger.
    /// - witness: `tests::checkpoint::a_resumed_run_certifies_as_an_unbroken_one`
    /// - witness: `tests::checkpoint::a_corrupt_checkpoint_is_refused_by_name`
    pub(crate) fn resume(
        plan: &ValidatedPlan,
        obligation: Obligation,
        steps: Vec<Step>,
        (quotas, split): (&CheckerQuotas, Split),
    ) -> Result<Self, ResumeError>
    {
        if steps.is_empty() {
            return Ok(Self::new(obligation, split));
        }
        replay_prefix(plan, &steps, quotas).map_err(ResumeError::Replay)?;
        if !chained(plan.plan(), obligation).0 {
            return Self::rerun(plan, Self::new(obligation, split), &steps, quotas);
        }
        let state = rebuilt(plan.plan(), obligation, &steps)?;
        return Ok(Self {
            obligation,
            steps,
            state,
            regions: PieceCount::ZERO,
            split,
        });
    }

    /// The work of `fresh`, on an obligation that no chain serves, as `steps`
    /// record it, rebuilt by running the machine again until it writes as
    /// many steps.
    ///
    /// # Specification
    /// - ensures: the work writes `steps` and is live, so it goes on as the
    ///   work that wrote them goes on. The machine is deterministic, so a run
    ///   writes the same steps from the same plan.
    /// - fails: refuses steps that the machine does not write, or that it
    ///   writes only after it settles, as [`ResumeError::Steps`].
    /// - panics: none.
    /// - executable: none — the clause speaks of the run that wrote the steps.
    /// - intension: one run of the machine over as many units as `steps`, and
    ///   one comparison of the steps.
    ///
    /// # Errors
    /// - [`ResumeError::Steps`]: the machine does not write these steps.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — a checkpoint of a generated quantified formula, and
    ///   of a comparison of builtins, at every turn resumes to the run that
    ///   never stops. L3 — steps that the machine does not write.
    /// - witness: `tests::quantifier::a_search_resumes_from_its_checkpoint`
    /// - witness: `tests::elementary::the_machine_certifies_the_builtins`
    fn rerun(
        plan: &ValidatedPlan,
        fresh: Self,
        steps: &[Step],
        quotas: &CheckerQuotas,
    ) -> Result<Self, ResumeError>
    {
        let mut progress = fresh;
        while progress.steps.len() < steps.len() && progress.settled().is_none() {
            progress.unit(plan.plan(), quotas);
        }
        if progress.settled().is_some() || progress.steps != steps {
            return Err(ResumeError::Steps);
        }
        return Ok(progress);
    }

    /// The obligation.
    ///
    /// # Specification
    /// trivial.
    pub(crate) const fn obligation(&self) -> Obligation
    {
        return self.obligation;
    }

    /// The steps written so far.
    ///
    /// # Specification
    /// trivial.
    pub(crate) fn steps(&self) -> &[Step]
    {
        return &self.steps;
    }

    /// The most pieces that a search of the work holds at once, or zero for
    /// work that searches no domain.
    ///
    /// # Specification
    /// trivial.
    pub(crate) const fn regions(&self) -> PieceCount
    {
        return self.regions;
    }

    /// The outcome of a settled obligation, or `None` while it is live.
    ///
    /// # Specification
    /// trivial.
    pub(crate) fn settled(&self) -> Option<Outcome<'_>>
    {
        return match self.state {
            State::Certified(ref certificate) => Some(Outcome::Certified(certificate)),
            State::Suspended(reason) => Some(Outcome::Suspended(reason)),
            State::Fresh
            | State::Enclosing(_)
            | State::Comparing { .. }
            | State::Cutting { .. }
            | State::Searching(_)
            | State::Composing(_) => None,
        };
    }

    /// The obligation, while the work has written no step.
    ///
    /// # Specification
    /// trivial.
    pub(crate) fn fresh(&self) -> Option<Obligation>
    {
        return match self.state {
            State::Fresh if self.steps.is_empty() => Some(self.obligation),
            State::Fresh
            | State::Enclosing(_)
            | State::Comparing { .. }
            | State::Cutting { .. }
            | State::Searching(_)
            | State::Composing(_)
            | State::Certified(_)
            | State::Suspended(_) => None,
        };
    }

    /// Settle the work with `certificate`, a certificate from a cache that
    /// replays to the evidence that the obligation asks for.
    ///
    /// # Specification
    /// - requires: the work has written no step.
    /// - ensures: the work is settled with `certificate`, and it spent no step.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — every obligation of the corpus that the cache answers
    ///   settles with the certificate of an uncached run.
    /// - witness: `tests::cache::the_corpus_answers_alike_cached_and_uncached`
    #[spec(requires: self.fresh().is_some(), ensures: self.steps.is_empty())]
    pub(crate) fn adopt(
        &mut self,
        certificate: Certificate,
    )
    {
        self.state = State::Certified(certificate);
    }

    /// Do at most `allowance` steps of work, and the number done.
    ///
    /// # Specification
    /// - ensures: each step of work adds one certificate step. The work stops
    ///   once the obligation settles: with a certificate whose replay concludes
    ///   the evidence asked for, or with the reason the machine cannot go on.
    /// - panics: none.
    /// - intension: at most `allowance` certificate steps, each at most two
    ///   exact squares within the checker's width quota, or the series of one
    ///   builtin.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — generated obligations on generated plans, each
    ///   certificate replayed to its evidence. L3 — each outcome of each form.
    /// - witness: `tests::dovetail::every_certificate_replays_to_its_evidence`
    /// - witness: `tests::dovetail::each_form_settles_or_suspends_by_name`
    #[spec(ensures: |ret| ret <= allowance)]
    pub(crate) fn advance(
        &mut self,
        plan: &ValidatedPlan,
        allowance: Steps,
        quotas: &CheckerQuotas,
    ) -> Steps
    {
        let limit = u64::from(allowance);
        let mut done = 0_u64;
        while done < limit && self.settled().is_none() {
            match self.unit(plan.plan(), quotas) {
                Unit::Stepped | Unit::Concluded => done = done.saturating_add(1),
                Unit::Stopped => {},
            }
        }
        return Steps::from(done);
    }

    /// One unit of work: one certificate step, or a settlement with no step.
    ///
    /// # Specification
    /// - requires: the obligation is live.
    /// - ensures: as [`Self::advance`] states for one step.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — as [`Self::advance`], which does each step here.
    /// - witness: `tests::dovetail::every_certificate_replays_to_its_evidence`
    /// - witness: `tests::dovetail::each_form_settles_or_suspends_by_name`
    #[spec(requires: self.settled().is_none())]
    fn unit(
        &mut self,
        plan: &Plan,
        quotas: &CheckerQuotas,
    ) -> Unit
    {
        let state = core::mem::replace(&mut self.state, State::Fresh);
        let (state, unit) = match state {
            State::Fresh => self.begin(plan, quotas),
            State::Enclosing(chain) => self.enclose(chain, quotas),
            State::Comparing { less, left, right } => {
                self.compare(plan, less, (left, right), quotas)
            },
            State::Cutting { open, point } => self.cutting(plan, open, point, quotas),
            State::Searching(search) => self.search(plan, search, quotas),
            State::Composing(compound) => self.compose(plan, compound, quotas),
            settled @ (State::Certified(_) | State::Suspended(_)) => (settled, Unit::Stopped),
        };
        if let State::Searching(ref search) = state {
            self.regions = self.regions.max(search.held());
        }
        self.state = state;
        return unit;
    }

    /// The first unit of work: the form of the node decides the work.
    ///
    /// # Specification
    /// trivial.
    fn begin(
        &mut self,
        plan: &Plan,
        quotas: &CheckerQuotas,
    ) -> (State, Unit)
    {
        let node = self.obligation.node;
        let suspended = (State::Suspended(SuspendReason::NoRule), Unit::Stopped);
        return match (plan.node(node), self.obligation.demand) {
            (Ok(&Node::Real(Real::Constant(_) | Real::Cut(_))), Demand::Encloses { .. })
                if chainable(plan, node).0 =>
            {
                match self.chain(plan, node, quotas) {
                    Ok(chain) => self.target(chain),
                    Err(reason) => (State::Suspended(reason), Unit::Stopped),
                }
            },
            (Ok(&Node::Open(Open::Less(first, second))), Demand::Holds | Demand::Fails)
                if chainable(plan, first.node()).0 && chainable(plan, second.node()).0 =>
            {
                self.compare(plan, node, (None, None), quotas)
            },
            (
                Ok(&Node::Open(Open::LowerCut(cut, point) | Open::UpperCut(cut, point))),
                Demand::Holds | Demand::Fails,
            ) if radicand(plan, cut.node()).is_ok() && chainable(plan, point.node()).0 => {
                self.cutting(plan, node, None, quotas)
            },
            (Ok(&Node::Open(Open::Exists(_) | Open::Forall(_))), Demand::Holds | Demand::Fails) => {
                match Search::new(plan, node, self.obligation.demand) {
                    Ok(search) => self.search(plan, search, quotas),
                    Err(reason) => (State::Suspended(reason), Unit::Stopped),
                }
            },
            (Ok(&Node::Real(_) | &Node::Open(Open::Less(..))), _) => {
                match Compound::new(plan, node, self.obligation.demand) {
                    Ok(compound) => self.compose(plan, compound, quotas),
                    Err(reason) => (State::Suspended(reason), Unit::Stopped),
                }
            },
            (Ok(_) | Err(_), _) => suspended,
        };
    }

    /// Write the first step of the chain of the real at `node`.
    ///
    /// # Specification
    /// - requires: the real is chainable.
    /// - ensures: one step is added.
    /// - fails: suspends with [`SuspendReason::Quota`] when the step does not
    ///   fit the quotas, and with [`SuspendReason::NoRule`] when the cut's hull
    ///   is not a pair of witnesses.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the first step of a constant, of a cut, and of each
    ///   suspension.
    /// - witness: `tests::dovetail::each_form_settles_or_suspends_by_name`
    /// - witness: `tests::dovetail::every_certificate_replays_to_its_evidence`
    #[spec(requires: chainable(plan, node).0)]
    fn chain(
        &mut self,
        plan: &Plan,
        node: NodeId,
        quotas: &CheckerQuotas,
    ) -> Result<Chain, SuspendReason>
    {
        let step = self.next(quotas)?;
        let chain = match plan.node(node) {
            Ok(&Node::Real(Real::Constant(ref value))) => {
                if value.width() > quotas.width {
                    return Err(SuspendReason::Quota);
                }
                self.steps.push(Step::Constant { real: node });
                Chain::Constant {
                    step,
                    value: value.clone(),
                }
            },
            Ok(&Node::Real(Real::Cut(_))) => {
                let (refinement, first) = Refinement::start(plan, node).map_err(suspension)?;
                self.steps.push(first);
                Chain::Cut { step, refinement }
            },
            Ok(_) | Err(_) => return Err(SuspendReason::NoRule),
        };
        return Ok(chain);
    }

    /// The identifier of the next step, when one more step fits the quotas.
    ///
    /// # Specification
    /// trivial.
    fn next(
        &self,
        quotas: &CheckerQuotas,
    ) -> Result<StepId, SuspendReason>
    {
        if self.steps.len() >= usize::from(quotas.steps) {
            return Err(SuspendReason::Quota);
        }
        return StepId::try_from(self.steps.len()).map_err(|_wide| SuspendReason::Quota);
    }

    /// Settle an enclosure that meets its target, or keep refining it.
    ///
    /// # Specification
    /// trivial.
    fn target(
        &mut self,
        chain: Chain,
    ) -> (State, Unit)
    {
        let Demand::Encloses { width } = self.obligation.demand
        else {
            return (State::Suspended(SuspendReason::NoRule), Unit::Stopped);
        };
        let met = match chain {
            Chain::Constant { .. } => Ok(true),
            Chain::Cut { ref refinement, .. } => Dyadic::new(BigInt::from(1_u8), width)
                .map_err(|_overflow| CertificateCheck::WidthQuota)
                .and_then(|target| refinement.gap().map(|gap| gap <= target)),
        };
        return match met {
            Ok(true) => (self.certified(), Unit::Concluded),
            Ok(false) => (State::Enclosing(chain), Unit::Stepped),
            Err(check) => (State::Suspended(suspension(check)), Unit::Stepped),
        };
    }

    /// One halving of an enclosure.
    ///
    /// # Specification
    /// trivial.
    fn enclose(
        &mut self,
        chain: Chain,
        quotas: &CheckerQuotas,
    ) -> (State, Unit)
    {
        return match self.halve(chain, quotas) {
            Ok(chain) => self.target(chain),
            Err(reason) => (State::Suspended(reason), Unit::Stopped),
        };
    }

    /// Halve the enclosure of a cut chain, adding one step.
    ///
    /// # Specification
    /// - ensures: one step is added, and the chain names it.
    /// - fails: suspends when the step does not fit the quotas, and with
    ///   [`SuspendReason::NoRule`] for a constant, which no halving narrows.
    /// - panics: none.
    /// - executable: none — the clause compares the steps before and after the
    ///   call.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — each halving of generated obligations, its
    ///   certificate replayed.
    /// - witness: `tests::dovetail::every_certificate_replays_to_its_evidence`
    fn halve(
        &mut self,
        chain: Chain,
        quotas: &CheckerQuotas,
    ) -> Result<Chain, SuspendReason>
    {
        let Chain::Cut {
            step: premise,
            mut refinement,
        } = chain
        else {
            return Err(SuspendReason::NoRule);
        };
        let step = self.next(quotas)?;
        let split = refinement
            .halve(premise, quotas, self.split)
            .map_err(suspension)?;
        self.steps.push(split);
        return Ok(Chain::Cut { step, refinement });
    }

    /// One unit of work on the comparison `less`: write a missing first step
    /// of an operand, conclude, or halve the wider operand.
    ///
    /// # Specification
    /// - ensures: concludes the asked pole as soon as the enclosures separate
    ///   on its side, and suspends with [`SuspendReason::Opposed`] as soon as
    ///   they separate on the other side.
    /// - panics: none.
    /// - executable: none — the clause speaks of the order in which the
    ///   enclosures separate.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — each pole on a comparison that holds, that fails and
    ///   that never separates.
    /// - witness: `tests::dovetail::each_form_settles_or_suspends_by_name`
    /// - witness: `tests::dovetail::every_certificate_replays_to_its_evidence`
    fn compare(
        &mut self,
        plan: &Plan,
        less: NodeId,
        operands: (Option<Chain>, Option<Chain>),
        quotas: &CheckerQuotas,
    ) -> (State, Unit)
    {
        let Ok(&Node::Open(Open::Less(first, second))) = plan.node(less)
        else {
            return (State::Suspended(SuspendReason::NoRule), Unit::Stopped);
        };
        let shared = first == second;
        let comparing = |left, right| State::Comparing { less, left, right };
        let (left, right) = match operands {
            (None, right) => {
                return match self.chain(plan, first.node(), quotas) {
                    Ok(left) => (comparing(Some(left), right), Unit::Stepped),
                    Err(reason) => (State::Suspended(reason), Unit::Stopped),
                };
            },
            (Some(left), None) if !shared => {
                return match self.chain(plan, second.node(), quotas) {
                    Ok(right) => (comparing(Some(left), Some(right)), Unit::Stepped),
                    Err(reason) => (State::Suspended(reason), Unit::Stopped),
                };
            },
            (Some(left), right) => (left, right),
        };
        let other = right.as_ref().unwrap_or(&left);
        // The ends of a cut's enclosure are witnesses outside the cut's value,
        // so a cut's enclosure that shares an end with the other separates.
        let below = match left.upper().cmp(other.lower()) {
            core::cmp::Ordering::Less => true,
            core::cmp::Ordering::Equal => {
                matches!(left, Chain::Cut { .. }) || matches!(*other, Chain::Cut { .. })
            },
            core::cmp::Ordering::Greater => false,
        };
        let not_below = left.lower() >= other.upper();
        let holds = self.obligation.demand == Demand::Holds;
        if (holds && not_below && !below) || (!holds && below) {
            return (State::Suspended(SuspendReason::Opposed), Unit::Stopped);
        }
        if (holds && below) || (!holds && not_below) {
            let (left_step, right_step) = (left.step(), other.step());
            if let Err(reason) = self.next(quotas) {
                return (State::Suspended(reason), Unit::Stopped);
            }
            self.steps.push(if holds {
                Step::Below {
                    less,
                    left: left_step,
                    right: right_step,
                }
            }
            else {
                Step::NotBelow {
                    less,
                    left: left_step,
                    right: right_step,
                }
            });
            return (self.certified(), Unit::Concluded);
        }
        // Neither pole separates yet: halve the wider operand, and keep room
        // for the step that concludes.
        if self.steps.len().saturating_add(2) > usize::from(quotas.steps) {
            return (State::Suspended(SuspendReason::Quota), Unit::Stopped);
        }
        let width = |chain: &Chain| match *chain {
            Chain::Constant { .. } => Ok(None),
            Chain::Cut { ref refinement, .. } => refinement.gap().map(Some),
        };
        let (left_width, right_width) = match (width(&left), right.as_ref().map(width)) {
            (Ok(left_width), Some(Ok(right_width))) => (left_width, right_width),
            (Ok(left_width), None) => (left_width, None),
            (Err(check), _) | (_, Some(Err(check))) => {
                return (State::Suspended(suspension(check)), Unit::Stopped);
            },
        };
        let halved = if right_width > left_width {
            right
                .map(|right| self.halve(right, quotas))
                .transpose()
                .map(|right| (Some(left), right))
        }
        else {
            self.halve(left, quotas).map(|left| (Some(left), right))
        };
        return match halved {
            Ok((left, right)) => (comparing(left, right), Unit::Stepped),
            Err(reason) => (State::Suspended(reason), Unit::Stopped),
        };
    }

    /// One unit of work on the lower or the upper cut `open`: write the first
    /// step of its operand, conclude, or halve the operand.
    ///
    /// # Specification
    /// - ensures: concludes the asked pole as soon as the end of the operand's
    ///   enclosure toward the cut's value lies on the cut's side, or the end
    ///   away from it lies off that side. Suspends with
    ///   [`SuspendReason::Opposed`] as soon as the other pole concludes.
    /// - panics: none.
    /// - executable: none — the clause speaks of the order in which the
    ///   enclosure leaves the cut's value.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — each pole on a cut that holds, that fails and that
    ///   never separates.
    /// - witness: `tests::elimination::the_machine_settles_each_cut_by_its_operand_alone`
    fn cutting(
        &mut self,
        plan: &Plan,
        open: NodeId,
        point: Option<Chain>,
        quotas: &CheckerQuotas,
    ) -> (State, Unit)
    {
        let (cut, operand, side) = match plan.node(open) {
            Ok(&Node::Open(Open::LowerCut(cut, operand))) => (cut, operand, Side::Lower),
            Ok(&Node::Open(Open::UpperCut(cut, operand))) => (cut, operand, Side::Upper),
            Ok(_) | Err(_) => return (State::Suspended(SuspendReason::NoRule), Unit::Stopped),
        };
        let Some(chain) = point
        else {
            return match self.chain(plan, operand.node(), quotas) {
                Ok(chain) => (
                    State::Cutting {
                        open,
                        point: Some(chain),
                    },
                    Unit::Stepped,
                ),
                Err(reason) => (State::Suspended(reason), Unit::Stopped),
            };
        };
        let radicand = match radicand(plan, cut.node()) {
            Ok(radicand) => radicand,
            Err(check) => return (State::Suspended(suspension(check)), Unit::Stopped),
        };
        // The step that concludes reads the end of the enclosure toward the
        // cut's value to hold, and the end away from it to fail.
        let (toward, away, wanted) = match side {
            Side::Lower => (chain.upper(), chain.lower(), Membership::Lower),
            Side::Upper => (chain.lower(), chain.upper(), Membership::Upper),
        };
        let (inside, outside) = match (membership(toward, &radicand), membership(away, &radicand)) {
            (Ok(toward), Ok(away)) => (toward == wanted, away != wanted),
            (Err(check), _) | (_, Err(check)) => {
                return (State::Suspended(suspension(check)), Unit::Stopped);
            },
        };
        let holds = self.obligation.demand == Demand::Holds;
        if (holds && outside) || (!holds && inside) {
            return (State::Suspended(SuspendReason::Opposed), Unit::Stopped);
        }
        if (holds && inside) || (!holds && outside) {
            if let Err(reason) = self.next(quotas) {
                return (State::Suspended(reason), Unit::Stopped);
            }
            let point = chain.step();
            self.steps.push(if holds {
                Step::Inside { open, point, side }
            }
            else {
                Step::Outside { open, point, side }
            });
            return (self.certified(), Unit::Concluded);
        }
        // Neither pole concludes yet: halve the operand, and keep room for the
        // step that concludes.
        if self.steps.len().saturating_add(2) > usize::from(quotas.steps) {
            return (State::Suspended(SuspendReason::Quota), Unit::Stopped);
        }
        return match self.halve(chain, quotas) {
            Ok(chain) => (
                State::Cutting {
                    open,
                    point: Some(chain),
                },
                Unit::Stepped,
            ),
            Err(reason) => (State::Suspended(reason), Unit::Stopped),
        };
    }

    /// One unit of work on a quantifier: one step of its search.
    ///
    /// # Specification
    /// trivial.
    fn search(
        &mut self,
        plan: &Plan,
        mut search: Search,
        quotas: &CheckerQuotas,
    ) -> (State, Unit)
    {
        return match search.unit(plan, &mut self.steps, quotas, self.split) {
            Ok(Turn::Stepped) => (State::Searching(search), Unit::Stepped),
            Ok(Turn::Concluded) => (self.certified(), Unit::Concluded),
            Err(reason) => (State::Suspended(reason), Unit::Stopped),
        };
    }

    /// One unit of work on a compound chain: one step of its attempt.
    ///
    /// # Specification
    /// trivial.
    fn compose(
        &mut self,
        plan: &Plan,
        mut compound: Compound,
        quotas: &CheckerQuotas,
    ) -> (State, Unit)
    {
        return match compound.unit(plan, &mut self.steps, quotas) {
            Ok(Turn::Stepped) => (State::Composing(compound), Unit::Stepped),
            Ok(Turn::Concluded) => (self.certified(), Unit::Concluded),
            Err(reason) => (State::Suspended(reason), Unit::Stopped),
        };
    }

    /// The certificate of the steps written so far.
    ///
    /// # Specification
    /// trivial.
    fn certified(&mut self) -> State
    {
        // The settled obligation keeps its steps in the certificate alone.
        let steps = core::mem::take(&mut self.steps);
        return State::Certified(Certificate::new(FormatVersion::CURRENT, steps));
    }
}

/// The reason a refusal of the producer suspends an obligation: a quota for
/// a step past the checker's bounds, and no rule for any other refusal.
///
/// # Specification
/// trivial.
pub(crate) const fn suspension(check: CertificateCheck) -> SuspendReason
{
    return match check {
        CertificateCheck::StepQuota
        | CertificateCheck::WidthQuota
        | CertificateCheck::TermQuota => SuspendReason::Quota,
        CertificateCheck::Format
        | CertificateCheck::Empty
        | CertificateCheck::ForwardPremise
        | CertificateCheck::PremiseConclusion
        | CertificateCheck::UnknownNode
        | CertificateCheck::WrongNode
        | CertificateCheck::ForgedCut
        | CertificateCheck::NotLower
        | CertificateCheck::NotUpper
        | CertificateCheck::InsideCut
        | CertificateCheck::OutsideEnclosure
        | CertificateCheck::NotSeparated
        | CertificateCheck::Reversed
        | CertificateCheck::Hypothesis
        | CertificateCheck::Hypothetical
        | CertificateCheck::OutsideDomain
        | CertificateCheck::Gap
        | CertificateCheck::Modality
        | CertificateCheck::Tail
        | CertificateCheck::ZeroDivisor => SuspendReason::NoRule,
    };
}

/// The state of the work on `obligation` that the replayed `steps` record.
///
/// # Specification
/// - requires: [`crate::certificate::check`] accepts `steps`, which are not
///   empty.
/// - ensures: each chain names the last step that narrows it, and the chains
///   stand in the order that the machine writes them: the first operand's
///   chain, then the second's.
/// - fails: refuses steps that the machine does not write for a live obligation
///   as [`ResumeError::Steps`].
/// - panics: none.
/// - executable: none — the clause speaks of the order in which the machine
///   writes its steps.
/// - intension: one walk of the steps, and one scan of at most two chains a
///   step.
///
/// # Errors
/// - [`ResumeError::Steps`]: the machine does not write these steps.
///
/// # Adequacy
/// - hypothesis: L2 — every checkpoint of generated runs at every turn resumes
///   to the unbroken run. L3 — each step that the machine does not write.
/// - witness: `tests::checkpoint::every_checkpoint_resumes_to_the_unbroken_run`
/// - witness: `tests::checkpoint::a_corrupt_checkpoint_is_refused_by_name`
fn rebuilt(
    plan: &Plan,
    obligation: Obligation,
    steps: &[Step],
) -> Result<State, ResumeError>
{
    // At most two chains: an enclosure has one, and a comparison one for each
    // operand.
    let mut chains: Vec<(NodeId, Chain)> = Vec::with_capacity(2);
    for (index, step) in steps.iter().enumerate() {
        let id = StepId::try_from(index).map_err(|_wide| ResumeError::Steps)?;
        match *step {
            Step::Witnesses {
                cut,
                ref lower,
                ref upper,
            } => {
                let refinement = Refinement::witnessed(plan, cut, (lower.clone(), upper.clone()))
                    .map_err(|_unregistered| ResumeError::Steps)?;
                chains.push((cut, Chain::Cut {
                    step: id,
                    refinement,
                }));
            },
            Step::Constant { real } => {
                let Ok(&Node::Real(Real::Constant(ref value))) = plan.node(real)
                else {
                    return Err(ResumeError::Steps);
                };
                chains.push((real, Chain::Constant {
                    step: id,
                    value: value.clone(),
                }));
            },
            Step::Split {
                premise,
                ref point,
                side,
            } => {
                let Some(&mut (
                    _,
                    Chain::Cut {
                        ref mut step,
                        ref mut refinement,
                    },
                )) = chains.iter_mut().find(|chain| chain.1.step() == premise)
                else {
                    return Err(ResumeError::Steps);
                };
                refinement.split(point.clone(), side);
                *step = id;
            },
            Step::Below { .. }
            | Step::NotBelow { .. }
            | Step::Inside { .. }
            | Step::Outside { .. }
            | Step::Variable { .. }
            | Step::Sum { .. }
            | Step::Difference { .. }
            | Step::Product { .. }
            | Step::Witness { .. }
            | Step::Cover { .. }
            | Step::Counterexample { .. }
            | Step::Refutation { .. }
            | Step::Pi { .. }
            | Step::Cosine { .. }
            | Step::Sine { .. }
            | Step::Angle { .. }
            | Step::Recurrence { .. }
            | Step::Quotient { .. }
            | Step::Power { .. } => return Err(ResumeError::Steps),
        }
    }
    let node = obligation.node;
    let mut chains = chains.into_iter();
    let (first, second) = (chains.next(), chains.next());
    if chains.next().is_some() {
        return Err(ResumeError::Steps);
    }
    return match (plan.node(node), obligation.demand, first, second) {
        (Ok(&Node::Real(_)), Demand::Encloses { .. }, Some((real, chain)), None)
            if real == node =>
        {
            Ok(State::Enclosing(chain))
        },
        (
            Ok(&Node::Open(Open::Less(left, right))),
            Demand::Holds | Demand::Fails,
            Some((one, chain)),
            other,
        ) if one == left.node() => {
            let right_chain = match other {
                None => None,
                Some((two, chain)) if two == right.node() && left != right => Some(chain),
                Some(_) => return Err(ResumeError::Steps),
            };
            Ok(State::Comparing {
                less: node,
                left: Some(chain),
                right: right_chain,
            })
        },
        (
            Ok(&Node::Open(Open::LowerCut(_, operand) | Open::UpperCut(_, operand))),
            Demand::Holds | Demand::Fails,
            Some((one, chain)),
            None,
        ) if one == operand.node() => Ok(State::Cutting {
            open: node,
            point: Some(chain),
        }),
        (Ok(_) | Err(_), ..) => Err(ResumeError::Steps),
    };
}
