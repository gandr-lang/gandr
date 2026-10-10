//! Duplication under a policy, observed through erasure.
//!
//! A duplicate is correct when it erases to the tree its input erases to: the
//! policy decides only which parts stay shared, never what the term is. The
//! property runs over generated overlays of both evaluation families —
//! abstractions shared among several occurrences, shares nested in legs and
//! bodies, occurrences of outer shares inside legs, opaque core terms reading
//! the binders around them — under both stances, and compares the two
//! erasures as trees with a walk that reads the core arena alone.
//!
//! The treatments are pinned beside it: the copying stance's output is the
//! expansion, the sharing stance keeps a leg that is no abstraction and
//! distributes an abstraction over its ribs, and a refusal leaves the overlay
//! at its watermark.

/// The tree oracle, shared with the deep suites.
#[cfg(test)]
#[path = "support/trees.rs"]
mod trees;

/// The duplication cases, in a `cfg(test)` module so the crate's lint wall
/// reads them as test code rather than as shipping code.
#[cfg(test)]
mod duplication
{
    use anodized::spec;
    use gandr_core_nbe::Bound;
    use gandr_core_nbe::CompGraft;
    use gandr_core_nbe::CompNode;
    use gandr_core_nbe::DuplicationFault;
    use gandr_core_nbe::DuplicationPolicy;
    use gandr_core_nbe::DuplicationStance;
    use gandr_core_nbe::Overlay;
    use gandr_core_nbe::OverlayCompId;
    use gandr_core_nbe::OverlayId;
    use gandr_core_nbe::OverlayRefusal;
    use gandr_core_nbe::OverlayValueId;
    use gandr_core_nbe::ShareArity;
    use gandr_core_nbe::ShareDistance;
    use gandr_core_nbe::SharePosition;
    use gandr_core_nbe::Sharing;
    use gandr_core_nbe::SharingMeasure;
    use gandr_core_nbe::TracedDuplication;
    use gandr_core_nbe::ValueGraft;
    use gandr_core_nbe::ValueNode;
    use gandr_core_nbe::duplicate_computation;
    use gandr_core_nbe::duplicate_value;
    use gandr_core_nbe::erase_computation;
    use gandr_core_nbe::erase_value;
    use gandr_core_term::ComputationId;
    use gandr_core_term::CoreArena;
    use gandr_core_term::ValueId;
    use gandr_core_term::Zone;
    use gandr_kernel_conversion_trace::TraceLog;
    use gandr_kernel_term::DeBruijnIndex;

    use crate::trees::Term;
    use crate::trees::Trees;
    use crate::trees::same_tree;

    /// How many overlays the property generates.
    const CASES: u32 = 600;

    /// The branching budget; share skeletons and returner wrappers add nodes.
    const BUDGET: u32 = 28;

    /// Which evaluation family a generated node stands in.
    #[derive(Clone, Copy, Debug, Eq, PartialEq)]
    enum Family
    {
        /// A value.
        Value,
        /// A computation.
        Computation,
    }

    /// Whether a generated node is a leaf.
    #[derive(Clone, Copy, Debug, Eq, PartialEq)]
    enum Grows
    {
        /// It is.
        Leaf,
        /// It has children.
        Internal,
    }

    /// The index of a generated node's plan.
    #[repr(transparent)]
    #[derive(Clone, Copy, Debug, Eq, PartialEq)]
    struct Slot(usize);

    /// The index of a scope cell.
    #[repr(transparent)]
    #[derive(Clone, Copy, Debug, Eq, PartialEq)]
    struct Scope(usize);

    /// How many links a doubling chain holds.
    #[repr(transparent)]
    #[derive(Clone, Copy, Debug, Eq, PartialEq)]
    struct Links(u32);

    /// One generated node, its children named by slot.
    #[derive(Clone, Copy, Debug)]
    enum Plan
    {
        /// Not yet generated.
        Pending,
        /// The unit value.
        Unit,
        /// An intuitionistic variable.
        Variable(u32),
        /// An opaque core value.
        OpaqueValue(ValueId),
        /// An opaque core computation.
        OpaqueComputation(ComputationId),
        /// An occurrence of the share `distance` frames out, in `family`.
        Occurrence
        {
            /// The occurrence's family, its leg's.
            family: Family,
            /// The shares between it and its own.
            distance: u32,
        },
        /// A pair.
        Pair(Slot, Slot),
        /// A thunk.
        Thunk(Slot),
        /// A lambda.
        Lambda(Slot),
        /// A returner.
        Return(Slot),
        /// A force.
        Force(Slot),
        /// An application.
        Application(Slot, Slot),
        /// A bind.
        Bind(Slot, Slot),
        /// A share, standing in `family`.
        Share
        {
            /// The share's own family, its body's.
            family: Family,
            /// The leg.
            leg: Slot,
            /// The body.
            body: Slot,
        },
    }

    /// A seeded xorshift generator, so a failing case reproduces from its
    /// index.
    #[repr(transparent)]
    struct Seeded(u64);

    impl Seeded
    {
        /// One seeded modular draw from `options`; repeated entries add weight.
        ///
        /// # Specification
        /// - requires: `options` is not empty.
        /// - ensures: an element of `options`; zero and nonzero seed states
        ///   stay in their respective classes. No uniformity guarantee is made.
        /// - provides: every draw the generator makes.
        /// - panics: when `options` is empty.
        ///
        /// # Adequacy
        /// - hypothesis: L2 — any nonempty slice of Copy choices is admitted;
        ///   equality is not required of its element type. The guard excludes
        ///   the empty draw and the zero-state law records the invertible
        ///   xorshift transition without pinning a seed stream. The generated
        ///   properties exercise the resulting choices through structural
        ///   erasure and expansion, not a fixture-frequency threshold.
        /// - witness: `duplication::duplication::spinal_duplication_is_invisible_to_erasure`
        /// - witness: `duplication::duplication::a_copying_duplicate_is_the_expansion`
        #[spec(
            requires: !options.is_empty(),
            captures: [was_zero = self.0 == 0],
            ensures: (self.0 == 0) == was_zero
        )]
        fn pick<Choice>(
            &mut self,
            options: &[Choice],
        ) -> Choice
        where
            Choice: Copy,
        {
            let mut word = self.0;
            word ^= word.wrapping_shl(13);
            word ^= word.wrapping_shr(7);
            word ^= word.wrapping_shl(17);
            self.0 = word;
            let count = u64::try_from(options.len()).expect("a slice's length fits a u64");
            let drawn = word
                .checked_rem(count)
                .expect("a draw is among a non-empty slice");
            options[usize::try_from(drawn).expect("a draw below a length fits one")]
        }

        /// A count from zero to `ceiling` inclusive.
        ///
        /// # Specification
        /// - requires: nothing.
        /// - ensures: a count no greater than `ceiling`.
        /// - provides: the budget splits.
        /// - panics: none.
        ///
        /// # Adequacy
        /// - hypothesis: L3 — any representable budget is admitted subject to
        ///   allocation resources. The inclusive upper bound distinguishes an
        ///   off-by-one split; generated overlays must validate, preserve
        ///   erasure and copy to exactly their measured expansion.
        /// - witness: `duplication::duplication::spinal_duplication_is_invisible_to_erasure`
        /// - witness: `duplication::duplication::a_copying_duplicate_is_the_expansion`
        #[spec(
            ensures: |ret| ret.0 <= ceiling.0
        )]
        fn up_to(
            &mut self,
            ceiling: Budget,
        ) -> Budget
        {
            let counts: Vec<u32> = (0 ..= ceiling.0).collect();
            Budget(self.pick(&counts))
        }
    }

    /// The remaining branching decisions available to a job.
    #[repr(transparent)]
    #[derive(Clone, Copy, Debug, Eq, PartialEq)]
    struct Budget(u32);

    /// One node still to generate.
    #[derive(Clone, Copy, Debug)]
    struct Job
    {
        /// Its slot.
        slot: Slot,
        /// Its family.
        family: Family,
        /// The remaining branching budget.
        budget: Budget,
        /// The intuitionistic binders around it.
        binders: u32,
        /// The innermost scope cell around it.
        scope: Scope,
    }

    /// The generator's state: the plans, the scope cells — each a share's leg
    /// family and the cell around it, cell zero empty — and the jobs left.
    struct Generator<'core>
    {
        /// The draws.
        seeded: &'core mut Seeded,
        /// The arena the opaque nodes name.
        core: &'core mut CoreArena,
        /// The plans, a parent before its children.
        plans: Vec<Plan>,
        /// The scope cells.
        scopes: Vec<Option<(Family, Scope)>>,
        /// The jobs left.
        jobs: Vec<Job>,
    }

    impl Generator<'_>
    {
        /// A fresh plan slot.
        ///
        /// # Specification
        /// trivial.
        fn slot(&mut self) -> Slot
        {
            let slot = Slot(self.plans.len());
            self.plans.push(Plan::Pending);
            slot
        }

        /// Settle `slot` to `plan`.
        ///
        /// # Specification
        /// trivial.
        fn set(
            &mut self,
            slot: Slot,
            plan: Plan,
        )
        {
            self.plans[slot.0] = plan;
        }

        /// Queue `job`.
        ///
        /// # Specification
        /// trivial.
        fn queue(
            &mut self,
            job: Job,
        )
        {
            self.jobs.push(job);
        }

        /// Run every job.
        ///
        /// # Specification
        /// - requires: each pending slot has exactly one queued job, jobs own
        ///   pending slots, and scope parents point to earlier cells.
        /// - ensures: every slot is settled.
        /// - provides: the generation loop.
        /// - panics: none.
        ///
        /// # Adequacy
        /// - hypothesis: L3 — every pending plan has exactly one queued job and
        ///   scope parents precede their children. Empty jobs and no pending
        ///   plans on return exclude skipped work. Generated validation and
        ///   independent erasure comparisons distinguish wrong families,
        ///   unclosed scopes and reversed child construction.
        /// - witness: `duplication::duplication::spinal_duplication_is_invisible_to_erasure`
        /// - witness: `duplication::duplication::a_copying_duplicate_is_the_expansion`
        #[spec(
            requires: self.jobs.iter().all(|job| matches!(self.plans.get(job.slot.0), Some(Plan::Pending)) && job.scope.0 < self.scopes.len())
                && self.plans.iter().enumerate().all(|(index, plan)| !matches!(plan, Plan::Pending) || self.jobs.iter().filter(|job| job.slot.0 == index).count() == 1)
                && self.scopes.iter().enumerate().all(|(index, scope)| scope.is_none_or(|(_, parent)| parent.0 < index)),
            ensures: self.jobs.is_empty() && self.plans.iter().all(|plan| !matches!(plan, Plan::Pending))
        )]
        fn run(&mut self)
        {
            while let Some(job) = self.jobs.pop() {
                let grows = self.seeded.pick(&[
                    Grows::Leaf,
                    Grows::Internal,
                    Grows::Internal,
                    Grows::Internal,
                    Grows::Internal,
                    Grows::Internal,
                ]);
                if job.budget.0 == 0 || grows == Grows::Leaf {
                    self.leaf(job);
                }
                else {
                    self.internal(job);
                }
            }
        }

        /// The occurrences `scope` admits in `family`, by distance.
        ///
        /// # Specification
        /// - requires: `scope` resolves and scope parents point backward.
        /// - ensures: the distance of every share around `scope` whose leg is
        ///   of `family`.
        /// - provides: the choice of an occurrence.
        /// - panics: none.
        ///
        /// # Adequacy
        /// - hypothesis: L3 — the start scope is in bounds and every parent
        ///   points backward. An ordered iterator over the answer must agree
        ///   with exactly the matching ancestor cells, excluding skipped,
        ///   duplicated, reversed or wrong-family distances. Generated closed
        ///   overlays exercise the occurrence choices in both evaluation
        ///   families.
        /// - witness: `duplication::duplication::spinal_duplication_is_invisible_to_erasure`
        /// - witness: `duplication::duplication::a_copying_duplicate_is_the_expansion`
        #[spec(
            requires: scope.0 < self.scopes.len()
                && self.scopes.iter().enumerate().all(|(index, cell)| cell.is_none_or(|(_, parent)| parent.0 < index)),
            ensures: |ret| {
                let mut found = ret.iter();
                let mut here = scope;
                let mut distance = 0_u32;
                while let Some((leg, parent)) = self.scopes.get(here.0).copied().flatten() {
                    if leg == family && found.next() != Some(&ShareDistance::from(distance)) { return false; }
                    here = parent;
                    distance = distance.saturating_add(1);
                }
                found.next().is_none()
            }
        )]
        fn reachable(
            &self,
            scope: Scope,
            family: Family,
        ) -> Vec<ShareDistance>
        {
            let mut found = Vec::new();
            let mut here = scope;
            let mut distance = 0_u32;
            while let Some((leg, parent)) = self.scopes[here.0] {
                if leg == family {
                    found.push(ShareDistance::from(distance));
                }
                here = parent;
                distance = distance.saturating_add(1);
            }
            found
        }

        /// Settle `job` as a leaf.
        ///
        /// # Specification
        /// - requires: the job owns a pending slot in a valid scope.
        /// - ensures: a well-scoped leaf of its family, or a computation
        ///   returner with one queued zero-budget value child.
        /// - provides: every leaf the property reads.
        /// - panics: none.
        ///
        /// # Adequacy
        /// - hypothesis: L3 — a pending slot and a valid scope describe the
        ///   job. The settled plan must preserve its family, keep variables
        ///   under the binder ceiling and resolve opaque nodes. A deferred
        ///   computation leaf queues exactly one zero-budget value job; an
        ///   occurrence must reach a matching ancestor. These guards exclude a
        ///   pending result, wrong polarity and an unscoped leaf before the
        ///   erasure properties run.
        /// - witness: `duplication::duplication::spinal_duplication_is_invisible_to_erasure`
        /// - witness: `duplication::duplication::a_copying_duplicate_is_the_expansion`
        #[spec(
            requires: matches!(self.plans.get(job.slot.0), Some(Plan::Pending)) && job.scope.0 < self.scopes.len(),
            captures: [before_plans = self.plans.len(), before_jobs = self.jobs.len()],
            ensures: {
                let direct = self.plans.len() == before_plans && self.jobs.len() == before_jobs;
                match self.plans.get(job.slot.0).copied() {
                    Some(Plan::Unit) => direct && job.family == Family::Value,
                    Some(Plan::Variable(index)) => direct && job.family == Family::Value && index < job.binders,
                    Some(Plan::OpaqueValue(id)) => direct && job.family == Family::Value && self.core.value(id).is_some(),
                    Some(Plan::OpaqueComputation(id)) => direct && job.family == Family::Computation && self.core.computation(id).is_some(),
                    Some(Plan::Occurrence { family, distance }) => {
                        let mut scope = job.scope;
                        for _ in 0..distance {
                            let Some((_, parent)) = self.scopes.get(scope.0).copied().flatten() else { return false; };
                            scope = parent;
                        }
                        direct && family == job.family
                            && self.scopes.get(scope.0).copied().flatten().is_some_and(|(leg, _)| leg == family)
                    },
                    Some(Plan::Return(child)) => job.family == Family::Computation && child.0 == before_plans
                        && self.plans.len() == before_plans.saturating_add(1) && self.jobs.len() == before_jobs.saturating_add(1)
                        && matches!(self.plans.get(child.0), Some(Plan::Pending))
                        && self.jobs.last().is_some_and(|queued| queued.slot == child && queued.family == Family::Value
                            && queued.budget.0 == 0 && queued.binders == job.binders && queued.scope == job.scope),
                    _ => false,
                }
            }
        )]
        fn leaf(
            &mut self,
            job: Job,
        )
        {
            let reachable = self.reachable(job.scope, job.family);
            if !reachable.is_empty() && self.seeded.pick(&[true, false]) {
                let distance = self.seeded.pick(&reachable);
                self.set(job.slot, Plan::Occurrence {
                    family: job.family,
                    distance: u32::from(distance),
                });
                return;
            }
            let indices: Vec<u32> = (0 .. job.binders).collect();
            let read = (!indices.is_empty()).then(|| self.seeded.pick(&indices));
            match job.family {
                | Family::Value => {
                    let plan = match (self.seeded.pick(&[0_u8, 1, 2, 3]), read) {
                        | (0, Some(index)) => Plan::Variable(index),
                        | (1, Some(index)) => {
                            let variable = self
                                .core
                                .value_variable(Zone::Intuitionistic, DeBruijnIndex::from(index));
                            let unit = self.core.value_unit();
                            Plan::OpaqueValue(self.core.value_pair(variable, unit))
                        },
                        | (2, _) => Plan::OpaqueValue(self.core.value_unit()),
                        | _ => Plan::Unit,
                    };
                    self.set(job.slot, plan);
                },
                | Family::Computation => {
                    let returned = match read {
                        | Some(index) => self
                            .core
                            .value_variable(Zone::Intuitionistic, DeBruijnIndex::from(index)),
                        | None => self.core.value_unit(),
                    };
                    if self.seeded.pick(&[true, false]) {
                        let opaque = self.core.computation_return(returned);
                        self.set(job.slot, Plan::OpaqueComputation(opaque));
                    }
                    else {
                        let value = self.slot();
                        self.set(job.slot, Plan::Return(value));
                        self.queue(Job {
                            slot: value,
                            family: Family::Value,
                            budget: Budget(0),
                            ..job
                        });
                    }
                },
            }
        }

        /// Settle `job` as an internal node, queueing its children.
        ///
        /// # Specification
        /// - requires: a positive-budget job owns a pending slot in a valid
        ///   scope.
        /// - ensures: the slot holds a former of the job's family over fresh
        ///   slots, each queued with a share of the budget and the binders and
        ///   shares it stands under.
        /// - provides: every internal node the property reads.
        /// - panics: none.
        ///
        /// # Adequacy
        /// - hypothesis: L3 — a positive-budget job owns a pending slot in a
        ///   valid scope. Its settled former has the requested family, fresh
        ///   child slots and at least one lower-budget queued job; share
        ///   construction has its own scope-transition predicate. Independent
        ///   generated erasure and expansion comparisons distinguish wrong
        ///   child order, family, binder shifts and exhausted work left
        ///   pending.
        /// - witness: `duplication::duplication::spinal_duplication_is_invisible_to_erasure`
        /// - witness: `duplication::duplication::a_copying_duplicate_is_the_expansion`
        #[spec(
            requires: job.budget.0 > 0 && matches!(self.plans.get(job.slot.0), Some(Plan::Pending)) && job.scope.0 < self.scopes.len(),
            captures: [before_plans = self.plans.len(), before_jobs = self.jobs.len()],
            ensures: {
                let family = match self.plans.get(job.slot.0).copied() {
                    Some(Plan::Pair(left, right)) => left.0 >= before_plans && right.0 >= before_plans && job.family == Family::Value,
                    Some(Plan::Thunk(child)) => child.0 >= before_plans && job.family == Family::Value,
                    Some(Plan::Lambda(child) | Plan::Return(child) | Plan::Force(child)) => child.0 >= before_plans && job.family == Family::Computation,
                    Some(Plan::Application(left, right) | Plan::Bind(left, right)) => left.0 >= before_plans && right.0 >= before_plans && job.family == Family::Computation,
                    Some(Plan::Share { family, leg, body }) => family == job.family && leg.0 >= before_plans && body.0 >= before_plans,
                    _ => false,
                };
                family && self.jobs.len() > before_jobs && self.jobs.get(before_jobs..).is_some_and(|queued|
                    queued.iter().all(|next| next.slot.0 < self.plans.len() && next.budget.0 < job.budget.0
                        && matches!(self.plans.get(next.slot.0), Some(Plan::Pending)) && next.scope.0 < self.scopes.len()))
            }
        )]
        fn internal(
            &mut self,
            job: Job,
        )
        {
            let budget = Budget(job.budget.0.saturating_sub(1));
            let first_budget = self.seeded.up_to(budget);
            let second_budget = Budget(budget.0.saturating_sub(first_budget.0));
            let child = |slot: Slot, family: Family, budget: Budget, binders: u32| Job {
                slot,
                family,
                budget,
                binders,
                scope: job.scope,
            };
            let under = job.binders.saturating_add(1);
            let choice = match job.family {
                | Family::Value => self.seeded.pick(&[0_u8, 1, 9, 9]),
                | Family::Computation => self.seeded.pick(&[4_u8, 5, 6, 7, 8, 9, 9]),
            };
            match choice {
                | 0 => {
                    let (first, second) = (self.slot(), self.slot());
                    self.set(job.slot, Plan::Pair(first, second));
                    self.queue(child(first, Family::Value, first_budget, job.binders));
                    self.queue(child(second, Family::Value, second_budget, job.binders));
                },
                | 1 => {
                    let body = self.slot();
                    self.set(job.slot, Plan::Thunk(body));
                    self.queue(child(body, Family::Computation, budget, job.binders));
                },
                | 4 => {
                    let body = self.slot();
                    self.set(job.slot, Plan::Lambda(body));
                    self.queue(child(body, Family::Computation, budget, under));
                },
                | 5 => {
                    let value = self.slot();
                    self.set(job.slot, Plan::Return(value));
                    self.queue(child(value, Family::Value, budget, job.binders));
                },
                | 6 => {
                    let value = self.slot();
                    self.set(job.slot, Plan::Force(value));
                    self.queue(child(value, Family::Value, budget, job.binders));
                },
                | 7 => {
                    let (head, argument) = (self.slot(), self.slot());
                    self.set(job.slot, Plan::Application(head, argument));
                    self.queue(child(head, Family::Computation, first_budget, job.binders));
                    self.queue(child(argument, Family::Value, second_budget, job.binders));
                },
                | 8 => {
                    let (bound, body) = (self.slot(), self.slot());
                    self.set(job.slot, Plan::Bind(bound, body));
                    self.queue(child(bound, Family::Computation, first_budget, job.binders));
                    self.queue(child(body, Family::Computation, second_budget, under));
                },
                | _ => self.share(job, Job {
                    budget: first_budget,
                    ..job
                }),
            }
        }

        /// Settle `job` as a share, its leg generated within `leg`'s budget and
        /// its body within what is left, its first occurrence placed first.
        ///
        /// # Specification
        /// - requires: `leg` keeps the job context and takes a strict
        ///   sub-budget.
        /// - ensures: a share in the job family; two weighted choice slots out
        ///   of three request an abstraction leg, outside its own share. Its
        ///   body begins with an occurrence and continues one scope deeper.
        /// - provides: the shares the property duplicates.
        /// - panics: none.
        ///
        /// # Adequacy
        /// - hypothesis: L3 — the leg keeps the job context and takes a strict
        ///   sub-budget. Exactly one backward-linked scope and two jobs are
        ///   added: the leg stays outside the new scope and the remaining body
        ///   enters it. The share retains its family and fresh leg/body slots.
        ///   Generated validation witnesses the first occurrence and arity
        ///   numbering; exact erasure and expansion witnesses distinguish scope
        ///   capture and reversed children.
        /// - witness: `duplication::duplication::spinal_duplication_is_invisible_to_erasure`
        /// - witness: `duplication::duplication::a_copying_duplicate_is_the_expansion`
        #[spec(
            requires: job.budget.0 > 0 && leg.budget.0 < job.budget.0 && leg.slot == job.slot && leg.family == job.family
                && leg.binders == job.binders && leg.scope == job.scope
                && matches!(self.plans.get(job.slot.0), Some(Plan::Pending)) && job.scope.0 < self.scopes.len(),
            captures: [before_plans = self.plans.len(), before_jobs = self.jobs.len(), before_scopes = self.scopes.len()],
            ensures: self.scopes.len() == before_scopes.saturating_add(1) && self.jobs.len() == before_jobs.saturating_add(2)
                && self.scopes.last().copied().flatten().is_some_and(|(_, parent)| parent == job.scope)
                && matches!(self.plans.get(job.slot.0), Some(Plan::Share { family, leg, body })
                    if *family == job.family && leg.0 == before_plans && body.0 == before_plans.saturating_add(1))
                && self.jobs.get(before_jobs).is_some_and(|queued| queued.scope == leg.scope && queued.budget == leg.budget
                    && queued.binders >= job.binders && queued.binders <= job.binders.saturating_add(1))
                && self.jobs.last().is_some_and(|queued| queued.family == job.family && queued.scope.0 == before_scopes
                    && queued.budget.0 == job.budget.0.saturating_sub(1).saturating_sub(leg.budget.0)
                    && queued.binders == job.binders.saturating_add(u32::from(job.family == Family::Computation)))
        )]
        fn share(
            &mut self,
            job: Job,
            leg: Job,
        )
        {
            let body_budget = Budget(job.budget.0.saturating_sub(1).saturating_sub(leg.budget.0));
            let leg_family = self.seeded.pick(&[Family::Value, Family::Computation]);
            let (leg_slot, body) = (self.slot(), self.slot());
            self.set(job.slot, Plan::Share {
                family: job.family,
                leg: leg_slot,
                body,
            });
            if self.seeded.pick(&[true, true, false]) {
                let lambda = match leg_family {
                    | Family::Value => {
                        let lambda = self.slot();
                        self.set(leg_slot, Plan::Thunk(lambda));
                        lambda
                    },
                    | Family::Computation => leg_slot,
                };
                let inner = self.slot();
                self.set(lambda, Plan::Lambda(inner));
                self.queue(Job {
                    slot: inner,
                    family: Family::Computation,
                    binders: job.binders.saturating_add(1),
                    ..leg
                });
            }
            else {
                self.queue(Job {
                    slot: leg_slot,
                    family: leg_family,
                    ..leg
                });
            }
            let inside = Scope(self.scopes.len());
            self.scopes.push(Some((leg_family, job.scope)));
            let (first, rest) = (self.slot(), self.slot());
            let occurrence = Plan::Occurrence {
                family: leg_family,
                distance: 0,
            };
            let embedded = match (job.family, leg_family) {
                | (Family::Value, Family::Value) | (Family::Computation, Family::Computation) => {
                    occurrence
                },
                | (Family::Value, Family::Computation) => {
                    let inner = self.slot();
                    self.set(inner, occurrence);
                    Plan::Thunk(inner)
                },
                | (Family::Computation, Family::Value) => {
                    let inner = self.slot();
                    self.set(inner, occurrence);
                    Plan::Return(inner)
                },
            };
            self.set(first, embedded);
            let (plan, binders) = match job.family {
                | Family::Value => (Plan::Pair(first, rest), job.binders),
                | Family::Computation => (Plan::Bind(first, rest), job.binders.saturating_add(1)),
            };
            self.set(body, plan);
            self.queue(Job {
                slot: rest,
                family: job.family,
                budget: body_budget,
                binders,
                scope: inside,
            });
        }
    }

    /// One pending step of the preorder numbering.
    #[derive(Clone, Copy, Debug)]
    enum Visit
    {
        /// Number a node's occurrences, or queue its children.
        Node(Slot),
        /// Bring a share into scope, between its leg and its body.
        Open(Slot),
        /// Take the innermost share out of scope.
        Close,
    }

    /// Generate one closed overlay of `family` from `seeded`, its opaque nodes
    /// in `core`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: an overlay that validates from the returned root, every
    ///   occurrence numbered in its share's preorder and every arity the count
    ///   of its occurrences.
    /// - provides: the inputs the property duplicates.
    /// - panics: when a mint is refused, which a plan this small never
    ///   provokes.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — any seed and either evaluation family are admitted.
    ///   The returned root must retain its family and validate, excluding bad
    ///   numbering, wrong polarity, repeated nodes and unused shares.
    ///   Independent erasure-tree equality under both stances and exact copying
    ///   expansion test meaning rather than seeded fixture frequencies.
    /// - witness: `duplication::duplication::spinal_duplication_is_invisible_to_erasure`
    /// - witness: `duplication::duplication::a_copying_duplicate_is_the_expansion`
    #[spec(
        ensures: |ret| ret.0.validate(ret.1).is_ok()
            && matches!((family, ret.1), (Family::Value, OverlayId::Value(_)) | (Family::Computation, OverlayId::Computation(_)))
    )]
    fn generated(
        seeded: &mut Seeded,
        core: &mut CoreArena,
        family: Family,
    ) -> (Overlay, OverlayId)
    {
        let mut generator = Generator {
            seeded,
            core,
            plans: Vec::new(),
            scopes: Vec::from([None]),
            jobs: Vec::new(),
        };
        let root = generator.slot();
        generator.queue(Job {
            slot: root,
            family,
            budget: Budget(BUDGET),
            binders: 0,
            scope: Scope(0),
        });
        generator.run();
        let plans = generator.plans;

        let mut positions = vec![0_u32; plans.len()];
        let mut arities = vec![0_u32; plans.len()];
        let mut open: Vec<Slot> = Vec::new();
        let mut visits = Vec::from([Visit::Node(root)]);
        while let Some(visit) = visits.pop() {
            match visit {
                | Visit::Open(share) => open.push(share),
                | Visit::Close => {
                    open.pop();
                },
                | Visit::Node(slot) => match plans[slot.0] {
                    | Plan::Share { leg, body, .. } => {
                        visits.push(Visit::Close);
                        visits.push(Visit::Node(body));
                        visits.push(Visit::Open(slot));
                        visits.push(Visit::Node(leg));
                    },
                    | Plan::Occurrence { distance, .. } => {
                        let innermost = open
                            .len()
                            .checked_sub(1)
                            .expect("an occurrence stands inside a share");
                        let distance = usize::try_from(distance).expect("a distance fits a usize");
                        let depth = innermost
                            .checked_sub(distance)
                            .expect("an occurrence names a share in scope");
                        let share = open[depth];
                        positions[slot.0] = arities[share.0];
                        arities[share.0] = arities[share.0].saturating_add(1);
                    },
                    | Plan::Pair(first, second)
                    | Plan::Application(first, second)
                    | Plan::Bind(first, second) => {
                        visits.push(Visit::Node(second));
                        visits.push(Visit::Node(first));
                    },
                    | Plan::Thunk(child)
                    | Plan::Lambda(child)
                    | Plan::Return(child)
                    | Plan::Force(child) => visits.push(Visit::Node(child)),
                    | Plan::Pending
                    | Plan::Unit
                    | Plan::Variable(_)
                    | Plan::OpaqueValue(_)
                    | Plan::OpaqueComputation(_) => {},
                },
            }
        }

        let mut overlay = Overlay::new();
        let mut minted: Vec<Option<OverlayId>> = vec![None; plans.len()];
        for slot in (0 .. plans.len()).rev() {
            let value = |child: Slot| match minted[child.0] {
                | Some(OverlayId::Value(id)) => id,
                | other => panic!("a value child, minted before its parent: {other:?}"),
            };
            let computation = |child: Slot| match minted[child.0] {
                | Some(OverlayId::Computation(id)) => id,
                | other => panic!("a computation child, minted before its parent: {other:?}"),
            };
            let as_value = |node: ValueNode, overlay: &mut Overlay| {
                OverlayId::Value(overlay.mint_value(node).expect("a small plan mints"))
            };
            let as_computation = |node: CompNode, overlay: &mut Overlay| {
                OverlayId::Computation(overlay.mint_computation(node).expect("a small plan mints"))
            };
            let made = match plans[slot] {
                | Plan::Pending => panic!("every slot is settled"),
                | Plan::Unit => as_value(ValueNode::Grafted(ValueGraft::Unit), &mut overlay),
                | Plan::Variable(index) => as_value(
                    ValueNode::Grafted(ValueGraft::Variable {
                        zone: Zone::Intuitionistic,
                        index: DeBruijnIndex::from(index),
                    }),
                    &mut overlay,
                ),
                | Plan::OpaqueValue(id) => as_value(ValueNode::Opaque(id), &mut overlay),
                | Plan::OpaqueComputation(id) => as_computation(CompNode::Opaque(id), &mut overlay),
                | Plan::Occurrence { family, distance } => {
                    let bound = Bound {
                        distance: ShareDistance::from(distance),
                        position: SharePosition::from(positions[slot]),
                    };
                    match family {
                        | Family::Value => as_value(ValueNode::Bound(bound), &mut overlay),
                        | Family::Computation => {
                            as_computation(CompNode::Bound(bound), &mut overlay)
                        },
                    }
                },
                | Plan::Pair(first, second) => as_value(
                    ValueNode::Grafted(ValueGraft::Pair(value(first), value(second))),
                    &mut overlay,
                ),
                | Plan::Thunk(body) => as_value(
                    ValueNode::Grafted(ValueGraft::Thunk(computation(body))),
                    &mut overlay,
                ),
                | Plan::Lambda(body) => as_computation(
                    CompNode::Grafted(CompGraft::Lambda(computation(body))),
                    &mut overlay,
                ),
                | Plan::Return(returned) => as_computation(
                    CompNode::Grafted(CompGraft::Return(value(returned))),
                    &mut overlay,
                ),
                | Plan::Force(forced) => as_computation(
                    CompNode::Grafted(CompGraft::Force(value(forced))),
                    &mut overlay,
                ),
                | Plan::Application(head, argument) => as_computation(
                    CompNode::Grafted(CompGraft::Application(computation(head), value(argument))),
                    &mut overlay,
                ),
                | Plan::Bind(bound, body) => as_computation(
                    CompNode::Grafted(CompGraft::Bind(computation(bound), computation(body))),
                    &mut overlay,
                ),
                | Plan::Share { family, leg, body } => {
                    let arity = ShareArity::from(arities[slot]);
                    let leg = minted[leg.0].expect("a leg is minted before its share");
                    match family {
                        | Family::Value => as_value(
                            ValueNode::Shared(Sharing {
                                arity,
                                leg,
                                body: value(body),
                            }),
                            &mut overlay,
                        ),
                        | Family::Computation => as_computation(
                            CompNode::Shared(Sharing {
                                arity,
                                leg,
                                body: computation(body),
                            }),
                            &mut overlay,
                        ),
                    }
                },
            };
            minted[slot] = Some(made);
        }
        let root = minted[root.0].expect("the root is minted");
        overlay
            .validate(root)
            .expect("a generated overlay validates");
        (overlay, root)
    }

    /// Erase `root` into `core`.
    ///
    /// # Specification
    /// - requires: `root` is an evaluation root that validates, and `core`
    ///   holds its opaque nodes.
    /// - ensures: the erased root.
    /// - provides: the one erasure both sides of a comparison go through.
    /// - panics: when erasure refuses, which the requirement excludes.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a valid evaluation root names live opaque core nodes.
    ///   The answer must retain its family and resolve in the destination
    ///   arena. The original and duplicated overlays are erased independently
    ///   and their ordered trees compared, excluding a wrong-family result and
    ///   a semantically changed duplicate.
    /// - witness: `duplication::duplication::spinal_duplication_is_invisible_to_erasure`
    /// - witness: `duplication::duplication::a_copying_duplicate_is_the_expansion`
    #[spec(
        requires: matches!(root, OverlayId::Value(_) | OverlayId::Computation(_)) && overlay.validate(root).is_ok(),
        ensures: |ret| match (root, ret) {
            (OverlayId::Value(_), Term::Value(id)) => core.value(id).is_some(),
            (OverlayId::Computation(_), Term::Computation(id)) => core.computation(id).is_some(),
            _ => false,
        }
    )]
    fn erased(
        overlay: &Overlay,
        root: OverlayId,
        core: &mut CoreArena,
    ) -> Term
    {
        match root {
            | OverlayId::Value(id) => {
                Term::Value(erase_value(overlay, id, core).expect("a valid root erases"))
            },
            | OverlayId::Computation(id) => Term::Computation(
                erase_computation(overlay, id, core).expect("a valid root erases"),
            ),
            | OverlayId::ValueType(_) | OverlayId::CompType(_) => {
                panic!("the property generates evaluation roots")
            },
        }
    }

    /// The measure of `root`.
    ///
    /// # Specification
    /// - requires: the overlay validates from `root`, and its expansion fits a
    ///   64-bit counter.
    /// - ensures: the root's five quantities.
    /// - provides: the comparison every treatment is read through.
    /// - panics: when the measure refuses, which the requirement excludes.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a valid root has a representable expansion. The four
    ///   measure laws constrain the answer; the copying witness independently
    ///   requires no shares and node/expansion counts equal to the original
    ///   expansion. A kept non-abstraction and a distributed abstraction
    ///   separate the sharing cases.
    /// - witness: `duplication::duplication::a_copying_duplicate_is_the_expansion`
    /// - witness: `duplication::duplication::a_spinal_duplicate_keeps_a_leg_that_is_no_abstraction`
    /// - witness: `duplication::duplication::a_spinal_duplicate_distributes_an_abstraction_over_its_ribs`
    #[spec(
        requires: overlay.validate(root).is_ok(),
        ensures: |ret| u64::from(ret.occurrences()) >= u64::from(ret.shares())
            && u64::from(ret.depth()) <= u64::from(ret.shares())
            && u64::from(ret.nodes()) > u64::from(ret.shares()).saturating_add(u64::from(ret.occurrences()))
            && u64::from(ret.expansion()) >= 1
    )]
    fn measured(
        overlay: &Overlay,
        root: OverlayId,
    ) -> SharingMeasure
    {
        SharingMeasure::of(overlay, root).expect("a small root measures")
    }

    /// Mint a value node.
    ///
    /// # Specification
    /// trivial.
    fn value(
        overlay: &mut Overlay,
        node: ValueNode,
    ) -> OverlayValueId
    {
        overlay.mint_value(node).expect("a hand-built node mints")
    }

    /// Mint a computation node.
    ///
    /// # Specification
    /// trivial.
    fn computation(
        overlay: &mut Overlay,
        node: CompNode,
    ) -> OverlayCompId
    {
        overlay
            .mint_computation(node)
            .expect("a hand-built node mints")
    }

    /// A value occurrence of the innermost share at `position`.
    ///
    /// # Specification
    /// trivial.
    fn occurrence(
        overlay: &mut Overlay,
        position: SharePosition,
    ) -> OverlayValueId
    {
        value(
            overlay,
            ValueNode::Bound(Bound {
                distance: ShareDistance::from(0_u32),
                position,
            }),
        )
    }

    /// A chain of `links` shares, each sharing the one below among the two
    /// components of a pair, over a unit: an expansion of `2^(links + 1) - 1`
    /// nodes held in `4 * links + 1`.
    ///
    /// # Specification
    /// - requires: the requested links fit the overlay id space.
    /// - ensures: the overlay and its root.
    /// - provides: the root whose expansion passes a counter while its overlay
    ///   stays small.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the link count fits overlay ids even when expansion
    ///   exceeds a counter. A bounded descent requires an arity-two share,
    ///   ordered positions zero and one and a unit at exactly the requested
    ///   depth. The refusal witness distinguishes an exponential-copy preflight
    ///   failure from a partial overlay mutation.
    /// - witness: `duplication::duplication::a_refused_duplication_leaves_the_overlay_as_it_found_it`
    #[spec(
        ensures: |ret| {
            let mut top = ret.1;
            for _ in 0..links.0 {
                let Some(&ValueNode::Shared(sharing)) = ret.0.value(top) else { return false; };
                let OverlayId::Value(leg) = sharing.leg else { return false; };
                let Some(&ValueNode::Grafted(ValueGraft::Pair(first, second))) = ret.0.value(sharing.body) else { return false; };
                if sharing.arity != ShareArity::from(2_u32)
                    || ret.0.value(first) != Some(&ValueNode::Bound(Bound { distance: ShareDistance::from(0_u32), position: SharePosition::from(0_u32) }))
                    || ret.0.value(second) != Some(&ValueNode::Bound(Bound { distance: ShareDistance::from(0_u32), position: SharePosition::from(1_u32) })) { return false; }
                top = leg;
            }
            ret.0.value(top) == Some(&ValueNode::Grafted(ValueGraft::Unit))
        }
    )]
    fn doubling(links: Links) -> (Overlay, OverlayValueId)
    {
        let mut overlay = Overlay::new();
        let mut below = value(&mut overlay, ValueNode::Grafted(ValueGraft::Unit));
        for _link in 0 .. links.0 {
            let first = occurrence(&mut overlay, SharePosition::from(0_u32));
            let second = occurrence(&mut overlay, SharePosition::from(1_u32));
            let body = value(
                &mut overlay,
                ValueNode::Grafted(ValueGraft::Pair(first, second)),
            );
            below = value(
                &mut overlay,
                ValueNode::Shared(Sharing {
                    arity: ShareArity::from(2_u32),
                    leg: OverlayId::Value(below),
                    body,
                }),
            );
        }
        (overlay, below)
    }

    #[test]
    fn spinal_duplication_is_invisible_to_erasure()
    {
        let mut seeded = Seeded(0x9E37_79B9_7F4A_7C15);
        for case in 0 .. CASES {
            let family = seeded.pick(&[Family::Value, Family::Computation]);
            let mut core = CoreArena::new();
            let (mut overlay, root) = generated(&mut seeded, &mut core, family);
            for stance in [DuplicationStance::EraseAndClone, DuplicationStance::Spinal] {
                let mut log = TraceLog::new();
                let installed = TracedDuplication::install(stance, &mut log)
                    .expect("a recording sink carries either stance");
                let rebuilt = match root {
                    | OverlayId::Value(id) => installed
                        .duplicate_value(&mut overlay, &core, id)
                        .map(OverlayId::Value),
                    | OverlayId::Computation(id) => installed
                        .duplicate_computation(&mut overlay, &core, id)
                        .map(OverlayId::Computation),
                    | OverlayId::ValueType(_) | OverlayId::CompType(_) => {
                        panic!("the property generates evaluation roots")
                    },
                }
                .unwrap_or_else(|fault| panic!("case {case} under {stance:?}: {fault:?}"));
                let mut erasures = core.clone();
                let before = erased(&overlay, root, &mut erasures);
                let after = erased(&overlay, rebuilt, &mut erasures);
                assert_eq!(
                    Trees::Same,
                    same_tree(&erasures, before, &erasures, after),
                    "case {case} under {stance:?}: the duplicate erases to another tree"
                );
            }
        }
    }

    #[test]
    fn a_copying_duplicate_is_the_expansion()
    {
        let mut seeded = Seeded(0x2545_F491_4F6C_DD1D);
        for case in 0 .. CASES {
            let family = seeded.pick(&[Family::Value, Family::Computation]);
            let mut core = CoreArena::new();
            let (mut overlay, root) = generated(&mut seeded, &mut core, family);
            let input = measured(&overlay, root);
            let policy = DuplicationPolicy::default();
            let rebuilt = match root {
                | OverlayId::Value(id) => {
                    duplicate_value(&mut overlay, &core, policy, id).map(OverlayId::Value)
                },
                | OverlayId::Computation(id) => {
                    duplicate_computation(&mut overlay, &core, policy, id)
                        .map(OverlayId::Computation)
                },
                | OverlayId::ValueType(_) | OverlayId::CompType(_) => {
                    panic!("the property generates evaluation roots")
                },
            }
            .unwrap_or_else(|fault| panic!("case {case}: {fault:?}"));
            let copied = measured(&overlay, rebuilt);
            let expansion = u64::from(input.expansion());
            assert_eq!(
                [0, 0, 0, expansion, expansion],
                [
                    u64::from(copied.shares()),
                    u64::from(copied.occurrences()),
                    u64::from(copied.depth()),
                    u64::from(copied.nodes()),
                    u64::from(copied.expansion()),
                ],
                "case {case}: copying every part mints the expansion, sharing nothing"
            );
            assert_eq!(
                input,
                measured(&overlay, root),
                "case {case}: the input is left as it was"
            );
        }
    }

    #[test]
    fn a_spinal_duplicate_keeps_a_leg_that_is_no_abstraction()
    {
        let mut overlay = Overlay::new();
        let first = value(&mut overlay, ValueNode::Grafted(ValueGraft::Unit));
        let second = value(&mut overlay, ValueNode::Grafted(ValueGraft::Unit));
        let leg = value(
            &mut overlay,
            ValueNode::Grafted(ValueGraft::Pair(first, second)),
        );
        let left = occurrence(&mut overlay, SharePosition::from(0_u32));
        let right = occurrence(&mut overlay, SharePosition::from(1_u32));
        let body = value(
            &mut overlay,
            ValueNode::Grafted(ValueGraft::Pair(left, right)),
        );
        let root = value(
            &mut overlay,
            ValueNode::Shared(Sharing {
                arity: ShareArity::from(2_u32),
                leg: OverlayId::Value(leg),
                body,
            }),
        );
        let core = CoreArena::new();

        let mut log = TraceLog::new();
        let spinal = TracedDuplication::install(DuplicationStance::Spinal, &mut log)
            .expect("a recording sink carries the spinal stance");
        let kept = spinal
            .duplicate_value(&mut overlay, &core, root)
            .expect("the root duplicates");
        assert_ne!(root, kept, "the duplicate is fresh");
        assert_eq!(
            measured(&overlay, OverlayId::Value(root)),
            measured(&overlay, OverlayId::Value(kept)),
            "a leg that is no abstraction is one rib, and the spinal stance shares it whole"
        );
        let Some(&ValueNode::Shared(Sharing { arity, .. })) = overlay.value(kept)
        else {
            panic!("the share is kept at the root");
        };
        assert_eq!(ShareArity::from(2_u32), arity);

        let copied = duplicate_value(&mut overlay, &core, DuplicationPolicy::default(), root)
            .expect("the root duplicates");
        let copied = measured(&overlay, OverlayId::Value(copied));
        assert_eq!(
            [0, 7],
            [u64::from(copied.shares()), u64::from(copied.nodes())],
            "and the copying stance inlines it at both occurrences"
        );
    }

    #[test]
    fn a_spinal_duplicate_distributes_an_abstraction_over_its_ribs()
    {
        // `share f = thunk (λ. return (x₀, (⟨⟩, ⟨⟩))) in (f, f)`: the pair of
        // units reads no binder and is the leg's one rib.
        let mut overlay = Overlay::new();
        let bound = value(
            &mut overlay,
            ValueNode::Grafted(ValueGraft::Variable {
                zone: Zone::Intuitionistic,
                index: DeBruijnIndex::from(0_u32),
            }),
        );
        let first = value(&mut overlay, ValueNode::Grafted(ValueGraft::Unit));
        let second = value(&mut overlay, ValueNode::Grafted(ValueGraft::Unit));
        let rib = value(
            &mut overlay,
            ValueNode::Grafted(ValueGraft::Pair(first, second)),
        );
        let returned = value(
            &mut overlay,
            ValueNode::Grafted(ValueGraft::Pair(bound, rib)),
        );
        let returner = computation(&mut overlay, CompNode::Grafted(CompGraft::Return(returned)));
        let lambda = computation(&mut overlay, CompNode::Grafted(CompGraft::Lambda(returner)));
        let leg = value(&mut overlay, ValueNode::Grafted(ValueGraft::Thunk(lambda)));
        let left = occurrence(&mut overlay, SharePosition::from(0_u32));
        let right = occurrence(&mut overlay, SharePosition::from(1_u32));
        let body = value(
            &mut overlay,
            ValueNode::Grafted(ValueGraft::Pair(left, right)),
        );
        let root = value(
            &mut overlay,
            ValueNode::Shared(Sharing {
                arity: ShareArity::from(2_u32),
                leg: OverlayId::Value(leg),
                body,
            }),
        );
        let core = CoreArena::new();

        let mut log = TraceLog::new();
        let spinal = TracedDuplication::install(DuplicationStance::Spinal, &mut log)
            .expect("a recording sink carries the spinal stance");
        let distributed = spinal
            .duplicate_value(&mut overlay, &core, root)
            .expect("the root duplicates");

        let Some(&ValueNode::Shared(Sharing {
            arity,
            leg: OverlayId::Value(shared),
            body: copies,
        })) = overlay.value(distributed)
        else {
            panic!(
                "the rib is shared at the root, in the abstraction's place: {:?}",
                overlay.value(distributed)
            );
        };
        assert_eq!(ShareArity::from(2_u32), arity, "once per copy of the spine");
        let Some(&ValueNode::Grafted(ValueGraft::Pair(rib_first, rib_second))) =
            overlay.value(shared)
        else {
            panic!("the rib share's leg is the pair of units");
        };
        for unit in [rib_first, rib_second] {
            assert!(matches!(
                overlay.value(unit),
                Some(&ValueNode::Grafted(ValueGraft::Unit))
            ));
        }
        let Some(&ValueNode::Grafted(ValueGraft::Pair(left_copy, right_copy))) =
            overlay.value(copies)
        else {
            panic!("the body keeps its pair");
        };
        for (position, copy) in [(0_u32, left_copy), (1_u32, right_copy)] {
            let Some(&ValueNode::Grafted(ValueGraft::Thunk(lambda))) = overlay.value(copy)
            else {
                panic!("each occurrence becomes a copy of the spine");
            };
            let Some(&CompNode::Grafted(CompGraft::Lambda(returner))) = overlay.computation(lambda)
            else {
                panic!("the copy keeps the lambda");
            };
            let Some(&CompNode::Grafted(CompGraft::Return(returned))) =
                overlay.computation(returner)
            else {
                panic!("and the returner");
            };
            let Some(&ValueNode::Grafted(ValueGraft::Pair(variable, pointed))) =
                overlay.value(returned)
            else {
                panic!("and the pair on the spine");
            };
            assert!(
                matches!(
                    overlay.value(variable),
                    Some(&ValueNode::Grafted(ValueGraft::Variable { index, .. }))
                        if index == DeBruijnIndex::from(0_u32)
                ),
                "the binder's occurrence is copied"
            );
            assert_eq!(
                Some(&ValueNode::Bound(Bound {
                    distance: ShareDistance::from(0_u32),
                    position: SharePosition::from(position),
                })),
                overlay.value(pointed),
                "the rib is an occurrence of its share, in preorder"
            );
        }
    }

    #[test]
    fn a_refused_duplication_leaves_the_overlay_as_it_found_it()
    {
        let core = CoreArena::new();
        let policy = DuplicationPolicy::default();

        let mut overlay = Overlay::new();
        let leg = value(&mut overlay, ValueNode::Grafted(ValueGraft::Unit));
        let body = value(&mut overlay, ValueNode::Grafted(ValueGraft::Unit));
        let empty = value(
            &mut overlay,
            ValueNode::Shared(Sharing {
                arity: ShareArity::from(0_u32),
                leg: OverlayId::Value(leg),
                body,
            }),
        );
        let mark = overlay.watermark();
        assert_eq!(
            Err(DuplicationFault::Refused(OverlayRefusal::ZeroArity {
                share: OverlayId::Value(empty),
            })),
            duplicate_value(&mut overlay, &core, policy, empty),
            "a root that does not validate is refused in validation's words"
        );
        assert_eq!(mark, overlay.watermark());

        let (mut overlay, root) = doubling(Links(40));
        let mark = overlay.watermark();
        let expansion = 2_u64
            .checked_pow(41)
            .and_then(|power| power.checked_sub(1))
            .expect("the expansion fits a u64");
        let refused = duplicate_value(&mut overlay, &core, policy, root);
        let Err(DuplicationFault::ExpansionPastIds { expansion: priced }) = refused
        else {
            panic!("copying an expansion past the ids is refused before minting: {refused:?}");
        };
        assert_eq!(expansion, u64::from(priced));
        assert_eq!(mark, overlay.watermark(), "and mints nothing");

        let (mut overlay, root) = doubling(Links(70));
        let mark = overlay.watermark();
        assert!(
            matches!(
                duplicate_value(&mut overlay, &core, policy, root),
                Err(DuplicationFault::Measure(_))
            ),
            "an expansion past the measure's counter is refused in the measure's words"
        );
        assert_eq!(mark, overlay.watermark(), "and mints nothing");

        let mut log = TraceLog::new();
        let spinal = TracedDuplication::install(DuplicationStance::Spinal, &mut log)
            .expect("a recording sink carries the spinal stance");
        let kept = spinal
            .duplicate_value(&mut overlay, &core, root)
            .expect("the sharing stance keeps every share and mints the overlay's size");
        assert!(overlay.validate(OverlayId::Value(kept)).is_ok());
    }
}
