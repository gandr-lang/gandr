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

    /// The internal nodes a generated overlay holds at most, legs included.
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
        /// One of `options`, uniformly; a repeated option weighs its count.
        ///
        /// # Specification
        /// - requires: `options` is not empty.
        /// - ensures: an element of `options`.
        /// - provides: every draw the generator makes.
        /// - panics: when `options` is empty.
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
        fn up_to(
            &mut self,
            ceiling: Budget,
        ) -> Budget
        {
            let counts: Vec<u32> = (0 ..= ceiling.0).collect();
            Budget(self.pick(&counts))
        }
    }

    /// The internal nodes a job may hold.
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
        /// The internal nodes it may hold.
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
        /// - requires: nothing.
        /// - ensures: every slot is settled.
        /// - provides: the generation loop.
        /// - panics: none.
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
        /// - requires: nothing.
        /// - ensures: the distance of every share around `scope` whose leg is
        ///   of `family`.
        /// - provides: the choice of an occurrence.
        /// - panics: none.
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
        /// - requires: nothing.
        /// - ensures: the slot holds a leaf of the job's family, well scoped
        ///   under its binders and shares.
        /// - provides: every leaf the property reads.
        /// - panics: none.
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
        /// - requires: the job's budget is positive.
        /// - ensures: the slot holds a former of the job's family over fresh
        ///   slots, each queued with a share of the budget and the binders and
        ///   shares it stands under.
        /// - provides: every internal node the property reads.
        /// - panics: none.
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
        /// - requires: `leg` is `job` with the leg's budget.
        /// - ensures: the slot holds a share in the job's family; its leg is an
        ///   abstraction two times in three, standing in the job's scope; its
        ///   body opens with an occurrence of it, so its arity is positive, and
        ///   goes on in a scope one share deeper.
        /// - provides: the shares the property duplicates.
        /// - panics: none.
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
    /// - requires: the overlay validates from `root`, and `core` holds its
    ///   opaque nodes.
    /// - ensures: the erased root.
    /// - provides: the one erasure both sides of a comparison go through.
    /// - panics: when erasure refuses, which the requirement excludes.
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
    /// - requires: nothing.
    /// - ensures: the overlay and its root.
    /// - provides: the root whose expansion passes a counter while its overlay
    ///   stays small.
    /// - panics: none.
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
        let mut distributed = 0_u32;
        let mut apart = 0_u32;
        for case in 0 .. CASES {
            let family = seeded.pick(&[Family::Value, Family::Computation]);
            let mut core = CoreArena::new();
            let (mut overlay, root) = generated(&mut seeded, &mut core, family);
            let input = measured(&overlay, root);
            let mut outputs = Vec::new();
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
                outputs.push(measured(&overlay, rebuilt));
            }
            let [copied, spinal] = outputs[..]
            else {
                panic!("one output per stance");
            };
            if spinal != input {
                distributed = distributed.saturating_add(1);
            }
            if copied != spinal {
                apart = apart.saturating_add(1);
            }
        }
        assert!(
            distributed.saturating_mul(10) > CASES,
            "the spinal stance distributed an abstraction in {distributed} cases, which does \
             not exercise the rib path"
        );
        assert!(
            apart.saturating_mul(2) > CASES,
            "the stances differed in {apart} cases, which does not exercise both"
        );
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
