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
//! A second property evaluates generated roots under both stances and reads
//! each weak head back: the spinal run reads back as the copying run's tree, or
//! refuses as it does. Each case runs a closed root and an open body applied
//! to two arguments, whose shares evaluate their legs under two bindings. That
//! agreement modulo erasure is the property the spinal stance is admitted on
//! (`policy`'s module doc).
//!
//! The treatments are pinned beside it: the copying stance's output is the
//! expansion, the sharing stance keeps a leg that is no abstraction and
//! distributes an abstraction over its ribs, and a refusal leaves the overlay
//! at its watermark.
//!
//! The duplication cases, in a `cfg(test)` module so the crate's lint wall
//! reads them as test code rather than as shipping code.

use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use alloc::string::String;

use anodized::spec;
use gandr_core_nbe::BinderLevel;
use gandr_core_nbe::Bound;
use gandr_core_nbe::CompGraft;
use gandr_core_nbe::CompNode;
use gandr_core_nbe::CoreTerm;
use gandr_core_nbe::Definitions;
use gandr_core_nbe::DomainArena;
use gandr_core_nbe::DuplicationFault;
use gandr_core_nbe::DuplicationPolicy;
use gandr_core_nbe::DuplicationStance;
use gandr_core_nbe::Environment;
use gandr_core_nbe::Fuel;
use gandr_core_nbe::LoweredChain;
use gandr_core_nbe::NeutralHead;
use gandr_core_nbe::Overlay;
use gandr_core_nbe::OverlayCompId;
use gandr_core_nbe::OverlayEvalFault;
use gandr_core_nbe::OverlayId;
use gandr_core_nbe::OverlayRefusal;
use gandr_core_nbe::OverlayValueId;
use gandr_core_nbe::ReadbackFault;
use gandr_core_nbe::ReadbackMode;
use gandr_core_nbe::ShareArity;
use gandr_core_nbe::ShareDistance;
use gandr_core_nbe::SharePosition;
use gandr_core_nbe::Sharing;
use gandr_core_nbe::SharingMeasure;
use gandr_core_nbe::TermFace;
use gandr_core_nbe::TracedDuplication;
use gandr_core_nbe::Unfolding;
use gandr_core_nbe::ValueGraft;
use gandr_core_nbe::ValueNode;
use gandr_core_nbe::compile_computation;
use gandr_core_nbe::compile_value;
use gandr_core_nbe::duplicate_computation;
use gandr_core_nbe::duplicate_value;
use gandr_core_nbe::erase_computation;
use gandr_core_nbe::erase_value;
use gandr_core_nbe::readback_computation;
use gandr_core_nbe::readback_computation_within;
use gandr_core_nbe::readback_value;
use gandr_core_nbe::readback_value_within;
use gandr_core_term::CertificateEquality;
use gandr_core_term::CompTypeId;
use gandr_core_term::ComputationId;
use gandr_core_term::CoreArena;
use gandr_core_term::DefinitionalEnvironment;
use gandr_core_term::ValueId;
use gandr_core_term::ValueTypeId;
use gandr_core_term::Zone;
use gandr_core_term::children;
use gandr_core_term::equal_certificate_syntax;
use gandr_core_term::support::Crossing;
use gandr_kernel_conversion_trace::TraceLog;
use gandr_kernel_strata::Level;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::FieldLabel;
use gandr_kernel_term::Summand;
use proptest::prelude::ProptestConfig;
use proptest::prelude::prop_assert;
use proptest::prelude::proptest;

use crate::free_indices::Former;
use crate::free_indices::computations;
use crate::free_indices::types;
use crate::free_indices::values;
use crate::trees::Term;

/// How many overlays the property generates.
const CASES: u32 = 600;

/// The branching budget; share skeletons and returner wrappers add nodes. It
/// stands where the largest generated root erases to as many core nodes as
/// the largest side that the checker's machine entries meet over the corpus.
const BUDGET: u32 = 48;

/// How many seeds the agreement property runs, and the census test reads.
const SEEDS: u32 = 2048;

/// The binders the applied root opens: one more than the largest index a row
/// of the full alphabet reads.
const OPENED: u32 = 8;

/// The names of the grafted formers, shares and occurrences.
const GRAFTED: [&str; 13] = [
    "grafted ⟨⟩",
    "grafted variable",
    "grafted pair",
    "grafted thunk",
    "grafted λ",
    "grafted return",
    "grafted force",
    "grafted application",
    "grafted bind",
    "value share",
    "computation share",
    "value occurrence",
    "computation occurrence",
];

/// The names of the opaque leaves the generator mints itself.
const MINTED: [&str; 3] = ["opaque (x, ⟨⟩)", "opaque ⟨⟩", "opaque return"];

/// The name of a transport along a path no rule reduces.
const STUCK_LINK: &str = "stuck link tr(y. El y, k, ⟨⟩)";

/// The name of a bind over a stuck link whose body transports the bound value.
const BIND_OVER_STUCK_LINK: &str = "x ← tr(y. El y, k, ⟨⟩); tr(y. El y, k′, x)";

/// The closed arguments of the applied root, by name.
const ARGUMENTS: [&str; 8] = [
    "argument ⟨⟩",
    "argument (⟨⟩, ⟨⟩)",
    "argument inl ⟨⟩",
    "argument inr ⟨⟩",
    "argument {a = ⟨⟩}",
    "argument [⟨⟩]",
    "argument thunk (λ. return x₀)",
    "argument k, rigid",
];

/// What the roots of a run hold, by name: each grafted former, each share and
/// occurrence by family, and each opaque leaf by the row it comes from.
type Census = BTreeMap<&'static str, u32>;

/// Count `name` once more in `census`.
///
/// # Specification
/// trivial.
fn counted_once(
    census: &mut Census,
    name: &'static str,
)
{
    let count = census.entry(name).or_insert(0);
    *count = count.saturating_add(1);
}

/// An opaque leaf of the full alphabet.
enum Leaf
{
    /// A row of the free-index table.
    Row(Former),
    /// A transport along a path no rule reduces.
    StuckLink,
    /// A bind over a stuck link whose body transports the bound value along
    /// another such path.
    BindOverStuckLink,
}

impl Leaf
{
    /// Whether the leaf reads no linear slot and each of its free indices
    /// stands below `binders`.
    ///
    /// # Specification
    /// trivial.
    fn fits(
        &self,
        binders: u32,
    ) -> bool
    {
        match self {
            Self::Row(row) => {
                row.linear.is_empty()
                    && row.consumed.is_empty()
                    && row.intuitionistic.iter().all(|&index| index < binders)
            },
            Self::StuckLink | Self::BindOverStuckLink => true,
        }
    }

    /// The leaf's name for the census, and its term built in `core`.
    ///
    /// # Specification
    /// trivial.
    fn built(
        &self,
        core: &mut CoreArena,
    ) -> (&'static str, CoreTerm)
    {
        match self {
            Self::Row(row) => (row.what, (row.build)(core)),
            Self::StuckLink => {
                let operand = core.value_unit();
                let link = transported(core, ConstantIndex::from(0_usize), operand);
                (STUCK_LINK, CoreTerm::Computation(link))
            },
            Self::BindOverStuckLink => {
                let operand = core.value_unit();
                let link = transported(core, ConstantIndex::from(0_usize), operand);
                let carried = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
                let body = transported(core, ConstantIndex::from(1_usize), carried);
                (
                    BIND_OVER_STUCK_LINK,
                    CoreTerm::Computation(core.computation_bind(link, body)),
                )
            },
        }
    }
}

/// A transport of `operand` along the constant `path`, which nothing defines,
/// under a motive that reads its binder: no rule reduces it.
///
/// # Specification
/// trivial.
fn transported(
    core: &mut CoreArena,
    path: ConstantIndex,
    operand: ValueId,
) -> ComputationId
{
    let path = core.value_constant(path);
    let code = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let motive = core.value_type_element(code, Level::zero());
    core.computation_path_transport(motive, path, operand)
}

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
    /// - ensures: an element of `options`; zero and nonzero seed states stay in
    ///   their respective classes. No uniformity guarantee is made.
    /// - provides: every draw the generator makes.
    /// - panics: when `options` is empty.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — any nonempty slice of Copy choices is admitted;
    ///   equality is not required of its element type. The guard excludes the
    ///   empty draw and the zero-state law records the invertible xorshift
    ///   transition without pinning a seed stream. The generated properties
    ///   exercise the resulting choices through structural erasure and
    ///   expansion, not a fixture-frequency threshold.
    /// - witness: `tests::duplication::spinal_duplication_is_invisible_to_erasure`
    /// - witness: `tests::duplication::a_copying_duplicate_is_the_expansion`
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
    ///   off-by-one split; generated overlays must validate, preserve erasure
    ///   and copy to exactly their measured expansion.
    /// - witness: `tests::duplication::spinal_duplication_is_invisible_to_erasure`
    /// - witness: `tests::duplication::a_copying_duplicate_is_the_expansion`
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

/// The intuitionistic binders a generated root stands under.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Binders(u32);

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
    /// The name of each opaque leaf, by slot.
    leaves: BTreeMap<usize, &'static str>,
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
    ///   scope parents precede their children. Empty jobs and no pending plans
    ///   on return exclude skipped work. Generated validation and independent
    ///   erasure comparisons distinguish wrong families, unclosed scopes and
    ///   reversed child construction.
    /// - witness: `tests::duplication::spinal_duplication_is_invisible_to_erasure`
    /// - witness: `tests::duplication::a_copying_duplicate_is_the_expansion`
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            spec_clause_traversal,
            reason = "test fixture: the generator runs once per generated overlay of a bounded budget, and the check reads its plans, jobs and scopes to state the generation invariant"
        )
    )]
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
    /// - ensures: the distance of every share around `scope` whose leg is of
    ///   `family`.
    /// - provides: the choice of an occurrence.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the start scope is in bounds and every parent points
    ///   backward. An ordered iterator over the answer must agree with exactly
    ///   the matching ancestor cells, excluding skipped, duplicated, reversed
    ///   or wrong-family distances. Generated closed overlays exercise the
    ///   occurrence choices in both evaluation families.
    /// - witness: `tests::duplication::spinal_duplication_is_invisible_to_erasure`
    /// - witness: `tests::duplication::a_copying_duplicate_is_the_expansion`
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            spec_clause_traversal,
            reason = "test fixture: the generated scope chains are a bounded budget deep, and the check re-reads every scope's parent to state the backward-pointing requirement"
        )
    )]
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
    /// - ensures: a well-scoped leaf of its family, or a computation returner
    ///   with one queued zero-budget value child.
    /// - provides: every leaf the property reads.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a pending slot and a valid scope describe the job.
    ///   The settled plan must preserve its family, keep variables under the
    ///   binder ceiling and resolve opaque nodes. A deferred computation leaf
    ///   queues exactly one zero-budget value job; an occurrence must reach a
    ///   matching ancestor. These guards exclude a pending result, wrong
    ///   polarity and an unscoped leaf before the erasure properties run.
    /// - witness: `tests::duplication::spinal_duplication_is_invisible_to_erasure`
    /// - witness: `tests::duplication::a_copying_duplicate_is_the_expansion`
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
        if self.seeded.pick(&[true, false])
            && let Some(plan) = self.drawn(job)
        {
            self.set(job.slot, plan);
            return;
        }
        match job.family {
            Family::Value => {
                let plan = match (self.seeded.pick(&[0_u8, 1, 2, 3]), read) {
                    (0, Some(index)) => Plan::Variable(index),
                    (1, Some(index)) => {
                        let variable = self
                            .core
                            .value_variable(Zone::Intuitionistic, DeBruijnIndex::from(index));
                        let unit = self.core.value_unit();
                        self.leaves.insert(job.slot.0, "opaque (x, ⟨⟩)");
                        Plan::OpaqueValue(self.core.value_tuple(&[variable, unit]))
                    },
                    (2, _) => {
                        self.leaves.insert(job.slot.0, "opaque ⟨⟩");
                        Plan::OpaqueValue(self.core.value_unit())
                    },
                    _ => Plan::Unit,
                };
                self.set(job.slot, plan);
            },
            Family::Computation => {
                let returned = match read {
                    Some(index) => self
                        .core
                        .value_variable(Zone::Intuitionistic, DeBruijnIndex::from(index)),
                    None => self.core.value_unit(),
                };
                if self.seeded.pick(&[true, false]) {
                    let opaque = self.core.computation_return(returned);
                    self.leaves.insert(job.slot.0, "opaque return");
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

    /// Draw an opaque leaf of `job`'s family from the full alphabet: a row of
    /// the free-index table whose free indices the job's binders bind, or a
    /// stuck link.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: an opaque plan of the job's family whose term resolves in the
    ///   arena, with its name kept for the census; `None` when the drawn row
    ///   builds a term of the other family.
    /// - provides: the full alphabet of core as opaque leaves.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a job of either family under any count of binders.
    ///   The plan keeps the job's family and resolves in the arena, and its
    ///   name stands in the census. A row drawn under too few binders makes
    ///   both runs refuse alike, and a row never drawn leaves the census test
    ///   short of its alphabet.
    /// - witness: `tests::duplication::the_property_draws_its_whole_alphabet`
    #[spec(
            ensures: |ret| ret.is_none_or(|plan| match plan {
                Plan::OpaqueValue(id) => job.family == Family::Value && self.core.value(id).is_some(),
                Plan::OpaqueComputation(id) => job.family == Family::Computation && self.core.computation(id).is_some(),
                _ => false,
            } && self.leaves.contains_key(&job.slot.0))
        )]
    fn drawn(
        &mut self,
        job: Job,
    ) -> Option<Plan>
    {
        let mut leaves: Vec<Leaf> = match job.family {
            Family::Value => values().into_iter().chain(types()).map(Leaf::Row).collect(),
            Family::Computation => computations()
                .into_iter()
                .map(Leaf::Row)
                .chain([Leaf::StuckLink, Leaf::BindOverStuckLink])
                .collect(),
        };
        leaves.retain(|leaf| leaf.fits(job.binders));
        let choices: Vec<usize> = (0 .. leaves.len()).collect();
        if choices.is_empty() {
            return None;
        }
        let leaf = leaves.swap_remove(self.seeded.pick(&choices));
        let (name, term) = leaf.built(self.core);
        let plan = match (job.family, term) {
            (Family::Value, CoreTerm::Value(id)) => Plan::OpaqueValue(id),
            (Family::Computation, CoreTerm::Computation(id)) => Plan::OpaqueComputation(id),
            _ => return None,
        };
        self.leaves.insert(job.slot.0, name);
        Some(plan)
    }

    /// Settle `job` as an internal node, queueing its children.
    ///
    /// # Specification
    /// - requires: a positive-budget job owns a pending slot in a valid scope.
    /// - ensures: the slot holds a former of the job's family over fresh slots,
    ///   each queued with a share of the budget and the binders and shares it
    ///   stands under.
    /// - provides: every internal node the property reads.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a positive-budget job owns a pending slot in a valid
    ///   scope. Its settled former has the requested family, fresh child slots
    ///   and at least one lower-budget queued job; share construction has its
    ///   own scope-transition predicate. Independent generated erasure and
    ///   expansion comparisons distinguish wrong child order, family, binder
    ///   shifts and exhausted work left pending.
    /// - witness: `tests::duplication::spinal_duplication_is_invisible_to_erasure`
    /// - witness: `tests::duplication::a_copying_duplicate_is_the_expansion`
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
            Family::Value => self.seeded.pick(&[0_u8, 1, 9, 9]),
            Family::Computation => self.seeded.pick(&[4_u8, 5, 6, 7, 8, 9, 9]),
        };
        match choice {
            0 => {
                let (first, second) = (self.slot(), self.slot());
                self.set(job.slot, Plan::Pair(first, second));
                self.queue(child(first, Family::Value, first_budget, job.binders));
                self.queue(child(second, Family::Value, second_budget, job.binders));
            },
            1 => {
                let body = self.slot();
                self.set(job.slot, Plan::Thunk(body));
                self.queue(child(body, Family::Computation, budget, job.binders));
            },
            4 => {
                let body = self.slot();
                self.set(job.slot, Plan::Lambda(body));
                self.queue(child(body, Family::Computation, budget, under));
            },
            5 => {
                let value = self.slot();
                self.set(job.slot, Plan::Return(value));
                self.queue(child(value, Family::Value, budget, job.binders));
            },
            6 => {
                let value = self.slot();
                self.set(job.slot, Plan::Force(value));
                self.queue(child(value, Family::Value, budget, job.binders));
            },
            7 => {
                let (head, argument) = (self.slot(), self.slot());
                self.set(job.slot, Plan::Application(head, argument));
                self.queue(child(head, Family::Computation, first_budget, job.binders));
                self.queue(child(argument, Family::Value, second_budget, job.binders));
            },
            8 => {
                let (bound, body) = (self.slot(), self.slot());
                self.set(job.slot, Plan::Bind(bound, body));
                self.queue(child(bound, Family::Computation, first_budget, job.binders));
                self.queue(child(body, Family::Computation, second_budget, under));
            },
            _ => self.share(job, Job {
                budget: first_budget,
                ..job
            }),
        }
    }

    /// Settle `job` as a share, its leg generated within `leg`'s budget and
    /// its body within what is left, its first occurrence placed first.
    ///
    /// # Specification
    /// - requires: `leg` keeps the job context and takes a strict sub-budget.
    /// - ensures: a share in the job family; two weighted choice slots out of
    ///   three request an abstraction leg, outside its own share. Its body
    ///   begins with an occurrence and continues one scope deeper.
    /// - provides: the shares the property duplicates.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the leg keeps the job context and takes a strict
    ///   sub-budget. Exactly one backward-linked scope and two jobs are added:
    ///   the leg stays outside the new scope and the remaining body enters it.
    ///   The share retains its family and fresh leg/body slots. Generated
    ///   validation witnesses the first occurrence and arity numbering; exact
    ///   erasure and expansion witnesses distinguish scope capture and reversed
    ///   children.
    /// - witness: `tests::duplication::spinal_duplication_is_invisible_to_erasure`
    /// - witness: `tests::duplication::a_copying_duplicate_is_the_expansion`
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
                Family::Value => {
                    let lambda = self.slot();
                    self.set(leg_slot, Plan::Thunk(lambda));
                    lambda
                },
                Family::Computation => leg_slot,
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
            (Family::Value, Family::Value) | (Family::Computation, Family::Computation) => {
                occurrence
            },
            (Family::Value, Family::Computation) => {
                let inner = self.slot();
                self.set(inner, occurrence);
                Plan::Thunk(inner)
            },
            (Family::Computation, Family::Value) => {
                let inner = self.slot();
                self.set(inner, occurrence);
                Plan::Return(inner)
            },
        };
        self.set(first, embedded);
        let (plan, binders) = match job.family {
            Family::Value => (Plan::Pair(first, rest), job.binders),
            Family::Computation => (Plan::Bind(first, rest), job.binders.saturating_add(1)),
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

/// Generate one overlay of `family` from `seeded`, standing under `binders`
/// intuitionistic binders and closed when there are none, its opaque nodes in
/// `core`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: an overlay that validates from the returned root, every
///   occurrence numbered in its share's preorder and every arity the count of
///   its occurrences.
/// - provides: the inputs the property duplicates.
/// - panics: when a mint is refused, which a plan this small never provokes.
///
/// # Adequacy
/// - hypothesis: L3 — any seed and either evaluation family are admitted. The
///   returned root must retain its family and validate, excluding bad
///   numbering, wrong polarity, repeated nodes and unused shares. Independent
///   erasure-tree equality under both stances and exact copying expansion test
///   meaning rather than seeded fixture frequencies.
/// - witness: `tests::duplication::spinal_duplication_is_invisible_to_erasure`
/// - witness: `tests::duplication::a_copying_duplicate_is_the_expansion`
#[spec(
        ensures: |ret| ret.0.validate(ret.1).is_ok()
            && matches!((family, ret.1), (Family::Value, OverlayId::Value(_)) | (Family::Computation, OverlayId::Computation(_)))
    )]
fn generated(
    seeded: &mut Seeded,
    core: &mut CoreArena,
    family: Family,
    binders: Binders,
) -> (Overlay, OverlayId)
{
    let (overlay, root, _) = counted(seeded, core, family, binders);
    (overlay, root)
}

/// Generate one overlay as [`generated`] does, with the census of what it
/// holds.
///
/// # Specification
/// - requires: nothing.
/// - ensures: as [`generated`], and a census that names each node of the
///   overlay once: each grafted former, each share and occurrence by family,
///   and each opaque leaf by the row it comes from.
/// - provides: the inputs the property duplicates, with the alphabet they draw.
/// - panics: when a mint is refused, which a plan this small never provokes.
///
/// # Adequacy
/// - hypothesis: L3 — any seed and either evaluation family are admitted. The
///   returned root validates in its family, and the census counts one name for
///   each plan slot. A census that drops a former or names a leaf by another
///   row changes the alphabet the census test compares with its declaration.
/// - witness: `tests::duplication::the_property_draws_its_whole_alphabet`
/// - witness: `tests::duplication::spinal_evaluation_agrees_with_the_copying_stance`
#[spec(
        ensures: |ret| ret.0.validate(ret.1).is_ok()
            && matches!((family, ret.1), (Family::Value, OverlayId::Value(_)) | (Family::Computation, OverlayId::Computation(_)))
            && ret.2.values().copied().map(u64::from).sum::<u64>() > 0
    )]
fn counted(
    seeded: &mut Seeded,
    core: &mut CoreArena,
    family: Family,
    binders: Binders,
) -> (Overlay, OverlayId, Census)
{
    let mut generator = Generator {
        seeded,
        core,
        plans: Vec::new(),
        scopes: Vec::from([None]),
        jobs: Vec::new(),
        leaves: BTreeMap::new(),
    };
    let root = generator.slot();
    generator.queue(Job {
        slot: root,
        family,
        budget: Budget(BUDGET),
        binders: binders.0,
        scope: Scope(0),
    });
    generator.run();
    let plans = generator.plans;
    let leaves = generator.leaves;

    let mut positions = vec![0_u32; plans.len()];
    let mut arities = vec![0_u32; plans.len()];
    let mut open: Vec<Slot> = Vec::new();
    let mut visits = Vec::from([Visit::Node(root)]);
    while let Some(visit) = visits.pop() {
        match visit {
            Visit::Open(share) => open.push(share),
            Visit::Close => {
                open.pop();
            },
            Visit::Node(slot) => match plans[slot.0] {
                Plan::Share { leg, body, .. } => {
                    visits.push(Visit::Close);
                    visits.push(Visit::Node(body));
                    visits.push(Visit::Open(slot));
                    visits.push(Visit::Node(leg));
                },
                Plan::Occurrence { distance, .. } => {
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
                Plan::Pair(first, second)
                | Plan::Application(first, second)
                | Plan::Bind(first, second) => {
                    visits.push(Visit::Node(second));
                    visits.push(Visit::Node(first));
                },
                Plan::Thunk(child)
                | Plan::Lambda(child)
                | Plan::Return(child)
                | Plan::Force(child) => visits.push(Visit::Node(child)),
                Plan::Pending
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
            Some(OverlayId::Value(id)) => id,
            other => panic!("a value child, minted before its parent: {other:?}"),
        };
        let computation = |child: Slot| match minted[child.0] {
            Some(OverlayId::Computation(id)) => id,
            other => panic!("a computation child, minted before its parent: {other:?}"),
        };
        let as_value = |node: ValueNode, overlay: &mut Overlay| {
            OverlayId::Value(overlay.mint_value(node).expect("a small plan mints"))
        };
        let as_computation = |node: CompNode, overlay: &mut Overlay| {
            OverlayId::Computation(overlay.mint_computation(node).expect("a small plan mints"))
        };
        let made = match plans[slot] {
            Plan::Pending => panic!("every slot is settled"),
            Plan::Unit => as_value(ValueNode::Grafted(ValueGraft::Unit), &mut overlay),
            Plan::Variable(index) => as_value(
                ValueNode::Grafted(ValueGraft::Variable {
                    zone: Zone::Intuitionistic,
                    index: DeBruijnIndex::from(index),
                }),
                &mut overlay,
            ),
            Plan::OpaqueValue(id) => as_value(ValueNode::Opaque(id), &mut overlay),
            Plan::OpaqueComputation(id) => as_computation(CompNode::Opaque(id), &mut overlay),
            Plan::Occurrence { family, distance } => {
                let bound = Bound {
                    distance: ShareDistance::from(distance),
                    position: SharePosition::from(positions[slot]),
                };
                match family {
                    Family::Value => as_value(ValueNode::Bound(bound), &mut overlay),
                    Family::Computation => as_computation(CompNode::Bound(bound), &mut overlay),
                }
            },
            Plan::Pair(first, second) => as_value(
                ValueNode::Grafted(ValueGraft::Pair(value(first), value(second))),
                &mut overlay,
            ),
            Plan::Thunk(body) => as_value(
                ValueNode::Grafted(ValueGraft::Thunk(computation(body))),
                &mut overlay,
            ),
            Plan::Lambda(body) => as_computation(
                CompNode::Grafted(CompGraft::Lambda(computation(body))),
                &mut overlay,
            ),
            Plan::Return(returned) => as_computation(
                CompNode::Grafted(CompGraft::Return(value(returned))),
                &mut overlay,
            ),
            Plan::Force(forced) => as_computation(
                CompNode::Grafted(CompGraft::Force(value(forced))),
                &mut overlay,
            ),
            Plan::Application(head, argument) => as_computation(
                CompNode::Grafted(CompGraft::Application(computation(head), value(argument))),
                &mut overlay,
            ),
            Plan::Bind(bound, body) => as_computation(
                CompNode::Grafted(CompGraft::Bind(computation(bound), computation(body))),
                &mut overlay,
            ),
            Plan::Share { family, leg, body } => {
                let arity = ShareArity::from(arities[slot]);
                let leg = minted[leg.0].expect("a leg is minted before its share");
                match family {
                    Family::Value => as_value(
                        ValueNode::Shared(Sharing {
                            arity,
                            leg,
                            body: value(body),
                        }),
                        &mut overlay,
                    ),
                    Family::Computation => as_computation(
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
    let mut census = Census::new();
    for (slot, plan) in plans.iter().enumerate() {
        let name = match plan {
            Plan::Pending => panic!("every slot is settled"),
            Plan::Unit => "grafted ⟨⟩",
            Plan::Variable(_) => "grafted variable",
            Plan::Pair(..) => "grafted pair",
            Plan::Thunk(_) => "grafted thunk",
            Plan::Lambda(_) => "grafted λ",
            Plan::Return(_) => "grafted return",
            Plan::Force(_) => "grafted force",
            Plan::Application(..) => "grafted application",
            Plan::Bind(..) => "grafted bind",
            Plan::Share {
                family: Family::Value,
                ..
            } => "value share",
            Plan::Share {
                family: Family::Computation,
                ..
            } => "computation share",
            Plan::Occurrence {
                family: Family::Value,
                ..
            } => "value occurrence",
            Plan::Occurrence {
                family: Family::Computation,
                ..
            } => "computation occurrence",
            Plan::OpaqueValue(_) | Plan::OpaqueComputation(_) => leaves
                .get(&slot)
                .copied()
                .expect("each opaque leaf carries its name"),
        };
        counted_once(&mut census, name);
    }
    (overlay, root, census)
}

/// Erase `root` into `core`.
///
/// # Specification
/// - requires: `root` is an evaluation root that validates, and `core` holds
///   its opaque nodes.
/// - ensures: the erased root.
/// - provides: the one erasure both sides of a comparison go through.
/// - panics: when erasure refuses, which the requirement excludes.
///
/// # Adequacy
/// - hypothesis: L3 — a valid evaluation root names live opaque core nodes. The
///   answer must retain its family and resolve in the destination arena. The
///   original and duplicated overlays are erased independently and their
///   ordered trees compared, excluding a wrong-family result and a semantically
///   changed duplicate.
/// - witness: `tests::duplication::spinal_duplication_is_invisible_to_erasure`
/// - witness: `tests::duplication::a_copying_duplicate_is_the_expansion`
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
        OverlayId::Value(id) => {
            Term::Value(erase_value(overlay, id, core).expect("a valid root erases"))
        },
        OverlayId::Computation(id) => {
            Term::Computation(erase_computation(overlay, id, core).expect("a valid root erases"))
        },
        OverlayId::ValueType(_) | OverlayId::CompType(_) => {
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
///   expansion. A kept non-abstraction and a distributed abstraction separate
///   the sharing cases.
/// - witness: `tests::duplication::a_copying_duplicate_is_the_expansion`
/// - witness: `tests::duplication::a_spinal_duplicate_keeps_a_leg_that_is_no_abstraction`
/// - witness: `tests::duplication::a_spinal_duplicate_distributes_an_abstraction_over_its_ribs`
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

/// How an evaluation and its readback refused.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Refused
{
    /// The overlay's evaluation refused.
    Evaluation(OverlayEvalFault),
    /// The readback of its weak head refused.
    Readback(ReadbackFault),
}

/// Fuel well above any generated root's evaluation or readback.
///
/// # Specification
/// trivial.
fn ample() -> Fuel
{
    Fuel::from(1_000_000_u32)
}

/// Evaluate `root` under `stance` in an environment of `rigid` rigid
/// variables, and read its weak head back with as many binders open, in a
/// copy of `overlay`, minting into `core`.
///
/// # Specification
/// - requires: `root` is an evaluation root that validates, `core` holds its
///   opaque nodes, and the root reads no binder past `rigid`.
/// - ensures: the term read back in the root's family, in `core`, each rigid
///   variable read back as the index of its binder; or how the run refused.
///   `overlay` is untouched, and `core` only grows. A closed root, `rigid`
///   zero, runs through the evaluators the checker's path installs.
/// - provides: the one run both stances of the agreement property go through,
///   both into one arena, so that the core's syntax comparison reads the two
///   results side by side.
/// - panics: when the root is a type root, which the requirement excludes, or
///   when a rigid variable does not mint.
///
/// # Adequacy
/// - hypothesis: L3 — a valid generated root of either family, closed or under
///   rigid variables. The term read back resolves in `core` in the root's
///   family, and the run under the other stance is compared with it as a tree,
///   or its refusal as a value: a run that read back another root, ran under
///   the other stance, dropped the environment or met a refusal the other run
///   did not changes that comparison.
/// - witness: `tests::duplication::spinal_evaluation_agrees_with_the_copying_stance`
#[spec(
        requires: matches!(root, OverlayId::Value(_) | OverlayId::Computation(_)) && overlay.validate(root).is_ok(),
        ensures: |ret| ret.as_ref().map_or(true, |&read| match (root, read) {
            (OverlayId::Value(_), Term::Value(id)) => core.value(id).is_some(),
            (OverlayId::Computation(_), Term::Computation(id)) => core.computation(id).is_some(),
            _ => false,
        })
    )]
fn evaluated(
    stance: DuplicationStance,
    overlay: &Overlay,
    core: &mut CoreArena,
    root: OverlayId,
    rigid: u32,
) -> Result<Term, Refused>
{
    let mut overlay = overlay.clone();
    let chain = LoweredChain::new();
    let definitional = DefinitionalEnvironment::new();
    let definitions = Definitions::new(&chain, &definitional, definitional.root());
    let mut domain = DomainArena::new();
    let mut environment = Environment::new();
    for level in 0 .. rigid {
        let neutral = domain
            .neutral_node(
                NeutralHead::Variable {
                    zone: Zone::Intuitionistic,
                    level: BinderLevel::from(level),
                },
                Vec::new(),
                Unfolding::Rigid,
            )
            .expect("a variable head mints rigid");
        let bound = domain
            .value_neutral(neutral, TermFace::Reduced)
            .expect("a spineless neutral stands in a value position");
        environment.extend(Zone::Intuitionistic, bound);
    }
    let mut log = TraceLog::new();
    let installed = TracedDuplication::install(stance, &mut log)
        .expect("a recording sink carries either stance");
    let mode = ReadbackMode::Unfolding;
    let read = match (root, rigid) {
        (OverlayId::Value(id), 0) => {
            let (head, _) = installed
                .eval_overlay_value(&mut overlay, core, &mut domain, definitions, ample(), id)
                .map_err(Refused::Evaluation)?;
            Term::Value(
                readback_value(core, &mut domain, definitions, mode, ample(), head)
                    .map_err(Refused::Readback)?,
            )
        },
        (OverlayId::Value(id), _) => {
            let (head, _) = installed
                .eval_overlay_value_within(
                    &mut overlay,
                    core,
                    &mut domain,
                    definitions,
                    ample(),
                    id,
                    environment.clone(),
                )
                .map_err(Refused::Evaluation)?;
            Term::Value(
                readback_value_within(
                    core,
                    &mut domain,
                    definitions,
                    mode,
                    ample(),
                    head,
                    &environment,
                )
                .map_err(Refused::Readback)?,
            )
        },
        (OverlayId::Computation(id), 0) => {
            let (head, _) = installed
                .eval_overlay_computation(&mut overlay, core, &mut domain, definitions, ample(), id)
                .map_err(Refused::Evaluation)?;
            Term::Computation(
                readback_computation(core, &mut domain, definitions, mode, ample(), head)
                    .map_err(Refused::Readback)?,
            )
        },
        (OverlayId::Computation(id), _) => {
            let (head, _) = installed
                .eval_overlay_computation_within(
                    &mut overlay,
                    core,
                    &mut domain,
                    definitions,
                    ample(),
                    id,
                    environment.clone(),
                )
                .map_err(Refused::Evaluation)?;
            Term::Computation(
                readback_computation_within(
                    core,
                    &mut domain,
                    definitions,
                    mode,
                    ample(),
                    head,
                    &environment,
                )
                .map_err(Refused::Readback)?,
            )
        },
        (OverlayId::ValueType(_) | OverlayId::CompType(_), _) => {
            panic!("the property generates evaluation roots")
        },
    };
    Ok(read)
}

/// Whether `left` and `right`, both in `core`, are one tree, by the core's own
/// syntax comparison: every former, leaf and child agrees, path evidence
/// aside. It reads every former of the full alphabet, and shares no code with
/// duplication, erasure or the machine. A computation is compared as its
/// thunk.
///
/// # Specification
/// trivial.
fn one_tree(
    core: &mut CoreArena,
    left: Term,
    right: Term,
) -> bool
{
    let (left, right) = match (left, right) {
        (Term::Value(left), Term::Value(right)) => (left, right),
        (Term::Computation(left), Term::Computation(right)) => {
            (core.value_thunk(left), core.value_thunk(right))
        },
        _ => return false,
    };
    equal_certificate_syntax(core, left, right) == CertificateEquality::Equal
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

/// `share f = thunk (λ. b) in (x ← force f ⟨⟩; y ← force f (⟨⟩, ⟨⟩); return
/// (x, y))`, with `b` a computation generated from `seeded` under one binder:
/// each share inside `b` whose leg reads that binder is evaluated under two
/// bindings of it.
///
/// # Specification
/// - requires: nothing.
/// - ensures: a computation overlay that validates from the returned root, its
///   root an arity-two share whose leg is a thunked abstraction, with the
///   census of its generated body.
/// - provides: the open configurations the agreement property reads.
/// - panics: when a mint is refused, which a plan this small never provokes.
///
/// # Adequacy
/// - hypothesis: L3 — any seed. The root validates as an arity-two share of a
///   thunked abstraction. Keying a remembered leg by the leg alone, ignoring
///   its binding, makes the second application read the first's evaluation,
///   which the agreement property's tree comparison sees.
/// - witness: `tests::duplication::spinal_evaluation_agrees_with_the_copying_stance`
#[spec(
        ensures: |ret| ret.0.validate(ret.1).is_ok() && matches!(ret.1, OverlayId::Computation(_))
    )]
fn applied_twice(
    seeded: &mut Seeded,
    core: &mut CoreArena,
) -> (Overlay, OverlayId, Census)
{
    let (mut overlay, body, census) = counted(seeded, core, Family::Computation, Binders(1));
    let OverlayId::Computation(body) = body
    else {
        panic!("a computation body was asked for");
    };
    let lambda = computation(&mut overlay, CompNode::Grafted(CompGraft::Lambda(body)));
    let leg = value(&mut overlay, ValueNode::Grafted(ValueGraft::Thunk(lambda)));
    let first = occurrence(&mut overlay, SharePosition::from(0_u32));
    let forced = computation(&mut overlay, CompNode::Grafted(CompGraft::Force(first)));
    let unit = value(&mut overlay, ValueNode::Grafted(ValueGraft::Unit));
    let applied = computation(
        &mut overlay,
        CompNode::Grafted(CompGraft::Application(forced, unit)),
    );
    let second = occurrence(&mut overlay, SharePosition::from(1_u32));
    let forced = computation(&mut overlay, CompNode::Grafted(CompGraft::Force(second)));
    let left = value(&mut overlay, ValueNode::Grafted(ValueGraft::Unit));
    let right = value(&mut overlay, ValueNode::Grafted(ValueGraft::Unit));
    let units = value(
        &mut overlay,
        ValueNode::Grafted(ValueGraft::Pair(left, right)),
    );
    let applied_again = computation(
        &mut overlay,
        CompNode::Grafted(CompGraft::Application(forced, units)),
    );
    let variable = |index: u32| {
        ValueNode::Grafted(ValueGraft::Variable {
            zone: Zone::Intuitionistic,
            index: DeBruijnIndex::from(index),
        })
    };
    let x = value(&mut overlay, variable(1));
    let y = value(&mut overlay, variable(0));
    let both = value(&mut overlay, ValueNode::Grafted(ValueGraft::Pair(x, y)));
    let returned = computation(&mut overlay, CompNode::Grafted(CompGraft::Return(both)));
    let rest = computation(
        &mut overlay,
        CompNode::Grafted(CompGraft::Bind(applied_again, returned)),
    );
    let chain = computation(
        &mut overlay,
        CompNode::Grafted(CompGraft::Bind(applied, rest)),
    );
    let root = OverlayId::Computation(computation(
        &mut overlay,
        CompNode::Shared(Sharing {
            arity: ShareArity::from(2_u32),
            leg: OverlayId::Value(leg),
            body: chain,
        }),
    ));
    overlay.validate(root).expect("the wrapper validates");
    (overlay, root, census)
}

/// One closed argument of the applied root, drawn from `seeded`, with its
/// name in [`ARGUMENTS`].
///
/// # Specification
/// trivial.
fn argument(
    seeded: &mut Seeded,
    core: &mut CoreArena,
) -> (&'static str, ValueId)
{
    let at = seeded.pick(&[0_usize, 1, 2, 3, 4, 5, 6, 7]);
    let unit = core.value_unit();
    let built = match at {
        0 => unit,
        1 => {
            let other = core.value_unit();
            core.value_tuple(&[unit, other])
        },
        2 => core.value_injection(Summand::from(0_usize), unit),
        3 => core.value_injection(Summand::from(1_usize), unit),
        4 => core.value_record(BTreeMap::from([(
            FieldLabel::from(String::from("a")),
            unit,
        )])),
        5 => {
            let nil = core.value_list_nil();
            core.value_list_cons(unit, nil)
        },
        6 => {
            let bound = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
            let returned = core.computation_return(bound);
            let lambda = core.computation_lambda(returned);
            core.value_thunk(lambda)
        },
        _ => core.value_constant(ConstantIndex::from(2_usize)),
    };
    (ARGUMENTS[at], built)
}

/// `(λ⁸. b) a₀ … a₇`, with `b` a computation generated from `seeded` under
/// [`OPENED`] binders and each argument a closed value drawn from
/// [`ARGUMENTS`]. Each leaf of the full alphabet reads its free indices as
/// those arguments, so the stuck links, cases, records and words compute.
///
/// # Specification
/// - requires: nothing.
/// - ensures: a computation overlay that validates from the returned root, with
///   the census of its body, its abstractions and its arguments.
/// - provides: the closed configurations over the full alphabet that the
///   agreement property reads.
/// - panics: when a mint is refused, which a plan this small never provokes.
///
/// # Adequacy
/// - hypothesis: L3 — any seed. The root validates as a computation, and each
///   row of the full alphabet stands under enough binders. A share whose leg
///   reads an argument is evaluated in the configuration the arguments make. A
///   run that remembers it under another configuration changes the tree the
///   property compares.
/// - witness: `tests::duplication::spinal_evaluation_agrees_with_the_copying_stance`
/// - witness: `tests::duplication::the_property_draws_its_whole_alphabet`
#[spec(
        ensures: |ret| ret.0.validate(ret.1).is_ok() && matches!(ret.1, OverlayId::Computation(_))
    )]
fn applied_to_arguments(
    seeded: &mut Seeded,
    core: &mut CoreArena,
) -> (Overlay, OverlayId, Census)
{
    let (mut overlay, body, mut census) =
        counted(seeded, core, Family::Computation, Binders(OPENED));
    let OverlayId::Computation(mut head) = body
    else {
        panic!("a computation body was asked for");
    };
    for _ in 0 .. OPENED {
        head = computation(&mut overlay, CompNode::Grafted(CompGraft::Lambda(head)));
        counted_once(&mut census, "grafted λ");
    }
    for _ in 0 .. OPENED {
        let (name, argument) = argument(seeded, core);
        counted_once(&mut census, name);
        let argument = value(&mut overlay, ValueNode::Opaque(argument));
        head = computation(
            &mut overlay,
            CompNode::Grafted(CompGraft::Application(head, argument)),
        );
        counted_once(&mut census, "grafted application");
    }
    let root = OverlayId::Computation(head);
    overlay.validate(root).expect("the applied root validates");
    (overlay, root, census)
}

/// One root the agreement property runs, with the arena its opaque nodes
/// name.
struct Root
{
    /// The shape the root comes from.
    shape: &'static str,
    /// The arena its opaque nodes name.
    core: CoreArena,
    /// The overlay.
    overlay: Overlay,
    /// The root.
    root: OverlayId,
    /// The rigid variables it is evaluated under: none for a closed root.
    rigid: u32,
}

/// Add each count of `from` into `into`.
///
/// # Specification
/// trivial.
fn merged(
    into: &mut Census,
    from: Census,
)
{
    for (name, count) in from {
        let total = into.entry(name).or_insert(0);
        *total = total.saturating_add(count);
    }
}

/// The roots the agreement property runs for `seed`, with the census of what
/// they hold: a closed root, an open body applied under two bindings of its
/// binder, a body over the full alphabet applied to eight closed arguments, a
/// body over the full alphabet under eight rigid variables, and the
/// compilations of the erasures of the closed root and of the root under
/// rigid variables.
///
/// # Specification
/// trivial.
fn roots(seed: u64) -> ([Root; 6], Census)
{
    let mut seeded = Seeded(seed);
    let family = seeded.pick(&[Family::Value, Family::Computation]);
    let mut census = Census::new();
    let mut closed_core = CoreArena::new();
    let (closed, closed_root, drawn) = counted(&mut seeded, &mut closed_core, family, Binders(0));
    merged(&mut census, drawn);
    let mut twice_core = CoreArena::new();
    let (twice, twice_root, drawn) = applied_twice(&mut seeded, &mut twice_core);
    merged(&mut census, drawn);
    let mut applied_core = CoreArena::new();
    let (applied, applied_root, drawn) = applied_to_arguments(&mut seeded, &mut applied_core);
    merged(&mut census, drawn);
    let mut open_core = CoreArena::new();
    let (open, open_root, drawn) = counted(&mut seeded, &mut open_core, family, Binders(OPENED));
    merged(&mut census, drawn);
    let (closed_compiled_core, _, closed_compiled, closed_compiled_root) =
        compiled(&closed, &closed_core, closed_root);
    let (open_compiled_core, _, open_compiled, open_compiled_root) =
        compiled(&open, &open_core, open_root);
    let roots = [
        Root {
            shape: "closed",
            core: closed_core,
            overlay: closed,
            root: closed_root,
            rigid: 0,
        },
        Root {
            shape: "applied twice",
            core: twice_core,
            overlay: twice,
            root: twice_root,
            rigid: 0,
        },
        Root {
            shape: "applied to eight arguments",
            core: applied_core,
            overlay: applied,
            root: applied_root,
            rigid: 0,
        },
        Root {
            shape: "under eight rigid variables",
            core: open_core,
            overlay: open,
            root: open_root,
            rigid: OPENED,
        },
        Root {
            shape: "compiled from the erasure of the closed root",
            core: closed_compiled_core,
            overlay: closed_compiled,
            root: closed_compiled_root,
            rigid: 0,
        },
        Root {
            shape: "compiled from the erasure of the root under rigid variables",
            core: open_compiled_core,
            overlay: open_compiled,
            root: open_compiled_root,
            rigid: OPENED,
        },
    ];
    (roots, census)
}

/// The term `root` erases to in a copy of `core`, compiled back into a fresh
/// overlay: the shape that the checker's path hands a stance.
///
/// # Specification
/// - requires: `root` is an evaluation root that validates, and `core` holds
///   its opaque nodes.
/// - ensures: the copy of `core` with the erasure in it, the erasure, and the
///   overlay and root its compilation mints.
/// - provides: the compiled roots of the agreement property and of the
///   compilation's round trip.
/// - panics: when the erasure does not compile, which the round trip test
///   reports as the defect it is.
///
/// # Adequacy
/// - hypothesis: L3 — any generated root. Its erasure shares each leg, so the
///   compilation meets nodes reached more than once; a compilation that loses a
///   share or grafts a former erasure does not invert changes the round trip
///   and the agreement over the compiled roots.
/// - witness: `tests::duplication::a_compiled_erasure_erases_to_itself`
/// - witness: `tests::duplication::spinal_evaluation_agrees_with_the_copying_stance`
#[spec(
        requires: matches!(root, OverlayId::Value(_) | OverlayId::Computation(_)) && overlay.validate(root).is_ok(),
        ensures: |ret| matches!((ret.1, ret.3), (Term::Value(_), OverlayId::Value(_)) | (Term::Computation(_), OverlayId::Computation(_)))
    )]
fn compiled(
    overlay: &Overlay,
    core: &CoreArena,
    root: OverlayId,
) -> (CoreArena, Term, Overlay, OverlayId)
{
    let mut arena = core.clone();
    let term = erased(overlay, root, &mut arena);
    let mut compiled = Overlay::new();
    let root = match term {
        Term::Value(id) => {
            OverlayId::Value(compile_value(&mut compiled, &arena, id).expect("an erasure compiles"))
        },
        Term::Computation(id) => OverlayId::Computation(
            compile_computation(&mut compiled, &arena, id).expect("an erasure compiles"),
        ),
        Term::ValueType(_) | Term::CompType(_) => panic!("an evaluation root erases to a term"),
    };
    (arena, term, compiled, root)
}

/// How many distinct nodes of `core` `root` reaches, of every family.
///
/// # Specification
/// trivial.
fn distinct(
    core: &CoreArena,
    root: Term,
) -> usize
{
    /// The children of one node, pushed for the walk.
    struct Pending(Vec<Term>);
    impl children::Visit for Pending
    {
        fn value(
            &mut self,
            child: ValueId,
            _crossing: Crossing,
        )
        {
            self.0.push(Term::Value(child));
        }

        fn computation(
            &mut self,
            child: ComputationId,
            _crossing: Crossing,
        )
        {
            self.0.push(Term::Computation(child));
        }

        fn value_type(
            &mut self,
            child: ValueTypeId,
            _crossing: Crossing,
        )
        {
            self.0.push(Term::ValueType(child));
        }

        fn comp_type(
            &mut self,
            child: CompTypeId,
            _crossing: Crossing,
        )
        {
            self.0.push(Term::CompType(child));
        }
    }
    let mut seen = BTreeSet::new();
    let mut pending = Pending(Vec::from([root]));
    while let Some(node) = pending.0.pop() {
        if !seen.insert(node) {
            continue;
        }
        match node {
            Term::Value(id) => {
                if let Some(value) = core.value(id) {
                    children::of_value(value, &mut pending);
                }
            },
            Term::Computation(id) => {
                if let Some(computation) = core.computation(id) {
                    children::of_computation(computation, &mut pending);
                }
            },
            Term::ValueType(id) => {
                if let Some(value_type) = core.value_type(id) {
                    children::of_value_type(value_type, &mut pending);
                }
            },
            Term::CompType(id) => {
                if let Some(comp_type) = core.comp_type(id) {
                    children::of_comp_type(comp_type, &mut pending);
                }
            },
        }
    }
    seen.len()
}

/// The alphabet the agreement property declares: the grafted formers, shares
/// and occurrences, the leaves the generator mints, each row of the
/// free-index table that reads no linear slot, the stuck links, and the
/// arguments of the applied root.
///
/// # Specification
/// trivial.
fn alphabet() -> BTreeSet<&'static str>
{
    let rows = values()
        .into_iter()
        .chain(types())
        .chain(computations())
        .filter(|row| row.linear.is_empty() && row.consumed.is_empty())
        .map(|row| row.what);
    GRAFTED
        .into_iter()
        .chain(MINTED)
        .chain(rows)
        .chain([STUCK_LINK, BIND_OVER_STUCK_LINK])
        .chain(ARGUMENTS)
        .collect()
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
///   exceeds a counter. A bounded descent requires an arity-two share, ordered
///   positions zero and one and a unit at exactly the requested depth. The
///   refusal witness distinguishes an exponential-copy preflight failure from a
///   partial overlay mutation.
/// - witness: `tests::duplication::a_refused_duplication_leaves_the_overlay_as_it_found_it`
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
        let (mut overlay, root) = generated(&mut seeded, &mut core, family, Binders(0));
        for stance in [DuplicationStance::EraseAndClone, DuplicationStance::Spinal] {
            let mut log = TraceLog::new();
            let installed = TracedDuplication::install(stance, &mut log)
                .expect("a recording sink carries either stance");
            let rebuilt = match root {
                OverlayId::Value(id) => installed
                    .duplicate_value(&mut overlay, &core, id)
                    .map(OverlayId::Value),
                OverlayId::Computation(id) => installed
                    .duplicate_computation(&mut overlay, &core, id)
                    .map(OverlayId::Computation),
                OverlayId::ValueType(_) | OverlayId::CompType(_) => {
                    panic!("the property generates evaluation roots")
                },
            }
            .unwrap_or_else(|fault| panic!("case {case} under {stance:?}: {fault:?}"));
            let mut erasures = core.clone();
            let before = erased(&overlay, root, &mut erasures);
            let after = erased(&overlay, rebuilt, &mut erasures);
            assert!(
                one_tree(&mut erasures, before, after),
                "case {case} under {stance:?}: the duplicate erases to another tree"
            );
        }
    }
}

proptest! {
    // About one root in seventy evaluates an open leg under two bindings, so
    // every run reaches one.
    #![proptest_config(ProptestConfig::with_cases(SEEDS))]

    /// Over generated overlay roots, a spinal run reads back as the copying
    /// stance's run, or refuses as it does: a closed root, an open body
    /// applied under two bindings of its binder, a body over the full alphabet
    /// applied to eight closed arguments, a body over the full alphabet under
    /// eight rigid variables, and the compilations of two erasures.
    #[test]
    fn spinal_evaluation_agrees_with_the_copying_stance(seed in 1_u64 ..)
    {
        let (roots, _) = roots(seed);
        for Root { shape, core, overlay, root, rigid } in roots {
            let mut arena = core;
            let reference = evaluated(DuplicationStance::EraseAndClone, &overlay, &mut arena, root, rigid);
            let spinal = evaluated(DuplicationStance::Spinal, &overlay, &mut arena, root, rigid);
            let agreed = match (reference.as_ref(), spinal.as_ref()) {
                (Ok(expected), Ok(read)) => one_tree(&mut arena, *read, *expected),
                (Err(expected), Err(refused)) => expected == refused,
                (Ok(_), Err(_)) | (Err(_), Ok(_)) => false,
            };
            prop_assert!(
                agreed,
                "seed {seed}, the {shape} root: the copying stance gave {:?}, the spinal stance {:?}",
                reference,
                spinal
            );
        }
    }
}

/// Over as many seeds as the agreement property runs, the generator draws
/// exactly the alphabet it declares: each grafted former, each share and
/// occurrence, and each opaque leaf of the full alphabet, and nothing else.
#[test]
fn the_property_draws_its_whole_alphabet()
{
    let mut census = Census::new();
    for seed in 1 ..= u64::from(SEEDS) {
        let (_, drawn) = roots(seed);
        merged(&mut census, drawn);
    }
    let drawn: BTreeSet<&str> = census.keys().copied().collect();
    assert_eq!(
        drawn,
        alphabet(),
        "over {SEEDS} seeds the property draws {census:#?}"
    );
}

#[test]
fn a_copying_duplicate_is_the_expansion()
{
    let mut seeded = Seeded(0x2545_F491_4F6C_DD1D);
    for case in 0 .. CASES {
        let family = seeded.pick(&[Family::Value, Family::Computation]);
        let mut core = CoreArena::new();
        let (mut overlay, root) = generated(&mut seeded, &mut core, family, Binders(0));
        let input = measured(&overlay, root);
        let policy = DuplicationPolicy::default();
        let rebuilt = match root {
            OverlayId::Value(id) => {
                duplicate_value(&mut overlay, &core, policy, id).map(OverlayId::Value)
            },
            OverlayId::Computation(id) => {
                duplicate_computation(&mut overlay, &core, policy, id).map(OverlayId::Computation)
            },
            OverlayId::ValueType(_) | OverlayId::CompType(_) => {
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
    let Some(&ValueNode::Grafted(ValueGraft::Pair(rib_first, rib_second))) = overlay.value(shared)
    else {
        panic!("the rib share's leg is the pair of units");
    };
    for unit in [rib_first, rib_second] {
        assert!(matches!(
            overlay.value(unit),
            Some(&ValueNode::Grafted(ValueGraft::Unit))
        ));
    }
    let Some(&ValueNode::Grafted(ValueGraft::Pair(left_copy, right_copy))) = overlay.value(copies)
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
        let Some(&CompNode::Grafted(CompGraft::Return(returned))) = overlay.computation(returner)
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

/// The erasure of each root the agreement property runs compiles back into an
/// overlay root that validates and erases to the same term, node for node.
#[test]
fn a_compiled_erasure_erases_to_itself()
{
    for seed in 1 ..= u64::from(SEEDS) {
        let (roots, _) = roots(seed);
        for Root {
            shape,
            core,
            overlay,
            root,
            ..
        } in roots
        {
            let (mut arena, erasure, compiled, compiled_root) = compiled(&overlay, &core, root);
            assert_eq!(
                Ok(()),
                compiled.validate(compiled_root),
                "seed {seed}, the {shape} root: the compilation validates"
            );
            let again = erased(&compiled, compiled_root, &mut arena);
            assert!(
                one_tree(&mut arena, erasure, again),
                "seed {seed}, the {shape} root: the compilation erases to another tree"
            );
            assert_eq!(
                distinct(&arena, erasure),
                distinct(&arena, again),
                "seed {seed}, the {shape} root: the compilation erases to another graph"
            );
        }
    }
}
