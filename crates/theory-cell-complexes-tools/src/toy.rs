//! The toy alphabet: a single-sorted first-order term language — `Zero`,
//! `Succ`, `Add` and metavariables — inhabiting [`CellAlphabet`] from outside
//! the substrate, the path every later alphabet takes.
//!
//! Every subterm is a command, so a law about a position below the root can be
//! exercised at all. Each term is one flat table in prefix order, every node
//! followed by its children's ranges, so no term routes ownership through
//! itself and no walk over one recurses.

use alloc::boxed::Box;
use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use alloc::collections::VecDeque;
use alloc::string::String;
use alloc::vec::Vec;

use gandr_theory_cell_complexes::Cell;
use gandr_theory_cell_complexes::CellAlphabet;
use gandr_theory_cell_complexes::CellInvertibility;
use gandr_theory_cell_complexes::CellStore;
use gandr_theory_cell_complexes::CommandSpliceRefusal;
use gandr_theory_cell_complexes::ConvexityDischarge;
use gandr_theory_cell_complexes::FiringPermission;
use gandr_theory_cell_complexes::PositionOrder;
use gandr_theory_cell_complexes::PositionStep;
use gandr_theory_cell_complexes::SeamRole;
use gandr_theory_cell_complexes::SubstitutionDecision;
use gandr_theory_cell_complexes::command_subterm;
use gandr_theory_cell_complexes::path_order;
use quenchant_shape::shape::Maybe;

/// The toy alphabet marker.
///
/// # Specification
/// - ensures: the implementation keeps the three inhabitant laws an engine
///   spends: substituting a match into its pattern reproduces the matched term,
///   a successful match binds every metavariable the pattern names, and
///   splicing at a position agrees with reading there, both ways.
/// - provides: terms that nest commands, so every subterm is a command position
///   and a splice below the root is exercised.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — each law is asserted pointwise on terms that bind
///   distinct, repeated and target-carried metavariables, and at every position
///   of a term nesting commands two deep.
/// - witness: `tests::inhabitant::matching_then_substituting_returns_the_matched_term`
/// - witness: `tests::inhabitant::a_successful_match_binds_every_metavariable_the_pattern_names`
/// - witness: `tests::inhabitant::splicing_at_a_position_agrees_with_reading_it`
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ToyAlphabet;

/// A toy metavariable name.
#[repr(transparent)]
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ToyVar(Box<str>);

impl ToyVar
{
    /// The name with one prime appended.
    ///
    /// # Specification
    /// trivial.
    fn primed(&self) -> Self
    {
        let mut primed = String::with_capacity(self.0.len().saturating_add(1));
        primed.push_str(&self.0);
        primed.push('\'');
        Self(primed.into_boxed_str())
    }
}

impl From<&str> for ToyVar
{
    /// A metavariable spelled by the name.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: &str) -> Self
    {
        Self(value.into())
    }
}

/// One node of a toy term.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
enum ToyHead
{
    /// A metavariable leaf.
    Var(ToyVar),
    /// A skolem constant leaf: irreducible.
    Konst(ToyVar),
    /// The nullary constructor.
    Zero,
    /// The unary constructor.
    Succ,
    /// The binary operation.
    Add,
}

impl ToyHead
{
    /// The node's number of children.
    ///
    /// # Specification
    /// trivial.
    const fn arity(&self) -> ToyCount
    {
        match *self {
            | Self::Var(_) | Self::Konst(_) | Self::Zero => ToyCount(0),
            | Self::Succ => ToyCount(1),
            | Self::Add => ToyCount(2),
        }
    }
}

/// A count or an index within one toy table.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct ToyCount(usize);

impl ToyCount
{
    /// The next index.
    ///
    /// # Specification
    /// - ensures: one more than `self`; a table held in memory never reaches
    ///   the saturation bound.
    /// - panics: none.
    const fn next(self) -> Self
    {
        Self(self.0.saturating_add(1))
    }
}

/// A toy term: its nodes in prefix order.
#[repr(transparent)]
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct Toy(Vec<ToyHead>);

impl Toy
{
    /// A metavariable leaf.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn var<N>(name: N) -> Self
    where
        N: Into<ToyVar>,
    {
        Self(alloc::vec![ToyHead::Var(name.into())])
    }

    /// The nullary constructor.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn zero() -> Self
    {
        Self(alloc::vec![ToyHead::Zero])
    }

    /// The unary constructor applied to `arg`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn succ(arg: Self) -> Self
    {
        let mut nodes = Vec::with_capacity(arg.0.len().saturating_add(1));
        nodes.push(ToyHead::Succ);
        nodes.extend(arg.0);
        Self(nodes)
    }

    /// The binary operation applied to `lhs` and `rhs`.
    ///
    /// # Specification
    /// trivial.
    #[expect(
        clippy::should_implement_trait,
        reason = "builds the `Add` node of a term; terms have no arithmetic for `core::ops::Add` to name"
    )]
    #[inline]
    #[must_use]
    pub fn add(
        lhs: Self,
        rhs: Self,
    ) -> Self
    {
        let mut nodes =
            Vec::with_capacity(lhs.0.len().saturating_add(rhs.0.len()).saturating_add(1));
        nodes.push(ToyHead::Add);
        nodes.extend(lhs.0);
        nodes.extend(rhs.0);
        Self(nodes)
    }

    /// The end of the subterm starting at `start`: one past its last node.
    ///
    /// # Specification
    /// - ensures: the index after the subterm rooted at `start`; the table's
    ///   length when the table is cut short.
    /// - panics: none.
    fn end_of(
        &self,
        start: ToyCount,
    ) -> ToyCount
    {
        let mut pending = ToyCount(1);
        let mut index = start;
        while pending > ToyCount(0) {
            let Some(head) = self.0.get(index.0)
            else {
                break;
            };
            pending = ToyCount(pending.0.saturating_sub(1).saturating_add(head.arity().0));
            index = index.next();
        }
        index
    }

    /// The range of the subterm reached by following `steps` from the root.
    ///
    /// # Specification
    /// - ensures: the start and end of the subterm `steps` reaches.
    /// - provides: [`command_subterm::Absent::OffTerm`] when a step indexes
    ///   past a node's children.
    /// - panics: none.
    fn range_at(
        &self,
        steps: &[PositionStep],
    ) -> Maybe<(ToyCount, ToyCount), command_subterm::Absent>
    {
        let mut start = ToyCount(0);
        for &step in steps {
            let Some(head) = self.0.get(start.0)
            else {
                return Maybe::Absent(command_subterm::Absent::OffTerm);
            };
            let step = ToyCount(usize::from(step));
            if step >= head.arity() {
                return Maybe::Absent(command_subterm::Absent::OffTerm);
            }
            let mut child = start.next();
            for _ in 0 .. step.0 {
                child = self.end_of(child);
            }
            start = child;
        }
        Maybe::Present((start, self.end_of(start)))
    }

    /// The subterm occupying `[start, end)`, owned.
    ///
    /// # Specification
    /// trivial.
    fn slice(
        &self,
        start: ToyCount,
        end: ToyCount,
    ) -> Self
    {
        Self(self.0.iter().take(end.0).skip(start.0).cloned().collect())
    }

    /// The term's metavariables, left to right with repeats.
    ///
    /// # Specification
    /// trivial.
    fn vars(&self) -> impl Iterator<Item = &ToyVar>
    {
        self.0.iter().filter_map(|head| match *head {
            | ToyHead::Var(ref var) => Some(var),
            | ToyHead::Konst(_) | ToyHead::Zero | ToyHead::Succ | ToyHead::Add => None,
        })
    }

    /// The term with every metavariable relabelled by `relabel`, which keeps
    /// every leaf a leaf.
    ///
    /// # Specification
    /// trivial.
    fn relabel<R>(
        &self,
        relabel: R,
    ) -> Self
    where
        R: Fn(&ToyVar) -> ToyHead,
    {
        Self(
            self.0
                .iter()
                .map(|head| match *head {
                    | ToyHead::Var(ref var) => relabel(var),
                    | ToyHead::Konst(_) | ToyHead::Zero | ToyHead::Succ | ToyHead::Add => {
                        head.clone()
                    },
                })
                .collect(),
        )
    }
}

/// A toy position: a path of child indices from the root.
#[repr(transparent)]
#[derive(Clone, Debug, Default, Eq, Hash, PartialEq)]
pub struct ToyPos(Box<[PositionStep]>);

impl ToyPos
{
    /// The child indices from the root outward.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn steps(&self) -> &[PositionStep]
    {
        &self.0
    }
}

/// A toy substitution: an ordered map from metavariables to terms.
#[repr(transparent)]
#[derive(Clone, Debug, Default, Eq, Hash, PartialEq)]
pub struct ToySubst(BTreeMap<ToyVar, Toy>);

impl ToySubst
{
    /// The term with every bound metavariable replaced by its image, once.
    ///
    /// # Specification
    /// trivial.
    fn apply_once(
        &self,
        term: &Toy,
    ) -> Toy
    {
        let mut nodes = Vec::with_capacity(term.0.len());
        for head in &term.0 {
            if let ToyHead::Var(ref var) = *head
                && let Some(image) = self.0.get(var)
            {
                nodes.extend(image.0.iter().cloned());
                continue;
            }
            nodes.push(head.clone());
        }
        Toy(nodes)
    }

    /// The term with the substitution applied to its fixpoint.
    ///
    /// # Specification
    /// - ensures: no bound metavariable remains when the bindings are acyclic;
    ///   at most one pass per binding plus one.
    /// - panics: none.
    fn apply_fully(
        &self,
        term: &Toy,
    ) -> Toy
    {
        let mut current = term.clone();
        for _ in 0 ..= self.0.len() {
            let next = self.apply_once(&current);
            if next == current {
                break;
            }
            current = next;
        }
        current
    }

    /// `term` followed through the bindings while it is a bare bound
    /// metavariable.
    ///
    /// # Specification
    /// - ensures: the first term on the binding chain that is not a bound
    ///   metavariable, or the term reached after one step per binding.
    /// - panics: none.
    fn walk(
        &self,
        term: Toy,
    ) -> Toy
    {
        let mut current = term;
        for _ in 0 ..= self.0.len() {
            let image = match current.0.as_slice() {
                | &[ToyHead::Var(ref var)] => self.0.get(var),
                | _ => None,
            };
            let Some(image) = image
            else {
                break;
            };
            current = image.clone();
        }
        current
    }
}

/// The toy orientation tag.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum ToyOrient
{
    /// Given with the cell.
    Given,
    /// Chosen by the reduction order.
    Derived,
}

/// The toy provenance tag.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum ToyProv
{
    /// A rule cell.
    Rule,
    /// Derived by completion.
    Derived,
}

/// The toy metadata: the metavariables of both faces, in first-occurrence
/// order, and the invertibility a cell was built with.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct ToyMeta
{
    /// The distinct metavariables of both faces.
    vars: Vec<ToyVar>,
    /// Whether the cell is an invertible certificate.
    invertible: CellInvertibility,
}

/// A count of one metavariable's occurrences.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Ord, PartialEq, PartialOrd)]
struct Occurrences(usize);

/// How often each metavariable occurs in a term.
///
/// # Specification
/// trivial.
fn occurrences(term: &Toy) -> BTreeMap<&ToyVar, Occurrences>
{
    let mut counts: BTreeMap<&ToyVar, Occurrences> = BTreeMap::new();
    for var in term.vars() {
        let count = counts.entry(var).or_default();
        count.0 = count.0.saturating_add(1);
    }
    counts
}

/// Whether one side carries every metavariable of the other at least as often.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum HoleDomination
{
    /// Every hole of the smaller side occurs at least as often on the larger.
    Dominates,
    /// Some hole of the smaller side occurs more often than on the larger.
    FallsShort,
}

/// Whether `larger` dominates `smaller` hole by hole.
///
/// # Specification
/// trivial.
fn dominates(
    larger: &BTreeMap<&ToyVar, Occurrences>,
    smaller: &BTreeMap<&ToyVar, Occurrences>,
) -> HoleDomination
{
    if smaller
        .iter()
        .all(|(var, count)| larger.get(var).is_some_and(|held| held >= count))
    {
        return HoleDomination::Dominates;
    }
    HoleDomination::FallsShort
}

impl CellAlphabet for ToyAlphabet
{
    type Cmd = Toy;
    type Hole = ToyVar;
    type Meta = ToyMeta;
    type Orientation = ToyOrient;
    type Pos = ToyPos;
    type Provenance = ToyProv;
    type Subst = ToySubst;
    type Var = ToyVar;

    /// Matching by one lockstep pass over the two prefix tables.
    ///
    /// # Specification
    /// - ensures: each pattern metavariable binds the target subterm at its
    ///   place, a bound one only an equal subterm; every other node must equal
    ///   the target's. `subst` is extended only on success.
    /// - panics: none.
    #[inline]
    fn match_cmd(
        pattern: &Self::Cmd,
        target: &Self::Cmd,
        subst: &mut Self::Subst,
    ) -> SubstitutionDecision
    {
        let mut found = subst.clone();
        let mut at = ToyCount(0);
        for head in &pattern.0 {
            let Some(target_head) = target.0.get(at.0)
            else {
                return SubstitutionDecision::from(false);
            };
            if let ToyHead::Var(ref var) = *head {
                let end = target.end_of(at);
                let image = target.slice(at, end);
                if found.0.get(var).is_some_and(|bound| *bound != image) {
                    return SubstitutionDecision::from(false);
                }
                found.0.insert(var.clone(), image);
                at = end;
                continue;
            }
            if head != target_head {
                return SubstitutionDecision::from(false);
            }
            at = at.next();
        }
        if at != ToyCount(target.0.len()) {
            return SubstitutionDecision::from(false);
        }
        *subst = found;
        SubstitutionDecision::from(true)
    }

    /// Robinson unification over owned subterm pairs.
    ///
    /// # Specification
    /// - ensures: a most general unifier extending `subst` on success, with the
    ///   occurs check; `subst` is extended only on success.
    /// - panics: none.
    #[inline]
    fn unify_cmd(
        lhs: &Self::Cmd,
        rhs: &Self::Cmd,
        subst: &mut Self::Subst,
    ) -> SubstitutionDecision
    {
        let mut found = subst.clone();
        let mut goals = alloc::vec![(lhs.clone(), rhs.clone())];
        while let Some((left, right)) = goals.pop() {
            let left = found.walk(left);
            let right = found.walk(right);
            let (var, image) = match (left.0.as_slice(), right.0.as_slice()) {
                | (&[ToyHead::Var(ref x)], &[ToyHead::Var(ref y)]) if x == y => continue,
                | (&[ToyHead::Var(ref var)], _) => (var.clone(), right.clone()),
                | (_, &[ToyHead::Var(ref var)]) => (var.clone(), left.clone()),
                | (&[ref left_head, ..], &[ref right_head, ..]) if left_head == right_head => {
                    let mut left_child = ToyCount(1);
                    let mut right_child = ToyCount(1);
                    for _ in 0 .. left_head.arity().0 {
                        let left_end = left.end_of(left_child);
                        let right_end = right.end_of(right_child);
                        goals.push((
                            left.slice(left_child, left_end),
                            right.slice(right_child, right_end),
                        ));
                        left_child = left_end;
                        right_child = right_end;
                    }
                    continue;
                },
                | _ => return SubstitutionDecision::from(false),
            };
            if found
                .apply_fully(&image)
                .vars()
                .any(|occurring| *occurring == var)
            {
                return SubstitutionDecision::from(false);
            }
            found.0.insert(var, image);
        }
        *subst = found;
        SubstitutionDecision::from(true)
    }

    /// The term with the substitution applied to its fixpoint.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn apply_subst(
        subst: &Self::Subst,
        cmd: &Self::Cmd,
    ) -> Self::Cmd
    {
        subst.apply_fully(cmd)
    }

    /// The term's metavariables, left to right with repeats.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn metavariables(cmd: &Self::Cmd) -> Vec<Self::Var>
    {
        cmd.vars().cloned().collect()
    }

    /// Every position of the term, breadth first: every subterm is a command.
    ///
    /// # Specification
    /// - ensures: one position per node, the root first and no position before
    ///   one enclosing it.
    /// - panics: none.
    #[inline]
    fn command_positions(cmd: &Self::Cmd) -> Vec<Self::Pos>
    {
        let mut positions = Vec::with_capacity(cmd.0.len());
        let mut queue: VecDeque<(Vec<PositionStep>, ToyCount)> = VecDeque::new();
        queue.push_back((Vec::new(), ToyCount(0)));
        while let Some((path, start)) = queue.pop_front() {
            let Some(head) = cmd.0.get(start.0)
            else {
                continue;
            };
            let mut child = start.next();
            for index in 0 .. head.arity().0 {
                let mut child_path = path.clone();
                child_path.push(PositionStep::from(index));
                queue.push_back((child_path, child));
                child = cmd.end_of(child);
            }
            positions.push(ToyPos(path.into_boxed_slice()));
        }
        positions
    }

    /// The empty path.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn root_position() -> Self::Pos
    {
        ToyPos::default()
    }

    /// The position of `path`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn position_at_path(path: &[PositionStep]) -> Self::Pos
    {
        ToyPos(path.into())
    }

    /// The path order of the two paths.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn position_order(
        left: &Self::Pos,
        right: &Self::Pos,
    ) -> PositionOrder
    {
        path_order(left.0.iter().copied(), right.0.iter().copied())
    }

    /// Discharged: left-hand sides are trees rooted at one node and targets are
    /// trees.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn convexity_discharge(_store: &CellStore<Self>) -> ConvexityDischarge
    {
        ConvexityDischarge::StronglyConnectedOverAcyclicTarget
    }

    /// The subterm at `pos`, owned.
    ///
    /// # Specification
    /// - ensures: the subterm `pos` addresses; every subterm is a command.
    /// - provides: [`command_subterm::Absent::OffTerm`] when a step of `pos`
    ///   indexes past a node's children.
    /// - panics: none.
    #[inline]
    fn subterm_cmd_at(
        cmd: &Self::Cmd,
        pos: &Self::Pos,
    ) -> Maybe<Self::Cmd, command_subterm::Absent>
    {
        cmd.range_at(&pos.0)
            .map(|(start, end)| cmd.slice(start, end))
    }

    /// `cmd` with the subterm at `pos` replaced.
    ///
    /// # Specification
    /// - ensures: the term equal to `cmd` except at `pos`, which holds
    ///   `replacement`.
    /// - fails: [`CommandSpliceRefusal::OffTerm`] when a step of `pos` indexes
    ///   past a node's children.
    /// - panics: none.
    ///
    /// # Errors
    /// As the failure clause states.
    #[inline]
    fn splice_cmd_at(
        cmd: &Self::Cmd,
        pos: &Self::Pos,
        replacement: Self::Cmd,
    ) -> Result<Self::Cmd, CommandSpliceRefusal>
    {
        let (start, end) = match cmd.range_at(&pos.0) {
            | Maybe::Present(range) => range,
            | Maybe::Absent(command_subterm::Absent::OffTerm) => {
                return Err(CommandSpliceRefusal::OffTerm);
            },
            | Maybe::Absent(command_subterm::Absent::NotACommand) => {
                return Err(CommandSpliceRefusal::NotACommand);
            },
        };
        let mut nodes: Vec<ToyHead> = Vec::with_capacity(
            cmd.0
                .len()
                .saturating_sub(end.0.saturating_sub(start.0))
                .saturating_add(replacement.0.len()),
        );
        nodes.extend(cmd.0.iter().take(start.0).cloned());
        nodes.extend(replacement.0);
        nodes.extend(cmd.0.iter().skip(end.0).cloned());
        Ok(Toy(nodes))
    }

    /// Size guarded by hole domination; a tie or an unlicensed difference is
    /// an obstruction.
    ///
    /// # Specification
    /// - ensures: the larger table wins when it carries every hole of the
    ///   smaller at least as often; every other pair is
    ///   [`core::cmp::Ordering::Equal`].
    /// - panics: none.
    #[inline]
    fn reduction_cmp(
        lhs: &Self::Cmd,
        rhs: &Self::Cmd,
    ) -> core::cmp::Ordering
    {
        let (left, right) = (occurrences(lhs), occurrences(rhs));
        match lhs.0.len().cmp(&rhs.0.len()) {
            | core::cmp::Ordering::Greater
                if dominates(&left, &right) == HoleDomination::Dominates =>
            {
                core::cmp::Ordering::Greater
            },
            | core::cmp::Ordering::Less if dominates(&right, &left) == HoleDomination::Dominates => {
                core::cmp::Ordering::Less
            },
            | core::cmp::Ordering::Greater
            | core::cmp::Ordering::Less
            | core::cmp::Ordering::Equal => core::cmp::Ordering::Equal,
        }
    }

    /// The renamed faces with each name primed apart from the anchor's.
    ///
    /// # Specification
    /// - ensures: every metavariable of `renamed` replaced by itself primed
    ///   until it is absent from `anchor` and from the other fresh names;
    ///   shapes kept, and a cell already apart returned unchanged.
    /// - panics: none.
    #[inline]
    fn rename_apart(
        anchor: (&Self::Cmd, &Self::Cmd),
        renamed: (&Self::Cmd, &Self::Cmd),
    ) -> (Self::Cmd, Self::Cmd)
    {
        let mut taken: BTreeSet<ToyVar> = anchor.0.vars().chain(anchor.1.vars()).cloned().collect();
        let mut fresh: BTreeMap<ToyVar, ToyVar> = BTreeMap::new();
        for var in renamed.0.vars().chain(renamed.1.vars()) {
            if fresh.contains_key(var) {
                continue;
            }
            let mut name = var.clone();
            while taken.contains(&name) {
                name = name.primed();
            }
            taken.insert(name.clone());
            fresh.insert(var.clone(), name);
        }
        // Every metavariable of both renamed faces was given a fresh name
        // above, so the fallback to the original name is never taken.
        let relabel =
            |var: &ToyVar| ToyHead::Var(fresh.get(var).cloned().unwrap_or_else(|| var.clone()));
        (renamed.0.relabel(relabel), renamed.1.relabel(relabel))
    }

    /// Every metavariable replaced by its constant.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn skolemize(cmd: &Self::Cmd) -> Self::Cmd
    {
        cmd.relabel(|var| ToyHead::Konst(var.clone()))
    }

    /// A metavariable is its own hole.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn hole_of(var: &Self::Var) -> Self::Hole
    {
        var.clone()
    }

    /// Positive for the derived provenance.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn completion_certificate(provenance: &Self::Provenance) -> CellInvertibility
    {
        CellInvertibility::from(matches!(*provenance, ToyProv::Derived))
    }

    /// The distinct metavariables of both faces.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn derive_meta(
        lhs: &Self::Cmd,
        rhs: &Self::Cmd,
        invertible: CellInvertibility,
    ) -> Self::Meta
    {
        let mut vars: Vec<ToyVar> = Vec::new();
        for var in lhs.vars().chain(rhs.vars()) {
            if !vars.contains(var) {
                vars.push(var.clone());
            }
        }
        ToyMeta { vars, invertible }
    }

    /// One forward endpoint for the hole when it occurs: a single-sorted
    /// language has no backward flow.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn hole_flow(
        meta: &Self::Meta,
        hole: &Self::Hole,
    ) -> Vec<(Self::Var, SeamRole)>
    {
        meta.vars
            .iter()
            .filter(|var| *var == hole)
            .map(|var| (var.clone(), SeamRole::Forward))
            .collect()
    }

    /// Every cell fires anywhere.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn may_fire(
        _provenance: &Self::Provenance,
        _target: &Self::Cmd,
    ) -> FiringPermission
    {
        FiringPermission::from(true)
    }

    /// The derived orientation.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn derived_orientation() -> Self::Orientation
    {
        ToyOrient::Derived
    }

    /// The derived provenance.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn derived_provenance() -> Self::Provenance
    {
        ToyProv::Derived
    }
}

/// A toy rule cell `lhs ~> rhs`, its orientation given.
///
/// # Specification
/// trivial.
#[inline]
#[must_use]
pub fn toy_cell(
    lhs: Toy,
    rhs: Toy,
) -> Cell<ToyAlphabet>
{
    Cell::new(lhs, rhs, ToyOrient::Given, ToyProv::Rule)
}
