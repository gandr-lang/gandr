//! A second, minimal [`CellAlphabet`] inhabitant: a single-sorted first-order
//! term language — `Zero`, `Succ`, `Add` and metavariables — implemented
//! outside the crate, the path every later alphabet takes.
//!
//! It is the inhabitant whose terms nest commands: every subterm is a command,
//! so a law about a position below the root can be exercised at all. Each
//! term is one flat table in prefix order, every node followed by its
//! children's ranges, so no fixture value routes ownership through itself and
//! no walk over one recurses.

use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use alloc::collections::VecDeque;

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
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ToyAlphabet;

/// A toy metavariable name.
#[repr(transparent)]
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ToyVar(Box<str>);

impl From<&str> for ToyVar
{
    /// A metavariable spelled by the name.
    ///
    /// # Specification
    /// trivial.
    fn from(value: &str) -> Self
    {
        Self(value.into())
    }
}

/// One node of a toy term.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum ToyHead
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
pub struct ToyCount(usize);

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
    pub fn var<N>(name: N) -> Self
    where
        N: Into<ToyVar>,
    {
        Self(vec![ToyHead::Var(name.into())])
    }

    /// The nullary constructor.
    ///
    /// # Specification
    /// trivial.
    pub fn zero() -> Self
    {
        Self(vec![ToyHead::Zero])
    }

    /// The unary constructor applied to `arg`.
    ///
    /// # Specification
    /// trivial.
    pub fn succ(arg: Self) -> Self
    {
        let mut nodes = vec![ToyHead::Succ];
        nodes.extend(arg.0);
        Self(nodes)
    }

    /// The binary operation applied to `lhs` and `rhs`.
    ///
    /// # Specification
    /// trivial.
    pub fn add(
        lhs: Self,
        rhs: Self,
    ) -> Self
    {
        let mut nodes = vec![ToyHead::Add];
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
        let mut pending = 1_usize;
        let mut index = start.0;
        while pending > 0 {
            let Some(head) = self.0.get(index)
            else {
                break;
            };
            pending = pending.saturating_sub(1).saturating_add(head.arity().0);
            index = index.saturating_add(1);
        }
        ToyCount(index)
    }

    /// The subterm ranges a position addresses: the start and end of the
    /// subterm reached by following `steps` from the root.
    ///
    /// # Specification
    /// - ensures: the range of the subterm `steps` reaches.
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
            if usize::from(step) >= head.arity().0 {
                return Maybe::Absent(command_subterm::Absent::OffTerm);
            }
            let mut child = ToyCount(start.0.saturating_add(1));
            for _ in 0 .. usize::from(step) {
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
        Self(self.0[start.0 .. end.0].to_vec())
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
            match *head {
                | ToyHead::Var(ref var) if self.0.contains_key(var) => {
                    nodes.extend(self.0[var].0.iter().cloned());
                },
                | ToyHead::Var(_)
                | ToyHead::Konst(_)
                | ToyHead::Zero
                | ToyHead::Succ
                | ToyHead::Add => nodes.push(head.clone()),
            }
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
    /// trivial.
    fn walk(
        &self,
        term: Toy,
    ) -> Toy
    {
        let mut current = term;
        for _ in 0 ..= self.0.len() {
            let [ToyHead::Var(ref var)] = current.0[..]
            else {
                break;
            };
            let Some(image) = self.0.get(var)
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

/// Whether `larger` carries every metavariable of `smaller` at least as
/// often.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Dominates(bool);

/// Whether `larger` dominates `smaller` hole by hole.
///
/// # Specification
/// trivial.
fn dominates(
    larger: &BTreeMap<&ToyVar, Occurrences>,
    smaller: &BTreeMap<&ToyVar, Occurrences>,
) -> Dominates
{
    Dominates(
        smaller
            .iter()
            .all(|(var, count)| larger.get(var).is_some_and(|held| held >= count)),
    )
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
            at = ToyCount(at.0.saturating_add(1));
        }
        if at.0 != target.0.len() {
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
    fn unify_cmd(
        lhs: &Self::Cmd,
        rhs: &Self::Cmd,
        subst: &mut Self::Subst,
    ) -> SubstitutionDecision
    {
        let mut found = subst.clone();
        let mut goals = vec![(lhs.clone(), rhs.clone())];
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
    fn metavariables(cmd: &Self::Cmd) -> Vec<Self::Var>
    {
        cmd.vars().cloned().collect()
    }

    /// Every position of the term, breadth first: every subterm is a command.
    ///
    /// # Specification
    /// trivial.
    fn command_positions(cmd: &Self::Cmd) -> Vec<Self::Pos>
    {
        let mut positions = Vec::new();
        let mut queue: VecDeque<(Vec<PositionStep>, ToyCount)> = VecDeque::new();
        queue.push_back((Vec::new(), ToyCount(0)));
        while let Some((path, start)) = queue.pop_front() {
            let Some(head) = cmd.0.get(start.0)
            else {
                continue;
            };
            let mut child = ToyCount(start.0.saturating_add(1));
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
    fn root_position() -> Self::Pos
    {
        ToyPos::default()
    }

    /// The position of `path`.
    ///
    /// # Specification
    /// trivial.
    fn position_at_path(path: &[PositionStep]) -> Self::Pos
    {
        ToyPos(path.into())
    }

    /// The path order of the two paths.
    ///
    /// # Specification
    /// trivial.
    fn position_order(
        left: &Self::Pos,
        right: &Self::Pos,
    ) -> PositionOrder
    {
        path_order(left.0.iter().copied(), right.0.iter().copied())
    }

    /// Discharged: left-hand sides are trees rooted at one operation and
    /// targets are trees.
    ///
    /// # Specification
    /// trivial.
    fn convexity_discharge(_store: &CellStore<Self>) -> ConvexityDischarge
    {
        ConvexityDischarge::StronglyConnectedOverAcyclicTarget
    }

    /// The subterm at `pos`, owned.
    ///
    /// # Specification
    /// trivial.
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
    /// trivial.
    fn splice_cmd_at(
        cmd: &Self::Cmd,
        pos: &Self::Pos,
        replacement: Self::Cmd,
    ) -> Result<Self::Cmd, CommandSpliceRefusal>
    {
        let Maybe::Present((start, end)) = cmd.range_at(&pos.0)
        else {
            return Err(CommandSpliceRefusal::OffTerm);
        };
        let mut nodes = cmd.0[.. start.0].to_vec();
        nodes.extend(replacement.0);
        nodes.extend_from_slice(&cmd.0[end.0 ..]);
        Ok(Toy(nodes))
    }

    /// Size guarded by hole domination; a tie or an unlicensed difference is
    /// an obstruction.
    ///
    /// # Specification
    /// trivial.
    fn reduction_cmp(
        lhs: &Self::Cmd,
        rhs: &Self::Cmd,
    ) -> core::cmp::Ordering
    {
        let (left, right) = (occurrences(lhs), occurrences(rhs));
        match lhs.0.len().cmp(&rhs.0.len()) {
            | core::cmp::Ordering::Greater if dominates(&left, &right).0 => {
                core::cmp::Ordering::Greater
            },
            | core::cmp::Ordering::Less if dominates(&right, &left).0 => core::cmp::Ordering::Less,
            | core::cmp::Ordering::Greater
            | core::cmp::Ordering::Less
            | core::cmp::Ordering::Equal => core::cmp::Ordering::Equal,
        }
    }

    /// The renamed faces with each name primed apart from the anchor's.
    ///
    /// # Specification
    /// trivial.
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
                let mut primed = String::from(&*name.0);
                primed.push('\'');
                name = ToyVar(primed.into_boxed_str());
            }
            taken.insert(name.clone());
            fresh.insert(var.clone(), name);
        }
        let relabel = |var: &ToyVar| ToyHead::Var(fresh[var].clone());
        (renamed.0.relabel(relabel), renamed.1.relabel(relabel))
    }

    /// Every metavariable replaced by its constant.
    ///
    /// # Specification
    /// trivial.
    fn skolemize(cmd: &Self::Cmd) -> Self::Cmd
    {
        cmd.relabel(|var| ToyHead::Konst(var.clone()))
    }

    /// A metavariable is its own hole.
    ///
    /// # Specification
    /// trivial.
    fn hole_of(var: &Self::Var) -> Self::Hole
    {
        var.clone()
    }

    /// Positive for the derived provenance.
    ///
    /// # Specification
    /// trivial.
    fn completion_certificate(provenance: &Self::Provenance) -> CellInvertibility
    {
        CellInvertibility::from(matches!(*provenance, ToyProv::Derived))
    }

    /// The distinct metavariables of both faces.
    ///
    /// # Specification
    /// trivial.
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
    fn derived_orientation() -> Self::Orientation
    {
        ToyOrient::Derived
    }

    /// The derived provenance.
    ///
    /// # Specification
    /// trivial.
    fn derived_provenance() -> Self::Provenance
    {
        ToyProv::Derived
    }
}
