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

use anodized::spec;
use gandr_theory_cell_complexes::Cell;
use gandr_theory_cell_complexes::CellAlphabet;
use gandr_theory_cell_complexes::CellInvertibility;
use gandr_theory_cell_complexes::CellStore;
use gandr_theory_cell_complexes::CommandSpliceRefusal;
use gandr_theory_cell_complexes::ConvexityDischarge;
use gandr_theory_cell_complexes::FiringPermission;
use gandr_theory_cell_complexes::Generalization;
use gandr_theory_cell_complexes::GeneralizationArm;
use gandr_theory_cell_complexes::GeneralizationPoint;
use gandr_theory_cell_complexes::PatternSize;
use gandr_theory_cell_complexes::PositionOrder;
use gandr_theory_cell_complexes::PositionStep;
use gandr_theory_cell_complexes::SeamRole;
use gandr_theory_cell_complexes::SubstitutionDecision;
use gandr_theory_cell_complexes::anti_unification;
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
/// - executable: none — this stateless marker owns no terms or substitutions;
///   its laws relate the operations exercised by the inhabitant witnesses.
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
    /// - ensures: the original name followed by exactly one prime.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — empty and already primed names are freshened through
    ///   a collision chain. Missing or repeated suffixes change exact renamed
    ///   terms.
    /// - witness: `toy::tests::metadata_names_and_orders_observe_boundaries`
    #[spec(ensures: |output| output.0.strip_suffix("'") == Some(self.0.as_ref()))]
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
    /// - ensures: one more than `self`, saturating at `usize::MAX`; a table
    ///   held in memory never reaches that bound.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — zero, ordinary, last-in-range and saturated indices
    ///   have exact successors. Wrapping or skipping the increment changes the
    ///   boundary observations.
    /// - witness: `toy::tests::positions_preserve_prefix_boundaries_and_splice_siblings`
    #[spec(ensures: |ret| if self.0 == usize::MAX { ret.0 == usize::MAX }
        else { matches!(ret.0.checked_sub(self.0), Some(1)) })]
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
    ///
    /// # Adequacy
    /// - hypothesis: L3 — leaf, nested, truncated and exhausted ranges have
    ///   exact ends. Incorrect pending arity, a skipped child or an off-by-one
    ///   end changes the selected subterm.
    /// - witness: `toy::tests::positions_preserve_prefix_boundaries_and_splice_siblings`
    #[spec(ensures: |output| output >= start && (start.0 > self.0.len() || output.0 <= self.0.len())
        && (start.0 != 0 || output.0 == self.0.len()))]
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
    ///
    /// # Adequacy
    /// - hypothesis: L3 — every node of a nested tree reads its exact subterm;
    ///   out-of-arity and below-leaf paths refuse. Shifted offsets or a missed
    ///   boundary changes those reads.
    /// - witness: `toy::tests::positions_preserve_prefix_boundaries_and_splice_siblings`
    #[spec(ensures: |output| match output {
        Maybe::Present((start, end)) => start <= end && end.0 <= self.0.len()
            && (!steps.is_empty() || (start.0 == 0 && end.0 == self.0.len())),
        Maybe::Absent(command_subterm::Absent::OffTerm) => !steps.is_empty(),
        Maybe::Absent(command_subterm::Absent::NotACommand) => false,
    })]
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
    /// - requires: ordered bounds within the node table.
    /// - ensures: exactly the selected node range, in its original order.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — valid leaf and nested ranges reconstruct exact
    ///   subterms. Reversed bounds or an extra node changes read and splice
    ///   round trips.
    /// - witness: `toy::tests::positions_preserve_prefix_boundaries_and_splice_siblings`
    #[spec(requires: start <= end && end.0 <= self.0.len(), ensures: |output| self.0.get(start.0 .. end.0) == Some(output.0.as_slice()))]
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
    /// - ensures: every metavariable occurrence in prefix order, with repeats.
    /// - panics: none.
    /// - executable: none — the wrapper closure receives an impl-Trait return
    ///   type that Rust rejects for closures.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — empty occurrence lists and repeated names are
    ///   observed through exact metadata and multiplicities. Dropped repeats,
    ///   invented variables and reversal change those observations.
    /// - witness: `toy::tests::metadata_names_and_orders_observe_boundaries`
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
    /// - requires: the relabeller returns a leaf for every variable it sees.
    /// - ensures: relabelled variables with all other heads and node arities
    ///   kept.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — leaf-preserving freshening and skolemization keep
    ///   exact constructor structure and repeated-name identity. Relabelling
    ///   other heads or changing arity changes the terms.
    /// - witness: `toy::tests::metadata_names_and_orders_observe_boundaries`
    #[spec(ensures: |output| output.0.len() == self.0.len()
        && output.0.iter().zip(&self.0).all(|(after, before)| after.arity() == before.arity()))]
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
    /// - ensures: each bound variable is replaced by its image once, without
    ///   visiting that image; unbound variables and other heads are kept.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a triangular map separates one-pass replacement from
    ///   full application; empty maps and absent names stay unchanged.
    ///   Re-entering an image or dropping a binding changes the resulting term.
    /// - witness: `toy::tests::substitution_walks_are_transactional_and_bounded`
    #[spec(ensures: |output| output.0.len() == term.0.iter().fold(0_usize, |size, head| size.saturating_add(match *head {
        ToyHead::Var(ref var) => self.0.get(var).map_or(1, |image| image.0.len()), _ => 1,
    })) && (term.vars().any(|var| self.0.contains_key(var)) || output == *term))]
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
    ///
    /// # Adequacy
    /// - hypothesis: L3 — ground images, triangular chains and a self-cycle
    ///   have exact final terms. Missing a triangular pass, substituting a
    ///   wrong image or changing an unbound term changes the result.
    /// - witness: `toy::tests::substitution_walks_are_transactional_and_bounded`
    #[spec(ensures: |output| (term.vars().any(|var| self.0.contains_key(var)) || output == *term)
        && (!self.0.values().all(|image| image.vars().all(|var| !self.0.contains_key(var)))
            || output.vars().all(|var| !self.0.contains_key(var))))]
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
    ///
    /// # Adequacy
    /// - hypothesis: L3 — bound and free leaves, compound terms and a
    ///   self-cycle separate head walking from full substitution. Losing a
    ///   chain link or descending into compound arguments changes the result.
    /// - witness: `toy::tests::substitution_walks_are_transactional_and_bounded`
    #[spec(captures: original = term.clone(), ensures: |output| output == original || self.0.values().any(|image| image == &output))]
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
/// - ensures: each occurring variable has its exact positive multiplicity.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — empty, single and repeated variable sets have exact keyed
///   counts. Deduplication, extra keys and a lost occurrence change the
///   domination decision.
/// - witness: `toy::tests::metadata_names_and_orders_observe_boundaries`
#[spec(ensures: |output| output.values().fold(0_usize, |sum, count| sum.saturating_add(count.0)) == term.vars().count()
    && output.iter().all(|(var, count)| count.0 > 0 && count.0 == term.vars().filter(|held| held == var).count()))]
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
/// - ensures: domination exactly when every smaller-side count is present on
///   the larger side with at least the same multiplicity.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — empty, missing, equal and smaller multiplicities separate
///   domination from refusal. Strict comparison at equality or a permissive
///   missing-key default changes the result.
/// - witness: `toy::tests::metadata_names_and_orders_observe_boundaries`
#[spec(ensures: |output| (output == HoleDomination::Dominates) == smaller.iter().all(|(var, count)| larger.get(var).is_some_and(|held| held >= count)))]
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

/// The least general generalization of a family of toy-term tuples, reported
/// for any alphabet whose terms, metavariables and substitutions are the toy
/// alphabet's own.
///
/// # Specification
/// - ensures: one pattern per component; every member's component is its
///   pattern with each point's arm applied; a head every member holds at a
///   position is kept and descended into, so a point stands only where two
///   members differ; two positions whose subterms agree member by member stand
///   one point; every point's name is `$g$` and a suffix, worn by no member;
///   the points are listed in the order the walk meets them, component by
///   component, in prefix order.
/// - provides: [`anti_unification::Absent::EmptyFamily`] for a family with no
///   member; [`anti_unification::Absent::RaggedFamily`] when two members have
///   different lengths. Every toy node may be a metavariable, so every family
///   that is neither generalizes.
/// - panics: none.
/// - intension: one lockstep walk emitting the pattern in prefix order, the
///   pending child columns on a heap stack; a new point is compared with every
///   point already stood.
///
/// # Adequacy
/// - hypothesis: L3 — a shared constructor is kept above a point, a repeated
///   disagreement stands one point, a point's name avoids every member's, and
///   each refusal is reached by its own family; the law that each member is its
///   generalization under its arms is checked on a nesting family.
/// - witness: `tests::inhabitant::each_member_is_its_generalization_under_its_arms`
/// - witness: `tests::inhabitant::a_repeated_disagreement_stands_one_point`
/// - witness: `tests::inhabitant::a_point_takes_a_name_no_member_wears`
/// - witness: `tests::inhabitant::a_family_without_a_generalization_is_refused_by_name`
#[inline]
#[spec(ensures: |output| match output {
    Maybe::Absent(anti_unification::Absent::EmptyFamily) => family.is_empty(),
    Maybe::Absent(anti_unification::Absent::RaggedFamily) => family.first().is_some_and(|first| family.iter().any(|member| member.len() != first.len())),
    Maybe::Absent(anti_unification::Absent::Ungeneralizable) => false,
    Maybe::Present(ref generalized) => family.first().is_some_and(|first| generalized.patterns.len() == first.len())
        && family.iter().all(|member| member.len() == generalized.patterns.len())
        && generalized.points.iter().all(|point| point.arms.len() == family.len()
            && family.iter().flat_map(|member| member.iter()).flat_map(Toy::vars).all(|var| var != &point.var)),
})]
pub fn anti_unify_toys<A>(family: &[&[Toy]]) -> Maybe<Generalization<A>, anti_unification::Absent>
where
    A: CellAlphabet<Cmd = Toy, Var = ToyVar, Subst = ToySubst>,
{
    let Some((first, rest)) = family.split_first()
    else {
        return Maybe::Absent(anti_unification::Absent::EmptyFamily);
    };
    if rest.iter().any(|member| member.len() != first.len()) {
        return Maybe::Absent(anti_unification::Absent::RaggedFamily);
    }
    let mut taken: BTreeSet<ToyVar> = family
        .iter()
        .flat_map(|member| member.iter())
        .flat_map(Toy::vars)
        .cloned()
        .collect();
    let mut suffix = ToyCount(0);
    let mut stood: Vec<(ToyVar, Vec<&[ToyHead]>)> = Vec::new();
    let mut patterns = Vec::with_capacity(first.len());
    for (component, term) in first.iter().enumerate() {
        let members: Vec<&Toy> = core::iter::once(term)
            .chain(rest.iter().filter_map(|member| member.get(component)))
            .collect();
        let mut nodes: Vec<ToyHead> = Vec::new();
        let mut visits: Vec<Vec<ToyCount>> = alloc::vec![alloc::vec![ToyCount(0); members.len()]];
        while let Some(starts) = visits.pop() {
            let mut heads = members
                .iter()
                .zip(&starts)
                .map(|(member, start)| member.0.get(start.0));
            let shared = match heads.next() {
                | Some(Some(head)) if heads.all(|other| other == Some(head)) => Some(head),
                | Some(_) | None => None,
            };
            if let Some(head) = shared {
                nodes.push(head.clone());
                let mut cursor: Vec<ToyCount> = starts.iter().map(|start| start.next()).collect();
                let mut children: Vec<Vec<ToyCount>> = Vec::with_capacity(head.arity().0);
                for _ in 0 .. head.arity().0 {
                    let next: Vec<ToyCount> = members
                        .iter()
                        .zip(&cursor)
                        .map(|(member, child)| member.end_of(*child))
                        .collect();
                    children.push(core::mem::replace(&mut cursor, next));
                }
                visits.extend(children.into_iter().rev());
                continue;
            }
            let column: Vec<&[ToyHead]> = members
                .iter()
                .zip(&starts)
                .map(|(member, start)| {
                    member
                        .0
                        .get(start.0 .. member.end_of(*start).0)
                        .unwrap_or_default()
                })
                .collect();
            if let Some(seen) = stood.iter().find(|seen| seen.1 == column) {
                nodes.push(ToyHead::Var(seen.0.clone()));
                continue;
            }
            let fresh = loop {
                let name = ToyVar(alloc::format!("$g${}", suffix.0).into_boxed_str());
                suffix = suffix.next();
                if taken.insert(name.clone()) {
                    break name;
                }
            };
            stood.push((fresh.clone(), column));
            nodes.push(ToyHead::Var(fresh));
        }
        patterns.push(Toy(nodes));
    }
    let points = stood
        .into_iter()
        .map(|(var, column)| {
            let arms = column
                .iter()
                .map(|subterm| GeneralizationArm {
                    binding: ToySubst(BTreeMap::from([(var.clone(), Toy(subterm.to_vec()))])),
                    size: PatternSize::from(subterm.len()),
                })
                .collect();
            GeneralizationPoint { var, arms }
        })
        .collect();
    Maybe::Present(Generalization { patterns, points })
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
    ///
    /// # Adequacy
    /// - hypothesis: L3 — ground and schematic matches reconstruct targets in
    ///   one pass; incompatible heads and repeated-hole conflicts preserve an
    ///   existing map. Wrong binding and partial commitment change the
    ///   observations.
    /// - witness: `toy::tests::substitution_walks_are_transactional_and_bounded`
    #[inline]
    #[spec(captures: before = subst.clone(), ensures: |output| if bool::from(output) { subst.apply_once(pattern) == *target } else { *subst == before })]
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
    ///
    /// # Adequacy
    /// - hypothesis: L3 — compatible distinct holes and triangular images
    ///   equate both faces; a head clash and an occurs cycle preserve prior
    ///   bindings. Eager commits and skipped occurs checks change the result.
    /// - witness: `toy::tests::substitution_walks_are_transactional_and_bounded`
    #[inline]
    #[spec(captures: before = subst.clone(), ensures: |output| if bool::from(output) { subst.apply_fully(lhs) == subst.apply_fully(rhs) } else { *subst == before })]
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

    /// The least general generalization of a family of toy-term tuples.
    ///
    /// # Specification
    /// - ensures: as [`anti_unify_toys`].
    /// - provides: as [`anti_unify_toys`].
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — nesting families reconstruct every member under their
    ///   arms, while empty and ragged families return distinct refusals. Lost
    ///   components or wrong arms change the observations.
    /// - witness: `tests::inhabitant::each_member_is_its_generalization_under_its_arms`
    #[inline]
    #[spec(ensures: |output| match output {
        Maybe::Present(ref generalized) => family.first().is_some_and(|first| generalized.patterns.len() == first.len()) && generalized.points.iter().all(|point| point.arms.len() == family.len()),
        Maybe::Absent(anti_unification::Absent::EmptyFamily) => family.is_empty(),
        Maybe::Absent(anti_unification::Absent::RaggedFamily) => family.first().is_some_and(|first| family.iter().any(|member| member.len() != first.len())),
        Maybe::Absent(anti_unification::Absent::Ungeneralizable) => false,
    })]
    fn anti_unify_cmd(
        family: &[&[Self::Cmd]]
    ) -> Maybe<Generalization<Self>, anti_unification::Absent>
    {
        anti_unify_toys(family)
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

    /// The bindings of `vars` alone.
    ///
    /// # Specification
    /// - ensures: exactly the existing bindings whose keys occur in vars.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — none, one, duplicate and absent requested keys expose
    ///   exact restricted maps. Extra bindings and missing retained images
    ///   change the result.
    /// - witness: `toy::tests::substitution_walks_are_transactional_and_bounded`
    #[inline]
    #[spec(ensures: |output| output.0.len() == subst.0.keys().filter(|var| vars.contains(var)).count()
        && output.0.iter().all(|(var, image)| vars.contains(var) && subst.0.get(var) == Some(image)))]
    fn restrict_subst(
        subst: &Self::Subst,
        vars: &[Self::Var],
    ) -> Self::Subst
    {
        ToySubst(
            subst
                .0
                .iter()
                .filter(|&(var, _)| vars.contains(var))
                .map(|(var, image)| (var.clone(), image.clone()))
                .collect(),
        )
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

    /// The table's length: one node per entry.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn cmd_size(cmd: &Self::Cmd) -> PatternSize
    {
        PatternSize::from(cmd.0.len())
    }

    /// Every position of the term, breadth first: every subterm is a command.
    ///
    /// # Specification
    /// - ensures: one position per node, the root first and no position before
    ///   one enclosing it.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a leaf and a nested binary tree expose their complete
    ///   breadth-first position list. Duplicates, omitted nodes and a child
    ///   before its parent change the list.
    /// - witness: `toy::tests::positions_preserve_prefix_boundaries_and_splice_siblings`
    #[inline]
    #[spec(ensures: |output| output.len() == cmd.0.len() && output.first().is_some_and(|pos| pos.0.is_empty())
        && output.iter().enumerate().all(|(index, pos)| !output.iter().take(index).any(|earlier| earlier == pos)
            && (pos.0.is_empty() || output.iter().take(index).any(|parent| pos.0.split_last().is_some_and(|(_, prefix)| parent.0.as_ref() == prefix)))))]
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
    ///
    /// # Adequacy
    /// - hypothesis: L3 — root and nested nodes return exact terms;
    ///   out-of-arity and below-leaf paths return `OffTerm`. A wrong range or a
    ///   merged absence changes the observation.
    /// - witness: `toy::tests::positions_preserve_prefix_boundaries_and_splice_siblings`
    #[inline]
    #[spec(ensures: |output| match output {
        Maybe::Present(ref subterm) => subterm.0.len() <= cmd.0.len() && (!pos.0.is_empty() || subterm == cmd),
        Maybe::Absent(command_subterm::Absent::OffTerm) => matches!(cmd.range_at(&pos.0), Maybe::Absent(command_subterm::Absent::OffTerm)),
        Maybe::Absent(command_subterm::Absent::NotACommand) => false,
    })]
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
    ///
    /// # Adequacy
    /// - hypothesis: L3 — root, shrinking and growing replacements preserve
    ///   exact siblings, and invalid paths refuse. Dropped context, shifted
    ///   bounds and incorrect replacement change the term.
    /// - witness: `toy::tests::positions_preserve_prefix_boundaries_and_splice_siblings`
    #[inline]
    #[spec(captures: expected = replacement.clone(), ensures: |output| match output {
        Ok(ref term) => matches!(Self::subterm_cmd_at(term, pos), Maybe::Present(ref found) if found == &expected),
        Err(CommandSpliceRefusal::OffTerm) => matches!(cmd.range_at(&pos.0), Maybe::Absent(command_subterm::Absent::OffTerm)),
        Err(CommandSpliceRefusal::NotACommand) => false,
    })]
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
    ///
    /// # Adequacy
    /// - hypothesis: L3 — increasing sizes with adequate, missing or
    ///   insufficient hole counts separate strict order from obstruction; equal
    ///   sizes remain equal. Reversed signs and a skipped guard change the
    ///   verdict.
    /// - witness: `toy::tests::metadata_names_and_orders_observe_boundaries`
    #[inline]
    #[spec(ensures: |output| match output {
        core::cmp::Ordering::Greater => lhs.0.len() > rhs.0.len() && dominates(&occurrences(lhs), &occurrences(rhs)) == HoleDomination::Dominates,
        core::cmp::Ordering::Less => lhs.0.len() < rhs.0.len() && dominates(&occurrences(rhs), &occurrences(lhs)) == HoleDomination::Dominates,
        core::cmp::Ordering::Equal => lhs.0.len() == rhs.0.len() || if lhs.0.len() > rhs.0.len() {
            dominates(&occurrences(lhs), &occurrences(rhs)) == HoleDomination::FallsShort
        } else { dominates(&occurrences(rhs), &occurrences(lhs)) == HoleDomination::FallsShort },
    })]
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
    ///
    /// # Adequacy
    /// - hypothesis: L3 — repeated names, colliding prime chains and
    ///   already-disjoint terms reconstruct exact renamed faces. Splitting a
    ///   shared name, reusing a taken name or changing a constructor changes
    ///   the result.
    /// - witness: `toy::tests::metadata_names_and_orders_observe_boundaries`
    #[inline]
    #[spec(ensures: |output| output.0.0.len() == renamed.0.0.len() && output.1.0.len() == renamed.1.0.len()
        && output.0.vars().chain(output.1.vars()).all(|var| anchor.0.vars().chain(anchor.1.vars()).all(|held| held != var)))]
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
    /// - ensures: every variable becomes the constant with the same name; all
    ///   other heads and the node count are unchanged.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — repeated variables become name-stable constants while
    ///   a ground term is unchanged. Missed grounding, merged names or changed
    ///   constructors alters the exact term.
    /// - witness: `toy::tests::metadata_names_and_orders_observe_boundaries`
    #[inline]
    #[spec(ensures: |output| output.vars().next().is_none() && output.0.len() == cmd.0.len()
        && output.0.iter().zip(&cmd.0).all(|(after, before)| match *before { ToyHead::Var(ref var) => matches!(*after, ToyHead::Konst(ref constant) if constant == var), _ => after == before }))]
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
    /// - ensures: one variable per distinct name, in first-occurrence order
    ///   over lhs then rhs, with the supplied invertibility flag.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — empty, repeated and right-only names expose ordered
    ///   unique entries with both invertibility values. Deduplication by the
    ///   wrong key, reordering and a lost flag change the metadata.
    /// - witness: `toy::tests::metadata_names_and_orders_observe_boundaries`
    #[inline]
    #[spec(ensures: |output| output.invertible == invertible
        && lhs.vars().chain(rhs.vars()).all(|var| output.vars.iter().filter(|held| *held == var).count() == 1)
        && output.vars.iter().all(|var| lhs.vars().chain(rhs.vars()).any(|held| held == var)))]
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
    /// - ensures: a forward endpoint for each matching metadata variable, and
    ///   no endpoint when the requested hole is absent.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — present and absent holes expose one forward endpoint
    ///   or none. Wrong filtering, extra endpoints and a backward role change
    ///   the observation.
    /// - witness: `toy::tests::metadata_names_and_orders_observe_boundaries`
    #[inline]
    #[spec(ensures: |output| output.len() == meta.vars.iter().filter(|var| *var == hole).count()
        && output.iter().all(|endpoint| endpoint.0 == *hole && endpoint.1 == SeamRole::Forward))]
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

#[cfg(test)]
mod tests
{
    use super::*;

    #[test]
    fn positions_preserve_prefix_boundaries_and_splice_siblings()
    {
        for (before, after) in [
            (0, 1),
            (7, 8),
            (usize::MAX - 1, usize::MAX),
            (usize::MAX, usize::MAX),
        ] {
            assert_eq!(ToyCount(after), ToyCount(before).next());
        }
        let x = Toy::var("x");
        let right = Toy::add(Toy::zero(), x.clone());
        let term = Toy::add(Toy::succ(x.clone()), right.clone());
        let paths = [
            alloc::vec![],
            alloc::vec![0],
            alloc::vec![1],
            alloc::vec![0, 0],
            alloc::vec![1, 0],
            alloc::vec![1, 1],
        ];
        let positions: Vec<_> = paths
            .iter()
            .map(|path| {
                ToyAlphabet::position_at_path(
                    &path
                        .iter()
                        .copied()
                        .map(PositionStep::from)
                        .collect::<Vec<_>>(),
                )
            })
            .collect();
        assert_eq!(positions, ToyAlphabet::command_positions(&term));
        assert_eq!(
            alloc::vec![ToyAlphabet::root_position()],
            ToyAlphabet::command_positions(&Toy::zero())
        );
        let subterms = [
            term.clone(),
            Toy::succ(x.clone()),
            right,
            x.clone(),
            Toy::zero(),
            x.clone(),
        ];
        for (pos, expected) in positions.iter().zip(subterms) {
            assert_eq!(
                Maybe::Present(expected.clone()),
                ToyAlphabet::subterm_cmd_at(&term, pos)
            );
            assert_eq!(
                Ok(term.clone()),
                ToyAlphabet::splice_cmd_at(&term, pos, expected)
            );
        }
        for (start, end) in [(0, 6), (1, 3), (2, 3), (3, 6), (4, 5), (5, 6), (6, 6)] {
            assert_eq!(ToyCount(end), term.end_of(ToyCount(start)));
        }
        assert_eq!(
            ToyCount(2),
            Toy(alloc::vec![ToyHead::Add, ToyHead::Zero]).end_of(ToyCount(0))
        );
        assert_eq!(ToyCount(0), Toy(alloc::vec![]).end_of(ToyCount(0)));
        let first = ToyAlphabet::position_at_path(&[PositionStep::from(0_usize)]);
        let inner = ToyAlphabet::position_at_path(&[
            PositionStep::from(1_usize),
            PositionStep::from(1_usize),
        ]);
        assert_eq!(
            Ok(Toy::add(Toy::zero(), Toy::add(Toy::zero(), x))),
            ToyAlphabet::splice_cmd_at(&term, &first, Toy::zero())
        );
        assert_eq!(
            Ok(Toy::add(
                Toy::succ(Toy::var("x")),
                Toy::add(Toy::zero(), term.clone())
            )),
            ToyAlphabet::splice_cmd_at(&term, &inner, term.clone())
        );
        assert_eq!(
            Ok(Toy::zero()),
            ToyAlphabet::splice_cmd_at(&term, &ToyAlphabet::root_position(), Toy::zero())
        );
        for path in [alloc::vec![2], alloc::vec![0, 1], alloc::vec![1, 1, 0]] {
            let pos = ToyAlphabet::position_at_path(
                &path.into_iter().map(PositionStep::from).collect::<Vec<_>>(),
            );
            assert_eq!(
                Maybe::Absent(command_subterm::Absent::OffTerm),
                ToyAlphabet::subterm_cmd_at(&term, &pos)
            );
            assert_eq!(
                Err(CommandSpliceRefusal::OffTerm),
                ToyAlphabet::splice_cmd_at(&term, &pos, Toy::zero())
            );
        }
    }

    #[test]
    fn substitution_walks_are_transactional_and_bounded()
    {
        let x = ToyVar::from("x");
        let y = ToyVar::from("y");
        let subst = ToySubst(BTreeMap::from([
            (x.clone(), Toy::var("y")),
            (y.clone(), Toy::zero()),
        ]));
        let term = Toy::add(Toy::var("x"), Toy::var("y"));
        assert_eq!(
            Toy::add(Toy::var("y"), Toy::zero()),
            subst.apply_once(&term)
        );
        assert_eq!(Toy::add(Toy::zero(), Toy::zero()), subst.apply_fully(&term));
        assert_eq!(Toy::zero(), subst.walk(Toy::var("x")));
        assert_eq!(term, subst.walk(term.clone()));
        assert_eq!(Toy::var("free"), subst.walk(Toy::var("free")));
        assert_eq!(Toy::var("free"), subst.apply_fully(&Toy::var("free")));
        assert_eq!(term, ToySubst::default().apply_fully(&term));
        assert_eq!(
            ToySubst::default(),
            ToyAlphabet::restrict_subst(&subst, &[])
        );
        assert_eq!(
            ToySubst::default(),
            ToyAlphabet::restrict_subst(&subst, &[ToyVar::from("missing")])
        );
        assert_eq!(
            ToySubst(BTreeMap::from([(x.clone(), Toy::var("y"))])),
            ToyAlphabet::restrict_subst(&subst, &[x.clone(), x.clone()])
        );
        assert_eq!(subst, ToyAlphabet::restrict_subst(&subst, &[x, y]));
        let self_cycle = ToySubst(BTreeMap::from([(ToyVar::from("self"), Toy::var("self"))]));
        assert_eq!(Toy::var("self"), self_cycle.walk(Toy::var("self")));
        assert_eq!(Toy::var("self"), self_cycle.apply_fully(&Toy::var("self")));
        let seed = ToySubst(BTreeMap::from([(
            ToyVar::from("held"),
            Toy::succ(Toy::zero()),
        )]));
        let pattern = Toy::add(Toy::var("p"), Toy::var("p"));
        let target = Toy::add(Toy::zero(), Toy::zero());
        let mut matched = seed.clone();
        assert!(bool::from(ToyAlphabet::match_cmd(
            &pattern,
            &target,
            &mut matched
        )));
        assert_eq!(target, matched.apply_once(&pattern));
        assert_eq!(
            Some(&Toy::succ(Toy::zero())),
            matched.0.get(&ToyVar::from("held"))
        );
        let saved = matched.clone();
        for (left, right) in [
            (
                pattern.clone(),
                Toy::add(Toy::zero(), Toy::succ(Toy::zero())),
            ),
            (Toy::succ(Toy::var("p")), Toy::zero()),
            (Toy::zero(), Toy::succ(Toy::zero())),
        ] {
            assert!(!bool::from(ToyAlphabet::match_cmd(
                &left,
                &right,
                &mut matched
            )));
            assert_eq!(saved, matched);
        }
        let left = Toy::add(Toy::var("a"), Toy::var("b"));
        let right = Toy::add(Toy::succ(Toy::var("b")), Toy::zero());
        let mut unified = seed.clone();
        assert!(bool::from(ToyAlphabet::unify_cmd(
            &left,
            &right,
            &mut unified
        )));
        assert_eq!(
            Toy::add(Toy::succ(Toy::zero()), Toy::zero()),
            unified.apply_fully(&left)
        );
        assert_eq!(unified.apply_fully(&left), unified.apply_fully(&right));
        for (left, right) in [
            (Toy::var("cycle"), Toy::succ(Toy::var("cycle"))),
            (
                Toy::add(Toy::zero(), Toy::var("fresh")),
                Toy::add(Toy::succ(Toy::zero()), Toy::zero()),
            ),
        ] {
            let mut refused = seed.clone();
            assert!(!bool::from(ToyAlphabet::unify_cmd(
                &left,
                &right,
                &mut refused
            )));
            assert_eq!(seed, refused);
        }
    }

    #[test]
    fn metadata_names_and_orders_observe_boundaries()
    {
        use core::cmp::Ordering;

        let x = ToyVar::from("x");
        let term = Toy::add(Toy::var("x"), Toy::var("x"));
        assert_eq!(BTreeMap::from([(&x, Occurrences(2))]), occurrences(&term));
        assert!(occurrences(&Toy::zero()).is_empty());
        let counts = occurrences(&term);
        assert_eq!(
            HoleDomination::Dominates,
            dominates(&counts, &BTreeMap::new())
        );
        for (var, count, expected) in [
            (&x, 1, HoleDomination::Dominates),
            (&x, 2, HoleDomination::Dominates),
            (&x, 3, HoleDomination::FallsShort),
            (&ToyVar::from("missing"), 1, HoleDomination::FallsShort),
        ] {
            assert_eq!(
                expected,
                dominates(&counts, &BTreeMap::from([(var, Occurrences(count))]))
            );
        }
        for (left, right, expected) in [
            (Toy::succ(Toy::var("x")), Toy::var("x"), Ordering::Greater),
            (Toy::succ(Toy::zero()), Toy::var("x"), Ordering::Equal),
            (
                Toy::succ(Toy::succ(Toy::var("x"))),
                term.clone(),
                Ordering::Equal,
            ),
            (
                Toy::succ(Toy::succ(Toy::succ(Toy::var("x")))),
                term.clone(),
                Ordering::Equal,
            ),
        ] {
            assert_eq!(expected, ToyAlphabet::reduction_cmp(&left, &right));
            assert_eq!(
                expected.reverse(),
                ToyAlphabet::reduction_cmp(&right, &left)
            );
        }
        for invertible in [false, true] {
            let meta = ToyAlphabet::derive_meta(
                &term,
                &Toy::add(Toy::var("new"), Toy::var("x")),
                CellInvertibility::from(invertible),
            );
            assert_eq!(alloc::vec![x.clone(), ToyVar::from("new")], meta.vars);
            assert_eq!(invertible, bool::from(meta.invertible));
            assert_eq!(
                alloc::vec![(x.clone(), SeamRole::Forward)],
                ToyAlphabet::hole_flow(&meta, &x)
            );
            assert!(ToyAlphabet::hole_flow(&meta, &ToyVar::from("missing")).is_empty());
        }
        assert!(
            ToyAlphabet::derive_meta(&Toy::zero(), &Toy::zero(), CellInvertibility::from(false))
                .vars
                .is_empty()
        );
        let expected_constants = Toy(alloc::vec![
            ToyHead::Add,
            ToyHead::Konst(x.clone()),
            ToyHead::Konst(x)
        ]);
        assert_eq!(expected_constants, ToyAlphabet::skolemize(&term));
        assert_eq!(
            expected_constants,
            ToyAlphabet::skolemize(&expected_constants)
        );
        for name in ["", "r'"] {
            let source = Toy::var(name);
            let expected = Toy::var(ToyVar(alloc::format!("{name}'").into_boxed_str()));
            assert_eq!(
                (expected.clone(), expected),
                ToyAlphabet::rename_apart((&source, &source), (&source, &source))
            );
        }
        let anchor = Toy::add(Toy::var("r"), Toy::add(Toy::var("r'"), Toy::var("r''")));
        let lhs = Toy::add(Toy::var("r"), Toy::var("r'"));
        let rhs = Toy::add(Toy::var("r"), Toy::var("r"));
        assert_eq!(
            (
                Toy::add(Toy::var("r'''"), Toy::var("r''''")),
                Toy::add(Toy::var("r'''"), Toy::var("r'''"))
            ),
            ToyAlphabet::rename_apart((&anchor, &anchor), (&lhs, &rhs))
        );
        assert_eq!(
            (lhs.clone(), rhs.clone()),
            ToyAlphabet::rename_apart((&Toy::zero(), &Toy::zero()), (&lhs, &rhs))
        );
    }
}
