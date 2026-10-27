//! Laws over an indexed sort, read over terms that carry their indices.
//!
//! A law over an indexed sort fixes its indices by the sorts its variables
//! stand at: in `comp(id(a), f) ==> f` over `Hom(dom, cod)`, the objects
//! `comp` composes at are `a`, `a` and the codomain of `f`. A term does not
//! carry them, so two laws' untyped overlap can part where the typing makes
//! its two sides one: `comp(id(a), id(b))` parts into `id(a)` and `id(b)`,
//! and over the sorting `a` is `b`. [`Indexing`] reads each application of an
//! operation with its implicit indices first, the variables its ports' sorts
//! name that no port binds, each solved from the sorts its arguments stand
//! at: `comp(a, a, b, id(a), f) ==> f`. Over those terms an overlap unifies
//! the indices too, so a critical pair is well sorted, and a closed call
//! carries the indices its arguments' sorts fix.
//!
//! The reading carries a presentation's own laws
//! ([`crate::elaborate_theory_desc`]), a closed call and the oriented rules it
//! normalizes under ([`crate::PresentedRules::call`]). The kernel re-derives
//! the same indices when it decides the presentation's rules, so the overlaps
//! the cell layer certifies are the ones the kernel joins.
//!
//! - **Choice.** Index arguments written into the term alphabet's operation
//!   applications, solved by first-order unification over the signature's
//!   sorts; a law the sorting does not fix the indices of, or a port that binds
//!   or abstracts, keeps the term reading's decline.
//! - **Alternatives.** Sorted terms whose every node carries its sort, which
//!   asks the cell substrate for a sorted alphabet; or the indices left off and
//!   the laws declined, which leaves a category's and a graded presentation's
//!   laws unread.
//! - **Reversal.** A term alphabet that carries each subterm's sort replaces
//!   the written indices.
//!
//! # References
//!
//! - John Cartmell. "Generalised Algebraic Theories and Contextual Categories."
//!   _Annals of Pure and Applied Logic_ 32 (1986), pages 209–243.
//!   `doi:10.1016/0168-0072(86)90053-9` — sorts indexed by terms, and an
//!   operation's implicit arguments: the indices its sorting fixes.

use alloc::boxed::Box;
use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use alloc::format;
use alloc::vec::Vec;

use anodized::spec;
use gandr_theory_levitation::FreeTerm;
use gandr_theory_levitation::Name;
use gandr_theory_levitation::RuleFace;
use gandr_theory_levitation::SortRef;
use gandr_theory_levitation::TermNode;
use gandr_theory_levitation::TermView;
use gandr_theory_levitation::TheoryDesc;
use quenchant_shape::shape::Maybe;

quenchant_shape::reason_enum! {
    /// Why a description's terms carry no indices.
    pub mod indexed_reading {
        /// The reason no operation application carries its indices.
        #[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
        pub enum Absent {
            /// Every sort is unindexed: an operation's argument sorts are
            /// fixed, and a term's sorting fixes nothing more.
            Unindexed,
            /// A family's rules compile to its operations, whose sorts its
            /// constructors fix: its terms carry no indices.
            Generated,
            /// A port binds or abstracts a variable, an operation has other
            /// than one output, an index names an operation that has indices
            /// of its own, or a law has no sorting, instantiates a variable
            /// or fires under a row: the reading carries none of them.
            Unsupported,
        }
    }
}

/// Why a term has no sorting under a description's operations.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Unsorted
{
    /// The term applies something other than an operation the description
    /// declares, at its port count.
    Unread,
    /// Two sorts the term's operations ask of one subterm do not unify.
    Clash,
    /// The right side names an index its left side's sorting does not fix.
    Unfixed,
}

/// One operation's sorting: the indices it is implicitly applied at, each
/// input port's name and sort, and its output's sort, a sort written as the
/// constructor application of the sort's name to its index terms.
#[derive(Clone, Debug, Eq, PartialEq)]
struct Sorting
{
    /// The variables the ports' sorts name that no input port binds, in order
    /// of first occurrence.
    implicits: Box<[Name]>,
    /// Each input port's name and sort.
    inputs: Box<[(Name, FreeTerm)]>,
    /// The output port's sort.
    output: FreeTerm,
}

/// The operations of a description over indexed sorts, each with the indices
/// its applications carry.
#[derive(Clone, Debug, Eq, PartialEq)]
#[repr(transparent)]
pub struct Indexing
{
    /// Each operation's sorting, by name.
    operations: BTreeMap<Name, Sorting>,
}

/// The first character of an unknown the solver mints; no written variable
/// begins with it.
const UNKNOWN: char = '·';

/// The sort a port stands at, as a term: its sort's name applied to its index
/// terms.
///
/// # Specification
/// trivial.
fn sort_term(port: &SortRef) -> FreeTerm
{
    FreeTerm::ctor(port.sort.clone(), port.arguments.iter().cloned())
}

/// How a rebuild treats the term it puts for a variable.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Substitution
{
    /// The term stands as given: written ports renamed to the arguments
    /// passed at them.
    Once,
    /// The term is read in its turn: a solution's own unknowns are solved too.
    Through,
}

/// What a rebuild leaves off an operation application's arguments.
#[derive(Clone, Copy, Debug)]
enum Dropping<'indexing>
{
    /// Every argument is kept.
    Nothing,
    /// An application carrying its implicit indices loses them.
    Indices(&'indexing Indexing),
}

/// A step of a rebuild: a subterm to read, or a head to apply to the terms
/// built for its arguments, the last ones built.
enum Step
{
    /// Read this subterm.
    Read(FreeTerm),
    /// Apply the operation to so many arguments.
    Op(Name, usize),
    /// Apply the constructor to so many arguments.
    Ctor(Name, usize),
    /// Tuple so many components.
    Results(usize),
    /// Instantiate the variable at so many arguments.
    Inst(Name, usize),
}

/// Schedule `head` over `args`: the head is applied once every argument,
/// read first to last, is built.
///
/// # Specification
/// trivial.
fn schedule<'term, A>(
    steps: &mut Vec<Step>,
    head: Step,
    args: A,
) where
    A: Iterator<Item = TermNode<'term>>,
{
    steps.push(head);
    let start = steps.len();
    steps.extend(args.map(|arg| Step::Read(arg.to_term())));
    // Pushed in reverse, so the first argument is read first.
    if let Some(reads) = steps.get_mut(start ..) {
        reads.reverse();
    }
}

/// `term` rebuilt with each variable `put` gives a term for replaced by it,
/// read in its turn under [`Substitution::Through`], and each operation
/// application losing what `dropping` leaves off.
///
/// # Specification
/// - ensures: every node kept but a replaced variable and a dropped argument;
///   an abstraction, an atom, a binding field and its variable kept whole.
/// - panics: none.
/// - intension: a worklist of steps, so no call recurses.
/// - executable: none — the rebuilt term is the clause's own statement; a
///   predicate would rebuild it a second time.
///
/// # Adequacy
/// - hypothesis: L3 — as [`Indexing::face`] and [`Indexing::strip`].
/// - witness: `indexing::tests::a_categorys_laws_carry_their_objects`
fn rebuilt<'put, P>(
    term: &FreeTerm,
    put: P,
    substitution: Substitution,
    dropping: Dropping<'_>,
) -> FreeTerm
where
    P: Fn(&Name) -> Option<&'put FreeTerm>,
{
    let mut steps = Vec::from([Step::Read(term.clone())]);
    let mut built: Vec<FreeTerm> = Vec::new();
    while let Some(step) = steps.pop() {
        match step {
            Step::Read(next) => match next.view() {
                TermView::Var(name) => match (put(name), substitution) {
                    (Some(put), Substitution::Through) => steps.push(Step::Read(put.clone())),
                    (Some(put), Substitution::Once) => built.push(put.clone()),
                    (None, Substitution::Once | Substitution::Through) => built.push(next.clone()),
                },
                TermView::Op { name, args } => {
                    schedule(&mut steps, Step::Op(name.clone(), args.len()), args);
                },
                TermView::Ctor { name, args } => {
                    schedule(&mut steps, Step::Ctor(name.clone(), args.len()), args);
                },
                TermView::Results { args } => {
                    schedule(&mut steps, Step::Results(args.len()), args);
                },
                TermView::Inst { name, args } => {
                    schedule(&mut steps, Step::Inst(name.clone(), args.len()), args);
                },
                TermView::Abs { .. }
                | TermView::Atom(_)
                | TermView::Lam { .. }
                | TermView::Bound(_) => {
                    built.push(next.clone());
                },
            },
            Step::Op(name, count) => {
                let start = built.len().saturating_sub(count);
                let skip = match dropping {
                    Dropping::Nothing => 0,
                    Dropping::Indices(indexing) => {
                        indexing.operations.get(&name).map_or(0, |sorting| {
                            let implicit = sorting.implicits.len();
                            if count == implicit.saturating_add(sorting.inputs.len()) {
                                implicit
                            }
                            else {
                                0
                            }
                        })
                    },
                };
                let applied = FreeTerm::op(name, built.drain(start ..).skip(skip));
                built.push(applied);
            },
            Step::Ctor(name, count) => {
                let start = built.len().saturating_sub(count);
                let applied = FreeTerm::ctor(name, built.drain(start ..));
                built.push(applied);
            },
            Step::Results(count) => {
                let start = built.len().saturating_sub(count);
                let applied = FreeTerm::results(built.drain(start ..));
                built.push(applied);
            },
            Step::Inst(name, count) => {
                let start = built.len().saturating_sub(count);
                let applied = FreeTerm::inst(name, built.drain(start ..));
                built.push(applied);
            },
        }
    }
    built.pop().unwrap_or_else(|| term.clone())
}

impl Indexing
{
    /// The indexed reading of `description`'s operations, when a sort is
    /// indexed and every operation's ports are ones the reading carries.
    ///
    /// # Specification
    /// - ensures: one sorting per operation, its implicit indices the variables
    ///   its ports' sorts name that no input port binds, in order of first
    ///   occurrence.
    /// - fails: [`indexed_reading::Absent::Unindexed`] when no sort is indexed;
    ///   [`indexed_reading::Absent::Unsupported`] when a port binds or
    ///   abstracts, an operation has other than one output, or an index term
    ///   applies an operation with implicit indices of its own.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a category's composition is implicit in its three
    ///   objects and its identity in none, and a plain signature has no indexed
    ///   reading.
    /// - witness: `indexing::tests::a_categorys_laws_carry_their_objects`
    #[spec(ensures: |ret| match ret {
        Maybe::Present(ref indexing) => indexing.operations.len() == description.opers.len(),
        Maybe::Absent(indexed_reading::Absent::Unindexed) => description.sorts.iter().all(|sort| sort.indices.is_empty()),
        Maybe::Absent(indexed_reading::Absent::Generated) => false,
        Maybe::Absent(indexed_reading::Absent::Unsupported) => true,
    })]
    #[inline]
    pub fn of<G>(description: &TheoryDesc<G>) -> Maybe<Self, indexed_reading::Absent>
    {
        if description.sorts.iter().all(|sort| sort.indices.is_empty()) {
            return Maybe::Absent(indexed_reading::Absent::Unindexed);
        }
        let mut operations = BTreeMap::new();
        let (mut bound, mut seen): (BTreeSet<&Name>, BTreeSet<&Name>) =
            (BTreeSet::new(), BTreeSet::new());
        for operation in &description.opers {
            let ports = operation
                .arity
                .inputs
                .iter()
                .chain(operation.arity.outputs.iter());
            if operation.arity.outputs.len() != 1
                || ports
                    .clone()
                    .any(|port| !port.bindings.is_empty() || !port.abstractions.is_empty())
            {
                return Maybe::Absent(indexed_reading::Absent::Unsupported);
            }
            bound.clear();
            bound.extend(operation.arity.inputs.iter().map(|port| &port.name));
            seen.clear();
            let implicits: Box<[Name]> = ports
                .flat_map(|port| port.arguments.iter())
                .flat_map(|argument| argument.to_node().vars())
                .filter(|&name| !bound.contains(name) && seen.insert(name))
                .cloned()
                .collect();
            let Some(output) = operation.arity.outputs.first().map(sort_term)
            else {
                return Maybe::Absent(indexed_reading::Absent::Unsupported);
            };
            let _first = operations.insert(operation.name.clone(), Sorting {
                implicits,
                inputs: operation
                    .arity
                    .inputs
                    .iter()
                    .map(|port| (port.name.clone(), sort_term(port)))
                    .collect(),
                output,
            });
        }
        let indexed_in_an_index = operations.values().any(|sorting| {
            sorting
                .inputs
                .iter()
                .map(|&(_, ref sort)| sort)
                .chain([&sorting.output])
                .any(|sort| {
                    applied(sort).iter().any(|name| {
                        operations
                            .get(name)
                            .is_some_and(|inner| !inner.implicits.is_empty())
                    })
                })
        });
        if indexed_in_an_index {
            return Maybe::Absent(indexed_reading::Absent::Unsupported);
        }
        Maybe::Present(Self { operations })
    }

    /// `face` with each operation application carrying its indices, solved
    /// from the sorts its variables stand at.
    ///
    /// # Specification
    /// - ensures: both sides with every application `f(t…)` written `f(i…,
    ///   t…)`, its implicit indices first, the two sides at one sort, each
    ///   [`Self::strip`]ped back to the side as written; an index no sort fixes
    ///   is a fresh variable of the left side.
    /// - fails: [`Unsorted::Unread`] for a side applying anything but a
    ///   declared operation at its port count, or naming a variable no other
    ///   way; [`Unsorted::Clash`] when two sorts asked of one subterm do not
    ///   unify; [`Unsorted::Unfixed`] when the right side names an index the
    ///   left side's sorting does not fix.
    /// - panics: none.
    /// - executable: none — the strip-back clause compares terms built from the
    ///   receiver's sorting, which a clause may not read.
    ///
    /// # Errors
    /// As the failure clause states.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the category's unit laws carry the objects their
    ///   variables fix, and a law equating two sorts apart is refused.
    /// - witness: `indexing::tests::a_categorys_laws_carry_their_objects`
    #[inline]
    pub fn face(
        &self,
        face: &RuleFace,
    ) -> Result<RuleFace, Unsorted>
    {
        let mut solving = Solving::new(self);
        let (left, left_sort) = solving.infer(&face.lhs)?;
        let (right, right_sort) = solving.infer(&face.rhs)?;
        solving.unify(&left_sort, &right_sort)?;
        let (lhs, rhs) = (solving.resolved(&left), solving.resolved(&right));
        let fixed: BTreeSet<&Name> = lhs.to_node().vars().collect();
        if rhs
            .to_node()
            .vars()
            .any(|name| name.as_ref().starts_with(UNKNOWN) && !fixed.contains(name))
        {
            return Err(Unsorted::Unfixed);
        }
        Ok(RuleFace {
            lhs,
            rhs,
            ..face.clone()
        })
    }

    /// `term`, a closed call, with each operation application carrying the
    /// indices its arguments' sorts fix.
    ///
    /// # Specification
    /// - ensures: every application `f(t…)` written `f(i…, t…)`, its implicit
    ///   indices first, [`Self::strip`]ped back to `term`.
    /// - fails: as [`Self::face`] does for one side; [`Unsorted::Unfixed`] when
    ///   an index no argument's sort fixes is left.
    /// - panics: none.
    /// - executable: none — as [`Self::face`].
    ///
    /// # Errors
    /// As the failure clause states.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a choice between a cut and a failure carries the
    ///   failure's grade, and an ill-sorted call is refused.
    /// - witness: `indexing::tests::a_closed_call_carries_the_grades_its_arguments_fix`
    #[inline]
    pub fn call(
        &self,
        term: &FreeTerm,
    ) -> Result<FreeTerm, Unsorted>
    {
        let mut solving = Solving::new(self);
        let (indexed, _sort) = solving.infer(term)?;
        let indexed = solving.resolved(&indexed);
        if indexed
            .to_node()
            .vars()
            .any(|name| name.as_ref().starts_with(UNKNOWN))
        {
            return Err(Unsorted::Unfixed);
        }
        Ok(indexed)
    }

    /// `term` with every operation application's indices left off: the term
    /// as written.
    ///
    /// # Specification
    /// - ensures: each application of a declared operation loses as many
    ///   leading arguments as the operation has implicit indices, where it has
    ///   that many more than its ports; every other node is kept.
    /// - panics: none.
    /// - executable: none — as [`Self::face`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an indexed law strips back to the law as written.
    /// - witness: `indexing::tests::a_categorys_laws_carry_their_objects`
    #[inline]
    #[must_use]
    pub fn strip(
        &self,
        term: &FreeTerm,
    ) -> FreeTerm
    {
        rebuilt(term, |_| None, Substitution::Once, Dropping::Indices(self))
    }
}

/// The names `sort`'s index terms apply, outermost first.
///
/// # Specification
/// trivial.
fn applied(sort: &FreeTerm) -> BTreeSet<Name>
{
    let mut names = BTreeSet::new();
    let mut pending = Vec::from([sort.clone()]);
    while let Some(next) = pending.pop() {
        match next.view() {
            TermView::Op { name, args } => {
                let _fresh = names.insert(name.clone());
                pending.extend(args.map(TermNode::to_term));
            },
            TermView::Ctor { args, .. }
            | TermView::Results { args }
            | TermView::Inst { args, .. }
            | TermView::Abs { args, .. }
            | TermView::Lam { args, .. } => pending.extend(args.map(TermNode::to_term)),
            TermView::Var(_) | TermView::Atom(_) | TermView::Bound(_) => {},
        }
    }
    names
}

/// One sorting problem: the unknowns solved so far and the sort each written
/// variable stands at.
struct Solving<'indexing>
{
    /// The description's operations.
    indexing: &'indexing Indexing,
    /// Each solved unknown's term.
    solved: BTreeMap<Name, FreeTerm>,
    /// Each written variable's sort.
    sorts: BTreeMap<Name, FreeTerm>,
    /// The unknowns minted so far.
    minted: usize,
}

impl<'indexing> Solving<'indexing>
{
    /// A problem over `indexing`'s operations, nothing solved.
    ///
    /// # Specification
    /// trivial.
    const fn new(indexing: &'indexing Indexing) -> Self
    {
        Self {
            indexing,
            solved: BTreeMap::new(),
            sorts: BTreeMap::new(),
            minted: 0,
        }
    }

    /// A fresh unknown.
    ///
    /// # Specification
    /// trivial.
    fn fresh(&mut self) -> FreeTerm
    {
        self.minted = self.minted.saturating_add(1);
        FreeTerm::var(format!("{UNKNOWN}{}", self.minted))
    }

    /// `term` with every solved unknown replaced by its solution, through.
    ///
    /// # Specification
    /// trivial.
    fn resolved(
        &self,
        term: &FreeTerm,
    ) -> FreeTerm
    {
        rebuilt(
            term,
            |name| self.solved.get(name),
            Substitution::Through,
            Dropping::Nothing,
        )
    }

    /// Unify `left` and `right`, binding unknowns only.
    ///
    /// # Specification
    /// trivial.
    fn unify(
        &mut self,
        left: &FreeTerm,
        right: &FreeTerm,
    ) -> Result<(), Unsorted>
    {
        let mut pending = Vec::from([(left.clone(), right.clone())]);
        while let Some((left, right)) = pending.pop() {
            let (left, right) = (self.resolved(&left), self.resolved(&right));
            if left == right {
                continue;
            }
            match (left.view(), right.view()) {
                (TermView::Var(name), _) if name.as_ref().starts_with(UNKNOWN) => {
                    self.bind(name, &right)?;
                },
                (_, TermView::Var(name)) if name.as_ref().starts_with(UNKNOWN) => {
                    self.bind(name, &left)?;
                },
                (
                    TermView::Op {
                        name: first,
                        args: first_args,
                    },
                    TermView::Op {
                        name: second,
                        args: second_args,
                    },
                )
                | (
                    TermView::Ctor {
                        name: first,
                        args: first_args,
                    },
                    TermView::Ctor {
                        name: second,
                        args: second_args,
                    },
                ) if first == second && first_args.len() == second_args.len() => {
                    pending.extend(
                        first_args
                            .map(TermNode::to_term)
                            .zip(second_args.map(TermNode::to_term)),
                    );
                },
                (
                    TermView::Var(_)
                    | TermView::Ctor { .. }
                    | TermView::Op { .. }
                    | TermView::Results { .. }
                    | TermView::Inst { .. }
                    | TermView::Abs { .. }
                    | TermView::Atom(_)
                    | TermView::Lam { .. }
                    | TermView::Bound(_),
                    _,
                ) => return Err(Unsorted::Clash),
            }
        }
        Ok(())
    }

    /// Solve the unknown `name` as `term`, refused where `term` names it.
    ///
    /// # Specification
    /// trivial.
    fn bind(
        &mut self,
        name: &Name,
        term: &FreeTerm,
    ) -> Result<(), Unsorted>
    {
        if term.to_node().vars().any(|named| named == name) {
            return Err(Unsorted::Clash);
        }
        let _unsolved = self.solved.insert(name.clone(), term.clone());
        Ok(())
    }

    /// `term` with each operation application carrying its indices, and the
    /// sort it stands at.
    ///
    /// # Specification
    /// - ensures: each variable at one sort wherever it stands, minted at its
    ///   first occurrence; each application's arguments read first to last,
    ///   each at the sort its port asks, the port's name standing for the
    ///   argument in the sorts after it, and its implicit indices fresh
    ///   unknowns.
    /// - fails: [`Unsorted::Unread`] for anything but a variable or a declared
    ///   operation at its port count; [`Unsorted::Clash`] as [`Self::unify`].
    /// - panics: none.
    /// - intension: a worklist of steps, so no call recurses.
    /// - executable: none — the sorts are the unknowns' solutions, which a
    ///   clause would re-derive by solving again.
    ///
    /// # Errors
    /// As the failure clause states.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Indexing::face`] and [`Indexing::call`].
    /// - witness: `indexing::tests::a_categorys_laws_carry_their_objects`
    /// - witness: `indexing::tests::a_closed_call_carries_the_grades_its_arguments_fix`
    fn infer(
        &mut self,
        term: &FreeTerm,
    ) -> Result<(FreeTerm, FreeTerm), Unsorted>
    {
        let indexing = self.indexing;
        let mut steps = Vec::from([Step::Read(term.clone())]);
        let mut done: Vec<(FreeTerm, FreeTerm)> = Vec::new();
        let mut renaming: BTreeMap<Name, FreeTerm> = BTreeMap::new();
        while let Some(step) = steps.pop() {
            match step {
                Step::Read(next) => match next.view() {
                    TermView::Var(name) => {
                        let sort = if let Some(sort) = self.sorts.get(name) {
                            sort.clone()
                        }
                        else {
                            let sort = self.fresh();
                            let _first = self.sorts.insert(name.clone(), sort.clone());
                            sort
                        };
                        done.push((next.clone(), sort));
                    },
                    TermView::Op { name, args } => {
                        let Some(sorting) = indexing.operations.get(name)
                        else {
                            return Err(Unsorted::Unread);
                        };
                        if args.len() != sorting.inputs.len() {
                            return Err(Unsorted::Unread);
                        }
                        schedule(&mut steps, Step::Op(name.clone(), args.len()), args);
                    },
                    TermView::Ctor { .. }
                    | TermView::Results { .. }
                    | TermView::Inst { .. }
                    | TermView::Abs { .. }
                    | TermView::Atom(_)
                    | TermView::Lam { .. }
                    | TermView::Bound(_) => return Err(Unsorted::Unread),
                },
                Step::Op(name, count) => {
                    let Some(sorting) = indexing.operations.get(&name)
                    else {
                        return Err(Unsorted::Unread);
                    };
                    renaming.clear();
                    for implicit in &sorting.implicits {
                        let unknown = self.fresh();
                        let _first = renaming.insert(implicit.clone(), unknown);
                    }
                    let start = done.len().saturating_sub(count);
                    for (&(ref port, ref expected), &(ref argument, ref sort)) in sorting
                        .inputs
                        .iter()
                        .zip(done.get(start ..).unwrap_or_default())
                    {
                        let expected = rebuilt(
                            expected,
                            |name| renaming.get(name),
                            Substitution::Once,
                            Dropping::Nothing,
                        );
                        self.unify(sort, &expected)?;
                        let _first = renaming.insert(port.clone(), argument.clone());
                    }
                    let output = rebuilt(
                        &sorting.output,
                        |name| renaming.get(name),
                        Substitution::Once,
                        Dropping::Nothing,
                    );
                    let indices = sorting
                        .implicits
                        .iter()
                        .filter_map(|implicit| renaming.get(implicit).cloned());
                    let applied = FreeTerm::op(
                        name,
                        indices.chain(done.drain(start ..).map(|(argument, _)| argument)),
                    );
                    done.push((applied, output));
                },
                Step::Ctor(..) | Step::Results(_) | Step::Inst(..) => {
                    return Err(Unsorted::Unread);
                },
            }
        }
        done.pop().ok_or(Unsorted::Unread)
    }
}

#[cfg(test)]
mod tests
{
    use alloc::vec::Vec;

    use gandr_theory_levitation::Attrs;
    use gandr_theory_levitation::BridgeArity;
    use gandr_theory_levitation::DeclPolarity;
    use gandr_theory_levitation::FreeTerm;
    use gandr_theory_levitation::Name;
    use gandr_theory_levitation::NominalId;
    use gandr_theory_levitation::NominalSerial;
    use gandr_theory_levitation::OperDesc;
    use gandr_theory_levitation::RuleFace;
    use gandr_theory_levitation::SortDesc;
    use gandr_theory_levitation::SortIndex;
    use gandr_theory_levitation::SortRef;
    use gandr_theory_levitation::SurfaceSpan;
    use gandr_theory_levitation::TheoryDesc;
    use quenchant_shape::shape::Maybe;

    use super::Indexing;
    use super::Unsorted;
    use super::indexed_reading;

    /// No grade: the descriptions here are ungraded.
    #[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
    enum Ungraded {}

    /// A variable.
    ///
    /// # Specification
    /// trivial.
    fn var<V>(name: V) -> FreeTerm
    where
        V: Into<Name>,
    {
        FreeTerm::var(name)
    }

    /// An operation applied.
    ///
    /// # Specification
    /// trivial.
    fn op<V, const N: usize>(
        name: V,
        args: [FreeTerm; N],
    ) -> FreeTerm
    where
        V: Into<Name>,
    {
        FreeTerm::op(name, args)
    }

    /// A port of the sort `sort` applied to `arguments`.
    ///
    /// # Specification
    /// trivial.
    fn port<P, S, const N: usize>(
        name: P,
        sort: S,
        arguments: [FreeTerm; N],
    ) -> SortRef
    where
        P: Into<Name>,
        S: Into<Name>,
    {
        SortRef::new(name, sort).applied(arguments)
    }

    /// The operation `name` from `inputs` to `output`.
    ///
    /// # Specification
    /// trivial.
    fn oper<O, const N: usize>(
        name: O,
        inputs: [SortRef; N],
        output: SortRef,
    ) -> OperDesc
    where
        O: Into<Name>,
    {
        OperDesc::new(
            name,
            BridgeArity::single_output(inputs, output),
            Attrs::empty(),
        )
    }

    /// A face over two sides.
    ///
    /// # Specification
    /// trivial.
    fn face(
        lhs: FreeTerm,
        rhs: FreeTerm,
    ) -> RuleFace
    {
        RuleFace::new(lhs, rhs, Vec::new(), SurfaceSpan::default())
    }

    /// A theory over `sorts` and `opers`.
    ///
    /// # Specification
    /// trivial.
    fn theory<const S: usize, const O: usize>(
        sorts: [SortDesc; S],
        opers: [OperDesc; O],
    ) -> TheoryDesc<Ungraded>
    {
        let mut description = TheoryDesc::new(
            NominalId::new(NominalSerial::from(0_u64), "T"),
            Vec::new(),
            [],
            opers,
            [],
            DeclPolarity::Data,
            Attrs::empty(),
        );
        description.sorts = sorts.into();
        description
    }

    /// The shape of a category: objects, homs between two of them, the
    /// identity and composition.
    ///
    /// # Specification
    /// trivial.
    fn category() -> TheoryDesc<Ungraded>
    {
        theory(
            [
                SortDesc::new("Ob", DeclPolarity::Data),
                SortDesc::family("Hom", DeclPolarity::Data, [
                    SortIndex::new("dom", "Ob"),
                    SortIndex::new("cod", "Ob"),
                ]),
            ],
            [
                oper(
                    "id",
                    [SortRef::new("a", "Ob")],
                    port("out", "Hom", [var("a"), var("a")]),
                ),
                oper(
                    "comp",
                    [
                        port("f", "Hom", [var("a"), var("b")]),
                        port("g", "Hom", [var("b"), var("c")]),
                    ],
                    port("out", "Hom", [var("a"), var("c")]),
                ),
            ],
        )
    }

    /// A choice with cut over a grade-indexed sort: a cut at the bottom grade,
    /// a failure at the top, and a choice whose first branch cuts.
    ///
    /// # Specification
    /// trivial.
    fn cut() -> TheoryDesc<Ungraded>
    {
        let bottom = || op("bot", []);
        theory(
            [
                SortDesc::new("Grade", DeclPolarity::Data),
                SortDesc::family("M", DeclPolarity::Data, [SortIndex::new("g", "Grade")]),
            ],
            [
                oper("bot", [], SortRef::new("out", "Grade")),
                oper("top", [], SortRef::new("out", "Grade")),
                oper("cut", [], port("out", "M", [bottom()])),
                oper("fail", [], port("out", "M", [op("top", [])])),
                oper(
                    "orBot",
                    [port("x", "M", [bottom()]), port("y", "M", [var("e")])],
                    port("out", "M", [bottom()]),
                ),
            ],
        )
    }

    /// A category's unit law carries the objects its variables fix and strips
    /// back to the law as written; two identities composed at objects apart
    /// are ill sorted; a plain signature has no indexed reading.
    #[test]
    fn a_categorys_laws_carry_their_objects()
    {
        let Maybe::Present(indexing) = Indexing::of(&category())
        else {
            panic!("a category's homs are indexed");
        };
        let unit = face(op("comp", [op("id", [var("a")]), var("f")]), var("f"));
        let indexed = indexing.face(&unit).expect("the unit law is well sorted");
        let Some(codomain) = indexed
            .lhs
            .collect_vars()
            .into_iter()
            .find(|name| name.as_ref().starts_with(super::UNKNOWN))
        else {
            panic!("the codomain is fixed by no written variable");
        };
        assert_eq!(
            indexed.lhs,
            op("comp", [
                var("a"),
                var("a"),
                var(codomain),
                op("id", [var("a")]),
                var("f")
            ]),
            "composition carries its three objects, two fixed by the identity"
        );
        assert_eq!(indexing.strip(&indexed.lhs), unit.lhs, "and strips back");
        let apart = face(
            op("comp", [op("id", [var("a")]), op("id", [var("b")])]),
            op("id", [var("a")]),
        );
        assert_eq!(
            indexing.face(&apart),
            Err(Unsorted::Clash),
            "two identities compose only at one object"
        );
        let mut plain = category();
        plain.sorts = [SortDesc::new("Ob", DeclPolarity::Data)].into();
        assert_eq!(
            Indexing::of(&plain),
            Maybe::Absent(indexed_reading::Absent::Unindexed),
            "a plain signature carries no indices"
        );
    }

    /// A closed choice carries the grade its failure stands at, and a failure
    /// passed where a cut is asked is refused.
    #[test]
    fn a_closed_call_carries_the_grades_its_arguments_fix()
    {
        let Maybe::Present(indexing) = Indexing::of(&cut())
        else {
            panic!("the computations are graded");
        };
        let call = op("orBot", [op("cut", []), op("fail", [])]);
        assert_eq!(
            indexing.call(&call),
            Ok(op("orBot", [op("top", []), op("cut", []), op("fail", [])])),
            "the choice carries its failure's grade"
        );
        assert_eq!(
            indexing.call(&op("orBot", [op("fail", []), op("cut", [])])),
            Err(Unsorted::Clash),
            "a failure where a cut is asked is ill sorted"
        );
    }
}
