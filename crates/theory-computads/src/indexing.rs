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
//! A sort is rigid when no law rewrites at it and none of its operations takes
//! an argument at a sort a law rewrites at. Two terms of a rigid sort are equal
//! exactly when they are one term. An index at a flexible sort, a context of a
//! category with families, is equal to another only modulo the laws.
//!
//! The reading carries every index when each law reads over every index and
//! the path order orients each law so read, an operation's written arguments
//! compared before its indices (#5016). A step may then rewrite inside an
//! index, and the order makes the carried rules terminate on their own. An
//! overlap the carried indices refuse is no peak of the carried rules, since
//! no term with those indices holds both redexes. Otherwise only an index at a
//! rigid sort is carried, and the reading keeps every overlap it would refuse:
//! a whisker's composite index `comp(f, h)` is not carried (#1510).
//!
//! A port's sort may apply an operation with indices of its own, as
//! `Tm(d, subTy(a, s))` does. The reading carries that index with the indices
//! its operation's sorting fixes, solved from the input ports' sorts (#5042).
//! Each law has a rank: the position of its left side's sort among the sorts.
//! A law's two sides stand at one sort modulo the laws of lower rank, the
//! discipline of a generalized algebraic theory: a `CwF`'s identity law on
//! terms sorts only modulo the identity law on types. A law whose sides sort
//! apart even so is refused by name. A left side whose carried index applies an
//! operation that a law of lower rank rewrites is refused too. A step inside
//! that index meets a peak, and the decision of such a law is #5117's.
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
use gandr_theory_levitation::OperDesc;
use gandr_theory_levitation::Precedence;
use gandr_theory_levitation::RuleFace;
use gandr_theory_levitation::SortRef;
use gandr_theory_levitation::TermNode;
use gandr_theory_levitation::TermView;
use gandr_theory_levitation::TheoryDesc;
use gandr_theory_levitation::path_greater;
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
            /// than one output, or a law has no sorting, instantiates a
            /// variable or fires under a row: the reading carries none of
            /// them.
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
    /// An index the term's sorting fixes applies an operation with indices
    /// of its own that the reading does not carry: no port of the operation
    /// it stands in fixes them (#4128).
    Nested,
    /// An index the left side's sorting fixes applies an operation with
    /// indices of its own, and a law at an earlier sort rewrites that
    /// operation: the law's decision meets a peak inside an index (#5117).
    Rewritten,
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

impl Sorting
{
    /// `operation`'s sorting, each port's sort the term `sort` writes it as.
    ///
    /// # Specification
    /// trivial.
    fn of<S>(
        operation: &OperDesc,
        output: &SortRef,
        sort: S,
    ) -> Self
    where
        S: Fn(&SortRef) -> FreeTerm,
    {
        let bound: BTreeSet<&Name> = operation
            .arity
            .inputs
            .iter()
            .map(|port| &port.name)
            .collect();
        let inputs: Box<[(Name, FreeTerm)]> = operation
            .arity
            .inputs
            .iter()
            .map(|port| (port.name.clone(), sort(port)))
            .collect();
        let output = sort(output);
        let mut implicits: Vec<Name> = Vec::new();
        let mut seen: BTreeSet<&Name> = BTreeSet::new();
        for stated in inputs
            .iter()
            .map(|&(_, ref stated)| stated)
            .chain([&output])
        {
            for name in stated.to_node().vars() {
                if !bound.contains(name) && seen.insert(name) {
                    implicits.push(name.clone());
                }
            }
        }
        Self {
            implicits: implicits.into(),
            inputs,
            output,
        }
    }

    /// `self` with each index term of its ports' sorts carrying the indices of
    /// the operations it applies, read under `earlier`, each input port at its
    /// sort so carried.
    ///
    /// # Specification
    /// - ensures: an index term that is a variable stays as written; every
    ///   other one is the term [`Solving::infer`] reads it as under `earlier`,
    ///   its unknowns solved over the ports read before it, and stays as
    ///   written where that reading fails or leaves an index unfixed. The
    ///   implicit indices are kept, so an operation's own indices are its
    ///   written ones.
    /// - panics: none.
    /// - executable: none — the carried terms are the solution itself.
    /// - intension: one sorting problem for the whole operation, its ports read
    ///   first to last.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the type a term substitution moves its term's type to
    ///   carries the two contexts the substitution stands between.
    /// - witness: `indexing::tests::a_cwfs_laws_on_terms_check_modulo_its_laws_on_types_5042`
    fn elaborated(
        self,
        earlier: &BTreeMap<Name, Self>,
    ) -> Self
    {
        // An index term as written, and as carried when it carries.
        type ReadIndex = (FreeTerm, Option<FreeTerm>);
        let mut solving = Solving::new(earlier, Carrying::Indices);
        let stated: Vec<&FreeTerm> = self
            .inputs
            .iter()
            .map(|&(_, ref stated)| stated)
            .chain([&self.output])
            .collect();
        // Each port's sort name and index terms, each as written and as
        // carried, read before any is resolved: a later port's sort may solve
        // an unknown an earlier one left open.
        let mut read: Vec<Option<(Name, Vec<ReadIndex>)>> = Vec::with_capacity(stated.len());
        for (place, &sort) in stated.iter().enumerate() {
            let TermView::Ctor { name, args } = sort.view()
            else {
                read.push(None);
                continue;
            };
            let terms: Vec<ReadIndex> = args
                .map(|arg| {
                    let written = arg.to_term();
                    let carried = match written.view() {
                        TermView::Var(_) => None,
                        TermView::Op { .. }
                        | TermView::Ctor { .. }
                        | TermView::Results { .. }
                        | TermView::Inst { .. }
                        | TermView::Abs { .. }
                        | TermView::Atom(_)
                        | TermView::Lam { .. }
                        | TermView::Bound(_) => solving.infer(&written).ok().map(|(term, _)| term),
                    };
                    (written, carried)
                })
                .collect();
            if let Some(&(ref port, _)) = self.inputs.get(place) {
                let carried = FreeTerm::ctor(
                    name.clone(),
                    terms.iter().map(|&(ref written, ref carried)| {
                        carried.as_ref().unwrap_or(written).clone()
                    }),
                );
                let _first = solving.sorts.insert(port.clone(), carried);
            }
            read.push(Some((name.clone(), terms)));
        }
        let mut finished = read.into_iter().zip(stated).map(|(read, stated)| {
            let Some((name, terms)) = read
            else {
                return stated.clone();
            };
            FreeTerm::ctor(
                name,
                terms.into_iter().map(|(written, carried)| {
                    carried
                        .map(|carried| solving.resolved(&carried))
                        .filter(|resolved| {
                            !resolved
                                .to_node()
                                .vars()
                                .any(|name| name.as_ref().starts_with(UNKNOWN))
                        })
                        .unwrap_or(written)
                }),
            )
        });
        let inputs: Box<[(Name, FreeTerm)]> = self
            .inputs
            .iter()
            .zip(finished.by_ref())
            .map(|(&(ref name, _), sort)| (name.clone(), sort))
            .collect();
        let output = finished.next().unwrap_or_else(|| self.output.clone());
        Self {
            implicits: self.implicits,
            inputs,
            output,
        }
    }
}

/// The operations of a description over indexed sorts, each with the indices
/// its applications carry.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Indexing
{
    /// Each operation's sorting over the indices it carries, at rigid sorts,
    /// by name.
    operations: BTreeMap<Name, Sorting>,
    /// Each operation's sorting over every index as written, by name: the
    /// check that a law's two sides stand at one sort.
    written: BTreeMap<Name, Sorting>,
    /// The place of each operation's output sort among the description's
    /// sorts, by the operation's name.
    ranks: BTreeMap<Name, Rank>,
    /// Each law that reads, in order of its rank: the laws a later sort's
    /// sorting is read modulo.
    laws: Vec<Law>,
}

/// The place of a sort among a description's sorts: a law's sort is the sort
/// its left side's operation outputs, and a law is read modulo the laws of
/// lower rank.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct Rank(usize);

/// A law that reads, as written and over the indices it carries, at its rank.
#[derive(Clone, Debug, Eq, PartialEq)]
struct Law
{
    /// The rank of its sort.
    rank: Rank,
    /// The law as written.
    written: RuleFace,
    /// The law over the indices the reading carries.
    carried: RuleFace,
}

/// Each indexed sort's index positions at a flexible sort, which the reading
/// does not carry.
#[repr(transparent)]
struct Flexible<'description>
{
    /// The positions left off, by sort.
    positions: BTreeMap<&'description Name, BTreeSet<usize>>,
}

impl<'description> Flexible<'description>
{
    /// The flexible positions of `description`'s sorts.
    ///
    /// # Specification
    /// - ensures: a sort is flexible when some law's side applies an operation
    ///   whose output stands at it, or an operation whose output stands at it
    ///   takes an input at a flexible sort; a position is left off when its
    ///   binder ranges over a flexible sort.
    /// - panics: none.
    /// - executable: none — the positions are the fixed point itself; a
    ///   predicate would grow it a second time.
    /// - intension: the flexible sorts grown to their least fixed point.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a category's objects are rigid, and a 2-cell's
    ///   1-cells under a law of composition are not.
    /// - witness: `indexing::tests::a_whiskers_composite_index_leaves_the_other_laws_indexed_1510`
    fn of<G>(description: &'description TheoryDesc<G>) -> Self
    {
        let outputs: BTreeMap<&Name, &Name> = description
            .opers
            .iter()
            .filter_map(|operation| Some((&operation.name, &operation.arity.outputs.first()?.sort)))
            .collect();
        let mut flexible: BTreeSet<&Name> = BTreeSet::new();
        for face in &description.rules {
            for side in [&face.lhs, &face.rhs] {
                if let TermView::Op { name, .. } = side.view()
                    && let Some(&sort) = outputs.get(name)
                {
                    let _first = flexible.insert(sort);
                }
            }
        }
        loop {
            let before = flexible.len();
            for operation in &description.opers {
                if operation
                    .arity
                    .inputs
                    .iter()
                    .any(|port| flexible.contains(&port.sort))
                    && let Some(output) = operation.arity.outputs.first()
                {
                    let _first = flexible.insert(&output.sort);
                }
            }
            if flexible.len() == before {
                break;
            }
        }
        let positions = description
            .sorts
            .iter()
            .filter_map(|sort| {
                let left: BTreeSet<usize> = sort
                    .indices
                    .iter()
                    .enumerate()
                    .filter(|&(_, index)| flexible.contains(&index.sort))
                    .map(|(place, _)| place)
                    .collect();
                (!left.is_empty()).then_some((&sort.name, left))
            })
            .collect();
        Self { positions }
    }

    /// The sort `port` stands at over the indices the reading carries.
    ///
    /// # Specification
    /// trivial.
    fn carried(
        &self,
        port: &SortRef,
    ) -> FreeTerm
    {
        let left = self.positions.get(&port.sort);
        FreeTerm::ctor(
            port.sort.clone(),
            port.arguments
                .iter()
                .enumerate()
                .filter(|&(place, _)| !left.is_some_and(|left| left.contains(&place)))
                .map(|(_, argument)| argument.clone()),
        )
    }
}

/// The first character of an unknown the solver mints; no written variable
/// begins with it.
const UNKNOWN: char = '·';

/// The most laws a sort check fires while it normalizes the two sorts of a
/// law's sides; past it, the two sides are refused as [`Unsorted::Clash`].
const SORT_STEPS: usize = 1 << 10;

/// `term` normalized by `laws`, each fired where its left side matches.
///
/// # Specification
/// - ensures: [`Ok`] with a term no law of `laws` matches at any operation
///   application, reached from `term` by firing laws, each application's
///   arguments normalized before the application.
/// - fails: [`Unsorted::Clash`] when more than [`SORT_STEPS`] laws fire.
/// - panics: none.
/// - intension: a worklist of steps, so no call recurses; a law's reduct is
///   read again, so its own redexes fire too.
/// - executable: none — a normal form is what this computes; checking one is
///   another match of every law at every application.
///
/// # Errors
/// As the failure clause states.
///
/// # Adequacy
/// - hypothesis: L3 — a type substituted along an identity normalizes to the
///   type, and a sort no law matches stays as it is.
/// - witness: `indexing::tests::a_cwfs_laws_on_terms_check_modulo_its_laws_on_types_5042`
fn normal(
    term: &FreeTerm,
    laws: &[&RuleFace],
) -> Result<FreeTerm, Unsorted>
{
    let mut steps = Vec::from([Step::Read(term.clone())]);
    let mut built: Vec<FreeTerm> = Vec::new();
    let mut fired = 0_usize;
    while let Some(step) = steps.pop() {
        match step {
            Step::Read(next) => match next.view() {
                TermView::Op { name, args } => {
                    schedule(&mut steps, Step::Op(name.clone(), args.len()), args);
                },
                TermView::Ctor { name, args } => {
                    schedule(&mut steps, Step::Ctor(name.clone(), args.len()), args);
                },
                TermView::Var(_)
                | TermView::Results { .. }
                | TermView::Inst { .. }
                | TermView::Abs { .. }
                | TermView::Atom(_)
                | TermView::Lam { .. }
                | TermView::Bound(_) => built.push(next.clone()),
            },
            Step::Op(name, count) => {
                let start = built.len().saturating_sub(count);
                let applied = FreeTerm::op(name, built.drain(start ..));
                match laws.iter().find_map(|law| reduct(law, &applied)) {
                    Some(reduct) => {
                        fired = fired.saturating_add(1);
                        if fired > SORT_STEPS {
                            return Err(Unsorted::Clash);
                        }
                        steps.push(Step::Read(reduct));
                    },
                    None => built.push(applied),
                }
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
    built.pop().ok_or(Unsorted::Unread)
}

/// `law`'s right side at the match of its left side against `term`, when it
/// matches at the root.
///
/// # Specification
/// trivial.
fn reduct(
    law: &RuleFace,
    term: &FreeTerm,
) -> Option<FreeTerm>
{
    let bindings = matched(&law.lhs, term)?;
    Some(rebuilt(
        &law.rhs,
        |name| bindings.get(name),
        Substitution::Once,
        Dropping::Nothing,
    ))
}

/// The binding of each variable of `pattern` that makes it `term`, when one
/// does: every variable of `term` stands as a constant.
///
/// # Specification
/// - ensures: [`Some`] exactly when each variable of `pattern` binds one
///   subterm of `term` at its every occurrence, and every other node of
///   `pattern` is the node of `term` at its place.
/// - panics: none.
/// - intension: a worklist of node pairs, so no call recurses.
/// - executable: none — the bindings are the match itself.
///
/// # Adequacy
/// - hypothesis: L3 — as [`normal`]: an identity's repeated context binds one
///   context only.
/// - witness: `indexing::tests::a_cwfs_laws_on_terms_check_modulo_its_laws_on_types_5042`
fn matched(
    pattern: &FreeTerm,
    term: &FreeTerm,
) -> Option<BTreeMap<Name, FreeTerm>>
{
    let mut bindings: BTreeMap<Name, FreeTerm> = BTreeMap::new();
    let mut pending = Vec::from([(pattern.clone(), term.clone())]);
    while let Some((pattern, term)) = pending.pop() {
        match (pattern.view(), term.view()) {
            (TermView::Var(name), _) => {
                if let Some(bound) = bindings.get(name) {
                    if *bound != term {
                        return None;
                    }
                }
                else {
                    let _first = bindings.insert(name.clone(), term.clone());
                }
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
                TermView::Ctor { .. }
                | TermView::Op { .. }
                | TermView::Results { .. }
                | TermView::Inst { .. }
                | TermView::Abs { .. }
                | TermView::Atom(_)
                | TermView::Lam { .. }
                | TermView::Bound(_),
                _,
            ) => {
                if pattern != term {
                    return None;
                }
            },
        }
    }
    Some(bindings)
}

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
    /// - ensures: one sorting per operation over the indices it carries, and
    ///   one over every index as written, each one's implicit indices the
    ///   variables its ports' sorts name that no input port binds, in order of
    ///   first occurrence. Where no index stands at a flexible sort
    ///   ([`Flexible`]) every index is carried. Otherwise every index is
    ///   carried when each law of `description` reads over every index and the
    ///   path order over the precedence its laws induce ([`Precedence::of`])
    ///   orients each law so read, a law refused by name ([`Unsorted::Clash`],
    ///   [`Unsorted::Rewritten`]) aside; else only the indices at rigid sorts
    ///   are.
    /// - fails: [`indexed_reading::Absent::Unindexed`] when no sort is indexed;
    ///   [`indexed_reading::Absent::Unsupported`] when a port binds or
    ///   abstracts, or an operation has other than one output. A carried index
    ///   applying an operation whose own indices no port fixes leaves the
    ///   reading whole: a term whose sorting meets it is refused
    ///   [`Unsorted::Nested`].
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a category's composition is implicit in its three
    ///   objects and its identity in none, and a plain signature has no indexed
    ///   reading; a category with families carries the context its
    ///   substitutions stand between, though its laws rewrite substitutions.
    /// - witness: `indexing::tests::a_categorys_laws_carry_their_objects`
    /// - witness: `indexing::tests::a_cwfs_laws_carry_every_index_5016`
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
        let flexible = Flexible::of(description);
        let rigid = Self::carrying(description, &flexible);
        if flexible.positions.is_empty() {
            return rigid;
        }
        let Maybe::Present(every) = Self::carrying(description, &Flexible {
            positions: BTreeMap::new(),
        })
        else {
            return rigid;
        };
        let precedence = Precedence::of(description);
        let oriented = description.rules.iter().all(|face| match every.face(face) {
            Ok(indexed) => bool::from(path_greater(&precedence, &indexed.lhs, &indexed.rhs)),
            Err(Unsorted::Clash | Unsorted::Rewritten) => true,
            Err(Unsorted::Unread | Unsorted::Unfixed | Unsorted::Nested) => false,
        });
        if oriented {
            Maybe::Present(every)
        }
        else {
            rigid
        }
    }

    /// The reading of `description`'s operations that leaves off the index
    /// positions `flexible` names, with the laws that read under it.
    ///
    /// # Specification
    /// - ensures: each operation's carried sorting elaborated
    ///   ([`Sorting::elaborated`]) under the operations declared before it;
    ///   each law of `description` that reads ([`Self::face`]) kept with its
    ///   rank, read in order of rank, so each is read modulo the laws of lower
    ///   rank.
    /// - fails: [`indexed_reading::Absent::Unsupported`] when a port binds or
    ///   abstracts, or an operation has other than one output.
    /// - panics: none.
    /// - executable: none — the reading is the construction itself.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the `CwF`'s term substitution carries `subTy` in its
    ///   type index, and its identity law on terms reads only after the
    ///   identity law on types, a law of lower rank.
    /// - witness: `indexing::tests::a_cwfs_laws_on_terms_check_modulo_its_laws_on_types_5042`
    /// - witness: `indexing::tests::a_cwfs_laws_carry_every_index_5016`
    fn carrying<G>(
        description: &TheoryDesc<G>,
        flexible: &Flexible<'_>,
    ) -> Maybe<Self, indexed_reading::Absent>
    {
        let (mut operations, mut written) = (BTreeMap::new(), BTreeMap::new());
        for operation in &description.opers {
            let ports = operation
                .arity
                .inputs
                .iter()
                .chain(operation.arity.outputs.iter());
            let (Some(output), 1) = (
                operation.arity.outputs.first(),
                operation.arity.outputs.len(),
            )
            else {
                return Maybe::Absent(indexed_reading::Absent::Unsupported);
            };
            if ports
                .clone()
                .any(|port| !port.bindings.is_empty() || !port.abstractions.is_empty())
            {
                return Maybe::Absent(indexed_reading::Absent::Unsupported);
            }
            let carried = Sorting::of(operation, output, |port| flexible.carried(port))
                .elaborated(&operations);
            let _first = operations.insert(operation.name.clone(), carried);
            let _first = written.insert(
                operation.name.clone(),
                Sorting::of(operation, output, sort_term),
            );
        }
        let places: BTreeMap<&Name, Rank> = description
            .sorts
            .iter()
            .enumerate()
            .map(|(place, sort)| (&sort.name, Rank(place)))
            .collect();
        let ranks = description
            .opers
            .iter()
            .filter_map(|operation| {
                let output = &operation.arity.outputs.first()?.sort;
                Some((operation.name.clone(), *places.get(output)?))
            })
            .collect();
        let mut indexing = Self {
            operations,
            written,
            ranks,
            laws: Vec::new(),
        };
        let mut ranked: Vec<(Rank, &RuleFace)> = description
            .rules
            .iter()
            .filter_map(|face| Some((indexing.rank(face)?, face)))
            .collect();
        ranked.sort_by_key(|&(rank, _)| rank);
        for (rank, face) in ranked {
            if let Ok(carried) = indexing.face(face) {
                indexing.laws.push(Law {
                    rank,
                    written: face.clone(),
                    carried,
                });
            }
        }
        Maybe::Present(indexing)
    }

    /// `face` with each operation application carrying its indices, solved
    /// from the sorts its variables stand at.
    ///
    /// # Specification
    /// - ensures: both sides with every application `f(t…)` written `f(i…,
    ///   t…)`, its carried implicit indices first, an index that applies an
    ///   operation with indices of its own carrying them too; the two sides at
    ///   one sort over every index as written and over the carried ones, each
    ///   [`Self::strip`]ped back to the side as written; an index no sort fixes
    ///   is a fresh variable of the left side. Two sides whose sorts do not
    ///   unify as they stand unify after each sort is normalized by the laws of
    ///   lower rank ([`Solving::unify_modulo`]).
    /// - fails: [`Unsorted::Unread`] for a side applying anything but a
    ///   declared operation at its port count, or naming a variable no other
    ///   way; [`Unsorted::Clash`] when two sorts asked of one subterm do not
    ///   unify, or the two sides' sorts do not unify modulo the laws of lower
    ///   rank; [`Unsorted::Nested`] when a carried index applies an operation
    ///   with indices of its own at its port count alone, which no port fixes;
    ///   [`Unsorted::Rewritten`] when the left side's carried index applies an
    ///   operation that heads a law of lower rank ([`Self::unnested`]);
    ///   [`Unsorted::Unfixed`] when the right side names an index the left
    ///   side's sorting does not fix.
    /// - panics: none.
    /// - executable: none — the strip-back clause compares terms built from the
    ///   receiver's sorting, which a clause may not read.
    ///
    /// # Errors
    /// As the failure clause states.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the category's unit laws carry the objects their
    ///   variables fix, and a law equating two sorts apart is refused; a
    ///   `CwF`'s identity law on terms sorts only modulo its identity law on
    ///   types.
    /// - witness: `indexing::tests::a_categorys_laws_carry_their_objects`
    /// - witness: `indexing::tests::a_cwfs_laws_on_terms_check_modulo_its_laws_on_types_5042`
    #[inline]
    pub fn face(
        &self,
        face: &RuleFace,
    ) -> Result<RuleFace, Unsorted>
    {
        let rank = self.rank(face);
        let mut written = Solving::new(&self.written, Carrying::Written);
        let (_, left_sort) = written.infer(&face.lhs)?;
        let (_, right_sort) = written.infer(&face.rhs)?;
        let laws: Vec<&RuleFace> = self.below(rank).map(|law| &law.written).collect();
        written.unify_modulo(&left_sort, &right_sort, &laws)?;
        let mut solving = Solving::new(&self.operations, Carrying::Indices);
        let (left, left_sort) = solving.infer(&face.lhs)?;
        let (right, right_sort) = solving.infer(&face.rhs)?;
        let laws: Vec<&RuleFace> = self.below(rank).map(|law| &law.carried).collect();
        solving.unify_modulo(&left_sort, &right_sort, &laws)?;
        let (lhs, rhs) = (solving.resolved(&left), solving.resolved(&right));
        let heads: BTreeSet<&Name> = self
            .below(rank)
            .filter_map(|law| match law.carried.lhs.view() {
                TermView::Op { name, .. } => Some(name),
                TermView::Var(_)
                | TermView::Ctor { .. }
                | TermView::Results { .. }
                | TermView::Inst { .. }
                | TermView::Abs { .. }
                | TermView::Atom(_)
                | TermView::Lam { .. }
                | TermView::Bound(_) => None,
            })
            .collect();
        self.unnested(&lhs, &heads)?;
        self.unnested(&rhs, &BTreeSet::new())?;
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
    /// - ensures: every application `f(t…)` written `f(i…, t…)`, its carried
    ///   implicit indices first, [`Self::strip`]ped back to `term`, its sorts
    ///   checked over every index as written.
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
        let _sorted = Solving::new(&self.written, Carrying::Written).infer(term)?;
        let mut solving = Solving::new(&self.operations, Carrying::Indices);
        let (indexed, _sort) = solving.infer(term)?;
        let indexed = solving.resolved(&indexed);
        self.unnested(&indexed, &BTreeSet::new())?;
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

    /// The rank of `face`'s sort: the place of the sort its left side's
    /// operation outputs.
    ///
    /// # Specification
    /// trivial.
    fn rank(
        &self,
        face: &RuleFace,
    ) -> Option<Rank>
    {
        let TermView::Op { name, .. } = face.lhs.view()
        else {
            return None;
        };
        self.ranks.get(name).copied()
    }

    /// The laws below `rank`, in order of rank; none without a rank.
    ///
    /// # Specification
    /// trivial.
    fn below(
        &self,
        rank: Option<Rank>,
    ) -> impl Iterator<Item = &Law>
    {
        self.laws
            .iter()
            .filter(move |law| rank.is_some_and(|rank| law.rank < rank))
    }

    /// `term` checked for an index, one of an application's implicit indices
    /// first, that applies an operation with indices of its own at its written
    /// arity, an index the elaboration of a port's sort did not carry; or one
    /// that applies such an operation `heads` names, which a law rewrites.
    ///
    /// # Specification
    /// - ensures: `Ok` when no application of a declared operation at its
    ///   implicit indices and port count together has, within one of its
    ///   implicit indices, an application of an operation whose sorting has
    ///   implicit indices at its port count alone, or one `heads` names.
    /// - fails: [`Unsorted::Nested`] for the first; [`Unsorted::Rewritten`] for
    ///   the second.
    /// - panics: none.
    /// - executable: none — the answer reads the receiver's sorting, which a
    ///   clause may not read.
    /// - intension: one walk of the term from a worklist.
    ///
    /// # Errors
    /// As the failure clause states.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a whisker's composite index composes a hom whose
    ///   objects no port fixes, and a category's laws nest none; the `CwF`'s
    ///   composite law on terms holds a type index the laws on types rewrite.
    /// - witness: `indexing::tests::a_whiskers_composite_index_leaves_the_other_laws_indexed_1510`
    /// - witness: `indexing::tests::a_cwfs_laws_on_terms_check_modulo_its_laws_on_types_5042`
    fn unnested(
        &self,
        term: &FreeTerm,
        heads: &BTreeSet<&Name>,
    ) -> Result<(), Unsorted>
    {
        let mut pending = Vec::from([(term.clone(), false)]);
        while let Some((next, in_index)) = pending.pop() {
            match next.view() {
                TermView::Op { name, args } => {
                    let sorting = self.operations.get(name);
                    let indices = sorting.map_or(0, |sorting| {
                        let implicit = sorting.implicits.len();
                        if args.len() == implicit.saturating_add(sorting.inputs.len()) {
                            implicit
                        }
                        else {
                            0
                        }
                    });
                    let own = sorting.is_some_and(|sorting| !sorting.implicits.is_empty());
                    if in_index && own && indices == 0 {
                        return Err(Unsorted::Nested);
                    }
                    if in_index && own && heads.contains(name) {
                        return Err(Unsorted::Rewritten);
                    }
                    pending.extend(
                        args.enumerate()
                            .map(|(place, arg)| (arg.to_term(), in_index || place < indices)),
                    );
                },
                TermView::Ctor { args, .. }
                | TermView::Results { args }
                | TermView::Inst { args, .. }
                | TermView::Abs { args, .. }
                | TermView::Lam { args, .. } => {
                    pending.extend(args.map(|arg| (arg.to_term(), in_index)));
                },
                TermView::Var(_) | TermView::Atom(_) | TermView::Bound(_) => {},
            }
        }
        Ok(())
    }
}

/// What an application read by a sorting problem is built with.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Carrying
{
    /// Its implicit indices first, then its arguments.
    Indices,
    /// Its arguments only: the problem checks sorts and builds the term as
    /// written.
    Written,
}

/// One sorting problem: the unknowns solved so far and the sort each written
/// variable stands at.
struct Solving<'indexing>
{
    /// The sorting the problem reads applications under.
    sorting: &'indexing BTreeMap<Name, Sorting>,
    /// What an application is built with.
    carrying: Carrying,
    /// Each solved unknown's term.
    solved: BTreeMap<Name, FreeTerm>,
    /// Each written variable's sort.
    sorts: BTreeMap<Name, FreeTerm>,
    /// The unknowns minted so far.
    minted: usize,
}

impl<'indexing> Solving<'indexing>
{
    /// A problem over `sorting`, nothing solved.
    ///
    /// # Specification
    /// trivial.
    const fn new(
        sorting: &'indexing BTreeMap<Name, Sorting>,
        carrying: Carrying,
    ) -> Self
    {
        Self {
            sorting,
            carrying,
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

    /// Unify `left` and `right`, the two sorts of a law's sides; where they do
    /// not unify as they stand, unify their normal forms under `laws`.
    ///
    /// # Specification
    /// - ensures: [`Ok`] when the two sorts unify, or when their normal forms
    ///   ([`normal`]) under `laws` unify, read after the unknowns solved so
    ///   far; a failed first attempt leaves no unknown solved.
    /// - fails: [`Unsorted::Clash`] when neither unifies, or the normal forms
    ///   take more than [`SORT_STEPS`] laws.
    /// - panics: none.
    /// - executable: none — the solution is the problem's own state.
    ///
    /// # Errors
    /// As the failure clause states.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a `CwF`'s identity law on terms sorts only after its
    ///   left side's type is normalized by the identity law on types.
    /// - witness: `indexing::tests::a_cwfs_laws_on_terms_check_modulo_its_laws_on_types_5042`
    fn unify_modulo(
        &mut self,
        left: &FreeTerm,
        right: &FreeTerm,
        laws: &[&RuleFace],
    ) -> Result<(), Unsorted>
    {
        if laws.is_empty() {
            return self.unify(left, right);
        }
        let before = self.solved.clone();
        match self.unify(left, right) {
            Err(Unsorted::Clash) => {
                self.solved = before;
                let left = normal(&self.resolved(left), laws)?;
                let right = normal(&self.resolved(right), laws)?;
                self.unify(&left, &right)
            },
            unified @ (Ok(())
            | Err(
                Unsorted::Unread | Unsorted::Unfixed | Unsorted::Nested | Unsorted::Rewritten,
            )) => unified,
        }
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
    ///   unknowns, built into the application under [`Carrying::Indices`].
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
        let sorting = self.sorting;
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
                        let Some(sorting) = sorting.get(name)
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
                    let Some(sorting) = sorting.get(&name)
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
                    let carried = match self.carrying {
                        Carrying::Indices => sorting.implicits.len(),
                        Carrying::Written => 0,
                    };
                    let indices = sorting
                        .implicits
                        .iter()
                        .take(carried)
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
    use gandr_theory_levitation::TermNode;
    use gandr_theory_levitation::TermView;
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

    /// The substitutions and types of a category with families, with its unit
    /// laws: no sort is rigid, since the laws rewrite `Sub`, `subTy` takes a
    /// `Sub` and `ext` takes a `Ty`.
    ///
    /// # Specification
    /// trivial.
    fn cwf() -> TheoryDesc<Ungraded>
    {
        let mut description = theory(
            [
                SortDesc::new("Con", DeclPolarity::Data),
                SortDesc::family("Sub", DeclPolarity::Data, [
                    SortIndex::new("d", "Con"),
                    SortIndex::new("g", "Con"),
                ]),
                SortDesc::family("Ty", DeclPolarity::Data, [SortIndex::new("g", "Con")]),
            ],
            [
                oper(
                    "id",
                    [SortRef::new("g", "Con")],
                    port("out", "Sub", [var("g"), var("g")]),
                ),
                oper(
                    "comp",
                    [
                        port("s", "Sub", [var("d"), var("g")]),
                        port("t", "Sub", [var("e"), var("d")]),
                    ],
                    port("out", "Sub", [var("e"), var("g")]),
                ),
                oper(
                    "ext",
                    [SortRef::new("g", "Con"), port("a", "Ty", [var("g")])],
                    SortRef::new("out", "Con"),
                ),
                oper(
                    "subTy",
                    [
                        port("a", "Ty", [var("g")]),
                        port("s", "Sub", [var("d"), var("g")]),
                    ],
                    port("out", "Ty", [var("d")]),
                ),
            ],
        );
        description.rules = [
            face(op("comp", [op("id", [var("g")]), var("s")]), var("s")),
            face(op("comp", [var("s"), op("id", [var("d")])]), var("s")),
        ]
        .into();
        description
    }

    /// #5016: the context a substitution stands between stands at a flexible
    /// sort, and the reading carries it, because the path order orients each
    /// unit law with its contexts last. The left unit law then carries the
    /// contexts its identity fixes, so its overlap with the right unit law is
    /// one context. The reading of rigid sorts alone leaves every context off.
    #[test]
    fn a_cwfs_laws_carry_every_index_5016()
    {
        let Maybe::Present(indexing) = Indexing::of(&cwf())
        else {
            panic!("a CwF's substitutions are indexed");
        };
        let unit = face(op("comp", [op("id", [var("g")]), var("s")]), var("s"));
        let indexed = indexing
            .face(&unit)
            .expect("the left unit law is well sorted");
        let Some(source) = indexed
            .lhs
            .collect_vars()
            .into_iter()
            .find(|name| name.as_ref().starts_with(super::UNKNOWN))
        else {
            panic!("the source of `s` is fixed by no written variable");
        };
        assert_eq!(
            indexed.lhs,
            op("comp", [
                var("g"),
                var("g"),
                var(source),
                op("id", [var("g")]),
                var("s")
            ]),
            "composition carries its three contexts, two fixed by the identity"
        );
        let description = cwf();
        let Maybe::Present(rigid) =
            Indexing::carrying(&description, &super::Flexible::of(&description))
        else {
            panic!("the rigid reading reads the CwF");
        };
        assert_eq!(
            rigid.face(&unit).map(|indexed| indexed.lhs),
            Ok(unit.lhs.clone()),
            "the rigid reading leaves every context off"
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

    /// A theory of 2-cells between homs: vertical composition, and a whisker
    /// whose output's indices compose homs.
    ///
    /// # Specification
    /// trivial.
    fn two_cells() -> TheoryDesc<Ungraded>
    {
        let mut description = category();
        description.sorts = [
            SortDesc::new("Ob", DeclPolarity::Data),
            SortDesc::family("Hom", DeclPolarity::Data, [
                SortIndex::new("dom", "Ob"),
                SortIndex::new("cod", "Ob"),
            ]),
            SortDesc::family("Two", DeclPolarity::Data, [
                SortIndex::new("src", "Hom"),
                SortIndex::new("tgt", "Hom"),
            ]),
        ]
        .into();
        let mut opers = Vec::from(core::mem::take(&mut description.opers));
        opers.extend([
            oper(
                "vcomp",
                [
                    port("s", "Two", [var("f"), var("g")]),
                    port("t", "Two", [var("g"), var("k")]),
                ],
                port("out", "Two", [var("f"), var("k")]),
            ),
            oper(
                "whiskerR",
                [
                    port("s", "Two", [var("f"), var("g")]),
                    SortRef::new("h", "Hom").applied([var("b"), var("c")]),
                ],
                port("out", "Two", [
                    op("comp", [var("f"), var("h")]),
                    op("comp", [var("g"), var("h")]),
                ]),
            ),
        ]);
        description.opers = opers.into();
        description
    }

    /// A whisker's composite index is carried only while no law rewrites the
    /// homs it composes. With none, the homs are rigid, vertical associativity
    /// reads with its 1-cells, and a law meeting the composite is refused.
    /// Under associativity the homs are flexible. Interchange over every index
    /// meets the whisker's composite, so the reading keeps the rigid sorts: a
    /// 2-cell carries no 1-cell, interchange reads with the objects its
    /// whiskering hom fixes, and a law whose sides stand at two 2-cell sorts is
    /// still refused (#1510).
    #[test]
    fn a_whiskers_composite_index_leaves_the_other_laws_indexed_1510()
    {
        let Maybe::Present(rigid) = Indexing::of(&two_cells())
        else {
            panic!("a whisker's composite index leaves the reading whole");
        };
        let associativity = face(
            op("vcomp", [op("vcomp", [var("s"), var("t")]), var("u")]),
            op("vcomp", [var("s"), op("vcomp", [var("t"), var("u")])]),
        );
        let indexed = rigid
            .face(&associativity)
            .expect("vertical associativity is well sorted");
        assert_eq!(
            (rigid.strip(&indexed.lhs), rigid.strip(&indexed.rhs)),
            (associativity.lhs, associativity.rhs),
            "it strips back to the law as written"
        );
        let whiskered = op("vcomp", [op("whiskerR", [var("s"), var("h")]), var("t")]);
        assert_eq!(
            rigid.face(&face(whiskered.clone(), whiskered)),
            Err(Unsorted::Nested),
            "a whiskered composite's index applies composition, which the reading does not carry"
        );
        let unit = || op("id", [var("a")]);
        let whiskered = |cell: FreeTerm| op("whiskerR", [cell, unit()]);
        let interchange = face(
            op("vcomp", [whiskered(var("s")), whiskered(var("t"))]),
            whiskered(op("vcomp", [var("s"), var("t")])),
        );
        let mut composed = two_cells();
        composed.rules = Vec::from([
            face(
                op("comp", [op("comp", [var("f"), var("g")]), var("h")]),
                op("comp", [var("f"), op("comp", [var("g"), var("h")])]),
            ),
            interchange.clone(),
        ])
        .into();
        let Maybe::Present(flexible) = Indexing::of(&composed)
        else {
            panic!("the objects stay indexed");
        };
        let carried = |cell: FreeTerm| op("whiskerR", [var("a"), var("a"), cell, unit()]);
        assert_eq!(
            flexible.face(&interchange),
            Ok(face(
                op("vcomp", [carried(var("s")), carried(var("t"))]),
                carried(op("vcomp", [var("s"), var("t")])),
            )),
            "interchange carries the objects its identity fixes, and no 1-cell"
        );
        let distributed = face(
            op("whiskerR", [op("vcomp", [var("s"), var("t")]), var("h")]),
            op("vcomp", [
                op("whiskerR", [var("s"), var("h")]),
                op("whiskerR", [var("t"), var("h")]),
            ]),
        );
        assert_eq!(
            flexible
                .face(&distributed)
                .map(|indexed| (flexible.strip(&indexed.lhs), flexible.strip(&indexed.rhs))),
            Ok((distributed.lhs.clone(), distributed.rhs.clone())),
            "a whisker distributes over vertical composition"
        );
        assert_eq!(
            flexible.face(&face(whiskered(var("s")), var("s"))),
            Err(Unsorted::Clash),
            "a whiskered 2-cell stands between composites, so it is no 2-cell between its own ends"
        );
    }

    /// A category with families with terms: a term's sort names a type in a
    /// context, and a term substitution moves its term's type along the
    /// substitution, an index that applies `subTy`. The laws on types come
    /// before the laws on terms.
    ///
    /// # Specification
    /// trivial.
    fn cwf_terms() -> TheoryDesc<Ungraded>
    {
        let mut description = cwf();
        let mut sorts = Vec::from(core::mem::take(&mut description.sorts));
        sorts.push(SortDesc::family("Tm", DeclPolarity::Data, [
            SortIndex::new("g", "Con"),
            SortIndex::new("a", "Ty").applied([var("g")]),
        ]));
        description.sorts = sorts.into();
        let mut opers = Vec::from(core::mem::take(&mut description.opers));
        opers.push(oper(
            "subTm",
            [
                port("t", "Tm", [var("g"), var("a")]),
                port("s", "Sub", [var("d"), var("g")]),
            ],
            port("out", "Tm", [var("d"), op("subTy", [var("a"), var("s")])]),
        ));
        description.opers = opers.into();
        let mut rules = Vec::from(core::mem::take(&mut description.rules));
        rules.extend([
            face(op("subTy", [var("a"), op("id", [var("g")])]), var("a")),
            face(
                op("subTy", [op("subTy", [var("a"), var("s")]), var("t")]),
                op("subTy", [var("a"), op("comp", [var("s"), var("t")])]),
            ),
        ]);
        description.rules = rules.into();
        description
    }

    /// #5042: a term substitution's output sort applies `subTy`, so the reading
    /// carries `subTy`'s two contexts inside the index. The identity law on
    /// terms sorts only modulo the identity law on types, and it reads. The
    /// composite law holds a type index the laws on types rewrite, and its
    /// decision is #5117's. A law whose sides sort apart modulo every law, and
    /// the identity law on terms without the identity law on types, are
    /// refused.
    #[test]
    fn a_cwfs_laws_on_terms_check_modulo_its_laws_on_types_5042()
    {
        let tm_id = face(op("subTm", [var("t"), op("id", [var("g")])]), var("t"));
        let tm_comp = face(
            op("subTm", [op("subTm", [var("t"), var("s")]), var("u")]),
            op("subTm", [var("t"), op("comp", [var("s"), var("u")])]),
        );
        let mut description = cwf_terms();
        let Maybe::Present(indexing) = Indexing::of(&description)
        else {
            panic!("the CwF's sorts are indexed");
        };
        assert_eq!(
            indexing
                .face(&tm_id)
                .map(|indexed| (indexing.strip(&indexed.lhs), indexing.strip(&indexed.rhs))),
            Ok((tm_id.lhs.clone(), tm_id.rhs.clone())),
            "the identity law on terms reads modulo the laws on types and strips back to the law as written"
        );
        assert_eq!(
            indexing.face(&tm_comp),
            Err(Unsorted::Rewritten),
            "the composite law's type index is one the composite law on types rewrites"
        );
        let Some((_, substitution)) = indexing
            .operations
            .iter()
            .find(|&(name, _)| name.as_ref() == "subTm")
        else {
            panic!("the CwF declares `subTm`");
        };
        let mut pending = Vec::from([substitution.output.clone()]);
        let mut carried = 0_usize;
        while let Some(next) = pending.pop() {
            match next.view() {
                TermView::Op { name, args } => {
                    if name.as_ref() == "subTy" && args.len() == 4 {
                        carried = carried.saturating_add(1);
                    }
                    pending.extend(args.map(TermNode::to_term));
                },
                TermView::Ctor { args, .. } => pending.extend(args.map(TermNode::to_term)),
                TermView::Var(_)
                | TermView::Results { .. }
                | TermView::Inst { .. }
                | TermView::Abs { .. }
                | TermView::Atom(_)
                | TermView::Lam { .. }
                | TermView::Bound(_) => {},
            }
        }
        assert_eq!(
            carried, 1,
            "a substitution's type index carries `subTy` with its two contexts"
        );
        assert_eq!(
            indexing.face(&face(op("subTm", [var("t"), var("s")]), var("t"))),
            Err(Unsorted::Clash),
            "a moved term stands at another context than the term, modulo every law"
        );
        let mut rules = Vec::from(core::mem::take(&mut description.rules));
        rules.retain(|law| law.lhs != op("subTy", [var("a"), op("id", [var("g")])]));
        description.rules = rules.into();
        let Maybe::Present(without) = Indexing::of(&description)
        else {
            panic!("the CwF's sorts are indexed");
        };
        assert_eq!(
            without.face(&tm_id),
            Err(Unsorted::Clash),
            "without the identity law on types, the identity law on terms sorts apart"
        );
    }
}
