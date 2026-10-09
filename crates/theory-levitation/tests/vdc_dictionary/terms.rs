//! The first-order term machinery the crate leaves to its consumers:
//! substitution, matching, positions, one-step rewriting and bounded path
//! enumeration over `FreeTerm`.
//!
//! The crate ships none of it. `FreeTerm` is the carrier; what acts on a term
//! belongs to the cell store that consumes the crate, and the suite supplies
//! its own (`law3::matching_and_substitution_are_supplied_test_side`). Every
//! walk is iterative over the term's borrowed nodes, and every binding is a
//! `BTreeMap` iterated in key order, so enumeration and replay are
//! reproducible.

use alloc::collections::BTreeMap;

use gandr_theory_levitation::FreeTerm;
use gandr_theory_levitation::Name;
use gandr_theory_levitation::RuleFace;
use gandr_theory_levitation::TermArgs;
use gandr_theory_levitation::TermNode;
use gandr_theory_levitation::TermPositionIndex;
use gandr_theory_levitation::TermView;
use quenchant_shape::shape::Maybe;

use crate::support::GeneratorIndex;
use crate::support::PatternMatch;
use crate::support::RewriteDepth;
use crate::support::TermArity;

/// A ground substitution or a match binding: variable name to term.
pub type Binding = BTreeMap<Name, FreeTerm>;

/// A rewrite path and the term it reaches.
pub type RewritePath = (Vec<RewriteStep>, FreeTerm);

/// One rewrite step of a path: which rule fired, at which position, under
/// which match binding.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RewriteStep
{
    /// The index of the fired rule in its signature's rule list.
    pub cell: GeneratorIndex,
    /// The position (argument-index path) the rewrite fired at.
    pub pos: Vec<TermPositionIndex>,
    /// The match binding recorded when the step fired.
    pub subst: Binding,
}

quenchant_shape::reason_enum! {
    /// Why a position names no subterm.
    pub mod position {
        /// The reason the position is unreadable.
        #[derive(Clone, Copy, Debug, Eq, PartialEq)]
        pub enum Absent {
            /// The position leaves the term: an index past an application's
            /// arguments, or a step below a variable.
            OffTerm,
        }
    }
}

quenchant_shape::reason_enum! {
    /// Why a rewrite does not fire.
    pub mod rewrite {
        /// The reason no rewritten term is produced.
        #[derive(Clone, Copy, Debug, Eq, PartialEq)]
        pub enum Absent {
            /// The position leaves the term.
            OffTerm,
            /// The rule's left-hand side does not match the subterm.
            NoMatch,
            /// The step names a rule the rule list does not hold.
            UnknownRule,
        }
    }
}

/// Which application a term node is.
#[derive(Clone, Copy)]
enum Application
{
    /// A constructor application.
    Ctor,
    /// An operation application.
    Op,
}

impl Application
{
    /// The application of this kind over the given head and arguments.
    ///
    /// # Specification
    /// trivial.
    fn build(
        self,
        name: Name,
        args: Vec<FreeTerm>,
    ) -> FreeTerm
    {
        match self {
            | Self::Ctor => FreeTerm::ctor(name, args),
            | Self::Op => FreeTerm::op(name, args),
        }
    }
}

/// One pending step of a bottom-up rebuild.
enum Rebuild<'term>
{
    /// Visit a node: emit a variable's image, or schedule an application.
    Enter(TermNode<'term>),
    /// Assemble an application from the most recent rebuilt arguments.
    Assemble
    {
        /// The application's kind.
        application: Application,
        /// The application's (renamed) head.
        name: Name,
        /// How many rebuilt arguments it takes.
        arity: TermArity,
    },
}

/// Schedules an application's assembly after its arguments, the first
/// argument entered first.
///
/// # Specification
/// trivial.
fn schedule<'term>(
    work: &mut Vec<Rebuild<'term>>,
    application: Application,
    name: Name,
    args: TermArgs<'term>,
)
{
    let args: Vec<TermNode<'term>> = args.collect();
    work.push(Rebuild::Assemble {
        application,
        name,
        arity: TermArity::from(args.len()),
    });
    work.extend(args.iter().rev().copied().map(Rebuild::Enter));
}

/// The term rebuilt bottom-up: every variable leaf replaced by its image and
/// every application head by its renaming.
///
/// # Specification
/// - ensures: the shape of `term`, with each variable occurrence replaced by
///   `on_var`'s image of it and each application head by `on_head`'s image of
///   it; application kinds and argument order are kept.
/// - panics: none; every assembly finds its arguments rebuilt.
/// - intension: an explicit work stack of nodes to enter and applications to
///   assemble, so a term of any depth is rebuilt without recursion.
pub fn rebuild<V, H>(
    term: &FreeTerm,
    mut on_var: V,
    mut on_head: H,
) -> FreeTerm
where
    V: FnMut(&Name) -> FreeTerm,
    H: FnMut(&Name) -> Name,
{
    let mut work = vec![Rebuild::Enter(term.to_node())];
    let mut built: Vec<FreeTerm> = Vec::new();
    while let Some(step) = work.pop() {
        match step {
            | Rebuild::Enter(node) => match node.view() {
                | TermView::Var(name) => built.push(on_var(name)),
                | TermView::Ctor { name, args } => {
                    schedule(&mut work, Application::Ctor, on_head(name), args);
                },
                | TermView::Op { name, args } => {
                    schedule(&mut work, Application::Op, on_head(name), args);
                },
            },
            | Rebuild::Assemble {
                application,
                name,
                arity,
            } => {
                let first = built.len().saturating_sub(usize::from(arity));
                let args = built.split_off(first);
                built.push(application.build(name, args));
            },
        }
    }
    built.pop().expect("a rebuild leaves the root rebuilt")
}

/// Substitutes terms for variables throughout a term; a variable the binding
/// does not name is kept.
///
/// # Specification
/// trivial.
pub fn subst_term(
    term: &FreeTerm,
    subst: &Binding,
) -> FreeTerm
{
    rebuild(
        term,
        |name| {
            subst
                .get(name)
                .cloned()
                .unwrap_or_else(|| FreeTerm::var(name))
        },
        Name::clone,
    )
}

/// Matches a pattern against a ground term: plain first-order matching, no
/// unification.
///
/// # Specification
/// - ensures: positive exactly when some extension of `out` makes `pattern`
///   equal to `ground` under [`subst_term`]; a variable binds the aligned
///   subterm, consistently on repeats, and an application must agree on kind,
///   head and arity and match argument-wise. Bindings made before a failure
///   stay in `out`.
/// - panics: none.
pub fn match_pattern(
    pattern: &FreeTerm,
    ground: &FreeTerm,
    out: &mut Binding,
) -> PatternMatch
{
    match_node(pattern.to_node(), ground.to_node(), out)
}

/// [`match_pattern`] over borrowed nodes.
///
/// # Specification
/// - ensures: as [`match_pattern`].
/// - panics: none.
/// - intension: a work stack of aligned pattern and ground nodes.
fn match_node(
    pattern: TermNode<'_>,
    ground: TermNode<'_>,
    out: &mut Binding,
) -> PatternMatch
{
    let mut pending = vec![(pattern, ground)];
    while let Some((pattern, ground)) = pending.pop() {
        let aligned = match (pattern.view(), ground.view()) {
            | (TermView::Var(name), _) => {
                if let Some(existing) = out.get(name) {
                    if existing.to_node() != ground {
                        return PatternMatch::from(false);
                    }
                }
                else {
                    out.insert(name.clone(), ground.to_term());
                }
                continue;
            },
            | (
                TermView::Ctor {
                    name: pattern_name,
                    args: pattern_args,
                },
                TermView::Ctor {
                    name: ground_name,
                    args: ground_args,
                },
            )
            | (
                TermView::Op {
                    name: pattern_name,
                    args: pattern_args,
                },
                TermView::Op {
                    name: ground_name,
                    args: ground_args,
                },
            ) if pattern_name == ground_name => (pattern_args, ground_args),
            | _ => return PatternMatch::from(false),
        };
        let (pattern_args, ground_args) = aligned;
        let pattern_args: Vec<TermNode<'_>> = pattern_args.collect();
        let ground_args: Vec<TermNode<'_>> = ground_args.collect();
        if pattern_args.len() != ground_args.len() {
            return PatternMatch::from(false);
        }
        pending.extend(pattern_args.into_iter().zip(ground_args).rev());
    }
    PatternMatch::from(true)
}

/// The subterm at a position, a path of argument indices from the root.
///
/// # Specification
/// - ensures: the node reached by descending into the indexed argument at each
///   step; [`position::Absent::OffTerm`] when a step indexes past an
///   application's arguments or descends below a variable.
/// - panics: none.
pub fn subterm_at<'term>(
    term: &'term FreeTerm,
    position: &[TermPositionIndex],
) -> Maybe<TermNode<'term>, position::Absent>
{
    let mut cursor = term.to_node();
    for &index in position {
        let next = match cursor.view() {
            | TermView::Ctor { mut args, .. } | TermView::Op { mut args, .. } => {
                args.nth(usize::from(index))
            },
            | TermView::Var(_) => None,
        };
        let Some(next) = next
        else {
            return Maybe::Absent(position::Absent::OffTerm);
        };
        cursor = next;
    }
    Maybe::Present(cursor)
}

/// The term with the subterm at a position replaced.
///
/// # Specification
/// - ensures: `term` with the node [`subterm_at`] reads at `position` replaced
///   by `replacement`, every other node kept; [`position::Absent::OffTerm`]
///   when the position leaves the term.
/// - panics: none.
/// - intension: the spine from the root to the position is recorded, then
///   reassembled from the bottom up.
pub fn replace_at(
    term: &FreeTerm,
    position: &[TermPositionIndex],
    replacement: FreeTerm,
) -> Maybe<FreeTerm, position::Absent>
{
    let mut cursor = term.to_node();
    let mut spine: Vec<(Application, Name, Vec<FreeTerm>, TermPositionIndex)> = Vec::new();
    for &index in position {
        let (application, name, args) = match cursor.view() {
            | TermView::Ctor { name, args } => (Application::Ctor, name, args),
            | TermView::Op { name, args } => (Application::Op, name, args),
            | TermView::Var(_) => return Maybe::Absent(position::Absent::OffTerm),
        };
        let args: Vec<TermNode<'_>> = args.collect();
        let Some(&child) = args.get(usize::from(index))
        else {
            return Maybe::Absent(position::Absent::OffTerm);
        };
        spine.push((
            application,
            name.clone(),
            args.into_iter().map(TermNode::to_term).collect(),
            index,
        ));
        cursor = child;
    }
    let mut rebuilt = replacement;
    for (application, name, mut args, index) in spine.into_iter().rev() {
        args[usize::from(index)] = rebuilt;
        rebuilt = application.build(name, args);
    }
    Maybe::Present(rebuilt)
}

/// Rewrites at a position with a face: matches the face's left-hand side
/// against the subterm there, then splices in its right-hand side under the
/// match.
///
/// # Specification
/// - ensures: the match binding and the rewritten whole term;
///   [`rewrite::Absent::OffTerm`] when the position leaves the term,
///   [`rewrite::Absent::NoMatch`] when the left-hand side does not match.
/// - panics: none.
pub fn rewrite_with_face(
    term: &FreeTerm,
    position: &[TermPositionIndex],
    face: &RuleFace,
) -> Maybe<(Binding, FreeTerm), rewrite::Absent>
{
    let Maybe::Present(subterm) = subterm_at(term, position)
    else {
        return Maybe::Absent(rewrite::Absent::OffTerm);
    };
    let mut binding = Binding::new();
    if !bool::from(match_node(face.lhs.to_node(), subterm, &mut binding)) {
        return Maybe::Absent(rewrite::Absent::NoMatch);
    }
    let rewritten = subst_term(&face.rhs, &binding);
    match replace_at(term, position, rewritten) {
        | Maybe::Present(whole) => Maybe::Present((binding, whole)),
        | Maybe::Absent(position::Absent::OffTerm) => Maybe::Absent(rewrite::Absent::OffTerm),
    }
}

/// Replays a stored path: folds each step's rewrite over the running term.
///
/// # Specification
/// - ensures: the endpoint reached by firing every step in order;
///   [`rewrite::Absent::UnknownRule`] when a step names a rule `cells` does not
///   hold, and the step's own reason when a step no longer fires.
/// - panics: none.
pub fn apply_path(
    start: &FreeTerm,
    steps: &[RewriteStep],
    cells: &[RuleFace],
) -> Maybe<FreeTerm, rewrite::Absent>
{
    let mut current = start.clone();
    for step in steps {
        let Some(face) = cells.get(usize::from(step.cell))
        else {
            return Maybe::Absent(rewrite::Absent::UnknownRule);
        };
        match rewrite_with_face(&current, &step.pos, face) {
            | Maybe::Present((_, whole)) => current = whole,
            | Maybe::Absent(reason) => return Maybe::Absent(reason),
        }
    }
    Maybe::Present(current)
}

/// Every subterm position of a term, in pre-order, root first.
///
/// # Specification
/// - ensures: one position per node, a parent before its arguments and the
///   arguments left to right.
/// - panics: none.
/// - intension: a work stack of positions and nodes, arguments pushed in
///   reverse so the first is visited first.
pub fn positions(term: &FreeTerm) -> Vec<Vec<TermPositionIndex>>
{
    let mut out = Vec::new();
    let mut stack: Vec<(Vec<TermPositionIndex>, TermNode<'_>)> = vec![(Vec::new(), term.to_node())];
    while let Some((position, node)) = stack.pop() {
        if let TermView::Ctor { args, .. } | TermView::Op { args, .. } = node.view() {
            let args: Vec<TermNode<'_>> = args.collect();
            for (index, arg) in args.iter().copied().enumerate().rev() {
                let mut child = position.clone();
                child.push(TermPositionIndex::from(index));
                stack.push((child, arg));
            }
        }
        out.push(position);
    }
    out
}

/// One deterministic step of rewriting: at every position (pre-order) and
/// with every rule (index order), the rewrites that fire.
///
/// # Specification
/// - ensures: one entry per position and rule whose left-hand side matches
///   there, positions outermost first and rules in list order, each with the
///   step recorded and the rewritten whole term.
/// - panics: none.
pub fn one_step_rewrites(
    term: &FreeTerm,
    cells: &[RuleFace],
) -> Vec<(RewriteStep, FreeTerm)>
{
    let mut out = Vec::new();
    for position in positions(term) {
        for (cell_index, face) in cells.iter().enumerate() {
            if let Maybe::Present((binding, whole)) = rewrite_with_face(term, &position, face) {
                out.push((
                    RewriteStep {
                        cell: GeneratorIndex::from(cell_index),
                        pos: position.clone(),
                        subst: binding,
                    },
                    whole,
                ));
            }
        }
    }
    out
}

/// Bounded, deterministic enumeration of rewrite paths from a start term.
///
/// # Specification
/// - ensures: every reduction sequence of length `0 ..= max_depth` from
///   `start`, the empty path (`refl`) first, then breadth-first by length, each
///   paired with the term it reaches.
/// - panics: none.
pub fn enumerate_paths(
    start: &FreeTerm,
    cells: &[RuleFace],
    max_depth: RewriteDepth,
) -> Vec<RewritePath>
{
    let mut out: Vec<RewritePath> = vec![(Vec::new(), start.clone())];
    let mut frontier: Vec<RewritePath> = vec![(Vec::new(), start.clone())];
    for _ in 0 .. usize::from(max_depth) {
        let mut next: Vec<RewritePath> = Vec::new();
        for entry in &frontier {
            let (ref steps, ref term) = *entry;
            for (step, whole) in one_step_rewrites(term, cells) {
                let mut extended = steps.clone();
                extended.push(step);
                out.push((extended.clone(), whole.clone()));
                next.push((extended, whole));
            }
        }
        frontier = next;
    }
    out
}
