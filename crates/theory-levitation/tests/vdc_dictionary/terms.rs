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

use anodized::spec;
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
/// - ensures: one assembly marker followed by the arguments in reverse stack
///   order, so popping visits them left to right before assembly.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — mixed nullary and nested applications expose callback
///   order and the rebuilt term. Reversing argument scheduling, scheduling
///   assembly early or dropping the zero-arity marker changes those
///   observations; the witness covers ordered finite terms rather than
///   stack-space bounds.
/// - witness: `tests::vdc_dictionary::terms::tests::rebuild_preserves_alphabets_and_callback_order`
#[spec(captures: before = work.len(), ensures: work.len() > before
    && matches!(work.get(before), Some(&Rebuild::Assemble { arity, .. })
        if usize::from(arity) == work.len().saturating_sub(before).saturating_sub(1))
    && work.iter().skip(before.saturating_add(1)).all(|step| matches!(*step, Rebuild::Enter(_))))]
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
///   it; application kinds and argument order are kept. Callbacks run once per
///   source node, in pre-order; inserted images are not visited again.
/// - panics: callback panics propagate; every assembly finds its arguments
///   rebuilt.
/// - intension: an explicit work stack of nodes to enter and applications to
///   assemble, so a term of any depth is rebuilt without recursion.
///
/// # Adequacy
/// - hypothesis: L3 — a mixed-alphabet tree with nullary applications and
///   repeated variables exposes its exact image and callback trace. The
///   observations detect reversed arguments, alphabet changes, duplicate
///   callbacks and re-traversal of images; they do not prove an asymptotic
///   space bound.
/// - witness: `tests::vdc_dictionary::terms::tests::rebuild_preserves_alphabets_and_callback_order`
#[spec(ensures: |ref rebuilt| match (term.to_node().view(), rebuilt.to_node().view()) {
    | (TermView::Var(_), _) => true,
    | (TermView::Ctor { args: before, .. }, TermView::Ctor { args: after, .. })
    | (TermView::Op { args: before, .. }, TermView::Op { args: after, .. }) => before.count() == after.count(),
    | _ => false,
})]
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
/// - ensures: simultaneous replacement of bound variable leaves; unbound leaves
///   and application heads are kept, and images are not substituted again.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — bound and unbound roots and nested leaves, with an image
///   mentioning another bound name, expose exact output terms. The observations
///   reject repeated substitution, head renaming and discarded unbound leaves;
///   this is first-order simultaneous substitution, not capture-avoiding
///   binding.
/// - witness: `tests::vdc_dictionary::terms::tests::substitution_is_simultaneous_with_unbound_leaves`
#[spec(ensures: |ref result| result.to_node().vars().eq(term.to_node().vars().flat_map(|name| {
    subst.get(name).into_iter().flat_map(|image| image.to_node().vars())
        .chain(core::iter::once(name).filter(move |_| !subst.contains_key(name)))
})))]
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
///
/// # Adequacy
/// - hypothesis: L3 — repeated and prebound variables, distinct head alphabets,
///   names and arities expose the verdict and exact extended binding.
///   Successful and partial failing matches reject inconsistent repeats,
///   rollback, overwrite and ignored head constraints; the domain is
///   first-order matching, not unification or a transactional binding update.
/// - witness: `tests::vdc_dictionary::terms::tests::matching_retains_consistent_and_partial_bindings`
#[spec(captures: before = out.len(), ensures: |matched| out.len() >= before
    && (!bool::from(matched) || pattern.to_node().vars().all(|name| out.contains_key(name))))]
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
///
/// # Adequacy
/// - hypothesis: L3 — root and nested patterns expose exact bindings and
///   refusal across repeated variables, alphabet/name/arity mismatches and an
///   existing binding. These observations detect overwriting a binding,
///   ignoring a head constraint or rolling back partial progress; no
///   unification is claimed.
/// - witness: `tests::vdc_dictionary::terms::tests::matching_retains_consistent_and_partial_bindings`
#[spec(captures: before = out.len(), ensures: |matched| out.len() >= before
    && (!bool::from(matched) || match (pattern.view(), ground.view()) {
        | (TermView::Var(name), _) => out.get(name).is_some_and(|image| image.to_node() == ground),
        | (TermView::Ctor { name: left, args: left_args }, TermView::Ctor { name: right, args: right_args })
        | (TermView::Op { name: left, args: left_args }, TermView::Op { name: right, args: right_args }) => left == right && left_args.count() == right_args.count(),
        | _ => false,
    }))]
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
///
/// # Adequacy
/// - hypothesis: L3 — empty, nested, first-out-of-range and below-variable
///   paths expose exact borrowed subterms or typed refusal. These observations
///   detect an off-by-one index, root refusal or descent through a leaf, for
///   argument positions rather than source spans or variable names.
/// - witness: `tests::vdc_dictionary::terms::tests::positions_and_replacement_preserve_the_spine`
#[spec(ensures: |ref found| *found == position.iter().try_fold(term.to_node(), |node, index| {
    match node.view() {
        | TermView::Ctor { mut args, .. } | TermView::Op { mut args, .. } => args.nth(usize::from(*index)),
        | TermView::Var(_) => None,
    }
}).map_or(Maybe::Absent(position::Absent::OffTerm), Maybe::Present))]
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
///
/// # Adequacy
/// - hypothesis: L3 — root and nested replacements in mixed applications expose
///   exact rebuilt terms; invalid argument and below-variable paths refuse. The
///   observations detect replacing a sibling, changing the spine's alphabet or
///   losing unchanged arguments, without extending replacement to invalid
///   paths.
/// - witness: `tests::vdc_dictionary::terms::tests::positions_and_replacement_preserve_the_spine`
#[spec(captures: replacement_variables = replacement.to_node().vars().count(),
    ensures: |ref result| match *result {
        | Maybe::Present(ref whole) => match subterm_at(term, position) {
            | Maybe::Present(before) => match subterm_at(whole, position) {
                | Maybe::Present(after) => after.vars().count() == replacement_variables
                    && whole.to_node().vars().count() == term.to_node().vars().count()
                        .saturating_sub(before.vars().count()).saturating_add(replacement_variables),
                | Maybe::Absent(_) => false,
            },
            | Maybe::Absent(_) => false,
        },
        | Maybe::Absent(position::Absent::OffTerm) => matches!(subterm_at(term, position), Maybe::Absent(_)),
    })]
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
///
/// # Adequacy
/// - hypothesis: L3 — a nested redex exposes its exact binding and rewritten
///   context; an invalid position and a valid nonmatch expose distinct reasons.
///   These observations reject rewriting the root instead, dropping the context
///   or conflating failure classes; the operation is one first-order rewrite.
/// - witness: `tests::vdc_dictionary::terms::tests::rewrites_and_path_replay_preserve_step_order`
#[spec(ensures: |ref result| match *result {
    | Maybe::Present((ref binding, ref whole)) => matches!(subterm_at(term, position), Maybe::Present(_))
        && face.lhs.to_node().vars().all(|name| binding.contains_key(name))
        && match subterm_at(whole, position) {
            | Maybe::Present(image) => image.vars().eq(face.rhs.to_node().vars().flat_map(|name| {
                binding.get(name).into_iter().flat_map(|value| value.to_node().vars())
                    .chain(core::iter::once(name).filter(move |_| !binding.contains_key(name)))
            })),
            | Maybe::Absent(_) => false,
        },
    | Maybe::Absent(rewrite::Absent::OffTerm) => matches!(subterm_at(term, position), Maybe::Absent(_)),
    | Maybe::Absent(rewrite::Absent::NoMatch) => matches!(subterm_at(term, position), Maybe::Present(_)),
    | Maybe::Absent(rewrite::Absent::UnknownRule) => false,
})]
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
///
/// # Adequacy
/// - hypothesis: L3 — empty, two-step and reversed paths expose exact endpoints
///   or failure; missing rules, invalid positions and nonmatches expose their
///   own first refusal. These observations detect skipping or reversing steps
///   and collapsing reasons; stored bindings are recomputed, not trusted.
/// - witness: `tests::vdc_dictionary::terms::tests::rewrites_and_path_replay_preserve_step_order`
#[spec(ensures: |ref result| match *result {
    | Maybe::Present(ref end) => steps.iter().all(|step| usize::from(step.cell) < cells.len())
        && (!steps.is_empty() || end == start),
    | Maybe::Absent(rewrite::Absent::UnknownRule) => steps.iter().any(|step| usize::from(step.cell) >= cells.len()),
    | Maybe::Absent(rewrite::Absent::OffTerm | rewrite::Absent::NoMatch) => !steps.is_empty(),
})]
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
///
/// # Adequacy
/// - hypothesis: L3 — a mixed tree with a nullary application exposes the exact
///   root-first argument paths, including depth two. The observation detects
///   omitted roots or leaves, reversed siblings and duplicate positions; it
///   concerns finite first-order trees rather than shared graph nodes.
/// - witness: `tests::vdc_dictionary::terms::tests::positions_and_replacement_preserve_the_spine`
#[spec(ensures: |ref paths| paths.first().is_some_and(Vec::is_empty)
    && paths.iter().zip(paths.iter().skip(1)).all(|(left, right)| left < right)
    && paths.iter().all(|path| matches!(subterm_at(term, path), Maybe::Present(_))))]
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
///
/// # Adequacy
/// - hypothesis: L3 — two rules at root and nested redexes expose every exact
///   step, binding and result in position-then-rule order. The observation
///   detects omitted alternatives, wrong substitutions, reordered rules and
///   rewriting only the selected subterm; enumeration preserves distinct rule
///   occurrences.
/// - witness: `tests::vdc_dictionary::terms::tests::enumeration_keeps_rule_position_and_breadth_first_order`
#[spec(ensures: |ref rewrites| rewrites.iter().all(|entry|
    usize::from(entry.0.cell) < cells.len()
        && matches!(subterm_at(term, &entry.0.pos), Maybe::Present(_))
        && matches!(subterm_at(&entry.1, &entry.0.pos), Maybe::Present(_)))
    && rewrites.iter().zip(rewrites.iter().skip(1)).all(|(left, right)|
        (&left.0.pos, left.0.cell) < (&right.0.pos, right.0.cell)))]
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
///
/// # Adequacy
/// - hypothesis: L3 — depth zero through two over two nested redexes exposes
///   exact paths and endpoints in breadth-first order, including distinct paths
///   with the same endpoint. The observation detects depth off-by-one,
///   depth-first traversal and endpoint deduplication; completeness is bounded
///   by the depth.
/// - witness: `tests::vdc_dictionary::terms::tests::enumeration_keeps_rule_position_and_breadth_first_order`
#[spec(ensures: |ref paths| paths.first().is_some_and(|entry| entry.0.is_empty() && &entry.1 == start)
    && paths.iter().all(|entry| entry.0.len() <= usize::from(max_depth))
    && paths.iter().skip(1).all(|entry| !entry.0.is_empty())
    && paths.iter().zip(paths.iter().skip(1)).all(|(left, right)| left.0.len() <= right.0.len()))]
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

#[cfg(test)]
mod tests
{
    use super::*;
    use crate::vdc_dictionary::fixtures::face;

    #[test]
    fn rebuild_preserves_alphabets_and_callback_order()
    {
        let term = FreeTerm::op("f", [
            FreeTerm::var("x"),
            FreeTerm::ctor("C", [FreeTerm::var("y"), FreeTerm::var("x")]),
            FreeTerm::ctor("Zero", []),
        ]);
        let trace = core::cell::RefCell::new(Vec::new());
        let rebuilt = rebuild(
            &term,
            |name| {
                trace.borrow_mut().push(format!("variable:{name}"));
                FreeTerm::ctor("Image", [FreeTerm::var(name)])
            },
            |name| {
                trace.borrow_mut().push(format!("head:{name}"));
                Name::from(format!("r.{name}"))
            },
        );
        assert_eq!(
            rebuilt,
            FreeTerm::op("r.f", [
                FreeTerm::ctor("Image", [FreeTerm::var("x")]),
                FreeTerm::ctor("r.C", [
                    FreeTerm::ctor("Image", [FreeTerm::var("y")]),
                    FreeTerm::ctor("Image", [FreeTerm::var("x")])
                ]),
                FreeTerm::ctor("r.Zero", [])
            ])
        );
        assert_eq!(trace.into_inner(), [
            "head:f",
            "variable:x",
            "head:C",
            "variable:y",
            "variable:x",
            "head:Zero"
        ]);
    }

    #[test]
    fn substitution_is_simultaneous_with_unbound_leaves()
    {
        let image = FreeTerm::ctor("Image", [FreeTerm::var("y")]);
        let binding = Binding::from([
            (Name::from("x"), image.clone()),
            (Name::from("y"), FreeTerm::var("z")),
        ]);
        assert_eq!(
            subst_term(
                &FreeTerm::op("f", [
                    FreeTerm::var("x"),
                    FreeTerm::ctor("G", [FreeTerm::var("y")]),
                    FreeTerm::var("u")
                ]),
                &binding
            ),
            FreeTerm::op("f", [
                image.clone(),
                FreeTerm::ctor("G", [FreeTerm::var("z")]),
                FreeTerm::var("u")
            ])
        );
        assert_eq!(subst_term(&FreeTerm::var("x"), &binding), image);
        assert_eq!(
            subst_term(&FreeTerm::var("u"), &binding),
            FreeTerm::var("u")
        );
    }

    #[test]
    fn matching_retains_consistent_and_partial_bindings()
    {
        let a = FreeTerm::ctor("A", []);
        let b = FreeTerm::ctor("B", []);
        let kept = Binding::from([(Name::from("kept"), FreeTerm::var("q"))]);
        let mut binding = kept.clone();
        let pattern = FreeTerm::op("f", [
            FreeTerm::var("x"),
            FreeTerm::ctor("C", [FreeTerm::var("x")]),
            FreeTerm::var("y"),
        ]);
        let ground = FreeTerm::op("f", [
            a.clone(),
            FreeTerm::ctor("C", [a.clone()]),
            b.clone(),
        ]);
        assert!(bool::from(match_pattern(&pattern, &ground, &mut binding)));
        assert_eq!(
            binding,
            Binding::from([
                (Name::from("kept"), FreeTerm::var("q")),
                (Name::from("x"), a.clone()),
                (Name::from("y"), b.clone())
            ])
        );
        let mut partial = kept.clone();
        assert!(!bool::from(match_pattern(
            &FreeTerm::op("f", [FreeTerm::var("x"), FreeTerm::var("x")]),
            &FreeTerm::op("f", [a.clone(), b.clone()]),
            &mut partial
        )));
        let expected = Binding::from([
            (Name::from("kept"), FreeTerm::var("q")),
            (Name::from("x"), a.clone()),
        ]);
        assert_eq!(partial, expected);
        assert!(!bool::from(match_pattern(
            &FreeTerm::var("x"),
            &b,
            &mut partial
        )));
        assert_eq!(partial, expected);
        assert!(bool::from(match_pattern(
            &FreeTerm::var("x"),
            &a,
            &mut partial
        )));
        for (pattern, ground) in [
            (FreeTerm::ctor("same", []), FreeTerm::op("same", [])),
            (FreeTerm::op("f", []), FreeTerm::op("g", [])),
            (
                FreeTerm::op("f", [FreeTerm::var("x")]),
                FreeTerm::op("f", []),
            ),
            (FreeTerm::op("f", []), FreeTerm::var("x")),
        ] {
            let mut out = kept.clone();
            assert!(!bool::from(match_pattern(&pattern, &ground, &mut out)));
            assert_eq!(out, kept);
        }
    }

    #[test]
    fn positions_and_replacement_preserve_the_spine()
    {
        let zero = TermPositionIndex::from(0_usize);
        let one = TermPositionIndex::from(1_usize);
        let two = TermPositionIndex::from(2_usize);
        let subtree = FreeTerm::ctor("G", [FreeTerm::var("y"), FreeTerm::ctor("Z", [])]);
        let term = FreeTerm::op("f", [FreeTerm::var("x"), subtree.clone()]);
        let expected_paths = vec![vec![], vec![zero], vec![one], vec![one, zero], vec![
            one, one,
        ]];
        assert_eq!(positions(&term), expected_paths);
        for (path, expected) in expected_paths.iter().zip([
            term.clone(),
            FreeTerm::var("x"),
            subtree,
            FreeTerm::var("y"),
            FreeTerm::ctor("Z", []),
        ]) {
            assert_eq!(subterm_at(&term, path), Maybe::Present(expected.to_node()));
        }
        let replacement = FreeTerm::op("H", [FreeTerm::var("q")]);
        assert_eq!(
            replace_at(&term, &[one, zero], replacement.clone()),
            Maybe::Present(FreeTerm::op("f", [
                FreeTerm::var("x"),
                FreeTerm::ctor("G", [replacement.clone(), FreeTerm::ctor("Z", [])])
            ]))
        );
        assert_eq!(
            replace_at(&term, &[], replacement.clone()),
            Maybe::Present(replacement.clone())
        );
        for invalid in [vec![two], vec![zero, zero], vec![one, two]] {
            assert_eq!(
                subterm_at(&term, &invalid),
                Maybe::Absent(position::Absent::OffTerm)
            );
            assert_eq!(
                replace_at(&term, &invalid, replacement.clone()),
                Maybe::Absent(position::Absent::OffTerm)
            );
        }
    }

    #[test]
    fn rewrites_and_path_replay_preserve_step_order()
    {
        let zero = TermPositionIndex::from(0_usize);
        let a = FreeTerm::ctor("A", []);
        let binding = Binding::from([(Name::from("x"), a.clone())]);
        let first = face(
            FreeTerm::op("f", [FreeTerm::var("x")]),
            FreeTerm::op("g", [FreeTerm::var("x")]),
        );
        let second = face(FreeTerm::op("g", [FreeTerm::var("x")]), FreeTerm::var("x"));
        let start = FreeTerm::ctor("Wrap", [FreeTerm::op("f", [a.clone()])]);
        assert_eq!(
            rewrite_with_face(&start, &[zero], &first),
            Maybe::Present((
                binding.clone(),
                FreeTerm::ctor("Wrap", [FreeTerm::op("g", [a.clone()])])
            ))
        );
        assert_eq!(
            rewrite_with_face(&start, &[], &first),
            Maybe::Absent(rewrite::Absent::NoMatch)
        );
        assert_eq!(
            rewrite_with_face(&start, &[TermPositionIndex::from(1_usize)], &first),
            Maybe::Absent(rewrite::Absent::OffTerm)
        );
        let steps = [
            RewriteStep {
                cell: GeneratorIndex::from(0_usize),
                pos: vec![zero],
                subst: binding.clone(),
            },
            RewriteStep {
                cell: GeneratorIndex::from(1_usize),
                pos: vec![zero],
                subst: binding,
            },
        ];
        let cells = [first, second];
        assert_eq!(
            apply_path(&start, &[], &cells),
            Maybe::Present(start.clone())
        );
        assert_eq!(
            apply_path(&start, &steps, &cells),
            Maybe::Present(FreeTerm::ctor("Wrap", [a]))
        );
        let reversed: Vec<_> = steps.iter().rev().cloned().collect();
        assert_eq!(
            apply_path(&start, &reversed, &cells),
            Maybe::Absent(rewrite::Absent::NoMatch)
        );
        let unknown = RewriteStep {
            cell: GeneratorIndex::from(2_usize),
            pos: vec![TermPositionIndex::from(99_usize)],
            subst: Binding::new(),
        };
        assert_eq!(
            apply_path(&start, &[unknown], &cells),
            Maybe::Absent(rewrite::Absent::UnknownRule)
        );
        let off_term = RewriteStep {
            cell: GeneratorIndex::from(0_usize),
            pos: vec![TermPositionIndex::from(1_usize)],
            subst: Binding::new(),
        };
        assert_eq!(
            apply_path(&start, &[off_term], &cells),
            Maybe::Absent(rewrite::Absent::OffTerm)
        );
    }

    #[test]
    fn enumeration_keeps_rule_position_and_breadth_first_order()
    {
        let a = FreeTerm::var("a");
        let fa = FreeTerm::op("f", [a.clone()]);
        let ga = FreeTerm::op("g", [a.clone()]);
        let ha = FreeTerm::op("h", [a.clone()]);
        let start = FreeTerm::op("f", [fa.clone()]);
        let cells = [
            face(
                FreeTerm::op("f", [FreeTerm::var("x")]),
                FreeTerm::op("g", [FreeTerm::var("x")]),
            ),
            face(
                FreeTerm::op("f", [FreeTerm::var("x")]),
                FreeTerm::op("h", [FreeTerm::var("x")]),
            ),
        ];
        let expected = vec![
            (vec![], start.clone()),
            (vec![(0_usize, vec![])], FreeTerm::op("g", [fa.clone()])),
            (vec![(1, vec![])], FreeTerm::op("h", [fa.clone()])),
            (vec![(0, vec![0_usize])], FreeTerm::op("f", [ga.clone()])),
            (vec![(1, vec![0])], FreeTerm::op("f", [ha.clone()])),
            (
                vec![(0, vec![]), (0, vec![0])],
                FreeTerm::op("g", [ga.clone()]),
            ),
            (
                vec![(0, vec![]), (1, vec![0])],
                FreeTerm::op("g", [ha.clone()]),
            ),
            (
                vec![(1, vec![]), (0, vec![0])],
                FreeTerm::op("h", [ga.clone()]),
            ),
            (
                vec![(1, vec![]), (1, vec![0])],
                FreeTerm::op("h", [ha.clone()]),
            ),
            (
                vec![(0, vec![0]), (0, vec![])],
                FreeTerm::op("g", [ga.clone()]),
            ),
            (vec![(0, vec![0]), (1, vec![])], FreeTerm::op("h", [ga])),
            (
                vec![(1, vec![0]), (0, vec![])],
                FreeTerm::op("g", [ha.clone()]),
            ),
            (vec![(1, vec![0]), (1, vec![])], FreeTerm::op("h", [ha])),
        ];
        let expected_steps: Vec<_> = expected
            .iter()
            .filter(|entry| entry.0.len() == 1)
            .map(|entry| {
                let (cell, ref position) = *entry.0.first().expect("one step");
                (
                    RewriteStep {
                        cell: GeneratorIndex::from(cell),
                        pos: position
                            .iter()
                            .copied()
                            .map(TermPositionIndex::from)
                            .collect(),
                        subst: Binding::from([(
                            Name::from("x"),
                            if position.is_empty() {
                                fa.clone()
                            }
                            else {
                                a.clone()
                            },
                        )]),
                    },
                    entry.1.clone(),
                )
            })
            .collect();
        assert_eq!(one_step_rewrites(&start, &cells), expected_steps);
        for depth in 0 ..= 2_usize {
            let actual: Vec<_> = enumerate_paths(&start, &cells, RewriteDepth::from(depth))
                .into_iter()
                .map(|(steps, end)| {
                    (
                        steps
                            .into_iter()
                            .map(|step| {
                                (
                                    usize::from(step.cell),
                                    step.pos.into_iter().map(usize::from).collect::<Vec<_>>(),
                                )
                            })
                            .collect::<Vec<_>>(),
                        end,
                    )
                })
                .collect();
            let bounded: Vec<_> = expected
                .iter()
                .filter(|entry| entry.0.len() <= depth)
                .cloned()
                .collect();
            assert_eq!(actual, bounded);
        }
    }
}
