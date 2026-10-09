//! Substitutions over pattern metavariables, one-sided matching, and
//! most-general unification.
//!
//! A [`Subst`] binds producer metavariables to producer patterns and consumer
//! metavariables to consumer patterns. [`match_cmd`] extends one so a pattern
//! instantiates to a target; [`unify_cmd`] extends one so two patterns
//! instantiate to the same pattern, its most general such extension.
//!
//! Both walks are explicit worklists over borrowed subtrees of their inputs:
//! no goal copies a pattern, and no step recurses. Both are transactional:
//! the bindings a walk finds are kept apart, as borrowed subtrees, and copied
//! into the substitution only once the whole walk succeeds, so a refusal
//! leaves the substitution as it was.

use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use alloc::vec::Vec;

use quenchant_shape::shape::Maybe;

use crate::boundary::SubstitutionBindingCount;
use crate::boundary::SubstitutionDecision;
use crate::boundary::SubstitutionEmptyStatus;
use crate::pattern::Cat;
use crate::pattern::CmdPat;
use crate::pattern::ConsPat;
use crate::pattern::ConsRef;
use crate::pattern::ConsView;
use crate::pattern::MetaVar;
use crate::pattern::ProdHead;
use crate::pattern::ProdPat;
use crate::pattern::ProdRef;
use crate::pattern::SpineEnd;
use crate::pattern::SpineFrame;

quenchant_shape::reason_enum! {
    /// Why a substitution holds no image for a metavariable.
    pub mod binding {
        /// The reason the lookup finds nothing.
        #[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
        pub enum Absent {
            /// The metavariable is unbound at that category.
            Unbound,
        }
    }
}

/// A refused binding.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum BindingRefusal
{
    /// The metavariable ranges over the other category.
    CategoryMismatch,
    /// The metavariable is already bound to a different image.
    ConflictingRebind,
}

impl core::fmt::Display for BindingRefusal
{
    /// Names the refusal.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result
    {
        f.write_str(match *self {
            | Self::CategoryMismatch => "the metavariable ranges over the other category",
            | Self::ConflictingRebind => "the metavariable is already bound to a different image",
        })
    }
}

impl core::error::Error for BindingRefusal
{
}

/// A substitution: producer metavariables to producer patterns, consumer
/// metavariables to consumer patterns.
#[derive(Clone, Debug, Default, Eq, Hash, PartialEq)]
pub struct Subst
{
    /// Producer bindings.
    prods: BTreeMap<MetaVar, ProdPat>,
    /// Consumer bindings.
    conss: BTreeMap<MetaVar, ConsPat>,
}

impl Subst
{
    /// The empty substitution.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn new() -> Self
    {
        Self::default()
    }

    /// Whether no metavariable is bound.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn is_empty(&self) -> SubstitutionEmptyStatus
    {
        SubstitutionEmptyStatus::from(self.prods.is_empty() && self.conss.is_empty())
    }

    /// The number of bindings, producer and consumer together.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn len(&self) -> SubstitutionBindingCount
    {
        SubstitutionBindingCount::from(self.prods.len().saturating_add(self.conss.len()))
    }

    /// The producer image bound to `var`.
    ///
    /// # Specification
    /// - provides: [`binding::Absent::Unbound`] when `var` has no producer
    ///   binding.
    /// - panics: none.
    #[inline]
    pub fn get_prod(
        &self,
        var: &MetaVar,
    ) -> Maybe<&ProdPat, binding::Absent>
    {
        match self.prods.get(var) {
            | Some(image) => Maybe::Present(image),
            | None => Maybe::Absent(binding::Absent::Unbound),
        }
    }

    /// The consumer image bound to `var`.
    ///
    /// # Specification
    /// - provides: [`binding::Absent::Unbound`] when `var` has no consumer
    ///   binding.
    /// - panics: none.
    #[inline]
    pub fn get_cons(
        &self,
        var: &MetaVar,
    ) -> Maybe<&ConsPat, binding::Absent>
    {
        match self.conss.get(var) {
            | Some(image) => Maybe::Present(image),
            | None => Maybe::Absent(binding::Absent::Unbound),
        }
    }

    /// The bindings of `vars` alone.
    ///
    /// # Specification
    /// - ensures: every binding whose metavariable is in `vars`, at that
    ///   metavariable's own category, and no other.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a two-binding substitution restricted to one of its
    ///   metavariables keeps that binding alone, and restricted to a
    ///   metavariable it leaves unbound is empty.
    /// - witness: `subst::tests::a_restriction_keeps_exactly_the_named_bindings`
    #[inline]
    #[must_use]
    pub fn restricted(
        &self,
        vars: &[MetaVar],
    ) -> Self
    {
        Self {
            prods: self
                .prods
                .iter()
                .filter(|&(var, _)| vars.contains(var))
                .map(|(var, image)| (var.clone(), image.clone()))
                .collect(),
            conss: self
                .conss
                .iter()
                .filter(|&(var, _)| vars.contains(var))
                .map(|(var, image)| (var.clone(), image.clone()))
                .collect(),
        }
    }

    /// Binds a producer metavariable.
    ///
    /// # Specification
    /// - ensures: `var` is bound to `image` when it was unbound; a rebind to an
    ///   equal image succeeds and changes nothing.
    /// - fails: [`BindingRefusal::CategoryMismatch`] when `var` is a consumer
    ///   metavariable; [`BindingRefusal::ConflictingRebind`] when `var` is
    ///   bound to a different image, which is kept.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`BindingRefusal::CategoryMismatch`]: `var` ranges over consumers.
    /// - [`BindingRefusal::ConflictingRebind`]: `var` is bound elsewhere.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the triangular-unification witness reads the bindings
    ///   back after commitment; L1 — the generated suite binds every producer
    ///   hole of each generated pattern through this path to build the instance
    ///   it then matches back.
    /// - witness: `subst::tests::unification_resolves_triangular_bindings`
    /// - witness: `tests::subst::every_match_reproduces_its_target`
    #[inline]
    pub fn bind_prod(
        &mut self,
        var: MetaVar,
        image: ProdPat,
    ) -> Result<(), BindingRefusal>
    {
        if var.cat() != Cat::Producer {
            return Err(BindingRefusal::CategoryMismatch);
        }
        match self.prods.get(&var) {
            | Some(existing) if *existing == image => Ok(()),
            | Some(_) => Err(BindingRefusal::ConflictingRebind),
            | None => {
                drop(self.prods.insert(var, image));
                Ok(())
            },
        }
    }

    /// Binds a consumer metavariable.
    ///
    /// # Specification
    /// - ensures: `var` is bound to `image` when it was unbound; a rebind to an
    ///   equal image succeeds and changes nothing.
    /// - fails: [`BindingRefusal::CategoryMismatch`] when `var` is a producer
    ///   metavariable; [`BindingRefusal::ConflictingRebind`] when `var` is
    ///   bound to a different image, which is kept.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`BindingRefusal::CategoryMismatch`]: `var` ranges over producers.
    /// - [`BindingRefusal::ConflictingRebind`]: `var` is bound elsewhere.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Subst::bind_prod`], for consumer images.
    /// - witness: `subst::tests::unification_finds_a_most_general_unifier`
    #[inline]
    pub fn bind_cons(
        &mut self,
        var: MetaVar,
        image: ConsPat,
    ) -> Result<(), BindingRefusal>
    {
        if var.cat() != Cat::Consumer {
            return Err(BindingRefusal::CategoryMismatch);
        }
        match self.conss.get(&var) {
            | Some(existing) if *existing == image => Ok(()),
            | Some(_) => Err(BindingRefusal::ConflictingRebind),
            | None => {
                drop(self.conss.insert(var, image));
                Ok(())
            },
        }
    }

    /// Resolves every image to its fixpoint, so the substitution becomes
    /// idempotent: one application pass then fully instantiates any pattern.
    ///
    /// Bindings found by [`unify_cmd`] may be triangular — an image may
    /// mention a metavariable bound after it, because the goal order is not
    /// topological. Each pass rewrites only the images that still mention a
    /// bound metavariable, so an image already resolved is never walked
    /// again.
    ///
    /// # Specification
    /// - requires: the bindings are acyclic, as every unifier and every match
    ///   is.
    /// - ensures: no image mentions a bound metavariable; the instantiation the
    ///   substitution denotes is unchanged, each image replaced by its
    ///   fixpoint.
    /// - panics: none.
    /// - intension: at most one pass per binding; a pass that changes nothing
    ///   ends the loop. Over cyclic bindings the passes run out and the cycle
    ///   stays, rather than diverging.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a unifier whose first binding mentions a metavariable
    ///   bound after it equates its two sides after one application pass only
    ///   when resolution ran; the L1 property checks the same equation over
    ///   generated pairs.
    /// - witness: `subst::tests::unification_resolves_triangular_bindings`
    /// - witness: `tests::subst::every_unifier_equates_its_two_sides`
    #[inline]
    pub fn resolve(&mut self)
    {
        for _ in 0 .. usize::from(self.len()) {
            let mut changed = false;
            let pending: Vec<MetaVar> = self
                .prods
                .iter()
                .filter(|&(_, image)| self.mentions_bound(image.to_ref().metavars()).0)
                .map(|(var, _)| var.clone())
                .collect();
            for var in pending {
                let resolved = match self.prods.get(&var) {
                    | Some(image) => self.apply_prod_ref(image.to_ref()),
                    | None => continue,
                };
                drop(self.prods.insert(var, resolved));
                changed = true;
            }
            let pending: Vec<MetaVar> = self
                .conss
                .iter()
                .filter(|&(_, image)| self.mentions_bound(image.to_ref().metavars()).0)
                .map(|(var, _)| var.clone())
                .collect();
            for var in pending {
                let resolved = match self.conss.get(&var) {
                    | Some(image) => self.apply_cons_ref(image.to_ref()),
                    | None => continue,
                };
                drop(self.conss.insert(var, resolved));
                changed = true;
            }
            if !changed {
                return;
            }
        }
    }

    /// Whether any of `vars` is bound at its own category.
    ///
    /// # Specification
    /// trivial.
    fn mentions_bound<'var, I>(
        &self,
        vars: I,
    ) -> BoundMention
    where
        I: IntoIterator<Item = &'var MetaVar>,
    {
        BoundMention(vars.into_iter().any(|var| match var.cat() {
            | Cat::Producer => self.prods.contains_key(var),
            | Cat::Consumer => self.conss.contains_key(var),
        }))
    }

    /// The substitution applied to a command pattern.
    ///
    /// # Specification
    /// - ensures: every bound metavariable is replaced by its image; unbound
    ///   metavariables stay, a partial instantiation. One pass: an image is
    ///   inserted as bound, so an image mentioning a bound metavariable stays
    ///   unresolved until [`Subst::resolve`] runs, as [`unify_cmd`] does.
    /// - panics: none.
    /// - intension: one copy of each table, the images appended in place; an
    ///   empty substitution is a plain copy.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a match of the successor rule's left-hand side
    ///   reconstructs its target exactly; the L1 property checks that over
    ///   generated pairs.
    /// - witness: `subst::tests::matching_binds_a_ground_configuration`
    /// - witness: `tests::subst::every_match_reproduces_its_target`
    #[inline]
    #[must_use]
    pub fn apply_cmd(
        &self,
        cmd: &CmdPat,
    ) -> CmdPat
    {
        CmdPat::cut(
            cmd.polarity(),
            self.apply_prod(cmd.producer()),
            self.apply_cons(cmd.consumer()),
        )
    }

    /// The substitution applied to a producer pattern.
    ///
    /// # Specification
    /// - ensures: as [`Subst::apply_cmd`], for a producer.
    /// - panics: none.
    #[inline]
    #[must_use]
    pub fn apply_prod(
        &self,
        prod: &ProdPat,
    ) -> ProdPat
    {
        self.apply_prod_ref(prod.to_ref())
    }

    /// The substitution applied to a consumer pattern.
    ///
    /// # Specification
    /// - ensures: as [`Subst::apply_cmd`], for a consumer.
    /// - panics: none.
    #[inline]
    #[must_use]
    pub fn apply_cons(
        &self,
        cons: &ConsPat,
    ) -> ConsPat
    {
        self.apply_cons_ref(cons.to_ref())
    }

    /// The substitution applied to a borrowed producer subtree.
    ///
    /// # Specification
    /// - ensures: as [`Subst::apply_cmd`], for a producer.
    /// - panics: none.
    fn apply_prod_ref(
        &self,
        prod: ProdRef<'_>,
    ) -> ProdPat
    {
        if self.prods.is_empty() {
            return prod.to_pattern();
        }
        crate::pattern::instantiate_prod(prod, &|var: &MetaVar| {
            self.get_prod(var).map(ProdPat::to_ref)
        })
    }

    /// The substitution applied to a borrowed consumer subtree.
    ///
    /// # Specification
    /// - ensures: as [`Subst::apply_cmd`], for a consumer: each operation
    ///   argument is substituted, and a bound end is replaced by its image's
    ///   frames and end, inside the frames above it.
    /// - panics: none.
    fn apply_cons_ref(
        &self,
        cons: ConsRef<'_>,
    ) -> ConsPat
    {
        let applied = cons.frames().iter().map(|frame| match *frame {
            | SpineFrame::Op { ref op, ref args } => SpineFrame::Op {
                op: op.clone(),
                args: args.iter().map(|arg| self.apply_prod(arg)).collect(),
            },
            | SpineFrame::Frame(ref ctor) => SpineFrame::Frame(ctor.clone()),
        });
        let image = match *cons.end() {
            | SpineEnd::Meta(ref var) => self.conss.get(var),
            | SpineEnd::Top => None,
        };
        match image {
            | Some(image) => {
                let image = image.to_ref();
                let mut frames = image.frames().to_vec();
                frames.extend(applied);
                ConsPat::from_parts(frames, image.end().clone())
            },
            | None => ConsPat::from_parts(applied.collect(), cons.end().clone()),
        }
    }

    /// Copies a walk's bindings in.
    ///
    /// # Specification
    /// - requires: no key of `found` is bound here.
    /// - ensures: every binding of `found` is bound here to a copy of its
    ///   subtree.
    /// - panics: none.
    fn commit(
        &mut self,
        found: Found<'_, '_>,
    )
    {
        for (var, image) in found.prods {
            drop(self.prods.insert(var.clone(), image.to_pattern()));
        }
        for (var, image) in found.conss {
            drop(self.conss.insert(var.clone(), image.to_pattern()));
        }
    }
}

/// A substitution from its two binding maps, for the crate's own renamings.
///
/// # Specification
/// - requires: every key of `prods` is a producer metavariable and every key of
///   `conss` a consumer metavariable.
/// - ensures: the substitution binding exactly those maps.
/// - panics: none.
#[inline]
pub fn substitution_from(
    prods: BTreeMap<MetaVar, ProdPat>,
    conss: BTreeMap<MetaVar, ConsPat>,
) -> Subst
{
    Subst { prods, conss }
}

/// The bindings a walk has found and not yet committed, as borrowed subtrees
/// of its inputs.
#[derive(Debug, Default)]
struct Found<'var, 'term>
{
    /// Producer bindings found.
    prods: BTreeMap<&'var MetaVar, ProdRef<'term>>,
    /// Consumer bindings found.
    conss: BTreeMap<&'var MetaVar, ConsRef<'term>>,
}

/// One pair of subtrees a walk must still reconcile.
#[derive(Clone, Copy, Debug)]
enum Goal<'left, 'right>
{
    /// A pair of producer subtrees.
    Prod(ProdRef<'left>, ProdRef<'right>),
    /// A pair of consumer subtrees.
    Cons(ConsRef<'left>, ConsRef<'right>),
}

/// Why a match or a unification stops.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Refusal
{
    /// The two sides differ in shape, symbol or arity.
    Clash,
    /// A metavariable meets a subterm unequal to the one it is bound to.
    Conflict,
    /// A metavariable occurs inside the subterm it would be bound to.
    Occurs,
    /// Walking through the bindings took more steps than there are bindings.
    Cyclic,
}

/// One step's outcome: its goals enqueued or its binding found, or a refusal.
type Step = Result<(), Refusal>;

/// Matches a pattern against a target, extending `subst` so that
/// `subst.apply_cmd(pattern)` equals `target`.
///
/// # Specification
/// - requires: none; a target may carry metavariables of its own, which a
///   pattern metavariable binds like any other subterm.
/// - ensures: positive with `subst` extended so `subst.apply_cmd(pattern) ==
///   *target` when the pattern matches; a metavariable `subst` already binds
///   must meet an equal subterm, and a repeated metavariable equal subterms.
///   Polarity must agree: a cell applies only at a cut of its own orientation.
/// - fails: negative on a polarity, symbol, arity or shape clash, or on a
///   conflicting binding; `subst` is then unchanged.
/// - panics: none.
/// - intension: one worklist over borrowed subtree pairs; bindings are copied
///   in once, after the whole walk succeeds.
///
/// # Adequacy
/// - hypothesis: L3 — a ground successor configuration is matched and
///   reconstructed exactly, and a polarity clash refuses with nothing bound; L1
///   — every generated pattern matches every instance of itself, reproducing
///   it.
/// - witness: `subst::tests::matching_binds_a_ground_configuration`
/// - witness: `subst::tests::a_polarity_clash_blocks_a_match`
/// - witness: `tests::subst::every_match_reproduces_its_target`
#[inline]
#[must_use]
pub fn match_cmd(
    pattern: &CmdPat,
    target: &CmdPat,
    subst: &mut Subst,
) -> SubstitutionDecision
{
    if pattern.polarity() != target.polarity() {
        return SubstitutionDecision::from(false);
    }
    let mut found = Found::default();
    let mut goals: Vec<Goal<'_, '_>> = alloc::vec![
        Goal::Prod(pattern.producer().to_ref(), target.producer().to_ref()),
        Goal::Cons(pattern.consumer().to_ref(), target.consumer().to_ref()),
    ];
    while let Some(goal) = goals.pop() {
        let step = match goal {
            | Goal::Prod(pat, tgt) => match_prod_step(pat, tgt, subst, &mut found, &mut goals),
            | Goal::Cons(pat, tgt) => match_cons_step(pat, tgt, subst, &mut found, &mut goals),
        };
        if step.is_err() {
            return SubstitutionDecision::from(false);
        }
    }
    subst.commit(found);
    SubstitutionDecision::from(true)
}

/// One producer match goal: binds a metavariable or enqueues the argument
/// pairs.
///
/// # Specification
/// - ensures: the pattern's metavariable bound in `found`, or each argument
///   pair enqueued, when the heads agree.
/// - fails: [`Refusal::Clash`] on a symbol or arity clash;
///   [`Refusal::Conflict`] on a binding that disagrees with `subst` or `found`.
/// - panics: none.
///
/// # Errors
/// As the failure clause states.
fn match_prod_step<'pattern, 'target>(
    pat: ProdRef<'pattern>,
    tgt: ProdRef<'target>,
    subst: &Subst,
    found: &mut Found<'pattern, 'target>,
    goals: &mut Vec<Goal<'pattern, 'target>>,
) -> Step
{
    match *pat.head() {
        | ProdHead::Meta(ref var) => {
            let agrees = match (subst.prods.get(var), found.prods.get(var)) {
                | (Some(existing), _) => existing.to_ref() == tgt,
                | (None, Some(&earlier)) => earlier == tgt,
                | (None, None) => {
                    found.prods.insert(var, tgt);
                    true
                },
            };
            if agrees {
                Ok(())
            }
            else {
                Err(Refusal::Conflict)
            }
        },
        | ProdHead::Ctor(ref ctor, arity) => match *tgt.head() {
            | ProdHead::Ctor(ref other, other_arity) if ctor == other && arity == other_arity => {
                goals.extend(
                    pat.children()
                        .zip(tgt.children())
                        .map(|(p, t)| Goal::Prod(p, t)),
                );
                Ok(())
            },
            | ProdHead::Ctor(..) | ProdHead::Meta(_) => Err(Refusal::Clash),
        },
    }
}

/// One consumer match goal: binds a metavariable end or enqueues the frame's
/// argument pairs and the continuation pair.
///
/// # Specification
/// - ensures: the pattern's metavariable bound in `found` to the rest of the
///   target's spine, or each argument pair and the continuation pair enqueued,
///   when the outermost frames agree.
/// - fails: [`Refusal::Clash`] on a frame, symbol or arity clash;
///   [`Refusal::Conflict`] on a binding that disagrees with `subst` or `found`.
/// - panics: none.
///
/// # Errors
/// As the failure clause states.
fn match_cons_step<'pattern, 'target>(
    pat: ConsRef<'pattern>,
    tgt: ConsRef<'target>,
    subst: &Subst,
    found: &mut Found<'pattern, 'target>,
    goals: &mut Vec<Goal<'pattern, 'target>>,
) -> Step
{
    match (pat.view(), tgt.view()) {
        | (ConsView::Meta(var), _) => {
            let agrees = match (subst.conss.get(var), found.conss.get(var)) {
                | (Some(existing), _) => existing.to_ref() == tgt,
                | (None, Some(&earlier)) => earlier == tgt,
                | (None, None) => {
                    found.conss.insert(var, tgt);
                    true
                },
            };
            if agrees {
                Ok(())
            }
            else {
                Err(Refusal::Conflict)
            }
        },
        | (ConsView::Top, ConsView::Top) => Ok(()),
        | (
            ConsView::Op { op, args, ret },
            ConsView::Op {
                op: other,
                args: other_args,
                ret: other_ret,
            },
        ) if op == other && args.len() == other_args.len() => {
            goals.extend(args.zip(other_args).map(|(p, t)| Goal::Prod(p, t)));
            goals.push(Goal::Cons(ret, other_ret));
            Ok(())
        },
        | (
            ConsView::Frame { ctor, ret },
            ConsView::Frame {
                ctor: other,
                ret: other_ret,
            },
        ) if ctor == other => {
            goals.push(Goal::Cons(ret, other_ret));
            Ok(())
        },
        | (ConsView::Top | ConsView::Op { .. } | ConsView::Frame { .. }, _) => Err(Refusal::Clash),
    }
}

/// Unifies two command patterns into their most general unifier, extending
/// `subst`.
///
/// # Specification
/// - requires: the two patterns' metavariables are kept apart — overlap
///   enumeration renames one cell before unifying — since a shared metavariable
///   is one hole.
/// - ensures: positive with `subst` extended to the most general unifier, so
///   `subst.apply_cmd(a) == subst.apply_cmd(b)` after one pass; the found
///   bindings are resolved to their fixpoint before returning.
/// - fails: negative on a polarity, symbol, arity or shape clash, when the
///   occurs check finds a metavariable inside its own image, or when `subst`'s
///   own bindings are cyclic; `subst` is then unchanged.
/// - panics: none.
/// - intension: one worklist over borrowed subtrees of both inputs and of
///   `subst`'s images, each walked through the bindings found so far; the
///   bindings are copied in once, after the whole walk succeeds.
///
/// # Adequacy
/// - hypothesis: L3 — a unifier is found, equates its sides and binds only what
///   it must; a cycle is refused by the occurs check with nothing bound; a
///   triangular unifier is resolved. L1 — every generated pair that unifies is
///   equated by its unifier.
/// - witness: `subst::tests::unification_finds_a_most_general_unifier`
/// - witness: `subst::tests::the_occurs_check_rejects_a_cycle`
/// - witness: `subst::tests::unification_resolves_triangular_bindings`
/// - witness: `tests::subst::every_unifier_equates_its_two_sides`
#[inline]
#[must_use]
pub fn unify_cmd(
    a: &CmdPat,
    b: &CmdPat,
    subst: &mut Subst,
) -> SubstitutionDecision
{
    if a.polarity() != b.polarity() {
        return SubstitutionDecision::from(false);
    }
    let Ok((prods, conss)) = unify_halves(a, b, subst)
    else {
        return SubstitutionDecision::from(false);
    };
    subst.prods.extend(prods);
    subst.conss.extend(conss);
    subst.resolve();
    SubstitutionDecision::from(true)
}

/// The owned producer and consumer bindings of a walk.
type OwnedBindings = (Vec<(MetaVar, ProdPat)>, Vec<(MetaVar, ConsPat)>);

/// The bindings that unify two cuts' halves, before they are committed.
///
/// # Specification
/// - ensures: the bindings found, copied out of the subtrees they borrow.
/// - fails: the first refusal a goal meets.
/// - panics: none.
///
/// # Errors
/// As the failure clause states.
fn unify_halves(
    a: &CmdPat,
    b: &CmdPat,
    existing: &Subst,
) -> Result<OwnedBindings, Refusal>
{
    let mut found: Found<'_, '_> = Found::default();
    let mut goals: Vec<Goal<'_, '_>> = alloc::vec![
        Goal::Prod(a.producer().to_ref(), b.producer().to_ref()),
        Goal::Cons(a.consumer().to_ref(), b.consumer().to_ref()),
    ];
    while let Some(goal) = goals.pop() {
        let step = match goal {
            | Goal::Prod(lhs, rhs) => unify_prod_step(lhs, rhs, existing, &mut found, &mut goals),
            | Goal::Cons(lhs, rhs) => unify_cons_step(lhs, rhs, existing, &mut found, &mut goals),
        };
        step?;
    }
    let prods = found
        .prods
        .into_iter()
        .map(|(var, image)| (var.clone(), image.to_pattern()))
        .collect();
    let conss = found
        .conss
        .into_iter()
        .map(|(var, image)| (var.clone(), image.to_pattern()))
        .collect();
    Ok((prods, conss))
}

/// One producer unification goal: binds a metavariable or enqueues the
/// argument pairs.
///
/// # Specification
/// - ensures: both sides walked through the bindings, then a metavariable bound
///   in `found` or each argument pair enqueued.
/// - fails: [`Refusal::Clash`] on a symbol or arity clash, [`Refusal::Occurs`]
///   on an occurs-check failure, [`Refusal::Cyclic`] on a cyclic walk.
/// - panics: none.
///
/// # Errors
/// As the failure clause states.
fn unify_prod_step<'term>(
    lhs: ProdRef<'term>,
    rhs: ProdRef<'term>,
    existing: &'term Subst,
    found: &mut Found<'term, 'term>,
    goals: &mut Vec<Goal<'term, 'term>>,
) -> Step
{
    let (Maybe::Present(lhs), Maybe::Present(rhs)) = (
        walk_prod(lhs, existing, found),
        walk_prod(rhs, existing, found),
    )
    else {
        return Err(Refusal::Cyclic);
    };
    match (lhs.head(), rhs.head()) {
        | (&ProdHead::Meta(ref x), &ProdHead::Meta(ref y)) if x == y => Ok(()),
        | (&ProdHead::Meta(ref var), _) => bind_found_prod(var, rhs, existing, found),
        | (_, &ProdHead::Meta(ref var)) => bind_found_prod(var, lhs, existing, found),
        | (&ProdHead::Ctor(ref f, arity), &ProdHead::Ctor(ref g, other_arity))
            if f == g && arity == other_arity =>
        {
            goals.extend(
                lhs.children()
                    .zip(rhs.children())
                    .map(|(l, r)| Goal::Prod(l, r)),
            );
            Ok(())
        },
        | (&ProdHead::Ctor(..), &ProdHead::Ctor(..)) => Err(Refusal::Clash),
    }
}

/// Binds a producer metavariable found by unification, after the occurs
/// check.
///
/// # Specification
/// - requires: `var` is unbound in `existing` and `found`.
/// - ensures: `var` bound to `image` in `found`.
/// - fails: [`Refusal::Occurs`] when `var` is a leaf of `image` or of the image
///   of any bound leaf reached from it.
/// - panics: none.
/// - intension: a worklist of subtrees; each bound metavariable's image is
///   visited once.
///
/// # Errors
/// As the failure clause states.
fn bind_found_prod<'term>(
    var: &'term MetaVar,
    image: ProdRef<'term>,
    existing: &'term Subst,
    found: &mut Found<'term, 'term>,
) -> Step
{
    let mut visited: BTreeSet<&MetaVar> = BTreeSet::new();
    let mut pending: Vec<ProdRef<'term>> = alloc::vec![image];
    while let Some(subtree) = pending.pop() {
        for leaf in subtree.metavars() {
            if leaf == var {
                return Err(Refusal::Occurs);
            }
            if !visited.insert(leaf) {
                continue;
            }
            match (found.prods.get(leaf), existing.prods.get(leaf)) {
                | (Some(&bound), _) => pending.push(bound),
                | (None, Some(bound)) => pending.push(bound.to_ref()),
                | (None, None) => {},
            }
        }
    }
    found.prods.insert(var, image);
    Ok(())
}

/// One consumer unification goal: binds a metavariable end or enqueues the
/// frame's argument pairs and the continuation pair.
///
/// # Specification
/// - ensures: both sides walked through the bindings, then a bare metavariable
///   bound in `found`, or each argument pair and the continuation pair
///   enqueued.
/// - fails: [`Refusal::Clash`] on a frame, symbol or arity clash,
///   [`Refusal::Occurs`] on an occurs-check failure, [`Refusal::Cyclic`] on a
///   cyclic walk.
/// - panics: none.
///
/// # Errors
/// As the failure clause states.
fn unify_cons_step<'term>(
    lhs: ConsRef<'term>,
    rhs: ConsRef<'term>,
    existing: &'term Subst,
    found: &mut Found<'term, 'term>,
    goals: &mut Vec<Goal<'term, 'term>>,
) -> Step
{
    let (Maybe::Present(lhs), Maybe::Present(rhs)) = (
        walk_cons(lhs, existing, found),
        walk_cons(rhs, existing, found),
    )
    else {
        return Err(Refusal::Cyclic);
    };
    match (lhs.bare_meta(), rhs.bare_meta()) {
        | (Maybe::Present(x), Maybe::Present(y)) if x == y => return Ok(()),
        | (Maybe::Present(var), _) => return bind_found_cons(var, rhs, existing, found),
        | (_, Maybe::Present(var)) => return bind_found_cons(var, lhs, existing, found),
        | (Maybe::Absent(_), Maybe::Absent(_)) => {},
    }
    match (lhs.view(), rhs.view()) {
        | (ConsView::Top, ConsView::Top) => Ok(()),
        | (
            ConsView::Op { op, args, ret },
            ConsView::Op {
                op: other,
                args: other_args,
                ret: other_ret,
            },
        ) if op == other && args.len() == other_args.len() => {
            goals.extend(args.zip(other_args).map(|(l, r)| Goal::Prod(l, r)));
            goals.push(Goal::Cons(ret, other_ret));
            Ok(())
        },
        | (
            ConsView::Frame { ctor, ret },
            ConsView::Frame {
                ctor: other,
                ret: other_ret,
            },
        ) if ctor == other => {
            goals.push(Goal::Cons(ret, other_ret));
            Ok(())
        },
        | (ConsView::Top | ConsView::Op { .. } | ConsView::Frame { .. } | ConsView::Meta(_), _) => {
            Err(Refusal::Clash)
        },
    }
}

/// Binds a consumer metavariable found by unification, after the occurs
/// check.
///
/// # Specification
/// - requires: `var` is unbound in `existing` and `found`.
/// - ensures: `var` bound to `image` in `found`.
/// - fails: [`Refusal::Occurs`] when `var` ends `image`'s spine, or the spine
///   of the image of any bound end reached from it. A consumer metavariable
///   occurs only at a spine's end: operation arguments are producers.
/// - panics: none.
///
/// # Errors
/// As the failure clause states.
fn bind_found_cons<'term>(
    var: &'term MetaVar,
    image: ConsRef<'term>,
    existing: &'term Subst,
    found: &mut Found<'term, 'term>,
) -> Step
{
    let mut visited: BTreeSet<&MetaVar> = BTreeSet::new();
    let mut cursor = image;
    while let SpineEnd::Meta(ref end) = *cursor.end() {
        if end == var {
            return Err(Refusal::Occurs);
        }
        if !visited.insert(end) {
            break;
        }
        cursor = match (found.conss.get(end), existing.conss.get(end)) {
            | (Some(&bound), _) => bound,
            | (None, Some(bound)) => bound.to_ref(),
            | (None, None) => break,
        };
    }
    found.conss.insert(var, image);
    Ok(())
}

quenchant_shape::reason_enum! {
    /// Why walking a subtree through the bindings reaches no unbound head.
    mod binding_walk {
        /// The reason the walk stops short.
        #[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
        pub enum Absent {
            /// The bindings form a cycle: the walk took more steps than there
            /// are bindings.
            Cyclic,
        }
    }
}

/// `prod` followed through the bindings until its head is a constructor or
/// an unbound metavariable.
///
/// # Specification
/// - ensures: the first subtree along the binding chain whose head is not a
///   bound metavariable.
/// - provides: [`binding_walk::Absent::Cyclic`] when the chain is longer than
///   the number of bindings, which only a cyclic chain is.
/// - panics: none.
fn walk_prod<'term>(
    prod: ProdRef<'term>,
    existing: &'term Subst,
    found: &Found<'term, 'term>,
) -> Maybe<ProdRef<'term>, binding_walk::Absent>
{
    let bound = existing.prods.len().saturating_add(found.prods.len());
    let mut cursor = prod;
    for _ in 0 ..= bound {
        let ProdHead::Meta(ref var) = *cursor.head()
        else {
            return Maybe::Present(cursor);
        };
        cursor = match (found.prods.get(var), existing.prods.get(var)) {
            | (Some(&image), _) => image,
            | (None, Some(image)) => image.to_ref(),
            | (None, None) => return Maybe::Present(cursor),
        };
    }
    Maybe::Absent(binding_walk::Absent::Cyclic)
}

/// `cons` followed through the bindings until it is not a bare bound
/// metavariable.
///
/// # Specification
/// - ensures: the first subtree along the binding chain that is not a bare
///   bound metavariable.
/// - provides: [`binding_walk::Absent::Cyclic`] when the chain is longer than
///   the number of bindings, which only a cyclic chain is.
/// - panics: none.
fn walk_cons<'term>(
    cons: ConsRef<'term>,
    existing: &'term Subst,
    found: &Found<'term, 'term>,
) -> Maybe<ConsRef<'term>, binding_walk::Absent>
{
    let bound = existing.conss.len().saturating_add(found.conss.len());
    let mut cursor = cons;
    for _ in 0 ..= bound {
        let Maybe::Present(var) = cursor.bare_meta()
        else {
            return Maybe::Present(cursor);
        };
        cursor = match (found.conss.get(var), existing.conss.get(var)) {
            | (Some(&image), _) => image,
            | (None, Some(image)) => image.to_ref(),
            | (None, None) => return Maybe::Present(cursor),
        };
    }
    Maybe::Absent(binding_walk::Absent::Cyclic)
}

/// Whether an image mentions a bound metavariable.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct BoundMention(bool);

#[cfg(test)]
mod tests
{
    use super::*;
    use crate::polarity::Polarity;

    #[test]
    fn a_restriction_keeps_exactly_the_named_bindings()
    {
        let (x, alpha) = (MetaVar::producer("x"), MetaVar::consumer("alpha"));
        let mut subst = Subst::new();
        subst
            .bind_prod(x.clone(), ProdPat::ctor("Zero", []))
            .expect("a fresh producer binding");
        subst
            .bind_cons(alpha.clone(), ConsPat::top())
            .expect("a fresh consumer binding");
        let kept = subst.restricted(core::slice::from_ref(&alpha));
        assert_eq!(
            (
                Maybe::Absent(binding::Absent::Unbound),
                Maybe::Present(&ConsPat::top())
            ),
            (kept.get_prod(&x), kept.get_cons(&alpha)),
            "the named binding is kept and the other dropped"
        );
        assert_eq!(
            Subst::new(),
            subst.restricted(&[MetaVar::producer("y")]),
            "a metavariable left unbound stays unbound"
        );
    }

    #[test]
    fn matching_binds_a_ground_configuration()
    {
        // ⟨Succ(m) | add(n; α)⟩ against ⟨Succ(Zero) | add(Zero; ★)⟩.
        let lhs = CmdPat::cut(
            Polarity::Positive,
            ProdPat::ctor("Succ", [ProdPat::meta("m")]),
            ConsPat::op("add", [ProdPat::meta("n")], ConsPat::meta("alpha")),
        );
        let ground = CmdPat::cut(
            Polarity::Positive,
            ProdPat::ctor("Succ", [ProdPat::ctor("Zero", [])]),
            ConsPat::op("add", [ProdPat::ctor("Zero", [])], ConsPat::top()),
        );
        let mut subst = Subst::new();
        assert!(
            bool::from(match_cmd(&lhs, &ground, &mut subst)),
            "the LHS matches the config"
        );
        assert_eq!(
            subst.apply_cmd(&lhs),
            ground,
            "the match reconstructs the config"
        );
    }

    #[test]
    fn a_polarity_clash_blocks_a_match()
    {
        let lhs = CmdPat::cut(Polarity::Positive, ProdPat::meta("x"), ConsPat::meta("a"));
        let ground = CmdPat::cut(
            Polarity::Negative,
            ProdPat::ctor("Zero", []),
            ConsPat::top(),
        );
        let mut subst = Subst::new();
        assert!(
            !bool::from(match_cmd(&lhs, &ground, &mut subst)),
            "a positive cell does not apply at a negative cut"
        );
        assert!(
            bool::from(subst.is_empty()),
            "and a refused match binds nothing"
        );
    }

    #[test]
    fn unification_finds_a_most_general_unifier()
    {
        // ⟨Succ(x) | α⟩ unifies with ⟨y | add(Zero; β)⟩ under y↦Succ(x),
        // α↦add(Zero; β).
        let a = CmdPat::cut(
            Polarity::Positive,
            ProdPat::ctor("Succ", [ProdPat::meta("x")]),
            ConsPat::meta("a"),
        );
        let b = CmdPat::cut(
            Polarity::Positive,
            ProdPat::meta("y"),
            ConsPat::op("add", [ProdPat::ctor("Zero", [])], ConsPat::meta("b")),
        );
        let mut subst = Subst::new();
        assert!(bool::from(unify_cmd(&a, &b, &mut subst)), "the cuts unify");
        assert_eq!(
            subst.apply_cmd(&a),
            subst.apply_cmd(&b),
            "the unifier equates both sides"
        );
        assert_eq!(
            SubstitutionBindingCount::from(2_usize),
            subst.len(),
            "and binds exactly y and α: the unifier is most general"
        );
    }

    #[test]
    fn the_occurs_check_rejects_a_cycle()
    {
        // x unified with Succ(x) must fail.
        let a = CmdPat::cut(Polarity::Positive, ProdPat::meta("x"), ConsPat::top());
        let b = CmdPat::cut(
            Polarity::Positive,
            ProdPat::ctor("Succ", [ProdPat::meta("x")]),
            ConsPat::top(),
        );
        let mut subst = Subst::new();
        assert!(
            !bool::from(unify_cmd(&a, &b, &mut subst)),
            "x = Succ(x) is rejected by the occurs-check"
        );
        assert!(
            bool::from(subst.is_empty()),
            "and a refused unification binds nothing"
        );
    }

    #[test]
    fn unification_resolves_triangular_bindings()
    {
        // A binding whose image mentions a metavariable bound after it (the
        // goal order is not topological: here `b2` binds first to an image
        // mentioning x, and x binds afterward) must be resolved to the
        // fixpoint before the unifier is returned, or single-pass application
        // leaves `apply(a) != apply(b)`.
        let a = CmdPat::cut(
            Polarity::Positive,
            ProdPat::meta("x"),
            ConsPat::op(
                "add",
                [ProdPat::ctor("Succ", [ProdPat::ctor("Succ", [
                    ProdPat::meta("x"),
                ])])],
                ConsPat::top(),
            ),
        );
        let b = CmdPat::cut(
            Polarity::Positive,
            ProdPat::ctor("Cons", [
                ProdPat::ctor("Succ", [ProdPat::ctor("Zero", [])]),
                ProdPat::ctor("Succ", [ProdPat::ctor("Nil", [])]),
            ]),
            ConsPat::meta("b2"),
        );
        let mut subst = Subst::new();
        assert!(bool::from(unify_cmd(&a, &b, &mut subst)), "the cuts unify");
        assert_eq!(
            subst.apply_cmd(&a),
            subst.apply_cmd(&b),
            "the unifier equates both sides after one application pass"
        );
        let Maybe::Present(image) = subst.get_cons(&MetaVar::consumer("b2"))
        else {
            panic!("b2 is bound");
        };
        assert!(
            bool::from(image.is_ground()),
            "and b2's image no longer mentions x"
        );
    }
}
