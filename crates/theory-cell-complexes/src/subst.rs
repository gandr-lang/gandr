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

use anodized::spec;
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
    ///
    /// # Adequacy
    /// - hypothesis: L3 — fresh, bound and wrong-category keys observe exact
    ///   producer images or named absence. Shifted keys and category confusion
    ///   change the result.
    /// - witness: `subst::tests::binding_refusals_preserve_both_category_maps`
    #[inline]
    #[spec(ensures: |output| match output {
        Maybe::Present(image) => self.prods.iter().any(|(held, value)| held == var && value == image),
        Maybe::Absent(_) => !self.prods.contains_key(var),
    })]
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
    ///
    /// # Adequacy
    /// - hypothesis: L3 — fresh, bound and wrong-category keys observe exact
    ///   consumer images or named absence. Shifted keys and category confusion
    ///   change the result.
    /// - witness: `subst::tests::binding_refusals_preserve_both_category_maps`
    #[inline]
    #[spec(ensures: |output| match output {
        Maybe::Present(image) => self.conss.iter().any(|(held, value)| held == var && value == image),
        Maybe::Absent(_) => !self.conss.contains_key(var),
    })]
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
    /// - hypothesis: L3 — empty, singleton, duplicated, complete and absent
    ///   variable lists select exact binding maps. Extra keys, missing images
    ///   and duplicate-count dependence change the result.
    /// - witness: `subst::tests::a_restriction_keeps_exactly_the_named_bindings`
    /// - witness: `subst::tests::binding_refusals_preserve_both_category_maps`
    #[inline]
    #[must_use]
    #[spec(ensures: |output| output.prods.iter().eq(self.prods.iter().filter(|&(var, _)| vars.contains(var)))
        && output.conss.iter().eq(self.conss.iter().filter(|&(var, _)| vars.contains(var))))]
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
    /// - hypothesis: L3 — fresh, equal-rebind, conflicting and wrong-category
    ///   producer offers expose exact results and preserved maps; L1 —
    ///   generated instances reconstruct their targets. Overwriting or
    ///   accepting a wrong category changes the observations.
    /// - witness: `subst::tests::unification_resolves_triangular_bindings`
    /// - witness: `tests::subst::every_match_reproduces_its_target`
    /// - witness: `subst::tests::binding_refusals_preserve_both_category_maps`
    #[inline]
    #[spec(
        captures: [
            expected = if var.cat() != Cat::Producer { Err(BindingRefusal::CategoryMismatch) }
                else if self.prods.get(&var).is_some_and(|held| *held != image) { Err(BindingRefusal::ConflictingRebind) }
                else { Ok(()) },
            bindings = self.prods.len(),
            grows = var.cat() == Cat::Producer && !self.prods.contains_key(&var),
        ],
        ensures: |output| output == expected && self.prods.len() == bindings.saturating_add(usize::from(grows)),
    )]
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
    /// - hypothesis: L3 — fresh, equal-rebind, conflicting and wrong-category
    ///   consumer offers expose exact results and preserved maps. Overwriting,
    ///   incorrect refusal precedence and accepting a producer key change the
    ///   observations.
    /// - witness: `subst::tests::unification_finds_a_most_general_unifier`
    /// - witness: `subst::tests::binding_refusals_preserve_both_category_maps`
    #[inline]
    #[spec(
        captures: [
            expected = if var.cat() != Cat::Consumer { Err(BindingRefusal::CategoryMismatch) }
                else if self.conss.get(&var).is_some_and(|held| *held != image) { Err(BindingRefusal::ConflictingRebind) }
                else { Ok(()) },
            bindings = self.conss.len(),
            grows = var.cat() == Cat::Consumer && !self.conss.contains_key(&var),
        ],
        ensures: |output| output == expected && self.conss.len() == bindings.saturating_add(usize::from(grows)),
    )]
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
    /// - hypothesis: L3 — acyclic two-category substitutions are empty,
    ///   resolved or triangular; exact one-pass images and idempotence
    ///   distinguish skipped resolution from repeated expansion. L1 — generated
    ///   unifiers equate both sides.
    /// - witness: `subst::tests::unification_resolves_triangular_bindings`
    /// - witness: `tests::subst::every_unifier_equates_its_two_sides`
    /// - witness: `subst::tests::substitution_applies_once_then_resolves_both_categories`
    #[inline]
    #[spec(ensures: self.prods.values().all(|image| !self.mentions_bound(image.to_ref().metavars()).0)
        && self.conss.values().all(|image| !self.mentions_bound(image.to_ref().metavars()).0))]
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
    /// - ensures: positive exactly when an occurrence is bound in its own
    ///   category; an empty map or occurrence sequence gives a negative answer.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — empty and populated maps distinguish bound holes in
    ///   each category from absent names and the opposite category. Missing
    ///   category dispatch, treating emptiness as positive or overlooking a
    ///   bound occurrence changes the observations.
    /// - witness: `subst::tests::binding_refusals_preserve_both_category_maps`
    #[spec(ensures: |output| !output.0 || !bool::from(self.is_empty()))]
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
    /// - hypothesis: L3 — empty, partial and triangular substitutions preserve
    ///   unbound holes and polarity while inserting images once. Exact terms
    ///   distinguish recursive expansion and lost frames; L1 — generated
    ///   matches reproduce their targets.
    /// - witness: `subst::tests::matching_binds_a_ground_configuration`
    /// - witness: `tests::subst::every_match_reproduces_its_target`
    /// - witness: `subst::tests::substitution_applies_once_then_resolves_both_categories`
    #[inline]
    #[must_use]
    #[spec(ensures: |output| output.polarity() == cmd.polarity()
        && (self.mentions_bound(cmd.metavars()).0 || output == *cmd))]
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
    ///
    /// # Adequacy
    /// - hypothesis: L3 — bound and unbound leaves, a nested constructor and a
    ///   triangular image are compared before and after resolution. Extra
    ///   passes or lost constructor children change exact terms.
    /// - witness: `subst::tests::substitution_applies_once_then_resolves_both_categories`
    #[inline]
    #[must_use]
    #[spec(ensures: |output| (matches!(prod.to_ref().head(), ProdHead::Meta(_)) || output.to_ref().head() == prod.to_ref().head())
        && (self.mentions_bound(prod.to_ref().metavars()).0 || output == *prod))]
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
    ///
    /// # Adequacy
    /// - hypothesis: L3 — terminal, unbound and bound consumer ends under
    ///   frames and operation arguments are compared before and after
    ///   resolution. Lost frames, skipped arguments and recursive expansion
    ///   change exact terms.
    /// - witness: `subst::tests::substitution_applies_once_then_resolves_both_categories`
    #[inline]
    #[must_use]
    #[spec(ensures: |output| output.to_ref().frames().len() >= cons.to_ref().frames().len()
        && (self.mentions_bound(cons.to_ref().metavars()).0 || output == *cons))]
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
    ///
    /// # Adequacy
    /// - hypothesis: L3 — bare and nested producers with bound, unbound and
    ///   triangular images have exact one-pass observations. Missing leaves or
    ///   an extra expansion pass changes the term.
    /// - witness: `subst::tests::substitution_applies_once_then_resolves_both_categories`
    #[spec(ensures: |output| (matches!(prod.head(), ProdHead::Meta(_)) || output.to_ref().head() == prod.head())
        && (self.mentions_bound(prod.metavars()).0 || output.to_ref() == prod))]
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
    ///
    /// # Adequacy
    /// - hypothesis: L3 — empty, framed and operation consumer spines with
    ///   bound or unbound ends have exact one-pass observations. Dropped
    ///   arguments or reordered frame suffixes change the term.
    /// - witness: `subst::tests::substitution_applies_once_then_resolves_both_categories`
    #[spec(ensures: |output| output.to_ref().frames().len() >= cons.frames().len()
        && (self.mentions_bound(cons.metavars()).0 || output.to_ref() == cons))]
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
    ///
    /// # Adequacy
    /// - hypothesis: L3 — successful matching extends an already populated
    ///   substitution in both categories; a later conflict leaves it unchanged.
    ///   Exact images and counts reject overwrite, omitted commitment and
    ///   premature commitment.
    /// - witness: `subst::tests::failed_walks_preserve_existing_and_staged_bindings`
    #[spec(
        requires: found.prods.keys().all(|var| !self.prods.contains_key(*var))
            && found.conss.keys().all(|var| !self.conss.contains_key(*var)),
        captures: bindings = usize::from(self.len()).saturating_add(found.prods.len()).saturating_add(found.conss.len()),
        ensures: usize::from(self.len()) == bindings,
    )]
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
///
/// # Adequacy
/// - hypothesis: L3 — empty and two-category renaming maps are observed by
///   exact lookups, restriction and application. Swapped categories, omitted
///   keys and lost images change the substitution.
/// - witness: `subst::tests::substitution_applies_once_then_resolves_both_categories`
#[inline]
#[spec(requires: prods.keys().all(|var| var.cat() == Cat::Producer)
    && conss.keys().all(|var| var.cat() == Cat::Consumer))]
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
/// - hypothesis: L3 — valid positive cuts with constructor, arity, frame,
///   polarity or binding clashes preserve a nonempty substitution despite
///   staged bindings; successful matches reproduce their targets. L1 —
///   generated instances reject skipped matching or commitment.
/// - witness: `subst::tests::matching_binds_a_ground_configuration`
/// - witness: `subst::tests::a_polarity_clash_blocks_a_match`
/// - witness: `tests::subst::every_match_reproduces_its_target`
/// - witness: `subst::tests::failed_walks_preserve_existing_and_staged_bindings`
#[inline]
#[must_use]
#[spec(captures: before = subst.clone(), ensures: |output| if bool::from(output) {
    subst.apply_cmd(pattern) == *target
} else { *subst == before })]
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
/// # Adequacy
/// - hypothesis: L3 — producer heads differing by symbol, arity or
///   repeated-hole image fail after a consumer binding has been staged. Exact
///   refusal and unchanged substitution reject early commitment and ignored
///   conflicts.
/// - witness: `subst::tests::failed_walks_preserve_existing_and_staged_bindings`
///
/// # Errors
/// As the failure clause states.
#[spec(captures: [bindings = found.prods.len(), pending = goals.len()],
    ensures: |output| output.is_ok() || (found.prods.len() == bindings && goals.len() == pending))]
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
/// # Adequacy
/// - hypothesis: L3 — consumer frames and operation arities disagree with a
///   pattern; compatible ends succeed. Exact substitutions and refusal
///   distinguish ignored frame clashes and conflicting end bindings.
/// - witness: `subst::tests::failed_walks_preserve_existing_and_staged_bindings`
///
/// # Errors
/// As the failure clause states.
#[spec(captures: [bindings = found.conss.len(), pending = goals.len()],
    ensures: |output| output.is_ok() || (found.conss.len() == bindings && goals.len() == pending))]
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
/// - hypothesis: L3 — renamed-apart equations distinguish unifiers, triangular
///   images, clashes and cyclic dereferences. Exact equations and unchanged
///   refusal states reject false success, skipped resolution and early
///   commitment. L1 — generated successful pairs are equated by their unifier.
/// - witness: `subst::tests::unification_finds_a_most_general_unifier`
/// - witness: `subst::tests::the_occurs_check_rejects_a_cycle`
/// - witness: `subst::tests::unification_resolves_triangular_bindings`
/// - witness: `tests::subst::every_unifier_equates_its_two_sides`
/// - witness: `subst::tests::failed_walks_preserve_existing_and_staged_bindings`
/// - witness: `subst::tests::walks_refuse_cycles_and_occurs_checks`
#[inline]
#[must_use]
#[spec(captures: before = subst.clone(), ensures: |output| if bool::from(output) {
    subst.apply_cmd(a) == subst.apply_cmd(b)
} else { *subst == before })]
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
/// # Adequacy
/// - hypothesis: L3 — successful and conflicting two-category equations begin
///   with existing bindings. Replayed equations and exact unchanged failure
///   states reject omitted bindings and partial commitment.
/// - witness: `subst::tests::failed_walks_preserve_existing_and_staged_bindings`
///
/// # Errors
/// As the failure clause states.
#[spec(ensures: |output| output.as_ref().map_or(true, |bindings|
    bindings.0.iter().all(|binding| binding.0.cat() == Cat::Producer && !existing.prods.contains_key(&binding.0))
        && bindings.1.iter().all(|binding| binding.0.cat() == Cat::Consumer && !existing.conss.contains_key(&binding.0))))]
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
/// # Adequacy
/// - hypothesis: L3 — unequal producer heads, equal holes, proper bindings and
///   cyclic dereferences separate successes and refusals. Exact resulting
///   equations and unchanged failure states reject skipped occurs checks and
///   false success.
/// - witness: `subst::tests::walks_refuse_cycles_and_occurs_checks`
///
/// # Errors
/// As the failure clause states.
#[spec(captures: [bindings = found.prods.len(), pending = goals.len()],
    ensures: |output| output.is_ok() || (found.prods.len() == bindings && goals.len() == pending))]
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
/// # Adequacy
/// - hypothesis: L3 — unbound producer holes meet ground, directly recursive
///   and indirectly recursive images. Exact bindings or unchanged maps reject a
///   lost occurs check and premature insertion.
/// - witness: `subst::tests::walks_refuse_cycles_and_occurs_checks`
///
/// # Errors
/// As the failure clause states.
#[spec(
    requires: !existing.prods.contains_key(var) && !found.prods.contains_key(var),
    ensures: |output| if output.is_ok() { found.prods.get(var) == Some(&image) }
        else { !found.prods.contains_key(var) },
)]
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
/// # Adequacy
/// - hypothesis: L3 — bare and framed consumer equations include direct and
///   indirect cycles. Exact substitutions or unchanged failure states
///   distinguish genuine binding from ignored cyclic ends.
/// - witness: `subst::tests::walks_refuse_cycles_and_occurs_checks`
///
/// # Errors
/// As the failure clause states.
#[spec(captures: [bindings = found.conss.len(), pending = goals.len()],
    ensures: |output| output.is_ok() || (found.conss.len() == bindings && goals.len() == pending))]
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
/// # Adequacy
/// - hypothesis: L3 — unbound consumer holes meet terminal, directly recursive
///   and indirectly recursive spines. Exact bindings or unchanged maps reject a
///   lost occurs check and premature insertion.
/// - witness: `subst::tests::walks_refuse_cycles_and_occurs_checks`
///
/// # Errors
/// As the failure clause states.
#[spec(
    requires: !existing.conss.contains_key(var) && !found.conss.contains_key(var),
    ensures: |output| if output.is_ok() { found.conss.get(var) == Some(&image) }
        else { !found.conss.contains_key(var) },
)]
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
///
/// # Adequacy
/// - hypothesis: L3 — empty, acyclic and cyclic producer maps expose a
///   constructor, unbound leaf or typed cycle. Premature stopping and an
///   incorrect traversal bound change the result.
/// - witness: `subst::tests::walks_refuse_cycles_and_occurs_checks`
#[spec(ensures: |output| match output {
    Maybe::Present(term) => match *term.head() {
        ProdHead::Ctor(..) => true,
        ProdHead::Meta(ref var) => !existing.prods.contains_key(var) && !found.prods.contains_key(var),
    },
    Maybe::Absent(_) => !existing.prods.is_empty() || !found.prods.is_empty(),
})]
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
///
/// # Adequacy
/// - hypothesis: L3 — empty, acyclic and cyclic consumer maps expose a
///   terminal, unbound end or typed cycle. Following beneath a frame or using
///   an incorrect traversal bound changes the result.
/// - witness: `subst::tests::walks_refuse_cycles_and_occurs_checks`
#[spec(ensures: |output| match output {
    Maybe::Present(term) => match term.bare_meta() {
        Maybe::Present(var) => !existing.conss.contains_key(var) && !found.conss.contains_key(var),
        Maybe::Absent(_) => true,
    },
    Maybe::Absent(_) => !existing.conss.is_empty() || !found.conss.is_empty(),
})]
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
    fn binding_refusals_preserve_both_category_maps()
    {
        let x = MetaVar::producer("x");
        let alpha = MetaVar::consumer("alpha");
        let zero = ProdPat::ctor("Zero", []);
        let top = ConsPat::top();
        let mut subst = Subst::new();
        assert!(!subst.mentions_bound([&x, &alpha]).0);
        assert_eq!(Maybe::Absent(binding::Absent::Unbound), subst.get_prod(&x));
        assert_eq!(
            Maybe::Absent(binding::Absent::Unbound),
            subst.get_cons(&alpha)
        );
        assert_eq!(
            Err(BindingRefusal::CategoryMismatch),
            subst.bind_prod(alpha.clone(), zero.clone())
        );
        assert_eq!(
            Err(BindingRefusal::CategoryMismatch),
            subst.bind_cons(x.clone(), top.clone())
        );
        assert_eq!(Subst::new(), subst);
        assert_eq!(Ok(()), subst.bind_prod(x.clone(), zero.clone()));
        assert_eq!(Ok(()), subst.bind_cons(alpha.clone(), top.clone()));
        assert!(!subst.mentions_bound(core::iter::empty()).0);
        assert!(subst.mentions_bound([&x]).0);
        assert!(subst.mentions_bound([&alpha]).0);
        assert!(
            !subst
                .mentions_bound([
                    &MetaVar::consumer("x"),
                    &MetaVar::producer("alpha"),
                    &MetaVar::producer("missing")
                ])
                .0
        );
        let before = subst.clone();
        assert_eq!(Ok(()), subst.bind_prod(x.clone(), zero.clone()));
        assert_eq!(Ok(()), subst.bind_cons(alpha.clone(), top.clone()));
        assert_eq!(before, subst);
        assert_eq!(
            Err(BindingRefusal::ConflictingRebind),
            subst.bind_prod(x.clone(), ProdPat::ctor("One", []))
        );
        assert_eq!(
            Err(BindingRefusal::ConflictingRebind),
            subst.bind_cons(alpha.clone(), ConsPat::frame("F", ConsPat::top()))
        );
        assert_eq!(before, subst);
        assert_eq!(Maybe::Present(&zero), subst.get_prod(&x));
        assert_eq!(Maybe::Present(&top), subst.get_cons(&alpha));
        assert_eq!(
            Maybe::Absent(binding::Absent::Unbound),
            subst.get_prod(&alpha)
        );
        assert_eq!(Maybe::Absent(binding::Absent::Unbound), subst.get_cons(&x));
        assert_eq!(subst, subst.restricted(&[alpha, x.clone(), x]));
        assert_eq!(Subst::new(), subst.restricted(&[]));
    }

    #[test]
    fn substitution_applies_once_then_resolves_both_categories()
    {
        let x = MetaVar::producer("x");
        let y = MetaVar::producer("y");
        let alpha = MetaVar::consumer("alpha");
        let beta = MetaVar::consumer("beta");
        let zero = ProdPat::ctor("Zero", []);
        let mut subst = substitution_from(
            BTreeMap::from([(x.clone(), ProdPat::meta("y")), (y, zero.clone())]),
            BTreeMap::from([
                (alpha.clone(), ConsPat::frame("F", ConsPat::meta("beta"))),
                (beta, ConsPat::top()),
            ]),
        );
        assert_eq!(
            Subst::new(),
            substitution_from(BTreeMap::new(), BTreeMap::new())
        );
        let prod = ProdPat::ctor("Pair", [ProdPat::meta("x"), ProdPat::meta("free")]);
        let cons = ConsPat::op(
            "op",
            [ProdPat::meta("x")],
            ConsPat::frame("Outer", ConsPat::meta("alpha")),
        );
        let before_prod = ProdPat::ctor("Pair", [ProdPat::meta("y"), ProdPat::meta("free")]);
        let before_cons = ConsPat::op(
            "op",
            [ProdPat::meta("y")],
            ConsPat::frame("Outer", ConsPat::frame("F", ConsPat::meta("beta"))),
        );
        assert_eq!(before_prod, subst.apply_prod(&prod));
        assert_eq!(before_cons, subst.apply_cons(&cons));
        let command = CmdPat::cut(Polarity::Negative, prod, cons);
        assert_eq!(
            CmdPat::cut(Polarity::Negative, before_prod, before_cons),
            subst.apply_cmd(&command)
        );
        assert_eq!(ConsPat::top(), subst.apply_cons(&ConsPat::top()));
        assert_eq!(
            ConsPat::meta("free"),
            subst.apply_cons(&ConsPat::meta("free"))
        );
        subst.resolve();
        assert_eq!(Maybe::Present(&zero), subst.get_prod(&x));
        assert_eq!(
            Maybe::Present(&ConsPat::frame("F", ConsPat::top())),
            subst.get_cons(&alpha)
        );
        let after_prod = ProdPat::ctor("Pair", [zero.clone(), ProdPat::meta("free")]);
        let after_cons = ConsPat::op(
            "op",
            [zero],
            ConsPat::frame("Outer", ConsPat::frame("F", ConsPat::top())),
        );
        let expected = CmdPat::cut(Polarity::Negative, after_prod, after_cons);
        assert_eq!(expected, subst.apply_cmd(&command));
        assert_eq!(expected, subst.apply_cmd(&expected));
        let resolved = subst.clone();
        subst.resolve();
        assert_eq!(resolved, subst);
    }

    #[test]
    fn failed_walks_preserve_existing_and_staged_bindings()
    {
        let cut = |prod, cons| CmdPat::cut(Polarity::Positive, prod, cons);
        let zero = ProdPat::ctor("Zero", []);
        let one = ProdPat::ctor("One", []);
        let mut base = Subst::new();
        base.bind_prod(MetaVar::producer("held"), zero.clone())
            .expect("fresh binding");
        base.bind_cons(MetaVar::consumer("held_cons"), ConsPat::top())
            .expect("fresh binding");
        let ordinary = cut(
            ProdPat::ctor("F", [ProdPat::meta("x")]),
            ConsPat::meta("alpha"),
        );
        let target = cut(
            ProdPat::ctor("F", [zero.clone()]),
            ConsPat::frame("K", ConsPat::top()),
        );
        for unifies in [false, true] {
            let mut accepted = base.clone();
            let decision = if unifies {
                unify_cmd(&ordinary, &target, &mut accepted)
            }
            else {
                match_cmd(&ordinary, &target, &mut accepted)
            };
            assert!(bool::from(decision));
            assert_eq!(target, accepted.apply_cmd(&ordinary));
            assert_eq!(SubstitutionBindingCount::from(4_usize), accepted.len());
            assert_eq!(
                base,
                accepted.restricted(&[MetaVar::producer("held"), MetaVar::consumer("held_cons")])
            );
        }
        let failures = [
            (
                ordinary.clone(),
                CmdPat::cut(
                    Polarity::Negative,
                    target.producer().clone(),
                    target.consumer().clone(),
                ),
            ),
            (
                ordinary.clone(),
                cut(ProdPat::ctor("G", [zero.clone()]), ConsPat::top()),
            ),
            (ordinary, cut(ProdPat::ctor("F", []), ConsPat::top())),
            (
                cut(
                    ProdPat::ctor("Pair", [ProdPat::meta("x"), ProdPat::meta("x")]),
                    ConsPat::meta("alpha"),
                ),
                cut(
                    ProdPat::ctor("Pair", [zero.clone(), one.clone()]),
                    ConsPat::top(),
                ),
            ),
            (
                cut(
                    ProdPat::meta("x"),
                    ConsPat::op("op", [ProdPat::meta("y")], ConsPat::meta("alpha")),
                ),
                cut(zero.clone(), ConsPat::op("op", [], ConsPat::top())),
            ),
            (
                cut(
                    ProdPat::meta("x"),
                    ConsPat::frame("F", ConsPat::meta("alpha")),
                ),
                cut(zero.clone(), ConsPat::frame("G", ConsPat::top())),
            ),
            (
                cut(ProdPat::meta("held"), ConsPat::meta("alpha")),
                cut(one, ConsPat::top()),
            ),
            (
                cut(ProdPat::meta("x"), ConsPat::meta("held_cons")),
                cut(zero, ConsPat::frame("F", ConsPat::top())),
            ),
        ];
        for (pattern, target) in failures {
            for unifies in [false, true] {
                let mut actual = base.clone();
                let decision = if unifies {
                    unify_cmd(&pattern, &target, &mut actual)
                }
                else {
                    match_cmd(&pattern, &target, &mut actual)
                };
                assert!(!bool::from(decision));
                assert_eq!(base, actual);
            }
        }
    }

    #[test]
    fn walks_refuse_cycles_and_occurs_checks()
    {
        let x = MetaVar::producer("x");
        let alpha = MetaVar::consumer("alpha");
        let px = ProdPat::meta("x");
        let ca = ConsPat::meta("alpha");
        let zero = ProdPat::ctor("Zero", []);
        let top = ConsPat::top();
        let empty = Subst::new();
        let found = Found::default();
        assert_eq!(
            Maybe::Present(px.to_ref()),
            walk_prod(px.to_ref(), &empty, &found)
        );
        assert_eq!(
            Maybe::Present(ca.to_ref()),
            walk_cons(ca.to_ref(), &empty, &found)
        );
        let cyclic = substitution_from(
            BTreeMap::from([
                (x.clone(), ProdPat::meta("y")),
                (MetaVar::producer("y"), px.clone()),
            ]),
            BTreeMap::from([
                (alpha.clone(), ConsPat::meta("beta")),
                (MetaVar::consumer("beta"), ca.clone()),
            ]),
        );
        assert_eq!(
            Maybe::Absent(binding_walk::Absent::Cyclic),
            walk_prod(px.to_ref(), &cyclic, &found)
        );
        assert_eq!(
            Maybe::Absent(binding_walk::Absent::Cyclic),
            walk_cons(ca.to_ref(), &cyclic, &found)
        );
        let framed = ConsPat::frame("F", ca.clone());
        assert_eq!(
            Maybe::Present(framed.to_ref()),
            walk_cons(framed.to_ref(), &cyclic, &found)
        );
        for (left, right) in [
            (
                CmdPat::cut(Polarity::Positive, px.clone(), top.clone()),
                CmdPat::cut(Polarity::Positive, zero.clone(), top.clone()),
            ),
            (
                CmdPat::cut(Polarity::Positive, zero.clone(), ca.clone()),
                CmdPat::cut(Polarity::Positive, zero.clone(), top.clone()),
            ),
        ] {
            let mut actual = cyclic.clone();
            assert!(!bool::from(unify_cmd(&left, &right, &mut actual)));
            assert_eq!(cyclic, actual);
        }
        let indirect = substitution_from(
            BTreeMap::from([(MetaVar::producer("y"), px.clone())]),
            BTreeMap::from([(MetaVar::consumer("beta"), ca.clone())]),
        );
        for image in [
            ProdPat::ctor("Succ", [px.clone()]),
            ProdPat::ctor("Succ", [ProdPat::meta("y")]),
        ] {
            let mut found = Found::default();
            assert_eq!(
                Err(Refusal::Occurs),
                bind_found_prod(&x, image.to_ref(), &indirect, &mut found)
            );
            assert!(found.prods.is_empty());
        }
        for image in [framed, ConsPat::frame("F", ConsPat::meta("beta"))] {
            let mut found = Found::default();
            assert_eq!(
                Err(Refusal::Occurs),
                bind_found_cons(&alpha, image.to_ref(), &indirect, &mut found)
            );
            assert!(found.conss.is_empty());
        }
        let mut found = Found::default();
        assert_eq!(
            Ok(()),
            bind_found_prod(&x, zero.to_ref(), &empty, &mut found)
        );
        assert_eq!(
            Ok(()),
            bind_found_cons(&alpha, top.to_ref(), &empty, &mut found)
        );
        assert_eq!(
            Maybe::Present(zero.to_ref()),
            walk_prod(px.to_ref(), &empty, &found)
        );
        assert_eq!(
            Maybe::Present(top.to_ref()),
            walk_cons(ca.to_ref(), &empty, &found)
        );
    }

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
