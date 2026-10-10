//! The name-modifier language and its interpreter.
//!
//! A name modifier is a term whose meaning is a transformation of one
//! namespace into another, run wherever a namespace meets another: at an
//! import, at an include, at the close of a section.
//!
//! # Six constructors
//!
//! ```text
//! m ::= assert-nonempty     perform not-found when the namespace is empty
//!     | in p m              run m on the subtree at p, keep everything outside it
//!     | renaming p p'       move the subtree at p to p', dropping whatever was at p'
//!     | seq (m₁, …, mₙ)     run in order; seq () is the identity
//!     | union (m₁, …, mₙ)   run each on the same input, union the results
//!     | hook h              an extension point, performed as an event
//! ```
//!
//! Every other builder derives from them:
//!
//! | builder | derivation |
//! | --- | --- |
//! | [`Modifier::all`] | `assert-nonempty` |
//! | [`Modifier::id`] | `seq ()` |
//! | [`Modifier::none`] | `seq (assert-nonempty, union ())` |
//! | [`Modifier::only`] | `seq (in p assert-nonempty, renaming p ., renaming . p)` |
//! | [`Modifier::except`] | `in p none` |
//! | [`Modifier::renaming`] | `seq (in p assert-nonempty, renaming p p')` |
//! | [`Modifier::alias_as`] | `renaming . name`, the checked builder |
//!
//! The emptiness check is its own constructor so each derived builder places
//! exactly one, at the path an author wants named: folding it into the
//! relocation would make `only p` on an empty subtree report the root as well
//! as `p`. The split runs the other way too: [`Modifier::relocation`] is the
//! unchecked core `renaming`, [`Modifier::renaming`] the checked builder the
//! language means by `renaming p p'`.
//!
//! # Three semantic decisions
//!
//! - **Operations are subtree-grained.** `only nat` keeps every binding under
//!   `nat`, not one binding named `nat`.
//! - **Renaming drops its target.** Whatever was under `p'` is discarded, so a
//!   client patching an interface need not fear what a newer version added
//!   under the target; a wrongly dropped binding fails later at resolution,
//!   where a silently kept one would change meaning.
//! - **Union is pointwise, and a conflict is an event.** With `a.x` and `b.a.y`
//!   bound, `union (all, renaming b .)` yields `a.x`, `a.y` and `b.a.y`, where
//!   a module-level open would shadow `a.x` away.
//!
//! # One arena, built only by the builders
//!
//! A modifier is its constructors in one [`Vec`], every operand an index into
//! it, laid out in post-order with the root last. The builders are the only
//! way to make one, and each appends in post-order, so a modifier has one
//! layout and the derived equality is structural. The interpreter is an
//! explicit instruction stack over one current namespace: apply a
//! constructor, regraft a finished `in` subtree, fold a finished `union`
//! branch — the continuations of the recursive reading.

use alloc::vec::Vec;
use core::mem;
use core::slice;

use anodized::spec;

use crate::namespace::event::EventRejection;
use crate::namespace::event::NamespaceEventHandler;
use crate::namespace::path::NamePath;
use crate::namespace::path::Segment;
use crate::namespace::trie::Emptiness;
use crate::namespace::trie::Trie;

/// A constructor's position in its modifier's arena.
///
/// # Specification
/// - requires: the owning modifier arena accompanies the position.
/// - ensures: the value identifies a constructor only in that arena.
/// - provides: non-recursive operand references.
/// - executable: none — an index alone holds neither its arena nor its extent.
///
/// # Adequacy
/// - hypothesis: L3 — nested composition preserves its meaning after operand
///   relocation; the bounds are checked when the interpreter enters.
/// - witness: `namespace::namespace::a_nested_modifier_survives_a_round_trip`
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct ConstructorId(usize);

impl ConstructorId
{
    /// This position moved `offset` places along.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: adds the offset to the position, saturating at the index
    ///   ceiling.
    /// - provides: operand relocation when arenas are concatenated.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — composed modifiers preserve their inner behavior
    ///   after relocation; the fixture covers representable arena positions,
    ///   not exhaustion.
    /// - witness: `namespace::namespace::a_nested_modifier_survives_a_round_trip`
    #[spec(
        ensures: |ret| ret.0 == self.0.saturating_add(offset.0),
    )]
    const fn shifted(
        self,
        offset: Offset,
    ) -> Self
    {
        Self(self.0.saturating_add(offset.0))
    }
}

/// How far a modifier's constructors move when it is appended to another's.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct Offset(usize);

/// One core constructor, its operands addressed in the modifier's arena.
///
/// # Specification
/// - requires: the owning post-order arena accompanies the constructor.
/// - ensures: operands refer to earlier constructors in that arena; paths and
///   labels retain the operands of the corresponding core form.
/// - provides: the six-constructor core of the modifier language.
/// - executable: none — a constructor holds neither its owning arena nor its
///   own position; builder and interpreter predicates check those boundaries.
///
/// # Adequacy
/// - hypothesis: L3 — every constructor has a namespace effect or event
///   witness; composition fixes the finite order of its operands.
/// - witness: `namespace::namespace::each_union_branch_runs_on_the_original_namespace`
/// - witness: `namespace::namespace::in_runs_the_inner_modifier_on_one_subtree`
/// - witness: `namespace::namespace::a_hook_can_replace_the_namespace`
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
enum Constructor<Label>
{
    /// `assert-nonempty`.
    AssertNonEmpty,
    /// `in p m`.
    In
    {
        /// The subtree the inner modifier runs on.
        path: NamePath,
        /// The inner modifier's root.
        inner: ConstructorId,
    },
    /// `renaming p p'`, unchecked.
    Relocation
    {
        /// The subtree to move.
        source: NamePath,
        /// Where it lands.
        target: NamePath,
    },
    /// `seq (…)`, its members' roots in order.
    Seq(Vec<ConstructorId>),
    /// `union (…)`, its branches' roots in order.
    Union(Vec<ConstructorId>),
    /// `hook h`.
    Hook(Label),
}

impl<Label> Constructor<Label>
{
    /// This constructor with every operand moved `offset` places along.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: preserves constructor kind, paths and labels while shifting
    ///   every operand position by the offset.
    /// - provides: arena relocation without interpreting a constructor.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — composition preserves the behavior of nested sequence
    ///   and union operands; scalar shift predicates and endpoint checks
    ///   constrain relocation without copying operand vectors.
    /// - witness: `namespace::namespace::a_nested_modifier_survives_a_round_trip`
    /// - witness: `namespace::namespace::each_union_branch_runs_on_the_original_namespace`
    #[spec(
        captures: before = (core::mem::discriminant(&self), match self {
            | Self::In { inner, .. } => Some((1_usize, Some(inner), Some(inner))),
            | Self::Seq(ref members) | Self::Union(ref members) => Some((
                members.len(),
                members.first().copied(),
                members.last().copied(),
            )),
            | Self::AssertNonEmpty | Self::Relocation { .. } | Self::Hook(_) => None,
        }),
        ensures: |ret| {
            core::mem::discriminant(&ret) == before.0
                && match (&ret, before.1) {
                    | (&Self::In { inner, .. }, Some((1, Some(first), Some(last)))) => {
                        first == last && inner == first.shifted(offset)
                    },
                    | (
                        &Self::Seq(ref members) | &Self::Union(ref members),
                        Some((count, first, last)),
                    ) => {
                        members.len() == count
                            && members.first().copied()
                                == first.map(|member| member.shifted(offset))
                            && members.last().copied() == last.map(|member| member.shifted(offset))
                    },
                    | (_, None) => true,
                    | _ => false,
                }
        },
    )]
    fn shifted(
        self,
        offset: Offset,
    ) -> Self
    {
        match self {
            | Self::In { path, inner } => Self::In {
                path,
                inner: inner.shifted(offset),
            },
            | Self::Seq(members) => Self::Seq(
                members
                    .into_iter()
                    .map(|member| member.shifted(offset))
                    .collect(),
            ),
            | Self::Union(branches) => Self::Union(
                branches
                    .into_iter()
                    .map(|branch| branch.shifted(offset))
                    .collect(),
            ),
            | leaf @ (Self::AssertNonEmpty | Self::Relocation { .. } | Self::Hook(_)) => leaf,
        }
    }
}

/// A term of the name-modifier language.
///
/// Made only by the builders below, each of which expands to the six core
/// constructors, so one interpreter covers the whole language.
///
/// # Specification
/// - requires: construction passes through the builders.
/// - ensures: the arena is nonempty, its root is last, and every operand refers
///   to an earlier constructor.
/// - provides: one finite post-order term interpreted without recursion.
/// - executable: none — this build's specification facade does not expose the
///   type-item runtime; builder predicates and the interpreter entry predicate
///   check the arena.
///
/// # Adequacy
/// - hypothesis: L3 — nested compositions agree with their direct reading; L2 —
///   a fixed deep modifier is constructed and run iteratively.
/// - witness: `namespace::namespace::a_nested_modifier_survives_a_round_trip`
/// - witness: `namespace::namespace::every_namespace_walk_is_iterative`
#[repr(transparent)]
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Modifier<Label>
{
    /// The constructors in post-order: each operand before the constructor
    /// that uses it, the root last.
    constructors: Vec<Constructor<Label>>,
}

impl<Label> Modifier<Label>
{
    /// The modifier of the one constructor `constructor`, which has no
    /// operands.
    ///
    /// # Specification
    /// - requires: the constructor has no operands.
    /// - ensures: one constructor of the supplied kind forms the whole
    ///   modifier.
    /// - provides: the base case for modifier construction.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — identity, emptiness checks, relocation and hooks
    ///   retain their distinct effects on the namespace and handler.
    /// - witness: `namespace::namespace::the_identity_checks_nothing_on_an_empty_namespace`
    /// - witness: `namespace::namespace::the_core_relocation_performs_no_emptiness_check`
    /// - witness: `namespace::namespace::a_hook_can_replace_the_namespace`
    #[spec(
        requires: match constructor {
            | Constructor::In { .. } => false,
            | Constructor::Seq(ref members) | Constructor::Union(ref members) => members.is_empty(),
            | Constructor::AssertNonEmpty
            | Constructor::Relocation { .. }
            | Constructor::Hook(_) => true,
        },
        captures: before = core::mem::discriminant(&constructor),
        ensures: |ret| {
            ret.constructors.len() == 1
                && ret
                    .constructors
                    .first()
                    .is_some_and(|constructor| core::mem::discriminant(constructor) == before)
        },
    )]
    fn leaf(constructor: Constructor<Label>) -> Self
    {
        Self {
            constructors: Vec::from([constructor]),
        }
    }

    /// The modifier whose root is `wrap` of the roots of `operands`, each
    /// appended in order.
    ///
    /// # Specification
    /// - requires: each operand has a root; wrap embeds their roots as a
    ///   sequence or union, without inventing operand references.
    /// - ensures: the operands' constructors in order, each relocated by the
    ///   constructors before it, then the root over their roots; post-order is
    ///   kept.
    /// - provides: `seq` and `union`.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — empty sequences and unions have different identities,
    ///   while nested composition preserves operand order and source isolation.
    /// - witness: `namespace::namespace::the_empty_sequence_is_the_identity`
    /// - witness: `namespace::namespace::the_empty_union_is_the_empty_namespace`
    /// - witness: `namespace::namespace::each_union_branch_runs_on_the_original_namespace`
    /// - witness: `namespace::namespace::a_nested_modifier_survives_a_round_trip`
    #[spec(
        requires: operands
            .iter()
            .all(|operand| !operand.constructors.is_empty()),
        captures: before = (
            operands.len(),
            operands.iter().fold(0_usize, |count, operand| {
                count.saturating_add(operand.constructors.len())
            }),
        ),
        ensures: |ret| {
            ret.constructors.len() == before.1.saturating_add(1)
                && ret.constructors.last().is_some_and(|root| match *root {
                    | Constructor::Seq(ref members) | Constructor::Union(ref members) => {
                        members.len() == before.0
                            && members.iter().all(|member| member.0 < before.1)
                            && members
                                .iter()
                                .zip(members.iter().skip(1))
                                .all(|(left, right)| left.0 < right.0)
                    },
                    | Constructor::AssertNonEmpty
                    | Constructor::In { .. }
                    | Constructor::Relocation { .. }
                    | Constructor::Hook(_) => false,
                })
        },
    )]
    fn composite(
        operands: Vec<Self>,
        wrap: fn(Vec<ConstructorId>) -> Constructor<Label>,
    ) -> Self
    {
        let mut constructors = Vec::new();
        let mut roots = Vec::with_capacity(operands.len());
        for operand in operands {
            let offset = Offset(constructors.len());
            constructors.extend(
                operand
                    .constructors
                    .into_iter()
                    .map(|constructor| constructor.shifted(offset)),
            );
            roots.push(ConstructorId(constructors.len().saturating_sub(1_usize)));
        }
        constructors.push(wrap(roots));
        Self { constructors }
    }

    /// `all`: keep everything, performing not-found when the namespace is
    /// empty; the core `assert-nonempty`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn all() -> Self
    {
        Self::leaf(Constructor::AssertNonEmpty)
    }

    /// `id`: keep everything, checking nothing; `seq ()`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn id() -> Self
    {
        Self::leaf(Constructor::Seq(Vec::new()))
    }

    /// `none`: drop everything, performing not-found when the namespace was
    /// already empty.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: checks nonemptiness before producing the empty namespace.
    /// - provides: a checked drop through the core constructors.
    /// - fails: never while building; interpretation may be refused by its
    ///   handler.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — dropping an empty namespace performs not-found,
    ///   whereas identity does not; excluding an absent subtree reaches the
    ///   same check.
    /// - witness: `namespace::namespace::except_on_an_absent_subtree_performs_not_found`
    /// - witness: `namespace::namespace::the_identity_checks_nothing_on_an_empty_namespace`
    #[spec(
        ensures: |ret| {
            ret.constructors.len() == 3
                && matches!(ret.constructors.first(), Some(Constructor::AssertNonEmpty))
                && matches!(ret.constructors.get(1), Some(Constructor::Union(branches)) if branches.is_empty())
                && matches!(ret.constructors.last(), Some(Constructor::Seq(members)) if members.iter().map(|member| member.0).eq([0_usize, 1_usize]))
        },
    )]
    #[inline]
    #[must_use]
    pub fn none() -> Self
    {
        Self::seq(Vec::from([Self::all(), Self::union(Vec::new())]))
    }

    /// `only p`: keep the subtree at `path` and drop everything else,
    /// performing not-found at `path` when that subtree is empty.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: checks the selected subtree, moves it to the root, then
    ///   restores its prefix without the other bindings.
    /// - provides: checked subtree selection.
    /// - fails: never while building; interpretation may be refused by its
    ///   handler.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — selecting an existing subtree drops its siblings, and
    ///   selecting an absent subtree reports the written path.
    /// - witness: `namespace::namespace::only_keeps_the_named_subtree_and_drops_the_rest`
    /// - witness: `namespace::namespace::a_selection_that_matched_nothing_performs_not_found`
    #[spec(
        ensures: |ret| {
            ret.constructors.len() == 5
                && matches!(ret.constructors.first(), Some(Constructor::AssertNonEmpty))
                && match (
                    ret.constructors.get(1),
                    ret.constructors.get(2),
                    ret.constructors.get(3),
                    ret.constructors.last(),
                ) {
                    | (
                        Some(&Constructor::In { ref path, inner }),
                        Some(&Constructor::Relocation {
                            ref source,
                            ref target,
                        }),
                        Some(&Constructor::Relocation {
                            source: ref root,
                            target: ref restored,
                        }),
                        Some(&Constructor::Seq(ref members)),
                    ) => {
                        inner.0 == 0
                            && path == source
                            && target.segments().is_empty()
                            && root.segments().is_empty()
                            && restored == path
                            && members
                                .iter()
                                .map(|member| member.0)
                                .eq([1_usize, 2_usize, 3_usize])
                    },
                    | _ => false,
                }
        },
    )]
    #[inline]
    #[must_use]
    pub fn only(path: NamePath) -> Self
    {
        Self::seq(Vec::from([
            Self::in_subtree(path.clone(), Self::all()),
            Self::relocation(path.clone(), NamePath::root()),
            Self::relocation(NamePath::root(), path),
        ]))
    }

    /// `except p`: drop the subtree at `path`, performing not-found at `path`
    /// when that subtree was already empty.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn except(path: NamePath) -> Self
    {
        Self::in_subtree(path, Self::none())
    }

    /// `renaming p p'`: move the subtree at `source` to `target`, performing
    /// not-found at `source` when that subtree is empty; the checked builder.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: checks the source before relocating its subtree to the
    ///   target.
    /// - provides: checked renaming rather than unchecked relocation.
    /// - fails: never while building; interpretation may be refused by its
    ///   handler.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an absent source is reported before a move; moving to
    ///   the root unqualifies, and an occupied target is replaced.
    /// - witness: `namespace::namespace::the_checked_renaming_builder_performs_not_found_on_an_absent_source`
    /// - witness: `namespace::namespace::renaming_to_the_root_unqualifies`
    /// - witness: `namespace::namespace::renaming_drops_whatever_was_at_the_target`
    #[spec(
        ensures: |ret| {
            ret.constructors.len() == 4
                && matches!(ret.constructors.first(), Some(Constructor::AssertNonEmpty))
                && match (
                    ret.constructors.get(1),
                    ret.constructors.get(2),
                    ret.constructors.last(),
                ) {
                    | (
                        Some(&Constructor::In { ref path, inner }),
                        Some(&Constructor::Relocation { ref source, .. }),
                        Some(&Constructor::Seq(ref members)),
                    ) => {
                        inner.0 == 0
                            && path == source
                            && members.iter().map(|member| member.0).eq([1_usize, 2_usize])
                    },
                    | _ => false,
                }
        },
    )]
    #[inline]
    #[must_use]
    pub fn renaming(
        source: NamePath,
        target: NamePath,
    ) -> Self
    {
        Self::seq(Vec::from([
            Self::in_subtree(source.clone(), Self::all()),
            Self::relocation(source, target),
        ]))
    }

    /// The core `renaming p p'`: move the subtree at `source` to `target`,
    /// dropping whatever was there, with no emptiness check.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn relocation(
        source: NamePath,
        target: NamePath,
    ) -> Self
    {
        Self::leaf(Constructor::Relocation { source, target })
    }

    /// `in p m`: run `inner` on the subtree at `path`.
    ///
    /// # Specification
    /// - requires: the inner modifier has a root.
    /// - ensures: appends an in-subtree constructor pointing to that root,
    ///   preserving post-order.
    /// - provides: nested interpretation with the accumulated event prefix.
    /// - fails: never while building.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — one subtree changes without its siblings; nested
    ///   events retain their full prefix. L2 — deep nesting is constructed
    ///   iteratively.
    /// - witness: `namespace::namespace::in_runs_the_inner_modifier_on_one_subtree`
    /// - witness: `namespace::namespace::a_nested_event_reports_the_accumulated_prefix`
    /// - witness: `namespace::namespace::a_nested_shadow_reports_the_accumulated_prefix`
    /// - witness: `namespace::namespace::a_nested_hook_reports_the_accumulated_prefix`
    /// - witness: `namespace::namespace::every_namespace_walk_is_iterative`
    #[spec(
        requires: !inner.constructors.is_empty(),
        captures: before = inner.constructors.len(),
        ensures: |ret| {
            ret.constructors.len() == before.saturating_add(1)
                && matches!(ret.constructors.last(), Some(Constructor::In { inner, .. }) if inner.0 == before.saturating_sub(1))
        },
    )]
    #[inline]
    #[must_use]
    pub fn in_subtree(
        path: NamePath,
        inner: Self,
    ) -> Self
    {
        let mut constructors = inner.constructors;
        let root = ConstructorId(constructors.len().saturating_sub(1_usize));
        constructors.push(Constructor::In { path, inner: root });
        Self { constructors }
    }

    /// `seq (…)`: run `members` in order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn seq(members: Vec<Self>) -> Self
    {
        Self::composite(members, Constructor::Seq)
    }

    /// `union (…)`: run each of `branches` on the same input and union the
    /// results left to right.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn union(branches: Vec<Self>) -> Self
    {
        Self::composite(branches, Constructor::Union)
    }

    /// `hook h`: the extension point labelled `label`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn hook(label: Label) -> Self
    {
        Self::leaf(Constructor::Hook(label))
    }

    /// The modifier `import "URI" as name ;` means: `renaming . name`, checked.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the alias qualifies a two-level namespace and retains
    ///   the checked renaming refusal on an empty import.
    /// - witness: `namespace::namespace::as_name_qualifies_every_imported_path`
    /// - witness: `namespace::namespace::as_name_on_an_empty_import_performs_not_found`
    #[inline]
    #[must_use]
    pub fn alias_as(alias: Segment) -> Self
    {
        Self::renaming(NamePath::root(), NamePath::from(Vec::from([alias])))
    }

    /// Run this modifier on `subject`, settling every event through
    /// `handler`.
    ///
    /// # Specification
    /// - requires: a nonempty post-order constructor arena, and a handler
    ///   interpreting the hook vocabulary with which it is labelled.
    /// - ensures: subtree-grained selection, target-dropping relocation and
    ///   pointwise union; every not-found, shadow and hook event reaches
    ///   `handler` at the accumulated prefix of the point that performed it, so
    ///   an event inside `in p m` reports a path under `p`.
    /// - provides: the whole language's meaning through one interpreter; the
    ///   derived builders add no interpretation.
    /// - fails: propagates a handler's rejection unchanged, abandoning the run
    ///   where the event was performed.
    /// - panics: none.
    /// - intension: no recursion — the instruction stack is as high as the
    ///   modifier is deep. A suspended `union` keeps a copy of its input and
    ///   the union so far, and a suspended `in` keeps the bindings outside its
    ///   subtree, so nested unions cost depth times namespace size at worst.
    ///
    /// # Errors
    /// The rejection a handler produced for a not-found, shadow or hook event.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the derived builders against the design's worked
    ///   examples as an external oracle: selective import, qualified import,
    ///   the deep patch, re-export control, typo resistance. L3 — the residue
    ///   per constructor: the empty namespace for `assert-nonempty`; the
    ///   checked builder against the core relocation on an absent source; the
    ///   root as source and as target; the empty `seq` and `union`; a `union`
    ///   whose first branch is not the identity; a nested `in` whose not-found,
    ///   shadow and hook each carry the outer prefix; `except` on an absent
    ///   subtree, which performs not-found through `none`, and `id` on the
    ///   empty namespace, which performs nothing. L2 — a composed modifier
    ///   agrees with its inner modifier run by hand, and nesting one hundred
    ///   thousand deep runs inside a small stack.
    /// - witness: `namespace::namespace::only_keeps_the_named_subtree_and_drops_the_rest`
    /// - witness: `namespace::namespace::except_drops_the_named_subtree`
    /// - witness: `namespace::namespace::except_on_an_absent_subtree_performs_not_found`
    /// - witness: `namespace::namespace::the_identity_checks_nothing_on_an_empty_namespace`
    /// - witness: `namespace::namespace::in_runs_the_inner_modifier_on_one_subtree`
    /// - witness: `namespace::namespace::renaming_to_the_root_unqualifies`
    /// - witness: `namespace::namespace::renaming_drops_whatever_was_at_the_target`
    /// - witness: `namespace::namespace::the_checked_renaming_builder_performs_not_found_on_an_absent_source`
    /// - witness: `namespace::namespace::the_core_relocation_performs_no_emptiness_check`
    /// - witness: `namespace::namespace::a_rejecting_handler_refuses_a_missing_renaming_source`
    /// - witness: `namespace::namespace::a_deep_patch_merges_instead_of_capturing`
    /// - witness: `namespace::namespace::each_union_branch_runs_on_the_original_namespace`
    /// - witness: `namespace::namespace::the_empty_sequence_is_the_identity`
    /// - witness: `namespace::namespace::the_empty_union_is_the_empty_namespace`
    /// - witness: `namespace::namespace::a_selection_that_matched_nothing_performs_not_found`
    /// - witness: `namespace::namespace::a_nested_event_reports_the_accumulated_prefix`
    /// - witness: `namespace::namespace::a_nested_shadow_reports_the_accumulated_prefix`
    /// - witness: `namespace::namespace::a_nested_hook_reports_the_accumulated_prefix`
    /// - witness: `namespace::namespace::a_hook_can_replace_the_namespace`
    /// - witness: `namespace::namespace::a_nested_modifier_survives_a_round_trip`
    /// - witness: `namespace::namespace::every_namespace_walk_is_iterative`
    #[spec(
        requires: !self.constructors.is_empty()
            && self.constructors.iter().enumerate().all(
                |(position, constructor)| match *constructor {
                    | Constructor::In { inner, .. } => inner.0 < position,
                    | Constructor::Seq(ref members) | Constructor::Union(ref members) => {
                        members.iter().all(|member| member.0 < position)
                    },
                    | Constructor::AssertNonEmpty
                    | Constructor::Relocation { .. }
                    | Constructor::Hook(_) => true,
                },
            ),
    )]
    #[inline]
    pub fn apply<Data, Tag, Handler>(
        &self,
        subject: Trie<Data, Tag>,
        handler: &mut Handler,
    ) -> Result<Trie<Data, Tag>, EventRejection>
    where
        Data: Clone,
        Tag: Clone,
        Handler: NamespaceEventHandler<Data, Tag, Label = Label>,
    {
        let mut current = subject;
        let mut stack: Vec<Instruction<'_, Data, Tag>> = Vec::new();
        stack.push(Instruction::Apply {
            prefix: NamePath::root(),
            constructor: ConstructorId(self.constructors.len().saturating_sub(1_usize)),
        });
        while let Some(instruction) = stack.pop() {
            match instruction {
                | Instruction::Apply {
                    prefix,
                    constructor,
                } => {
                    self.step(&mut current, &mut stack, handler, prefix, constructor)?;
                },
                | Instruction::Regraft {
                    prefix,
                    mut outside,
                } => {
                    let inner = mem::take(&mut current);
                    outside.graft_subtree(&prefix, inner);
                    current = outside;
                },
                | Instruction::UnionFold {
                    prefix,
                    input,
                    mut accumulated,
                    mut remaining,
                } => {
                    let branch = mem::take(&mut current);
                    accumulated.union_resolving(branch, &mut |path, collision| {
                        let path = prefix.extended(path);
                        handler.shadow(&path, collision)
                    })?;
                    match remaining.next() {
                        | Some(&next) => {
                            current = input.clone();
                            stack.push(Instruction::UnionFold {
                                prefix: prefix.clone(),
                                input,
                                accumulated,
                                remaining,
                            });
                            stack.push(Instruction::Apply {
                                prefix,
                                constructor: next,
                            });
                        },
                        | None => current = accumulated,
                    }
                },
            }
        }
        Ok(current)
    }

    /// Run the constructor at `constructor` on `current`, pushing the
    /// continuations it needs.
    ///
    /// # Specification
    /// - requires: `constructor` is a position of this modifier.
    /// - ensures: the constructor's meaning, its nested cases pushed as
    ///   instructions rather than recursed into; events report at `prefix`.
    /// - provides: the step function of [`Self::apply`].
    /// - fails: propagates the handler's rejection unchanged.
    /// - panics: none.
    ///
    /// # Errors
    /// The rejection the handler produced for the event this step performed.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the constructor fixtures cover empty and occupied
    ///   subjects, nested full-path events, target replacement, branch
    ///   isolation and hook replacement; rejecting policies cover the two
    ///   immediate event kinds. L2 — nested interpretation uses the explicit
    ///   stack.
    /// - witness: `namespace::namespace::the_identity_checks_nothing_on_an_empty_namespace`
    /// - witness: `namespace::namespace::in_runs_the_inner_modifier_on_one_subtree`
    /// - witness: `namespace::namespace::renaming_drops_whatever_was_at_the_target`
    /// - witness: `namespace::namespace::each_union_branch_runs_on_the_original_namespace`
    /// - witness: `namespace::namespace::a_hook_can_replace_the_namespace`
    /// - witness: `namespace::namespace::a_rejecting_handler_refuses_a_missing_selection`
    /// - witness: `namespace::namespace::a_rejecting_handler_refuses_a_hook`
    /// - witness: `namespace::namespace::every_namespace_walk_is_iterative`
    #[spec(
        requires: constructor.0 < self.constructors.len(),
        captures: before = (stack.len(), usize::from(current.binding_count())),
        ensures: |ret| {
            match self.constructors.get(constructor.0) {
            | Some(&Constructor::AssertNonEmpty) => {
                stack.len() == before.0 && usize::from(current.binding_count()) == before.1
            },
            | Some(&Constructor::In { inner, .. }) => {
                ret.is_ok()
                    && stack.len() == before.0.saturating_add(2)
                    && usize::from(current.binding_count()) <= before.1
                    && matches!(stack.get(before.0), Some(Instruction::Regraft { outside, .. })
                        if usize::from(outside.binding_count()) == before.1.saturating_sub(usize::from(current.binding_count())))
                    && matches!(stack.last(), Some(Instruction::Apply { constructor, .. }) if *constructor == inner)
            },
            | Some(&Constructor::Relocation { .. }) => {
                ret.is_ok() && stack.len() == before.0 && usize::from(current.binding_count()) <= before.1
            },
            | Some(&Constructor::Seq(ref members)) => {
                ret.is_ok()
                    && stack.len() == before.0.saturating_add(members.len())
                    && usize::from(current.binding_count()) == before.1
                    && stack.get(before.0..).is_some_and(|added| {
                        added.iter().zip(members.iter().rev()).all(|(instruction, member)| {
                            matches!(instruction, Instruction::Apply { constructor, .. } if constructor == member)
                        })
                    })
            },
            | Some(&Constructor::Union(ref branches)) => {
                ret.is_ok() && if branches.is_empty() {
                    stack.len() == before.0 && usize::from(current.binding_count()) == 0
                } else {
                    stack.len() == before.0.saturating_add(2)
                        && usize::from(current.binding_count()) == before.1
                        && matches!(stack.last(), Some(Instruction::Apply { constructor, .. }) if branches.first() == Some(constructor))
                }
            },
            | Some(&Constructor::Hook(_)) => {
                stack.len() == before.0 && (ret.is_ok() || usize::from(current.binding_count()) == 0)
            },
            | None => false,
        }
        },
    )]
    fn step<'modifier, Data, Tag, Handler>(
        &'modifier self,
        current: &mut Trie<Data, Tag>,
        stack: &mut Vec<Instruction<'modifier, Data, Tag>>,
        handler: &mut Handler,
        prefix: NamePath,
        constructor: ConstructorId,
    ) -> Result<(), EventRejection>
    where
        Data: Clone,
        Tag: Clone,
        Handler: NamespaceEventHandler<Data, Tag, Label = Label>,
    {
        let Some(constructor) = self.constructors.get(constructor.0)
        else {
            return Ok(());
        };
        match *constructor {
            | Constructor::AssertNonEmpty => {
                if current.emptiness() == Emptiness::EMPTY {
                    handler.not_found(&prefix)?;
                }
            },
            | Constructor::In {
                path: ref subtree,
                inner,
            } => {
                let detached = current.detach_subtree(subtree);
                let outside = mem::replace(current, detached);
                stack.push(Instruction::Regraft {
                    prefix: subtree.clone(),
                    outside,
                });
                stack.push(Instruction::Apply {
                    prefix: prefix.extended(subtree),
                    constructor: inner,
                });
            },
            | Constructor::Relocation {
                ref source,
                ref target,
            } => {
                let moved = current.detach_subtree(source);
                current.graft_subtree(target, moved);
            },
            | Constructor::Seq(ref members) => {
                for &member in members.iter().rev() {
                    stack.push(Instruction::Apply {
                        prefix: prefix.clone(),
                        constructor: member,
                    });
                }
            },
            | Constructor::Union(ref branches) => {
                let mut remaining = branches.iter();
                match remaining.next() {
                    | None => *current = Trie::empty(),
                    | Some(&first) => {
                        stack.push(Instruction::UnionFold {
                            prefix: prefix.clone(),
                            input: current.clone(),
                            accumulated: Trie::empty(),
                            remaining,
                        });
                        stack.push(Instruction::Apply {
                            prefix,
                            constructor: first,
                        });
                    },
                }
            },
            | Constructor::Hook(ref label) => {
                let subject = mem::take(current);
                let replaced = handler.hook(&prefix, label, subject)?;
                *current = replaced;
            },
        }
        Ok(())
    }
}

/// One step of the interpreter's explicit stack: what is left to run, what to
/// do with a finished `in` subtree, and what to do with a finished `union`
/// branch.
///
/// # Specification
/// - requires: the owning modifier and active interpreter state accompany the
///   continuation.
/// - ensures: apply frames preserve accumulated prefixes; regraft frames retain
///   outside bindings; union frames retain original input and the completed
///   branches.
/// - provides: suspended work without recursive calls.
/// - executable: none — a frame does not hold the active current namespace or
///   the owning constructor arena; step predicates check frontier transitions.
///
/// # Adequacy
/// - hypothesis: L3 — nested events retain their prefixes and each union branch
///   reads the original input; L2 — a fixed deep run uses this frontier.
/// - witness: `namespace::namespace::a_nested_event_reports_the_accumulated_prefix`
/// - witness: `namespace::namespace::a_nested_shadow_reports_the_accumulated_prefix`
/// - witness: `namespace::namespace::a_nested_hook_reports_the_accumulated_prefix`
/// - witness: `namespace::namespace::each_union_branch_runs_on_the_original_namespace`
/// - witness: `namespace::namespace::every_namespace_walk_is_iterative`
enum Instruction<'modifier, Data, Tag>
{
    /// Run `constructor` on the current namespace, reporting at `prefix`.
    Apply
    {
        /// The accumulated prefix events report at.
        prefix: NamePath,
        /// The constructor still to run.
        constructor: ConstructorId,
    },
    /// An `in` finished: put the current namespace back at `prefix` inside
    /// `outside`.
    Regraft
    {
        /// Where the inner namespace came from, relative to `outside`.
        prefix: NamePath,
        /// The bindings outside the subtree.
        outside: Trie<Data, Tag>,
    },
    /// A `union` branch finished: fold the current namespace into
    /// `accumulated`, then start the next branch on `input` or finish.
    UnionFold
    {
        /// The accumulated prefix events report at.
        prefix: NamePath,
        /// The namespace every branch runs on.
        input: Trie<Data, Tag>,
        /// The union of the branches finished so far.
        accumulated: Trie<Data, Tag>,
        /// The branches not yet started.
        remaining: slice::Iter<'modifier, ConstructorId>,
    },
}
