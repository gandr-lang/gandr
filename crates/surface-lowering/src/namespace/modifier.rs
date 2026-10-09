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

use crate::namespace::event::EventRejection;
use crate::namespace::event::NamespaceEventHandler;
use crate::namespace::path::NamePath;
use crate::namespace::path::Segment;
use crate::namespace::trie::Emptiness;
use crate::namespace::trie::Trie;

/// A constructor's position in its modifier's arena.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct ConstructorId(usize);

impl ConstructorId
{
    /// This position moved `offset` places along.
    ///
    /// # Specification
    /// trivial.
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
    /// trivial.
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
    /// trivial.
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
    /// - requires: nothing.
    /// - ensures: the operands' constructors in order, each relocated by the
    ///   constructors before it, then the root over their roots; post-order is
    ///   kept.
    /// - provides: `seq` and `union`.
    /// - fails: never.
    /// - panics: none.
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
    /// trivial.
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
    /// trivial.
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
    /// trivial.
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
    /// trivial.
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
    /// - requires: nothing.
    /// - ensures: equal to [`Self::renaming`] from the root to the one-segment
    ///   path `alias`.
    /// - provides: the import desugaring the lowering applies to an import's
    ///   root binding.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L0 — the equality with the general builder is asserted
    ///   exactly, so a change to either side, the unchecked core included,
    ///   separates them; L3 — the qualifying behaviour on a two-level namespace
    ///   and the inherited emptiness check on the empty one.
    /// - witness: `namespace::namespace::as_name_is_renaming_to_the_alias`
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
    /// - requires: `handler` interprets the hook vocabulary this modifier is
    ///   labelled with.
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
