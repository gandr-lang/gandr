//! The scope: lexical scoping as two namespaces.
//!
//! A [`Scope`] carries two namespaces: **visible**, what resolves here, and
//! **export**, what an importer of this unit sees. Keeping them apart makes "in
//! scope here" and "re-exported" independent, and each operation is known by
//! which of the two it touches:
//!
//! | operation | visible | export |
//! | --- | --- | --- |
//! | [`Scope::include_subtree`] | yes | yes |
//! | [`Scope::import_subtree`] | yes | no |
//! | [`Scope::modify_visible`] | yes | no |
//! | [`Scope::modify_export`] | no | yes |
//! | [`Scope::export_visible`] | no | yes |
//! | [`Scope::end_section`] | yes | yes |
//!
//! # Sections
//!
//! A section is a child scope. [`Scope::begin_section`] opens one that
//! inherits the parent's visible namespace and starts with an empty export;
//! [`Scope::end_section`] runs a modifier over the child's export, prefixes the
//! result and includes it into the parent. A section's imports touch only its
//! visible namespace, which is discarded at close, so they evaporate; only
//! what it exported survives, under its prefix.

use alloc::vec::Vec;
use core::error::Error;
use core::fmt;
use core::mem;

use anodized::spec;
use quenchant_shape::shape::Maybe;

use crate::namespace::event::EventRejection;
use crate::namespace::event::NamespaceEventHandler;
use crate::namespace::modifier::Modifier;
use crate::namespace::path::NamePath;
use crate::namespace::trie::Binding;
use crate::namespace::trie::Trie;
use crate::namespace::trie::binding;

/// A scope operation's failure.
///
/// # Specification
/// - requires: the producer reports the failed scope operation.
/// - ensures: a refused event retains its typed rejection; closing with no
///   section is distinguished from policy refusal.
/// - provides: structural and policy failures without erasing either cause.
/// - executable: none — a failure value holds neither the prior section stack
///   nor the handler run that establishes its correspondence.
///
/// # Adequacy
/// - hypothesis: L3 — closing outside a section and refusing a collision
///   produce distinct variants while the retained namespace is observed.
/// - witness: `namespace::namespace::closing_without_an_open_section_fails`
/// - witness: `namespace::namespace::a_refused_multi_entry_import_leaves_the_visible_namespace_as_it_was`
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ScopeError
{
    /// A handler refused one of the three namespace events.
    Rejected(EventRejection),
    /// A section was closed while none was open.
    NoOpenSection,
}

impl From<EventRejection> for ScopeError
{
    /// The failure carrying `rejection`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(rejection: EventRejection) -> Self
    {
        Self::Rejected(rejection)
    }
}

impl fmt::Display for ScopeError
{
    /// Writes a rejection as the rejection itself, and a structural failure
    /// as its own message.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// The formatter's error.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        match *self {
            | Self::Rejected(ref rejection) => fmt::Display::fmt(rejection, f),
            | Self::NoOpenSection => f.write_str("no open section to close"),
        }
    }
}

impl Error for ScopeError
{
}

/// One scope's pair of namespaces.
#[derive(Clone, Debug, Eq, PartialEq)]
struct Namespaces<Data, Tag>
{
    /// What resolves here.
    visible: Trie<Data, Tag>,
    /// What an importer of this unit sees.
    export: Trie<Data, Tag>,
}

/// A lexical scope: a visible namespace, an export namespace, and the stack of
/// sections enclosing them.
///
/// The current scope is a field rather than the top of a stack, so there is
/// always a current scope by construction.
///
/// # Specification
/// - requires: mutations pass through the scope operations.
/// - ensures: visible and export namespaces remain independent; opening saves
///   the parent and closing consumes exactly the innermost saved parent.
/// - provides: lexical sections with separately controlled exports.
/// - executable: none — this build's specification facade does not expose the
///   type-item runtime; operation predicates check counts and stack
///   transitions.
///
/// # Adequacy
/// - hypothesis: L3 — import and include differ in export visibility; two
///   nested sections restore their parents in stack order, and failed closes
///   consume the section at both modifier and merge boundaries.
/// - witness: `namespace::namespace::import_touches_only_the_visible_namespace`
/// - witness: `namespace::namespace::include_touches_both_namespaces`
/// - witness: `namespace::namespace::nested_sections_close_innermost_first`
/// - witness: `namespace::namespace::a_refused_closing_modifier_restores_the_parent_and_closes_the_section`
/// - witness: `namespace::namespace::a_refused_closing_merge_keeps_its_prefix_and_closes_the_section`
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Scope<Data, Tag>
{
    /// The innermost scope, which every operation acts on.
    current: Namespaces<Data, Tag>,
    /// The enclosing scopes, outermost first; non-empty exactly when a section
    /// is open.
    enclosing: Vec<Namespaces<Data, Tag>>,
}

impl<Data, Tag> Default for Scope<Data, Tag>
{
    /// A scope with both namespaces empty and no section open.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn default() -> Self
    {
        Self::new()
    }
}

impl<Data, Tag> Scope<Data, Tag>
{
    /// A scope with both namespaces empty and no section open.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn new() -> Self
    {
        Self::with_init_visible(Trie::empty())
    }

    /// A scope whose visible namespace starts as `init_visible`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the visible namespace is exactly `init_visible`; the export
    ///   is empty, because a unit does not re-export the builtins it was read
    ///   against.
    /// - provides: the entry point of the outermost scope: builtin tables are
    ///   an initial visible namespace, and a declaration reaching the same path
    ///   is a shadow event under a policy.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — both namespaces asserted exactly over a non-empty
    ///   initial namespace, and a later import over it performing shadow.
    /// - witness: `namespace::namespace::init_visible_seeds_only_the_visible_namespace`
    /// - witness: `namespace::namespace::a_user_binding_over_the_prelude_is_a_shadow_event`
    #[spec(
        captures: before = init_visible.binding_count(),
        ensures: |ret| {
            ret.current.visible.binding_count() == before
                && usize::from(ret.current.export.binding_count()) == 0
                && ret.enclosing.is_empty()
        },
    )]
    #[inline]
    #[must_use]
    pub fn with_init_visible(init_visible: Trie<Data, Tag>) -> Self
    {
        Self {
            current: Namespaces {
                visible: init_visible,
                export: Trie::empty(),
            },
            enclosing: Vec::new(),
        }
    }

    /// What resolves in this scope.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn visible(&self) -> &Trie<Data, Tag>
    {
        &self.current.visible
    }

    /// What an importer of this scope sees.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn export(&self) -> &Trie<Data, Tag>
    {
        &self.current.export
    }

    /// The binding `path` resolves to in the visible namespace.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn resolve(
        &self,
        path: &NamePath,
    ) -> Maybe<&Binding<Data, Tag>, binding::Absent>
    {
        self.current.visible.get(path)
    }

    /// Graft `subtree` at `prefix` in the visible namespace, dropping
    /// whatever was there.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: nothing the visible namespace held at or under `prefix`
    ///   resolves; each binding of `subtree` resolves at its path prefixed by
    ///   `prefix`; the export is unchanged.
    /// - provides: the binding step of a declaration in the outermost scope,
    ///   which displaces a whole subtree once its policy has spoken.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a declaration over a seeded namespace with members,
    ///   the namespace, a former member and an unrelated namespace asserted
    ///   exactly after.
    /// - witness: `recognition::recognition::a_declaration_displaces_the_whole_builtin_subtree`
    #[spec(
        captures: before = (
            usize::from(self.current.visible.binding_count()),
            self.current.export.binding_count(),
            self.enclosing.len(),
            usize::from(subtree.binding_count()),
        ),
        ensures: self.current.export.binding_count() == before.1
            && self.enclosing.len() == before.2
            && usize::from(self.current.visible.binding_count()) >= before.3
            && usize::from(self.current.visible.binding_count())
                <= before.0.saturating_add(before.3),
    )]
    #[inline]
    pub fn graft_visible(
        &mut self,
        prefix: &NamePath,
        subtree: Trie<Data, Tag>,
    )
    {
        self.current.visible.graft_subtree(prefix, subtree);
    }
}

impl<Data, Tag> Scope<Data, Tag>
where
    Data: Clone,
    Tag: Clone,
{
    /// Merge `subtree` under `prefix` into both namespaces.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: each namespace receives `subtree` prefixed by `prefix`,
    ///   merged pointwise, every collision settled by `handler`.
    /// - provides: `include`, which makes a binding usable here and visible to
    ///   importers.
    /// - fails: propagates a rejection from either merge. The visible merge
    ///   runs first, so a rejection there leaves the export untouched; neither
    ///   merge is atomic, so the namespace being merged keeps what it took
    ///   before the rejection.
    /// - panics: none.
    ///
    /// # Errors
    /// [`ScopeError::Rejected`] when `handler` refuses a collision.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — which namespaces are touched, against
    ///   [`Self::import_subtree`] on the same input; the merge order, by a
    ///   rejected collision after a merged sibling, both namespaces asserted
    ///   exactly.
    /// - witness: `namespace::namespace::include_touches_both_namespaces`
    /// - witness: `namespace::namespace::import_touches_only_the_visible_namespace`
    /// - witness: `namespace::namespace::include_merges_the_visible_namespace_before_the_export`
    #[spec(
        captures: before = (
            usize::from(self.current.visible.binding_count()),
            usize::from(self.current.export.binding_count()),
            self.enclosing.len(),
            usize::from(subtree.binding_count()),
        ),
        ensures: |ret| {
            self.enclosing.len() == before.2
                && !matches!(ret, Err(ScopeError::NoOpenSection))
                && usize::from(self.current.visible.binding_count()) >= before.0
                && usize::from(self.current.export.binding_count()) >= before.1
                && usize::from(self.current.visible.binding_count())
                    <= before.0.saturating_add(before.3)
                && usize::from(self.current.export.binding_count())
                    <= before.1.saturating_add(before.3)
                && (ret.is_err()
                    || (usize::from(self.current.visible.binding_count()) >= before.3
                        && usize::from(self.current.export.binding_count()) >= before.3))
        },
    )]
    #[inline]
    pub fn include_subtree<Handler>(
        &mut self,
        prefix: &NamePath,
        subtree: Trie<Data, Tag>,
        handler: &mut Handler,
    ) -> Result<(), ScopeError>
    where
        Handler: NamespaceEventHandler<Data, Tag>,
    {
        let prefixed = subtree.into_prefixed(prefix);
        self.current
            .visible
            .union_resolving(prefixed.clone(), &mut |path, collision| {
                handler.shadow(path, collision)
            })?;
        self.current
            .export
            .union_resolving(prefixed, &mut |path, collision| {
                handler.shadow(path, collision)
            })?;
        Ok(())
    }

    /// Merge `subtree` under `prefix` into the visible namespace only.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the export is unchanged, so an import is not a re-export.
    /// - provides: `import`.
    /// - fails: propagates a rejection, leaving both namespaces as they were.
    /// - panics: none.
    ///
    /// # Errors
    /// [`ScopeError::Rejected`] when `handler` refuses a collision.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — which namespaces are touched, against
    ///   [`Self::include_subtree`]; the prefixing, by an import under a
    ///   non-root prefix; atomicity, by a rejection after a merged sibling.
    /// - witness: `namespace::namespace::import_touches_only_the_visible_namespace`
    /// - witness: `namespace::namespace::an_import_arrives_under_its_prefix`
    /// - witness: `namespace::namespace::a_refused_multi_entry_import_leaves_the_visible_namespace_as_it_was`
    #[spec(
        captures: before = (
            usize::from(self.current.visible.binding_count()),
            self.current.export.binding_count(),
            self.enclosing.len(),
            usize::from(subtree.binding_count()),
        ),
        ensures: |ret| {
            self.current.export.binding_count() == before.1
                && self.enclosing.len() == before.2
                && !matches!(ret, Err(ScopeError::NoOpenSection))
                && if ret.is_err() {
                    usize::from(self.current.visible.binding_count()) == before.0
                }
                else {
                    usize::from(self.current.visible.binding_count()) >= before.0
                        && usize::from(self.current.visible.binding_count()) >= before.3
                        && usize::from(self.current.visible.binding_count())
                            <= before.0.saturating_add(before.3)
                }
        },
    )]
    #[inline]
    pub fn import_subtree<Handler>(
        &mut self,
        prefix: &NamePath,
        subtree: Trie<Data, Tag>,
        handler: &mut Handler,
    ) -> Result<(), ScopeError>
    where
        Handler: NamespaceEventHandler<Data, Tag>,
    {
        let prefixed = subtree.into_prefixed(prefix);
        let mut visible = self.current.visible.clone();
        visible.union_resolving(prefixed, &mut |path, collision| {
            handler.shadow(path, collision)
        })?;
        self.current.visible = visible;
        Ok(())
    }

    /// Replace the visible namespace with `modifier`'s result on it.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the export is unchanged.
    /// - provides: modifying what resolves here.
    /// - fails: propagates a rejection, leaving both namespaces as they were.
    /// - panics: none.
    ///
    /// # Errors
    /// [`ScopeError::Rejected`] when `handler` refuses an event the modifier
    /// performed.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — which namespace is rewritten, against
    ///   [`Self::modify_export`]; that the rewrite lands only on success, by a
    ///   rejected event over a non-empty namespace.
    /// - witness: `namespace::namespace::modifying_visible_leaves_export_alone`
    /// - witness: `namespace::namespace::modifying_export_leaves_visible_alone`
    /// - witness: `namespace::namespace::a_refused_modifier_leaves_the_visible_namespace_as_it_was`
    #[spec(
        captures: before = (
            self.current.visible.binding_count(),
            self.current.export.binding_count(),
            self.enclosing.len(),
        ),
        ensures: |ret| {
            self.current.export.binding_count() == before.1
                && self.enclosing.len() == before.2
                && !matches!(ret, Err(ScopeError::NoOpenSection))
                && (ret.is_ok() || self.current.visible.binding_count() == before.0)
        },
    )]
    #[inline]
    pub fn modify_visible<Handler>(
        &mut self,
        modifier: &Modifier<Handler::Label>,
        handler: &mut Handler,
    ) -> Result<(), ScopeError>
    where
        Handler: NamespaceEventHandler<Data, Tag>,
    {
        let modified = modifier.apply(self.current.visible.clone(), handler)?;
        self.current.visible = modified;
        Ok(())
    }

    /// Replace the export namespace with `modifier`'s result on it.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the visible namespace is unchanged.
    /// - provides: modifying what an importer sees.
    /// - fails: propagates a rejection, leaving both namespaces as they were.
    /// - panics: none.
    ///
    /// # Errors
    /// [`ScopeError::Rejected`] when `handler` refuses an event the modifier
    /// performed.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — which namespace the modifier reads, by a visible
    ///   binding the export lacks; that the rewrite lands only on success.
    /// - witness: `namespace::namespace::modifying_export_leaves_visible_alone`
    /// - witness: `namespace::namespace::a_refused_modifier_leaves_the_export_namespace_as_it_was`
    #[spec(
        captures: before = (
            self.current.visible.binding_count(),
            self.current.export.binding_count(),
            self.enclosing.len(),
        ),
        ensures: |ret| {
            self.current.visible.binding_count() == before.0
                && self.enclosing.len() == before.2
                && !matches!(ret, Err(ScopeError::NoOpenSection))
                && (ret.is_ok() || self.current.export.binding_count() == before.1)
        },
    )]
    #[inline]
    pub fn modify_export<Handler>(
        &mut self,
        modifier: &Modifier<Handler::Label>,
        handler: &mut Handler,
    ) -> Result<(), ScopeError>
    where
        Handler: NamespaceEventHandler<Data, Tag>,
    {
        let modified = modifier.apply(self.current.export.clone(), handler)?;
        self.current.export = modified;
        Ok(())
    }

    /// Copy the visible namespace through `modifier` into the export.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the visible namespace is unchanged; the export receives the
    ///   modifier's result, merged pointwise with what it held.
    /// - provides: re-export control: a unit chooses which of the things it
    ///   sees it passes on.
    /// - fails: propagates a rejection. One from the modifier leaves both
    ///   namespaces as they were; one from the merge leaves the export with
    ///   what it merged before the refused path and what it held there.
    /// - panics: none.
    ///
    /// # Errors
    /// [`ScopeError::Rejected`] when `handler` refuses an event the modifier
    /// or the merge performed.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — which namespace is read, which receives, and that it
    ///   merges, by a selection over bindings the export lacks against a
    ///   non-empty prior export; that the export is undisturbed until the
    ///   modifier succeeds, by a rejected event against the same.
    /// - witness: `namespace::namespace::export_visible_re_exports_a_selection`
    /// - witness: `namespace::namespace::a_refused_re_export_leaves_the_prior_export_as_it_was`
    #[spec(
        captures: before = (
            self.current.visible.binding_count(),
            usize::from(self.current.export.binding_count()),
            self.enclosing.len(),
        ),
        ensures: |ret| {
            self.current.visible.binding_count() == before.0
                && self.enclosing.len() == before.2
                && usize::from(self.current.export.binding_count()) >= before.1
                && !matches!(ret, Err(ScopeError::NoOpenSection))
        },
    )]
    #[inline]
    pub fn export_visible<Handler>(
        &mut self,
        modifier: &Modifier<Handler::Label>,
        handler: &mut Handler,
    ) -> Result<(), ScopeError>
    where
        Handler: NamespaceEventHandler<Data, Tag>,
    {
        let selected = modifier.apply(self.current.visible.clone(), handler)?;
        self.current
            .export
            .union_resolving(selected, &mut |path, collision| {
                handler.shadow(path, collision)
            })?;
        Ok(())
    }

    /// Open a section: a child scope inheriting the visible namespace, with
    /// an empty export.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the child sees the visible namespace unchanged and starts
    ///   with an empty export; the parent is kept for [`Self::end_section`];
    ///   sections nest as a stack.
    /// - provides: the child scope of a section.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — which namespace the child inherits and that its
    ///   export starts empty, over a parent with both namespaces non-empty;
    ///   stack order, by two nested sections closed in turn.
    /// - witness: `namespace::namespace::a_section_inherits_the_visible_namespace_and_exports_nothing_yet`
    /// - witness: `namespace::namespace::nested_sections_close_innermost_first`
    #[spec(
        captures: before = (
            self.current.visible.binding_count(),
            self.current.export.binding_count(),
            self.enclosing.len(),
        ),
        ensures: self.current.visible.binding_count() == before.0
            && usize::from(self.current.export.binding_count()) == 0
            && self.enclosing.len() == before.2.saturating_add(1)
            && self.enclosing.last().is_some_and(|parent| {
                parent.visible.binding_count() == before.0
                    && parent.export.binding_count() == before.1
            }),
    )]
    #[inline]
    pub fn begin_section(&mut self)
    {
        let inherited = self.current.visible.clone();
        let parent = mem::replace(&mut self.current, Namespaces {
            visible: inherited,
            export: Trie::empty(),
        });
        self.enclosing.push(parent);
    }

    /// Close the innermost section, including its export under `prefix`.
    ///
    /// # Specification
    /// - requires: nothing; a closed stack returns a structural refusal.
    /// - ensures: the child's export runs through `modifier`, is prefixed by
    ///   `prefix` and is included into the parent's two namespaces; the child's
    ///   visible namespace is discarded, so what it only imported evaporates;
    ///   the parent is restored with everything it held, and a close inside a
    ///   nested section returns into the enclosing section.
    /// - provides: the close of a section.
    /// - fails: [`ScopeError::NoOpenSection`] when none is open; a rejection
    ///   from the modifier or the merge. The section is popped before the
    ///   modifier runs, so a rejection leaves it closed and its export
    ///   discarded.
    /// - panics: none.
    ///
    /// # Errors
    /// [`ScopeError::NoOpenSection`] outside a section, and
    /// [`ScopeError::Rejected`] when `handler` refuses an event.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — which namespace survives, the closing modifier, the
    ///   prefixing and the guard, by a section that imports and exports closed
    ///   under the identity, under a selection and with none open; the restored
    ///   parent, over a parent holding its own binding and over two nested
    ///   sections.
    /// - witness: `namespace::namespace::a_section_exports_under_its_prefix`
    /// - witness: `namespace::namespace::a_sections_imports_evaporate_at_close`
    /// - witness: `namespace::namespace::a_sections_closing_modifier_chooses_what_it_passes_on`
    /// - witness: `namespace::namespace::closing_without_an_open_section_fails`
    /// - witness: `namespace::namespace::closing_a_section_restores_what_the_parent_already_held`
    /// - witness: `namespace::namespace::nested_sections_close_innermost_first`
    /// - witness: `namespace::namespace::a_refused_closing_modifier_restores_the_parent_and_closes_the_section`
    /// - witness: `namespace::namespace::a_refused_closing_merge_keeps_its_prefix_and_closes_the_section`
    #[spec(
        captures: before = (
            self.enclosing.len(),
            self.current.visible.binding_count(),
            self.current.export.binding_count(),
            self.enclosing.last().map(|parent| {
                (
                    usize::from(parent.visible.binding_count()),
                    usize::from(parent.export.binding_count()),
                )
            }),
        ),
        ensures: |ret| {
            if before.0 == 0 {
                self.enclosing.is_empty()
                    && matches!(ret, Err(ScopeError::NoOpenSection))
                    && self.current.visible.binding_count() == before.1
                    && self.current.export.binding_count() == before.2
            }
            else {
                self.enclosing.len() == before.0.saturating_sub(1)
                    && !matches!(ret, Err(ScopeError::NoOpenSection))
                    && before.3.is_some_and(|parent| {
                        usize::from(self.current.visible.binding_count()) >= parent.0
                            && usize::from(self.current.export.binding_count()) >= parent.1
                    })
            }
        },
    )]
    #[inline]
    pub fn end_section<Handler>(
        &mut self,
        prefix: &NamePath,
        modifier: &Modifier<Handler::Label>,
        handler: &mut Handler,
    ) -> Result<(), ScopeError>
    where
        Handler: NamespaceEventHandler<Data, Tag>,
    {
        let Some(parent) = self.enclosing.pop()
        else {
            return Err(ScopeError::NoOpenSection);
        };
        let child = mem::replace(&mut self.current, parent);
        let selected = modifier.apply(child.export, handler)?;
        self.include_subtree(prefix, selected, handler)
    }
}
