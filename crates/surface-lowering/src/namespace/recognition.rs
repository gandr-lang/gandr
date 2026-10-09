//! The outermost scope: builtin names seeded from ordered tables, under a
//! shadow policy.
//!
//! Builtin names are bindings in one outermost visible namespace, built over
//! [`Scope::with_init_visible`] from ordered [`SeedTable`]s, rather than a
//! table consulted by name at each use: asking whether a path is a builtin is
//! [`Recognition::resolve`], the same lookup a source path takes. The tables
//! are empty until the builtins are written; the mechanism does not depend on
//! what they hold.
//!
//! # What a declaration does to a builtin
//!
//! A top-level declaration shadows whatever the outermost scope held at its
//! name, together with the whole subtree: declaring `list` displaces `list`,
//! `list.each` and every other `list.*` binding at once, so no partially
//! shadowed namespace resolves `list` to the source and `list.each` to the
//! builtin. The displacement is a shadow event settled by a handler, so its
//! policy is a value rather than an engine mode:
//!
//! | policy | a shadowed builtin |
//! | --- | --- |
//! | [`ShadowPolicy::WarnAndAllow`] | the declaration wins; the event is recorded as a [`ShadowedBuiltin`] |
//! | [`ShadowPolicy::Reject`] | the event is refused |
//!
//! Warn-and-allow is the default.
//!
//! # Binders are reported, not bound
//!
//! A lambda, function or `run` binder is checked against the outermost roots
//! where it is introduced ([`Recognition::note_binder`]) and reported under the
//! same policy, but it binds nothing here: resolving a binder is the binder
//! chain's job, and the outermost scope stays as it was.

use alloc::vec::Vec;

use gandr_surface_syntax::ByteSpan;
use quenchant_shape::shape::Maybe;

use crate::namespace::event::EventKind;
use crate::namespace::event::EventRejection;
use crate::namespace::event::NamespaceEventHandler;
use crate::namespace::event::RejectionReason;
use crate::namespace::path::NamePath;
use crate::namespace::path::Segment;
use crate::namespace::path::SegmentCount;
use crate::namespace::scope::Scope;
use crate::namespace::trie::Binding;
use crate::namespace::trie::Collision;
use crate::namespace::trie::Trie;
use crate::namespace::trie::binding;

/// Where a seeded binding came from: its table's position in the seeding
/// order and its entry's position in that table.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct SeedPosition
{
    /// The table's position among the tables seeded.
    pub table: usize,
    /// The entry's position in its table.
    pub entry: usize,
}

/// What an outermost path resolves to.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Recognized
{
    /// A namespace a seed table binds, which governs its members.
    BuiltinNamespace(SeedPosition),
    /// A member a seed table binds.
    BuiltinMember(SeedPosition),
    /// A `module` declaration, or a module nested in one.
    ModuleNamespace,
    /// A value component of a `module` declaration.
    ModuleComponent,
    /// A top-level definition.
    Definition,
}

/// Whether a namespace declines an unknown member rather than leaving it to a
/// projection.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Declines(pub bool);

impl Recognized
{
    /// Whether an unknown member under this name is refused rather than read
    /// as a projection.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: declines exactly for [`Self::BuiltinNamespace`] and
    ///   [`Self::ModuleNamespace`]: a builtin namespace is not a record value,
    ///   and a module's scope holds exactly its components.
    /// - provides: the governance test of [`Recognition::resolve_path`].
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the answer asserted for every variant.
    /// - witness: `recognition::recognition::only_governed_namespaces_decline_an_unknown_member`
    #[inline]
    #[must_use]
    pub const fn declines_unknown_member(&self) -> Declines
    {
        Declines(matches!(
            *self,
            Self::BuiltinNamespace(_) | Self::ModuleNamespace
        ))
    }
}

/// What the outermost scope says about a whole dotted path.
///
/// A path can be governed without resolving: `M.nope` under a module is a
/// refusal, while `stranger.nope` is no business of the scope's.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum PathResolution
{
    /// Every segment resolved; the payload is what the whole path names.
    Complete(Recognized),
    /// A proper prefix resolved to a namespace that governs its members, and
    /// the next segment is not one of them.
    UnknownMember
    {
        /// How many leading segments resolved.
        depth: SegmentCount,
        /// The governing namespace those segments named.
        namespace: Recognized,
    },
    /// The scope does not govern the path: its root is unbound, or the
    /// deepest name it resolved is an ordinary value whose fields are not the
    /// scope's.
    Ungoverned,
}

/// Where a binding came from.
///
/// Displacing a [`Self::Builtin`] binding is the event a policy settles; one
/// source declaration replacing another is ordinary rebinding.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum RecognitionSite
{
    /// Seeded from a table when the scope was built.
    Builtin,
    /// Declared by the source at these bytes.
    Source(ByteSpan),
}

/// The outermost scope's shadow policy.
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum ShadowPolicy
{
    /// The source binding wins and the event is recorded.
    #[default]
    WarnAndAllow,
    /// The shadow is refused.
    Reject,
}

/// One shadowing of a builtin by the source.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ShadowedBuiltin
{
    /// The path the source took over.
    pub path: NamePath,
    /// The bytes of the name that took it over.
    pub span: ByteSpan,
}

/// What one seed entry binds its path as.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum SeedKind
{
    /// A namespace, governing its members.
    Namespace,
    /// A member.
    Member,
}

/// One entry of an ordered seed table.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct SeedEntry
{
    /// The path the entry binds.
    pub path: NamePath,
    /// What it binds the path as.
    pub kind: SeedKind,
}

/// An ordered table of builtin bindings the outermost scope is seeded from.
///
/// The table keeps every entry in order; a later entry at a path an earlier
/// one bound shadows it, within a table and across tables seeded later.
#[repr(transparent)]
#[derive(Clone, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct SeedTable(Vec<SeedEntry>);

impl From<Vec<SeedEntry>> for SeedTable
{
    /// The table of `entries`, in order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(entries: Vec<SeedEntry>) -> Self
    {
        Self(entries)
    }
}

impl SeedTable
{
    /// The entries, in order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn entries(&self) -> &[SeedEntry]
    {
        self.0.as_slice()
    }
}

/// The handler giving the namespace events their outermost meaning.
///
/// Not-found and hook events are inert: no outermost modifier performs them
/// to any purpose.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
struct RecognitionHandler
{
    /// How a shadowed builtin is settled.
    policy: ShadowPolicy,
    /// Every builtin the source displaced, in the order displaced.
    shadowed: Vec<ShadowedBuiltin>,
}

impl NamespaceEventHandler<Recognized, RecognitionSite> for RecognitionHandler
{
    type Label = ();

    /// Continue: an empty selection means nothing here.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// Never.
    #[inline]
    fn not_found(
        &mut self,
        _path: &NamePath,
    ) -> Result<(), EventRejection>
    {
        Ok(())
    }

    /// Settle a collision by the policy when it displaces a builtin, and keep
    /// the later binding otherwise.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: displacing a builtin is refused under
    ///   [`ShadowPolicy::Reject`]; under warn-and-allow it is recorded at the
    ///   later binding's source span and the later binding survives. Any other
    ///   collision keeps the later binding and records nothing.
    /// - provides: the policy of every outermost shadow.
    /// - fails: under the reject policy, on a builtin.
    /// - panics: none.
    ///
    /// # Errors
    /// A shadow rejection at `path` under the reject policy.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the same builtin shadow under each policy, a source
    ///   redeclaration under the reject policy and a binder over a builtin
    ///   under each, asserted as the exact records and refusals.
    /// - witness: `recognition::recognition::shadowing_a_builtin_warns_by_default_and_rejects_under_policy`
    /// - witness: `recognition::recognition::redeclaring_a_source_name_is_not_a_shadow_event`
    /// - witness: `recognition::recognition::a_binder_over_a_builtin_reports_without_shadowing`
    #[inline]
    fn shadow(
        &mut self,
        path: &NamePath,
        collision: Collision<Recognized, RecognitionSite>,
    ) -> Result<Binding<Recognized, RecognitionSite>, EventRejection>
    {
        if collision.former.tag == RecognitionSite::Builtin {
            if self.policy == ShadowPolicy::Reject {
                return Err(EventRejection::new(
                    EventKind::Shadow,
                    path.clone(),
                    RejectionReason::from(
                        "this declaration shadows a builtin name, which the active policy forbids",
                    ),
                ));
            }
            if let RecognitionSite::Source(span) = collision.latter.tag {
                self.shadowed.push(ShadowedBuiltin {
                    path: path.clone(),
                    span,
                });
            }
        }
        Ok(collision.latter)
    }

    /// Run the identity.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// Never.
    #[inline]
    fn hook(
        &mut self,
        _path: &NamePath,
        _label: &(),
        subject: Trie<Recognized, RecognitionSite>,
    ) -> Result<Trie<Recognized, RecognitionSite>, EventRejection>
    {
        Ok(subject)
    }
}

/// The outermost visible scope and the shadow policy governing it.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Recognition
{
    /// The scope, seeded with the builtin namespace.
    scope: Scope<Recognized, RecognitionSite>,
    /// The handler carrying the policy and the recorded shadowings.
    handler: RecognitionHandler,
}

impl Default for Recognition
{
    /// The outermost scope of no table, under warn-and-allow.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn default() -> Self
    {
        Self::new(&[], ShadowPolicy::WarnAndAllow)
    }
}

impl Recognition
{
    /// The outermost scope seeded from `tables`, in order, under `policy`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: each entry's path resolves to its kind at its seed position,
    ///   and nothing else resolves; a later entry at a path displaces an
    ///   earlier one, within a table and across tables; every seeded binding is
    ///   a builtin, so a declaration over it is a shadow event.
    /// - provides: the outermost scope a lowering starts from.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a table with a duplicate path and a later table
    ///   overriding an earlier, asserted as the exact entries and resolutions.
    /// - witness: `namespace::recognition::tests::ordered_bindings_shadow_from_the_right`
    #[inline]
    #[must_use]
    pub fn new(
        tables: &[SeedTable],
        policy: ShadowPolicy,
    ) -> Self
    {
        let mut builtins = Trie::empty();
        for (table, seeded) in tables.iter().enumerate() {
            for (entry, seed) in seeded.entries().iter().enumerate() {
                let position = SeedPosition { table, entry };
                let recognized = match seed.kind {
                    | SeedKind::Namespace => Recognized::BuiltinNamespace(position),
                    | SeedKind::Member => Recognized::BuiltinMember(position),
                };
                let _displaced = builtins.insert(
                    &seed.path,
                    Binding::new(recognized, RecognitionSite::Builtin),
                );
            }
        }
        Self {
            scope: Scope::with_init_visible(builtins),
            handler: RecognitionHandler {
                policy,
                shadowed: Vec::new(),
            },
        }
    }

    /// The scope a previous lowering left, for the next submission under
    /// `policy`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: resolution agrees with `previous` on every path; no shadowing
    ///   is recorded, because each submission reports its own; the policy is
    ///   `policy`, because it belongs to the run.
    /// - provides: the carry a session needs.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a scope holding a shadowing declaration and its
    ///   record, resumed, asserted as the exact resolutions and the empty
    ///   record.
    /// - witness: `recognition::recognition::resuming_carries_the_names_and_drops_the_events`
    #[inline]
    #[must_use]
    pub fn resumed(
        previous: &Self,
        policy: ShadowPolicy,
    ) -> Self
    {
        Self {
            scope: previous.scope.clone(),
            handler: RecognitionHandler {
                policy,
                shadowed: Vec::new(),
            },
        }
    }

    /// What `path` resolves to in the outermost scope.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn resolve(
        &self,
        path: &NamePath,
    ) -> Maybe<&Recognized, binding::Absent>
    {
        self.scope.resolve(path).map(|bound| &bound.data)
    }

    /// What the whole dotted path `path` resolves to, walked prefix by
    /// prefix.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: [`PathResolution::Complete`] exactly when every prefix
    ///   resolved; [`PathResolution::UnknownMember`] exactly when the walk
    ///   stopped after a proper prefix of `depth` segments resolving to a name
    ///   that declines unknown members; [`PathResolution::Ungoverned`]
    ///   otherwise, the root and an unbound first segment included.
    /// - provides: the governed reading of a dotted path.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — paths stopping at each depth under each kind of
    ///   deepest binding, asserted as the exact resolution.
    /// - witness: `recognition::recognition::a_path_is_governed_by_its_deepest_resolved_prefix`
    #[inline]
    #[must_use]
    pub fn resolve_path(
        &self,
        path: &NamePath,
    ) -> PathResolution
    {
        match self.scope.visible().resolved_prefix(path) {
            | Maybe::Present((depth, found)) if depth == path.depth() => {
                PathResolution::Complete(found.data)
            },
            | Maybe::Present((depth, found)) if found.data.declines_unknown_member().0 => {
                PathResolution::UnknownMember {
                    depth,
                    namespace: found.data,
                }
            },
            | Maybe::Present(_) | Maybe::Absent(_) => PathResolution::Ungoverned,
        }
    }

    /// Every builtin the source displaced, in the order displaced.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn shadowed(&self) -> &[ShadowedBuiltin]
    {
        self.handler.shadowed.as_slice()
    }

    /// Bind one top-level declaration named `name`, whose name is written at
    /// `site`, shadowing whatever the scope held under `name`.
    ///
    /// `subtree` is the declaration's namespace relative to `name`: its root
    /// binding is the declaration, a deeper path one of its components.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: on success `name` and every path of `subtree` resolve to
    ///   `subtree`'s bindings and nothing the scope held under `name` resolves;
    ///   displacing a builtin — the first binding at or under `name` — is one
    ///   shadow event at `name`, recorded at `site`; displacing a source
    ///   binding is none.
    /// - provides: the outermost binding of a top-level declaration.
    /// - fails: under [`ShadowPolicy::Reject`] when the declaration displaces a
    ///   builtin, leaving the scope unchanged.
    /// - panics: none.
    ///
    /// # Errors
    /// The policy's shadow rejection.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — subtree displacement over a seeded namespace with
    ///   members; the site test, over a fresh name and over a source
    ///   declaration; the policy, the same builtin shadow under each, the
    ///   refusal leaving the scope as it was.
    /// - witness: `recognition::recognition::a_declaration_displaces_the_whole_builtin_subtree`
    /// - witness: `recognition::recognition::shadowing_a_builtin_warns_by_default_and_rejects_under_policy`
    /// - witness: `recognition::recognition::redeclaring_a_source_name_is_not_a_shadow_event`
    #[inline]
    pub fn declare(
        &mut self,
        name: Segment,
        subtree: Trie<Recognized, RecognitionSite>,
        site: ByteSpan,
    ) -> Result<(), EventRejection>
    {
        let path = NamePath::from(Vec::from([name]));
        let displaced = self
            .scope
            .visible()
            .first_at_or_below(&path)
            .map(Clone::clone);
        if let Maybe::Present(former) = displaced {
            let data = match subtree.get(&NamePath::root()) {
                | Maybe::Present(root) => root.data,
                | Maybe::Absent(_) => Recognized::Definition,
            };
            let latter = Binding::new(data, RecognitionSite::Source(site));
            let _survivor = self.handler.shadow(&path, Collision { former, latter })?;
        }
        self.scope.graft_visible(&path, subtree);
        Ok(())
    }

    /// Report one binder named `name`, written at `site`, that collides with
    /// an outermost root, changing nothing.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the scope is unchanged whatever the outcome; a binder whose
    ///   one-segment path is bound to a builtin is one shadow event, recorded
    ///   at `site`; a binder over a source root or over nothing is none.
    /// - provides: the outermost report on a lambda, function or `run` binder.
    /// - fails: under [`ShadowPolicy::Reject`] on a builtin root.
    /// - panics: none.
    ///
    /// # Errors
    /// The policy's shadow rejection.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a binder over a builtin root, over nothing and over a
    ///   builtin under the reject policy, resolution asserted exactly after
    ///   each.
    /// - witness: `recognition::recognition::a_binder_over_a_builtin_reports_without_shadowing`
    #[inline]
    pub fn note_binder(
        &mut self,
        name: Segment,
        site: ByteSpan,
    ) -> Result<(), EventRejection>
    {
        let path = NamePath::from(Vec::from([name]));
        let Maybe::Present(former) = self.scope.resolve(&path).map(Clone::clone)
        else {
            return Ok(());
        };
        if former.tag != RecognitionSite::Builtin {
            return Ok(());
        }
        let latter = Binding::new(Recognized::Definition, RecognitionSite::Source(site));
        let _survivor = self.handler.shadow(&path, Collision { former, latter })?;
        Ok(())
    }

    /// Bind a declaration carried from an earlier submission, recording and
    /// refusing nothing.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: resolution afterwards is as [`Self::declare`] would leave it;
    ///   [`Self::shadowed`] is unchanged whatever the policy, because the
    ///   shadowing belonged to the submission that wrote it.
    /// - provides: replaying a session's earlier declarations.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a carried declaration over a builtin under the reject
    ///   policy, asserted as the exact resolution and the empty record.
    /// - witness: `recognition::recognition::a_resumed_declaration_binds_without_reporting`
    #[inline]
    pub fn declare_resumed(
        &mut self,
        name: Segment,
        subtree: Trie<Recognized, RecognitionSite>,
    )
    {
        let path = NamePath::from(Vec::from([name]));
        self.scope.graft_visible(&path, subtree);
    }
}

#[cfg(test)]
mod tests
{
    use alloc::vec::Vec;

    use quenchant_shape::shape::Maybe;

    use super::Recognition;
    use super::Recognized;
    use super::SeedEntry;
    use super::SeedKind;
    use super::SeedPosition;
    use super::SeedTable;
    use super::ShadowPolicy;
    use crate::namespace::path::DottedName;
    use crate::namespace::path::NamePath;

    /// The path `text` renders.
    ///
    /// # Specification
    /// trivial.
    fn path<Text>(text: Text) -> NamePath
    where
        Text: Into<DottedName<'static>>,
    {
        NamePath::from(text.into())
    }

    /// The member entry at `text`.
    ///
    /// # Specification
    /// trivial.
    fn member<Text>(text: Text) -> SeedEntry
    where
        Text: Into<DottedName<'static>>,
    {
        SeedEntry {
            path: path(text),
            kind: SeedKind::Member,
        }
    }

    #[test]
    fn ordered_bindings_shadow_from_the_right()
    {
        let entries = Vec::from([member("x"), member("x")]);
        let table = SeedTable::from(entries.clone());
        assert_eq!(
            table.entries(),
            entries.as_slice(),
            "the table keeps every entry, duplicates included, in order"
        );
        let recognition =
            Recognition::new(core::slice::from_ref(&table), ShadowPolicy::WarnAndAllow);
        assert_eq!(
            recognition.resolve(&path("x")),
            Maybe::Present(&Recognized::BuiltinMember(SeedPosition {
                table: 0_usize,
                entry: 1_usize,
            })),
            "the later duplicate entry shadows the earlier one"
        );
        let later = SeedTable::from(Vec::from([SeedEntry {
            path: path("x"),
            kind: SeedKind::Namespace,
        }]));
        let recognition = Recognition::new(&[table, later], ShadowPolicy::WarnAndAllow);
        assert_eq!(
            recognition.resolve(&path("x")),
            Maybe::Present(&Recognized::BuiltinNamespace(SeedPosition {
                table: 1_usize,
                entry: 0_usize,
            })),
            "a table seeded later shadows an earlier table"
        );
    }
}
