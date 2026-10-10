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

use anodized::spec;
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
///
/// # Specification
/// - requires: the seed-table sequence accompanies the coordinate.
/// - ensures: the pair identifies an entry within that sequence, not a globally
///   owned binding.
/// - provides: source coordinates for builtin recognition.
/// - executable: none — a coordinate does not hold the tables needed to check
///   its bounds or meaning.
///
/// # Adequacy
/// - hypothesis: L3 — duplicate entries and later tables resolve to the exact
///   winning table and entry positions.
/// - witness: `namespace::recognition::tests::ordered_bindings_shadow_from_the_right`
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct SeedPosition
{
    /// The table's position among the tables seeded.
    pub table: usize,
    /// The entry's position in its table.
    pub entry: usize,
}

/// What an outermost path resolves to.
///
/// # Specification
/// - requires: the producer supplies the recognition kind and any seed
///   coordinate.
/// - ensures: namespace kinds govern unknown members; member and definition
///   kinds do not. A builtin coordinate remains relative to its seed sequence.
/// - provides: recognition kind independently of the binding's site tag.
/// - executable: none — a kind does not hold the seed tables or producing
///   declaration; the governance method checks its local classification.
///
/// # Adequacy
/// - hypothesis: L3 — every kind has a governance result, and site tags govern
///   shadow policy independently of the recognized kind.
/// - witness: `recognition::recognition::only_governed_namespaces_decline_an_unknown_member`
/// - witness: `recognition::recognition::shadow_policy_uses_site_tags_independently_of_recognized_kinds`
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Recognized
{
    /// A namespace a seed table binds, which governs its members.
    BuiltinNamespace(SeedPosition),
    /// A member a seed table binds.
    BuiltinMember(SeedPosition),
    /// A native prelude member with its table-owned signature and operation.
    BuiltinPrimitive
    {
        /// The winning seed coordinate.
        position: SeedPosition,
        /// The shared native table row.
        primitive: gandr_core_term::primitive::Primitive,
    },
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
    #[spec(
        ensures: |ret| ret.0 == matches!(*self, Self::BuiltinNamespace(_) | Self::ModuleNamespace),
    )]
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
///
/// # Specification
/// - requires: the producing scope and queried path accompany the answer.
/// - ensures: complete answers consume the path; unknown members name a proper
///   governed prefix; ungoverned answers leave interpretation outside the
///   scope.
/// - provides: a whole-path decision rather than mere exact-key lookup.
/// - executable: none — the answer holds neither its query path nor the scope
///   that establishes the prefix relation.
///
/// # Adequacy
/// - hypothesis: L3 — paths stop at each tested depth and kind; a seeded root
///   does not bridge an unbound first segment.
/// - witness: `recognition::recognition::a_path_is_governed_by_its_deepest_resolved_prefix`
/// - witness: `recognition::recognition::root_seeds_do_not_bridge_an_unbound_namespace_prefix`
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
///
/// # Specification
/// - requires: the producer assigns the binding's provenance tag.
/// - ensures: builtin tags trigger shadow policy; source tags carry their
///   producer's span and permit ordinary rebinding.
/// - provides: provenance independently of recognition kind.
/// - executable: none — the tag holds neither the seeding history nor source
///   text that establishes its provenance.
///
/// # Adequacy
/// - hypothesis: L3 — policy distinguishes builtin and source tags even when
///   their recognition kinds suggest a different origin.
/// - witness: `recognition::recognition::shadow_policy_uses_site_tags_independently_of_recognized_kinds`
/// - witness: `recognition::recognition::redeclaring_a_source_name_is_not_a_shadow_event`
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
///
/// # Specification
/// - requires: a source-tagged arrival displaced a builtin-tagged binding under
///   warning policy.
/// - ensures: the record retains the displaced path and arriving source span.
/// - provides: one diagnostic event, not a certificate of a past collision.
/// - executable: none — a record does not hold the collision or policy run that
///   establishes its correspondence.
///
/// # Adequacy
/// - hypothesis: L3 — one source shadow records its exact path and span; a
///   builtin arrival supplies no source event to record.
/// - witness: `recognition::recognition::shadowing_a_builtin_warns_by_default_and_rejects_under_policy`
/// - witness: `namespace::recognition::tests::a_builtin_arrival_does_not_invent_a_source_shadow_record`
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
    /// A native member with its table-owned semantics.
    Primitive(gandr_core_term::primitive::Primitive),
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
///
/// # Specification
/// - requires: the complete sequence of tables accompanies seeding.
/// - ensures: stored entry order participates in last-wins seeding, within this
///   table and across later tables.
/// - provides: an ordered builtin input, without deduplicating entries.
/// - executable: none — cross-table winners depend on the other tables;
///   `Recognition::new` checks the complete seeding boundary.
///
/// # Adequacy
/// - hypothesis: L3 — repeated paths within one table and across two tables
///   resolve to the exact final position and kind.
/// - witness: `namespace::recognition::tests::ordered_bindings_shadow_from_the_right`
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
    /// Derive recognition names and namespaces from the native vocabulary.
    ///
    /// # Specification
    /// - ensures: every native row appears once, after any namespace prefix it
    ///   needs.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — every table name resolves with its own operation;
    ///   declared shadows displace the subtree.
    /// - witness: `namespace::recognition::tests::native_prelude_seeds_names_and_shadowing`
    #[spec(ensures: |ref ret| gandr_core_term::primitive::PRELUDE.iter().all(|primitive|
        ret.entries().iter().filter(|entry| entry.kind == SeedKind::Primitive(*primitive)).count() == 1))]
    #[inline]
    #[must_use]
    pub fn prelude() -> Self
    {
        let mut entries: Vec<SeedEntry> = Vec::new();
        for &primitive in gandr_core_term::primitive::PRELUDE {
            let spelling: &'static str = primitive.name().into();
            let mut segments = Vec::new();
            let mut parts = spelling.split('.').peekable();
            while let Some(part) = parts.next() {
                segments.push(Segment::from(part));
                let path = NamePath::from(segments.clone());
                if parts.peek().is_some() {
                    if !entries.iter().any(|entry| entry.path == path) {
                        entries.push(SeedEntry {
                            path,
                            kind: SeedKind::Namespace,
                        });
                    }
                }
                else {
                    entries.push(SeedEntry {
                        path,
                        kind: SeedKind::Primitive(primitive),
                    });
                }
            }
        }
        Self(entries)
    }
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
///
/// # Specification
/// - requires: collision callbacks receive the producing path and binding
///   sites.
/// - ensures: rejection records nothing; warning records only source arrivals
///   over builtin tags; other arrivals preserve the log.
/// - provides: outermost shadow policy and its ordered diagnostic log.
/// - executable: none — this build's specification facade does not expose the
///   type-item runtime; the shadow predicate checks the callback transition.
///
/// # Adequacy
/// - hypothesis: L3 — both policies, source rebinding and builtin arrivals
///   produce their exact decisions and bounded record changes.
/// - witness: `recognition::recognition::shadowing_a_builtin_warns_by_default_and_rejects_under_policy`
/// - witness: `namespace::recognition::tests::a_builtin_arrival_does_not_invent_a_source_shadow_record`
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
    /// - ensures: a formerly builtin-tagged binding is refused under
    ///   [`ShadowPolicy::Reject`]; under warn-and-allow the later binding
    ///   survives, and a source-tagged arrival is recorded at its span. A
    ///   builtin-tagged arrival supplies no source span and is not recorded.
    ///   Any collision over a source-tagged binding records nothing.
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
    /// - witness: `namespace::recognition::tests::a_builtin_arrival_does_not_invent_a_source_shadow_record`
    /// - witness: `recognition::recognition::shadow_policy_uses_site_tags_independently_of_recognized_kinds`
    #[spec(
        captures: before = (
            self.policy,
            self.shadowed.len(),
            collision.former.tag,
            collision.latter,
        ),
        ensures: |ret| {
            if before.2 == RecognitionSite::Builtin && before.0 == ShadowPolicy::Reject {
                self.shadowed.len() == before.1
                    && ret.as_ref().is_err_and(|rejection| {
                        rejection.kind() == EventKind::Shadow && rejection.path() == path
                    })
            }
            else {
                ret.as_ref().is_ok_and(|binding| *binding == before.3)
                    && match (before.2, before.3.tag) {
                        | (RecognitionSite::Builtin, RecognitionSite::Source(span)) => {
                            self.shadowed.len() == before.1.saturating_add(1)
                                && self.shadowed.last().is_some_and(|record| {
                                    record.path == *path && record.span == span
                                })
                        },
                        | _ => self.shadowed.len() == before.1,
                    }
            }
        },
    )]
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
///
/// # Specification
/// - requires: names and site tags are supplied by their producers.
/// - ensures: visible recognition is independent of exports; mutations apply
///   the selected shadow policy and resume starts a fresh diagnostic log.
/// - provides: an outermost namespace carried across submissions.
/// - executable: none — this build's specification facade does not expose the
///   type-item runtime; construction and mutation predicates check their
///   boundaries.
///
/// # Adequacy
/// - hypothesis: L3 — ordered seeding, rejected and accepted declarations,
///   nonbinding binder reports and resumed names cover the state transitions.
/// - witness: `namespace::recognition::tests::ordered_bindings_shadow_from_the_right`
/// - witness: `recognition::recognition::shadowing_a_builtin_warns_by_default_and_rejects_under_policy`
/// - witness: `recognition::recognition::a_binder_over_a_builtin_reports_without_shadowing`
/// - witness: `recognition::recognition::resuming_carries_the_names_and_drops_the_events`
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
    /// The native prelude's outermost scope, under warn-and-allow.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn default() -> Self
    {
        Self::new(&[SeedTable::prelude()], ShadowPolicy::WarnAndAllow)
    }
}

impl Recognition
{
    /// The outermost scope seeded from `tables`, in order, under `policy`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: each distinct path resolves to the last entry's kind and seed
    ///   position, within a table and across tables; nothing else resolves.
    ///   Every seeded binding has a builtin site tag, so a declaration over it
    ///   is a shadow event.
    /// - provides: the outermost scope a lowering starts from.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — duplicate paths within and across tables resolve to
    ///   the exact winning kind and position; root seeds do not fill gaps.
    /// - witness: `namespace::recognition::tests::ordered_bindings_shadow_from_the_right`
    /// - witness: `recognition::recognition::root_seeds_do_not_bridge_an_unbound_namespace_prefix`
    #[spec(
        ensures: |ret| {
            let mut distinct = 0_usize;
            let matches_inputs = tables.iter().enumerate().all(|(table, seeded)| {
                seeded.entries().iter().enumerate().all(|(entry, seed)| {
                    let Maybe::Present(found) = ret.scope.resolve(&seed.path)
                    else {
                        return false;
                    };
                    let (position, kind) = match found.data {
                        | Recognized::BuiltinNamespace(position) => (position, SeedKind::Namespace),
                        | Recognized::BuiltinMember(position) => (position, SeedKind::Member),
                        | Recognized::BuiltinPrimitive { position, primitive } => (position, SeedKind::Primitive(primitive)),
                        | Recognized::ModuleNamespace
                        | Recognized::ModuleComponent
                        | Recognized::Definition => return false,
                    };
                    if (position.table, position.entry) == (table, entry) {
                        distinct = distinct.saturating_add(1);
                    }
                    found.tag == RecognitionSite::Builtin
                        && (position.table, position.entry) >= (table, entry)
                        && tables
                            .get(position.table)
                            .and_then(|seeded| seeded.entries().get(position.entry))
                            .is_some_and(|winner| winner.path == seed.path && winner.kind == kind)
                })
            });
            matches_inputs
                && usize::from(ret.scope.visible().binding_count()) == distinct
                && usize::from(ret.scope.export().binding_count()) == 0
                && ret.handler.policy == policy
                && ret.handler.shadowed.is_empty()
        },
    )]
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
                    | SeedKind::Primitive(primitive) => Recognized::BuiltinPrimitive {
                        position,
                        primitive,
                    },
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
    #[spec(
        ensures: |ret| {
            ret.handler.policy == policy
                && ret.handler.shadowed.is_empty()
                && ret.scope.visible().binding_count() == previous.scope.visible().binding_count()
                && ret.scope.export().binding_count() == previous.scope.export().binding_count()
        },
    )]
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
    /// - witness: `recognition::recognition::root_seeds_do_not_bridge_an_unbound_namespace_prefix`
    #[spec(
        ensures: |ret| {
            ret == match self.scope.visible().resolved_prefix(path) {
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
        },
    )]
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
    #[spec(
        captures: before = (
            self.handler.policy,
            self.handler.shadowed.len(),
            usize::from(self.scope.visible().binding_count()),
            self.scope.export().binding_count(),
            usize::from(subtree.binding_count()),
        ),
        ensures: |ret| {
            self.handler.policy == before.0
                && self.scope.export().binding_count() == before.3
                && if ret.is_err() {
                    self.handler.policy == ShadowPolicy::Reject
                        && self.handler.shadowed.len() == before.1
                        && usize::from(self.scope.visible().binding_count()) == before.2
                        && ret.as_ref().is_err_and(|rejection| {
                            rejection.kind() == EventKind::Shadow
                                && rejection.path().segments().len() == 1
                        })
                }
                else {
                    usize::from(self.scope.visible().binding_count()) >= before.4
                        && usize::from(self.scope.visible().binding_count())
                            <= before.2.saturating_add(before.4)
                        && (self.handler.shadowed.len() == before.1
                            || (self.handler.policy == ShadowPolicy::WarnAndAllow
                                && self.handler.shadowed.len() == before.1.saturating_add(1)
                                && self.handler.shadowed.last().is_some_and(|record| {
                                    record.span == site && record.path.segments().len() == 1
                                })))
                }
        },
    )]
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
    /// - witness: `recognition::recognition::shadow_policy_uses_site_tags_independently_of_recognized_kinds`
    #[spec(
        captures: before = (
            self.handler.policy,
            self.handler.shadowed.len(),
            self.scope.visible().binding_count(),
            self.scope.export().binding_count(),
        ),
        ensures: |ret| {
            self.handler.policy == before.0
                && self.scope.visible().binding_count() == before.2
                && self.scope.export().binding_count() == before.3
                && if ret.is_err() {
                    self.handler.policy == ShadowPolicy::Reject
                        && self.handler.shadowed.len() == before.1
                        && ret.as_ref().is_err_and(|rejection| {
                            rejection.kind() == EventKind::Shadow
                                && rejection.path().segments().len() == 1
                        })
                }
                else {
                    self.handler.shadowed.len() == before.1
                        || (self.handler.policy == ShadowPolicy::WarnAndAllow
                            && self.handler.shadowed.len() == before.1.saturating_add(1)
                            && self.handler.shadowed.last().is_some_and(|record| {
                                record.span == site && record.path.segments().len() == 1
                            }))
                }
        },
    )]
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
    #[spec(
        captures: before = (
            self.handler.policy,
            self.handler.shadowed.len(),
            usize::from(self.scope.visible().binding_count()),
            self.scope.export().binding_count(),
            usize::from(subtree.binding_count()),
        ),
        ensures: self.handler.policy == before.0
            && self.handler.shadowed.len() == before.1
            && self.scope.export().binding_count() == before.3
            && usize::from(self.scope.visible().binding_count()) >= before.4
            && usize::from(self.scope.visible().binding_count())
                <= before.2.saturating_add(before.4),
    )]
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

    #[test]
    fn native_prelude_seeds_names_and_shadowing()
    {
        let recognition = Recognition::default();
        assert!(
            matches!(recognition.resolve(&path("add")), Maybe::Present(Recognized::BuiltinPrimitive { primitive, .. }) if primitive.operator() == gandr_core_term::primitive::Operator::Infix("+"))
        );
        assert!(
            matches!(recognition.resolve(&path("int.div")), Maybe::Present(Recognized::BuiltinPrimitive { primitive, .. }) if primitive.name().as_ref() == "int.div")
        );
        let mut shadowed = Recognition::new(
            &[
                SeedTable::prelude(),
                SeedTable::from(Vec::from([member("int")])),
            ],
            ShadowPolicy::WarnAndAllow,
        );
        assert_eq!(
            shadowed.resolve(&path("int")),
            Maybe::Present(&Recognized::BuiltinMember(SeedPosition {
                table: 1,
                entry: 0
            }))
        );
        shadowed.declare_resumed(
            crate::namespace::path::Segment::from("int"),
            crate::namespace::Trie::empty(),
        );
        assert!(
            matches!(shadowed.resolve(&path("int.div")), Maybe::Absent(_)),
            "rebinding the prefix removes the seeded subtree"
        );
    }

    use alloc::vec::Vec;

    use quenchant_shape::shape::Maybe;

    use super::Recognition;
    use super::Recognized;
    use super::SeedEntry;
    use super::SeedKind;
    use super::SeedPosition;
    use super::SeedTable;
    use super::ShadowPolicy;
    use crate::namespace::Binding;
    use crate::namespace::Collision;
    use crate::namespace::EventKind;
    use crate::namespace::NamespaceEventHandler as _;
    use crate::namespace::RecognitionSite;
    use crate::namespace::path::DottedName;
    use crate::namespace::path::NamePath;
    use crate::namespace::recognition::RecognitionHandler;

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
    fn a_builtin_arrival_does_not_invent_a_source_shadow_record()
    {
        let former = Binding::new(
            Recognized::BuiltinMember(SeedPosition {
                table: 0_usize,
                entry: 0_usize,
            }),
            RecognitionSite::Builtin,
        );
        let latter = Binding::new(
            Recognized::BuiltinNamespace(SeedPosition {
                table: 1_usize,
                entry: 0_usize,
            }),
            RecognitionSite::Builtin,
        );
        let at = path("x");
        let mut warning = RecognitionHandler {
            policy: ShadowPolicy::WarnAndAllow,
            shadowed: Vec::new(),
        };
        assert_eq!(
            warning.shadow(&at, Collision { former, latter }),
            Ok(latter)
        );
        assert!(warning.shadowed.is_empty());
        let mut rejecting = RecognitionHandler {
            policy: ShadowPolicy::Reject,
            shadowed: Vec::new(),
        };
        let refused = rejecting
            .shadow(&at, Collision { former, latter })
            .expect_err("a formerly builtin-tagged binding is protected under rejection");
        assert_eq!(refused.kind(), EventKind::Shadow);
        assert_eq!(refused.path(), &at);
        assert!(rejecting.shadowed.is_empty());
    }
    #[test]
    fn ordered_bindings_shadow_from_the_right()
    {
        let table = SeedTable::from(Vec::from([member("x"), member("x")]));
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
