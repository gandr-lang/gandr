//! Imports: `import "<path>" ;` and `import "<path>" as name ;`, kept as
//! source-ordered declarations, resolved against the sources of the
//! [`Unit`](crate::Unit) the importer is lowered in.
//!
//! # An import resolves a sibling source
//!
//! An address with no scheme is a path relative to the importing source. The
//! dispatcher reads the importer's closure — every source it reaches through
//! path imports, each once — and lays it out as one text, each source after
//! every source it imports and the importer last; the [`Unit`](crate::Unit)
//! records where each source starts and what each of its path imports, in
//! source order, resolved to: an earlier source, a path naming nothing in the
//! root ([`ImportTarget::Unresolved`]), or an edge of a cycle
//! ([`ImportTarget::Cycle`]). The unit is parsed as one tree and lowered into
//! one arena: each top-level declaration and constructor is collected under
//! its own source (`Container::TopLevel`), so the sibling's declarations are
//! the prefix of the importer's constants, checked and admitted first, and a
//! reference to one lowers to its constant. Nothing is copied into the
//! importer, and the kernel replays the sibling's certificate before the
//! importer's, which refers to it by content.
//!
//! A name a source does not declare is looked up through its resolved
//! imports. The export of a source is its top-level declarations and its
//! constructors under their families — not what it imports, since an import
//! is not a re-export. `import "<path>" ;` brings the export in unqualified;
//! `import "<path>" as m ;` binds `m` in the import scope and answers
//! `m.Name` with the export's `Name`, as a term and as a type head. A
//! declaration with no definition is not exported: a use refuses
//! `UnexportedName` naming it. A declaration its source refuses is not
//! exported either: its constant has no type, and a use is refused
//! `UnknownConstant` at the use, as a use of a refused declaration of the
//! source's own is. An address with a scheme is bound and not resolved, as
//! before.
//!
//! # Refusals by name
//!
//! - `ImportUnresolved` and `ImportCycle`: every declaration of a source whose
//!   import names nothing in the root, or closes a cycle, is refused at the
//!   import, naming it — no declaration of such a source can be trusted to read
//!   what its author meant. A sibling the lowering refuses as a whole refuses
//!   its importer whole, with the sibling's refusal.
//! - `ImportShadows`: a top-level declaration or constructor an unqualified
//!   import already binds is refused at the declaration, naming the import; two
//!   unqualified imports binding one name refuse a use of it, naming both, and
//!   leave every other name of both usable.
//! - `DuplicateImportAlias`: of two imports binding one alias, the second is
//!   refused, naming the first, rather than silently hiding it. The refusal is
//!   the import's own: the rest of the source lowers against the first import's
//!   binding, and the attribute blocks written before the second import state
//!   it, `@[ refuses("DuplicateImportAlias") ] import … as … ;`. A refusal of a
//!   whole source that no item can carry would be stated by an inner block at
//!   the source's head, `@![ refuses("…") ]`, built when the first such refusal
//!   appears.
//!
//! The recorded design refuses an ambiguous unqualified import outright; this
//! refuses the use instead, as Haskell refuses an ambiguous occurrence and
//! not the import: a source that imports two siblings sharing one helper's
//! name stays usable for everything else, and the refusal still names both
//! sources where the name is read.
//!
//! # Alternatives and reversal
//!
//! - An export table per source, each source lowered into its own arena and the
//!   importer reading the table: declined, because the checker, the program and
//!   the kernel each read one arena and one environment, and a second arena per
//!   sibling would need every constant translated between them.
//! - A forest lowerer, one tree per source: declined, because the collector,
//!   the namespace engine and the origin table already address one tree;
//!   concatenation keeps them as they are and scopes names by source.
//! - Reversal: when packages land, an address names an export namespace
//!   (`Modifier` runs over it, `| only …` included), and a unit becomes a
//!   package's import-connected component judged once.
//!
//! Witnesses:
//! `tests::namespace::an_unqualified_import_answers_a_name_its_source_declares`,
//! `tests::namespace::an_aliased_import_qualifies_its_source_s_names`,
//! `tests::namespace::two_imports_binding_one_name_refuse_its_use`,
//! `tests::namespace::a_pending_declaration_is_not_exported`,
//! `tests::namespace::an_unresolved_import_refuses_its_source`,
//! `tests::namespace::a_declaration_an_import_binds_again_is_refused`,
//! `tests::namespace::duplicate_source_import_alias_becomes_a_refusal` and
//! `import::tests::an_identical_import_is_still_a_duplicate_and_preserves_the_next_position`.

use alloc::collections::BTreeMap;
use alloc::string::String;
use alloc::vec::Vec;
use core::fmt;

use anodized::spec;
use gandr_surface_syntax::ByteSpan;
use quenchant_shape::shape::Maybe;

use crate::error::LoweringRefusal;
use crate::namespace::Binding;
use crate::namespace::Collision;
use crate::namespace::EventKind;
use crate::namespace::EventRejection;
use crate::namespace::Modifier;
use crate::namespace::NamePath;
use crate::namespace::NamespaceEventHandler;
use crate::namespace::RejectionReason;
use crate::namespace::Scope;
use crate::namespace::ScopeError;
use crate::namespace::Segment;
use crate::namespace::Trie;
use crate::resolve::SurfaceName;
use crate::unit::ImportTarget;
use crate::unit::SourceIndex;

/// The reason the import policy gives for refusing a second binding of one
/// alias.
pub const ONE_SOURCE: &str = "an import alias must name one source";

/// An import's position among the module's imports, in source order.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ImportIndex(usize);

impl From<usize> for ImportIndex
{
    /// The import at source position `position`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(position: usize) -> Self
    {
        Self(position)
    }
}

impl From<ImportIndex> for usize
{
    /// The source position `index` names.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(index: ImportIndex) -> Self
    {
        index.0
    }
}

/// The address an import names, its escapes decoded and nothing resolved.
#[repr(transparent)]
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ImportUri(String);

impl From<String> for ImportUri
{
    /// The address `text`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(text: String) -> Self
    {
        Self(text)
    }
}

impl AsRef<str> for ImportUri
{
    /// The address's text.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn as_ref(&self) -> &str
    {
        self.0.as_str()
    }
}

impl fmt::Display for ImportUri
{
    /// Writes the address's text.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        f.write_str(self.0.as_str())
    }
}

/// What an import binds in its source: the sibling's exports by their own
/// names, or the sibling itself under an alias.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum ImportBinding<'source>
{
    /// `import "…" ;`: each export answers by its own name.
    Unqualified,
    /// `import "…" as name ;`: each export answers as `name.Export`.
    Aliased(SurfaceName<'source>),
}

/// What an import's address came to.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum ImportResolution
{
    /// An address with a scheme: kept as written and resolved by no pass of
    /// this lowering.
    Foreign,
    /// A path, relative to the importing source, and what the unit's caller
    /// resolved it to.
    Path(ImportTarget),
}

/// One `import "URI" ;` or `import "URI" as name ;`, as the source wrote it,
/// with what its address came to.
///
/// # Specification
/// - requires: the caller supplies a decoded URI, binding, span, source and
///   resolution belonging to the same import declaration.
/// - ensures: every component is retained as given.
/// - provides: source-associated import metadata.
/// - fails: construction does not validate source association or addresses.
/// - panics: none.
/// - executable: none — the syntax tree and written spelling are absent;
///   parsing witnesses establish their association with these stored fields.
///
/// # Adequacy
/// - hypothesis: L3 — a quoted URI with escapes is retained decoded beside its
///   exact alias and span, even when no such address exists. Raw constructors
///   remain able to represent caller-supplied metadata.
/// - witness: `tests::namespace::an_import_binds_its_alias_and_resolves_no_address`
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct ImportDeclaration<'source>
{
    /// The address the import names.
    uri: ImportUri,
    /// What it binds.
    binding: ImportBinding<'source>,
    /// The bytes the import covers.
    span: ByteSpan,
    /// The source of the unit that wrote it.
    source: SourceIndex,
    /// What its address came to.
    resolution: ImportResolution,
}

impl<'source> ImportDeclaration<'source>
{
    /// The import of `uri` binding `binding`, written over `span` in
    /// `source`, its address come to `resolution`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn new(
        uri: ImportUri,
        binding: ImportBinding<'source>,
        span: ByteSpan,
        source: SourceIndex,
        resolution: ImportResolution,
    ) -> Self
    {
        Self {
            uri,
            binding,
            span,
            source,
            resolution,
        }
    }

    /// The address the import names.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn uri(&self) -> &ImportUri
    {
        &self.uri
    }

    /// What the import binds.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn binding(&self) -> ImportBinding<'source>
    {
        self.binding
    }

    /// The bytes the import covers.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn span(&self) -> ByteSpan
    {
        self.span
    }

    /// The source of the unit that wrote the import.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn source(&self) -> SourceIndex
    {
        self.source
    }

    /// What the import's address came to.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn resolution(&self) -> ImportResolution
    {
        self.resolution
    }
}

quenchant_shape::reason_enum! {
    /// Why a source has no alias scope.
    pub mod alias_scope {
        /// The reason no scope is held.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The source binds no alias.
            Unaliased,
        }
    }
}

quenchant_shape::reason_enum! {
    /// Why an alias names no import.
    pub mod aliased {
        /// The reason the alias answers nothing.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// No import of the source binds the alias.
            Unbound,
        }
    }
}

/// A unit's imports: the declarations in source order, and the scope each
/// source's aliases are bound in.
///
/// # Specification
/// - requires: nothing; the empty collection holds no scope.
/// - ensures: declarations remain in successful binding order; each source's
///   visible aliases correspond to its aliased declarations' indices and spans;
///   no export is ever bound. A rejected duplicate leaves both collections
///   unchanged.
/// - provides: an import inventory and its read-only namespace views.
/// - fails: an alias a source already binds is refused by bind.
/// - panics: allocation failure follows the allocator policy.
/// - executable: none — type refinements require the disabled logic feature;
///   bind checks list/namespace counts and append metadata.
///
/// # Adequacy
/// - hypothesis: L3 — distinct parsed aliases resolve to successive declaration
///   positions with an empty export. Repeating the same URI and alias still
///   refuses, preserves the entire state and leaves the next position
///   available; one alias in two sources binds in each.
/// - witness: `tests::namespace::source_import_reaches_the_namespace_engine_and_exposes_its_alias`
/// - witness: `import::tests::an_identical_import_is_still_a_duplicate_and_preserves_the_next_position`
/// - witness: `import::tests::each_source_binds_its_own_aliases`
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct ModuleImports<'source>
{
    /// The imports, in source order.
    declarations: Vec<ImportDeclaration<'source>>,
    /// The scope each source's aliases are bound in, to their imports'
    /// positions, tagged with the imports' bytes.
    scopes: BTreeMap<SourceIndex, Scope<ImportIndex, ByteSpan>>,
}

impl<'source> ModuleImports<'source>
{
    /// No import, and no scope.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn new() -> Self
    {
        Self::default()
    }

    /// The imports, in source order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn declarations(&self) -> &[ImportDeclaration<'source>]
    {
        &self.declarations
    }

    /// The scope `source`'s aliases are bound in.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the scope of every alias `source` binds;
    ///   [`alias_scope::Absent::Unaliased`] when it binds none.
    /// - provides: the namespace view an alias resolves through.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — two sources binding one alias each answer their own,
    ///   and a source binding none answers unaliased.
    /// - witness: `import::tests::each_source_binds_its_own_aliases`
    #[inline]
    #[spec(ensures: |ret| matches!(ret, Maybe::Absent(_)) != self.scopes.contains_key(&source))]
    pub fn scope(
        &self,
        source: SourceIndex,
    ) -> Maybe<&Scope<ImportIndex, ByteSpan>, alias_scope::Absent>
    {
        self.scopes.get(&source).map_or(
            Maybe::Absent(alias_scope::Absent::Unaliased),
            Maybe::Present,
        )
    }

    /// The import `source` binds `alias` to.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the declaration whose alias `alias` is among `source`'s
    ///   imports; [`aliased::Absent::Unbound`] when none is.
    /// - provides: the qualifier a path `alias.Name` is resolved through.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — one alias bound in two sources answers each source's
    ///   own import, and an alias another source binds answers nothing.
    /// - witness: `import::tests::each_source_binds_its_own_aliases`
    #[inline]
    #[spec(ensures: |ret| match ret {
        Maybe::Present(found) => found.source == source && found.binding == ImportBinding::Aliased(alias),
        Maybe::Absent(_) => true,
    })]
    pub fn aliased(
        &self,
        source: SourceIndex,
        alias: SurfaceName<'source>,
    ) -> Maybe<&ImportDeclaration<'source>, aliased::Absent>
    {
        let Maybe::Present(scope) = self.scope(source)
        else {
            return Maybe::Absent(aliased::Absent::Unbound);
        };
        let path = NamePath::from(Vec::from([Segment::from(alias.as_ref())]));
        match scope.resolve(&path) {
            Maybe::Present(bound) => self
                .declarations
                .get(usize::from(bound.data))
                .map_or(Maybe::Absent(aliased::Absent::Unbound), Maybe::Present),
            Maybe::Absent(_) => Maybe::Absent(aliased::Absent::Unbound),
        }
    }

    /// The imports `source` writes, in source order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn of(
        &self,
        source: SourceIndex,
    ) -> impl Iterator<Item = &ImportDeclaration<'source>>
    {
        self.declarations
            .iter()
            .filter(move |declaration| declaration.source == source)
    }

    /// Keep `declaration`, binding its alias, when it has one, in its
    /// source's scope.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: on success the declaration is the last kept, at position `n`
    ///   for the `n` kept before it; an aliased one's source scope binds its
    ///   alias to that position, tagged with its bytes, and no export is ever
    ///   touched. The binding is the import's root binding run through
    ///   [`Modifier::alias_as`] and imported under a policy that refuses every
    ///   shadow. An unqualified import binds no alias.
    /// - provides: the import collection.
    /// - fails: [`LoweringRefusal::DuplicateImportAlias`] at the declaration's
    ///   bytes, naming the first import's, when an earlier import of its source
    ///   binds the alias; the declarations and the scopes are left as they
    ///   were.
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoweringRefusal::DuplicateImportAlias`] for an alias already bound.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — parsed imports retain URI, alias, span and visible
    ///   position. A duplicate names both sources; an identical URI does not
    ///   bypass refusal or consume the next position; one alias in two sources
    ///   binds in each. Witnesses check the exact bindings and the complete
    ///   rejected state.
    /// - witness: `tests::namespace::source_import_reaches_the_namespace_engine_and_exposes_its_alias`
    /// - witness: `tests::namespace::an_import_binds_its_alias_and_resolves_no_address`
    /// - witness: `tests::namespace::duplicate_source_import_alias_is_rejected_as_a_shadow`
    /// - witness: `tests::namespace::duplicate_source_import_alias_becomes_a_refusal`
    /// - witness: `import::tests::an_identical_import_is_still_a_duplicate_and_preserves_the_next_position`
    /// - witness: `import::tests::each_source_binds_its_own_aliases`
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            spec_clause_traversal,
            reason = "bounded: an accepted import is checked at the appended declaration; only a refused duplicate scans the module's imports, once, for the first binding of its alias"
        )
    )]
    #[spec(
        captures: before = (self.declarations.len(), declaration.binding, declaration.span),
        ensures: |ret| {
            self.scopes.values().all(|scope| usize::from(scope.export().binding_count()) == 0_usize)
                && match ret {
                    | Ok(()) => {
                        before.0.checked_add(1_usize) == Some(self.declarations.len())
                            && self
                                .declarations
                                .last()
                                .is_some_and(|last| (last.binding, last.span) == (before.1, before.2))
                    },
                    | Err(LoweringRefusal::DuplicateImportAlias { span, alias, first }) => {
                        self.declarations.len() == before.0
                            && (span, ImportBinding::Aliased(alias)) == (before.2, before.1)
                            && self.declarations.iter().any(|held| {
                                held.binding == ImportBinding::Aliased(alias) && held.span == first
                            })
                    },
                    | Err(_) => false,
                }
        },
    )]
    #[inline]
    pub fn bind(
        &mut self,
        declaration: ImportDeclaration<'source>,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let ImportBinding::Aliased(written) = declaration.binding
        else {
            self.declarations.push(declaration);
            return Ok(());
        };
        let index = ImportIndex(self.declarations.len());
        let alias = Segment::from(written.as_ref());
        let mut root = Trie::empty();
        let _fresh = root.insert(&NamePath::root(), Binding::new(index, declaration.span));
        let mut policy = OneSource;
        let mut scope = self
            .scopes
            .get(&declaration.source)
            .cloned()
            .unwrap_or_default();
        let bound = match Modifier::alias_as(alias.clone()).apply(root, &mut policy) {
            Ok(qualified) => scope.import_subtree(&NamePath::root(), qualified, &mut policy),
            Err(rejection) => Err(ScopeError::from(rejection)),
        };
        if let Err(_shadowed) = bound {
            let path = NamePath::from(Vec::from([alias]));
            let first = match self.scope(declaration.source) {
                Maybe::Present(held) => match held.resolve(&path) {
                    Maybe::Present(binding) => binding.tag,
                    Maybe::Absent(_) => declaration.span,
                },
                Maybe::Absent(_) => declaration.span,
            };
            return Err(LoweringRefusal::DuplicateImportAlias {
                span: declaration.span,
                alias: written,
                first,
            });
        }
        let _replaced = self.scopes.insert(declaration.source, scope);
        self.declarations.push(declaration);
        Ok(())
    }
}

/// The import policy: every shadow is refused, every other event is inert.
///
/// # Specification
/// - requires: namespace operations supply their event path and collision.
/// - ensures: every shadow is refused; other events leave the import
///   transformation unchanged.
/// - provides: the one-source-per-alias policy used by `ModuleImports`.
/// - fails: shadow callbacks return a typed rejection at the offered path.
/// - panics: allocation failure follows the allocator policy.
/// - executable: none — this stateless policy has no event payload to inspect;
///   the shadow callback checks its typed rejection.
///
/// # Adequacy
/// - hypothesis: L3 — distinct imports succeed, while both different and
///   identical URI duplicates dispatch a refusal. These import scenarios do not
///   enumerate arbitrary modifier hooks, whose implementation forwards its
///   subject.
/// - witness: `tests::namespace::duplicate_source_import_alias_is_rejected_as_a_shadow`
/// - witness: `import::tests::an_identical_import_is_still_a_duplicate_and_preserves_the_next_position`
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
struct OneSource;

impl NamespaceEventHandler<ImportIndex, ByteSpan> for OneSource
{
    type Label = ();

    /// Continue: an import's root binding is never empty.
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

    /// Refuse: one alias names one source.
    ///
    /// # Specification
    /// - requires: nothing; every collision is refused, even when its bindings
    ///   have equal payloads.
    /// - ensures: a Shadow rejection at the supplied path, with `ONE_SOURCE` as
    ///   its reason.
    /// - provides: duplicate-alias refusal without choosing either binding.
    /// - fails: always returns the typed shadow rejection.
    /// - panics: allocation failure follows the allocator policy.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — duplicate aliases with different and identical URIs
    ///   dispatch this callback. Enforcement checks event kind, path and
    ///   reason; the public refusal observes both source spans and unchanged
    ///   import state.
    /// - witness: `tests::namespace::duplicate_source_import_alias_is_rejected_as_a_shadow`
    /// - witness: `import::tests::an_identical_import_is_still_a_duplicate_and_preserves_the_next_position`
    ///
    /// # Errors
    /// Always, a shadow rejection at `path` for [`ONE_SOURCE`].
    #[spec(
        ensures: |ret| {
            ret.as_ref().is_err_and(|rejection| {
                rejection.kind() == EventKind::Shadow
                    && rejection.path() == path
                    && rejection.reason().as_ref() == ONE_SOURCE
            })
        },
    )]
    #[inline]
    fn shadow(
        &mut self,
        path: &NamePath,
        _collision: Collision<ImportIndex, ByteSpan>,
    ) -> Result<Binding<ImportIndex, ByteSpan>, EventRejection>
    {
        Err(EventRejection::new(
            EventKind::Shadow,
            path.clone(),
            RejectionReason::from(ONE_SOURCE),
        ))
    }

    /// Run the identity: no import modifier carries a hook.
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
        subject: Trie<ImportIndex, ByteSpan>,
    ) -> Result<Trie<ImportIndex, ByteSpan>, EventRejection>
    {
        Ok(subject)
    }
}

#[cfg(test)]
mod tests
{
    use alloc::string::String;

    use gandr_surface_syntax::ByteOffset;
    use gandr_surface_syntax::ByteSpan;
    use quenchant_shape::shape::Maybe;

    use super::ImportBinding;
    use super::ImportDeclaration;
    use super::ImportIndex;
    use super::ImportResolution;
    use super::ImportUri;
    use super::ModuleImports;
    use crate::error::LoweringRefusal;
    use crate::fixture::span;
    use crate::namespace::Binding;
    use crate::namespace::NamePath;
    use crate::namespace::Segment;
    use crate::resolve::SurfaceName;
    use crate::unit::SourceIndex;

    #[test]
    fn an_identical_import_is_still_a_duplicate_and_preserves_the_next_position()
    {
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));
        let aliased = |uri: &str, alias: &'static str, at: ByteSpan, source: usize| {
            ImportDeclaration::new(
                ImportUri::from(String::from(uri)),
                ImportBinding::Aliased(SurfaceName::from(alias)),
                at,
                SourceIndex::from(source),
                ImportResolution::Foreign,
            )
        };
        let first = at(0_usize, 10_usize);
        let repeated = at(11_usize, 21_usize);
        let later = at(22_usize, 32_usize);
        let mut imports = ModuleImports::new();
        imports
            .bind(aliased("file:///same.gandr", "same", first, 0_usize))
            .unwrap();
        let before = imports.clone();
        assert_eq!(
            imports.bind(aliased("file:///same.gandr", "same", repeated, 0_usize)),
            Err(LoweringRefusal::DuplicateImportAlias {
                span: repeated,
                alias: SurfaceName::from("same"),
                first,
            })
        );
        assert_eq!(imports, before);
        imports
            .bind(aliased("file:///next.gandr", "next", later, 0_usize))
            .unwrap();
        let next = NamePath::from(alloc::vec::Vec::from([Segment::from("next")]));
        let Maybe::Present(scope) = imports.scope(SourceIndex::from(0_usize))
        else {
            panic!("the source binds aliases");
        };
        assert_eq!(
            scope.resolve(&next),
            Maybe::Present(&Binding::new(ImportIndex::from(1_usize), later))
        );
        assert_eq!(imports.declarations().len(), 2_usize);
        assert_eq!(
            imports.declarations().last().unwrap().uri().as_ref(),
            "file:///next.gandr"
        );
        assert_eq!(usize::from(scope.export().binding_count()), 0_usize);
    }

    #[test]
    fn each_source_binds_its_own_aliases()
    {
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));
        let aliased = |uri: &str, alias: &'static str, at: ByteSpan, source: usize| {
            ImportDeclaration::new(
                ImportUri::from(String::from(uri)),
                ImportBinding::Aliased(SurfaceName::from(alias)),
                at,
                SourceIndex::from(source),
                ImportResolution::Foreign,
            )
        };
        let mut imports = ModuleImports::new();
        imports
            .bind(aliased("./a.gandr", "m", at(0_usize, 5_usize), 0_usize))
            .unwrap();
        imports
            .bind(aliased("./b.gandr", "m", at(10_usize, 15_usize), 1_usize))
            .unwrap();
        imports
            .bind(ImportDeclaration::new(
                ImportUri::from(String::from("./c.gandr")),
                ImportBinding::Unqualified,
                at(16_usize, 20_usize),
                SourceIndex::from(1_usize),
                ImportResolution::Foreign,
            ))
            .unwrap();
        let named = |source: usize| match imports
            .aliased(SourceIndex::from(source), SurfaceName::from("m"))
        {
            Maybe::Present(found) => Some(found.uri().as_ref()),
            Maybe::Absent(_) => None,
        };
        assert_eq!(named(0_usize), Some("./a.gandr"));
        assert_eq!(named(1_usize), Some("./b.gandr"));
        assert_eq!(named(2_usize), None);
        assert!(matches!(
            imports.scope(SourceIndex::from(2_usize)),
            Maybe::Absent(super::alias_scope::Absent::Unaliased)
        ));
        assert_eq!(imports.of(SourceIndex::from(1_usize)).count(), 2_usize);
    }
}
