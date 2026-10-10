//! Imports: `import "URI" as name ;`, kept as a source-ordered declaration
//! and bound by its alias in the module's import scope.
//!
//! An import resolves no address. Its URI is kept decoded, as written, for
//! the pass that will resolve it. What the lowering does now is the namespace
//! half: the import's own namespace is one binding at the root, the import's
//! position, and `as name` is [`Modifier::alias_as`] — the checked
//! `renaming . name` — run over it before the result is imported into the
//! module's import scope. The scope's visible namespace then answers each
//! alias with the import it names, and its export stays empty, because an
//! import is not a re-export.
//!
//! # One alias, one source
//!
//! The import scope is settled by a policy that refuses every shadow, so two
//! imports binding one alias refuse the module, naming both, rather than a
//! later import silently hiding an earlier one.

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

/// One `import "URI" as name ;`, as the source wrote it.
///
/// # Specification
/// - requires: the caller supplies a decoded URI, alias and source span
///   belonging to the same import declaration.
/// - ensures: all three components are retained without resolving the URI.
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
/// - witness: `namespace::namespace::an_import_binds_its_alias_and_resolves_no_address`
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ImportDeclaration<'source>
{
    /// The address the import names.
    uri: ImportUri,
    /// The alias it binds.
    alias: SurfaceName<'source>,
    /// The bytes the import covers.
    span: ByteSpan,
}

impl<'source> ImportDeclaration<'source>
{
    /// The import of `uri` as `alias`, written over `span`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn new(
        uri: ImportUri,
        alias: SurfaceName<'source>,
        span: ByteSpan,
    ) -> Self
    {
        Self { uri, alias, span }
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

    /// The alias the import binds.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn alias(&self) -> SurfaceName<'source>
    {
        self.alias
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
}

/// A module's imports: the declarations in source order, and the scope their
/// aliases are bound in.
///
/// # Specification
/// - requires: nothing; the empty collection starts with an empty scope.
/// - ensures: declarations remain in successful binding order; visible aliases
///   correspond to their declaration indices and spans; the export remains
///   empty. A rejected duplicate leaves both collections unchanged.
/// - provides: an import inventory and its read-only namespace view.
/// - fails: duplicate aliases are refused by bind, without address lookup.
/// - panics: allocation failure follows the allocator policy.
/// - executable: none — type refinements require the disabled logic feature;
///   bind checks list/namespace counts and append metadata.
///
/// # Adequacy
/// - hypothesis: L3 — distinct parsed aliases resolve to successive declaration
///   positions with an empty export. Repeating the same URI and alias still
///   refuses, preserves the entire state and leaves the next position
///   available.
/// - witness: `namespace::namespace::source_import_reaches_the_namespace_engine_and_exposes_its_alias`
/// - witness: `import::tests::an_identical_import_is_still_a_duplicate_and_preserves_the_next_position`
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct ModuleImports<'source>
{
    /// The imports, in source order.
    declarations: Vec<ImportDeclaration<'source>>,
    /// The scope each alias is bound in, to its import's position, tagged
    /// with the import's bytes.
    scope: Scope<ImportIndex, ByteSpan>,
}

impl<'source> ModuleImports<'source>
{
    /// No import, and an empty scope.
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

    /// The scope the aliases are bound in.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn scope(&self) -> &Scope<ImportIndex, ByteSpan>
    {
        &self.scope
    }

    /// Bind `declaration`'s alias to its position, and keep it.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: on success the declaration is the last kept, at position `n`
    ///   for the `n` kept before it, and the visible namespace binds its alias
    ///   to that position, tagged with its bytes; the export is never touched.
    ///   The binding is the import's root binding run through
    ///   [`Modifier::alias_as`] and imported under a policy that refuses every
    ///   shadow.
    /// - provides: the import lowering: an alias in scope, no address resolved.
    /// - fails: [`LoweringRefusal::DuplicateImportAlias`] at the declaration's
    ///   bytes, naming the first import's, when an earlier import binds the
    ///   alias; the declarations and the scope are left as they were.
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoweringRefusal::DuplicateImportAlias`] for an alias already bound.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — parsed imports retain URI, alias, span and visible
    ///   position. A duplicate names both sources; an identical URI does not
    ///   bypass refusal or consume the next position. The predicate observes
    ///   counts and append metadata without cloning the namespace; witnesses
    ///   check the exact bindings and the complete rejected state.
    /// - witness: `namespace::namespace::source_import_reaches_the_namespace_engine_and_exposes_its_alias`
    /// - witness: `namespace::namespace::an_import_binds_its_alias_and_resolves_no_address`
    /// - witness: `namespace::namespace::duplicate_source_import_alias_is_rejected_as_a_shadow`
    /// - witness: `namespace::namespace::duplicate_source_import_alias_becomes_a_refusal`
    /// - witness: `import::tests::an_identical_import_is_still_a_duplicate_and_preserves_the_next_position`
    #[spec(
        captures: before = (self.declarations.len(), declaration.alias, declaration.span),
        ensures: |ret| {
            usize::from(self.scope.export().binding_count()) == 0_usize
                && usize::from(self.scope.visible().binding_count()) == self.declarations.len()
                && match ret {
                    | Ok(()) => {
                        before.0.checked_add(1_usize) == Some(self.declarations.len())
                            && self
                                .declarations
                                .last()
                                .is_some_and(|last| (last.alias, last.span) == (before.1, before.2))
                    },
                    | Err(LoweringRefusal::DuplicateImportAlias { span, alias, first }) => {
                        self.declarations.len() == before.0
                            && (span, alias) == (before.2, before.1)
                            && self
                                .declarations
                                .iter()
                                .any(|held| held.alias == alias && held.span == first)
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
        let index = ImportIndex(self.declarations.len());
        let alias = Segment::from(declaration.alias.as_ref());
        let mut root = Trie::empty();
        let _fresh = root.insert(&NamePath::root(), Binding::new(index, declaration.span));
        let mut policy = OneSource;
        let bound = match Modifier::alias_as(alias.clone()).apply(root, &mut policy) {
            | Ok(qualified) => self
                .scope
                .import_subtree(&NamePath::root(), qualified, &mut policy),
            | Err(rejection) => Err(ScopeError::from(rejection)),
        };
        if let Err(_shadowed) = bound {
            let first = match self.scope.resolve(&NamePath::from(Vec::from([alias]))) {
                | Maybe::Present(held) => held.tag,
                | Maybe::Absent(_) => declaration.span,
            };
            return Err(LoweringRefusal::DuplicateImportAlias {
                span: declaration.span,
                alias: declaration.alias,
                first,
            });
        }
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
/// - witness: `namespace::namespace::duplicate_source_import_alias_is_rejected_as_a_shadow`
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
    /// - witness: `namespace::namespace::duplicate_source_import_alias_is_rejected_as_a_shadow`
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
    use quenchant_shape::shape::Maybe;

    use super::ImportDeclaration;
    use super::ImportIndex;
    use super::ImportUri;
    use super::ModuleImports;
    use crate::error::LoweringRefusal;
    use crate::fixture::span;
    use crate::namespace::Binding;
    use crate::namespace::NamePath;
    use crate::namespace::Segment;
    use crate::resolve::SurfaceName;

    #[test]
    fn an_identical_import_is_still_a_duplicate_and_preserves_the_next_position()
    {
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));
        let first = at(0_usize, 10_usize);
        let repeated = at(11_usize, 21_usize);
        let later = at(22_usize, 32_usize);
        let mut imports = ModuleImports::new();
        imports
            .bind(ImportDeclaration::new(
                ImportUri::from(String::from("file:///same.gandr")),
                SurfaceName::from("same"),
                first,
            ))
            .unwrap();
        let before = imports.clone();
        assert_eq!(
            imports.bind(ImportDeclaration::new(
                ImportUri::from(String::from("file:///same.gandr")),
                SurfaceName::from("same"),
                repeated,
            )),
            Err(LoweringRefusal::DuplicateImportAlias {
                span: repeated,
                alias: SurfaceName::from("same"),
                first,
            })
        );
        assert_eq!(imports, before);
        imports
            .bind(ImportDeclaration::new(
                ImportUri::from(String::from("file:///next.gandr")),
                SurfaceName::from("next"),
                later,
            ))
            .unwrap();
        let next = NamePath::from(alloc::vec::Vec::from([Segment::from("next")]));
        assert_eq!(
            imports.scope().resolve(&next),
            Maybe::Present(&Binding::new(ImportIndex::from(1_usize), later))
        );
        assert_eq!(imports.declarations().len(), 2_usize);
        assert_eq!(
            imports.declarations().last().unwrap().uri().as_ref(),
            "file:///next.gandr"
        );
        assert_eq!(
            usize::from(imports.scope().export().binding_count()),
            0_usize
        );
    }
}
