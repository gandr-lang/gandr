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
    /// - hypothesis: L3 — two imports kept and bound in order, a second import
    ///   of one alias refused naming both, each asserted exactly over the
    ///   parsed source.
    /// - witness: `namespace::namespace::source_import_reaches_the_namespace_engine_and_exposes_its_alias`
    /// - witness: `namespace::namespace::an_import_binds_its_alias_and_resolves_no_address`
    /// - witness: `namespace::namespace::duplicate_source_import_alias_is_rejected_as_a_shadow`
    /// - witness: `namespace::namespace::duplicate_source_import_alias_becomes_a_refusal`
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
    /// trivial.
    ///
    /// # Errors
    /// Always, a shadow rejection at `path` for [`ONE_SOURCE`].
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
