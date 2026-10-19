//! What a written name refers to: the binder or the declaration a use resolves
//! to, kept beside the type table as an index of the source's uses.
//!
//! The lowering resolves every name once and keeps what it resolved to: a
//! variable the span of its binder ([`OriginTable::bindings`]), a declaration's
//! use the constant it admits, a written type head the family it names, a
//! constructor its family and tag. [`Referents::of`] reads those records once
//! per table, so a face answering a definition request looks the use up rather
//! than resolving the name again.
//!
//! # Items
//!
//! - **A variable** refers to the binder the origin table records for it, named
//!   and extended by the binder's span.
//! - **A declaration's use**, a written type naming a family and a constructor
//!   written in a term refer to the declaration the lowering assembled for the
//!   constant: named by its name tile ([`LoweredDeclaration::named`]), extended
//!   by its declaring form. A constructor refers to its own name tile in the
//!   family's declaration.
//! - **A constructor pattern's name** refers to the constructor its family and
//!   tag name, read off the scrutinee's type as the hover types it.
//!
//! A referent may stand in a sibling the source imports: it names the unit's
//! source and its span in that source's own text.
//!
//! [`OriginTable::bindings`]: gandr_surface_lowering::OriginTable::bindings
//! [`LoweredDeclaration::named`]: gandr_surface_lowering::LoweredDeclaration::named

use alloc::collections::BTreeMap;
use alloc::vec::Vec;

use anodized::spec;
use gandr_core_term::ConstructorTag;
use gandr_core_term::CoreArena;
use gandr_core_term::Value;
use gandr_core_term::ValueType;
use gandr_kernel_term::ConstantIndex;
use gandr_surface_lowering::LoweredModule;
use gandr_surface_lowering::Provenance;
use gandr_surface_lowering::Role;
use gandr_surface_lowering::SourceIndex;
use gandr_surface_lowering::Unit;
use gandr_surface_lowering::description::written::WrittenConstructor;
use gandr_surface_syntax::ByteOffset;
use gandr_surface_syntax::ByteSpan;
use quenchant_shape::shape::Maybe;

quenchant_shape::reason_enum! {
    /// Why a position refers to nothing.
    pub mod referred {
        /// The reason no referent is answered.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// No written use the lowering resolved holds the position.
            Unreferred,
        }
    }
}

/// Where the unit writes what a use refers to: the source holding it, the
/// name, and the whole binder or declaration form, each span in that source's
/// own text.
///
/// # Specification
/// - requires: answered by [`super::TypeTable::referent`] or
///   [`super::TypeTable::type_referents`].
/// - ensures: `named` lies inside `extent`, both in the text of `source`.
/// - panics: none.
/// - executable: none — a carrier; [`Referents::of`] states what it holds.
///
/// # Adequacy
/// - hypothesis: L3 — as [`Referents::of`].
/// - witness: `typed::tests::a_use_refers_to_its_binder_and_its_declaration_795`
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Referent
{
    /// The unit's source writing it.
    source: SourceIndex,
    /// The name's bytes.
    named: ByteSpan,
    /// The binder's or the declaring form's bytes.
    extent: ByteSpan,
}

impl Referent
{
    /// The unit's source writing it.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn source(&self) -> SourceIndex
    {
        self.source
    }

    /// The name's bytes in its source's own text.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn named(&self) -> ByteSpan
    {
        self.named
    }

    /// The binder's or the declaring form's bytes in its source's own text.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn extent(&self) -> ByteSpan
    {
        self.extent
    }
}

/// What a declared name names, which decides where it may be written.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum NameKind
{
    /// A data family: written as a type.
    Family,
    /// A family's constructor: written as a value or a pattern's head.
    Constructor,
    /// Any other declaration: written as a value.
    Value,
}

/// What a use refers to, and whether that is a family a type names.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct Target
{
    /// Where the referent is written.
    referent: Referent,
    /// Whether the use is a written type naming a data family.
    family: bool,
}

impl Target
{
    /// Where the referent is written.
    ///
    /// # Specification
    /// trivial.
    pub(super) const fn referent(&self) -> Referent
    {
        self.referent
    }

    /// The referent, when the use is a written type naming a data family.
    ///
    /// # Specification
    /// trivial.
    pub(super) const fn family(&self) -> Option<Referent>
    {
        if self.family {
            Some(self.referent)
        }
        else {
            None
        }
    }
}

/// The uses of one source, each with what it refers to, and every
/// declaration's referent by the constant it admits.
///
/// # Specification
/// - requires: built by [`Referents::of`].
/// - ensures: the uses ascend by start, each span in the source's own text;
///   `widest` is at least the width of every use; the declarations ascend by
///   constant; the offered names ascend by referent.
/// - panics: none.
/// - executable: none — a carrier; [`Referents::of`] and [`Referents::at`]
///   carry the predicates.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub(super) struct Referents
{
    /// Each use, with what it refers to.
    uses: Vec<(ByteSpan, Target)>,
    /// The widest use's width in bytes.
    widest: usize,
    /// Each declaration's referent, by the constant it admits.
    declarations: Vec<(ConstantIndex, Referent)>,
    /// Each name the unit declares, a family's constructors included, with
    /// what it names.
    offered: Vec<(Referent, NameKind)>,
}

/// `span`, a span of the unit's text, as the source holding its start writes
/// it, with that source.
///
/// # Specification
/// trivial.
fn placed(
    unit: &Unit,
    span: ByteSpan,
) -> Option<(SourceIndex, ByteSpan)>
{
    let source = unit.source_at(span.start());
    let start = unit.sources().get(usize::from(source))?.start();
    Some((source, moved(span, start)?))
}

/// `span` moved back by `base` bytes, when it starts at or past `base`.
///
/// # Specification
/// trivial.
fn moved(
    span: ByteSpan,
    base: ByteOffset,
) -> Option<ByteSpan>
{
    let start = usize::from(span.start()).checked_sub(usize::from(base))?;
    let end = usize::from(span.end()).checked_sub(usize::from(base))?;
    ByteSpan::new(ByteOffset::from(start), ByteOffset::from(end)).ok()
}

impl Referents
{
    /// The uses `module`, lowered into `arena` over `unit`, writes in its
    /// source starting at `base`, each with what it refers to.
    ///
    /// # Specification
    /// - requires: `module` was lowered into `arena` over `unit`, `base` starts
    ///   the source the table is of, `patterns` holds each constructor
    ///   pattern's name span with the family and tag its scrutinee's type gives
    ///   it, and `hidden` the forms whose sites answer nothing.
    /// - ensures: a use is kept when the source wrote it at or past `base` and
    ///   inside no `hidden` form, at its span moved back by `base`: each
    ///   written variable the origin table records a binder for, referring to
    ///   that binder; each written value that is a constant, and each written
    ///   type naming a data family, referring to the declaration admitting the
    ///   constant, by its name tile and its declaring form; each written
    ///   constructor value and each of `patterns`, referring to the name tile
    ///   the family's declaration writes for the tag, extended by the family's
    ///   form. A referent's spans are in the text of the source holding it. A
    ///   use whose referent no record places is not kept.
    /// - provides: the index a definition request answers from.
    /// - fails: never.
    /// - panics: none.
    /// - intension: one pass over each origin record and each declaration.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a parameter's use, a declaration's use, a family
    ///   written in a signature, a constructor in a term and in a pattern, and
    ///   an imported declaration's use each refer to their own site; a position
    ///   in no use refers to nothing.
    /// - witness: `typed::tests::a_use_refers_to_its_binder_and_its_declaration_795`
    /// - witness: `typed::tests::an_imported_name_refers_to_its_sibling_795`
    #[spec(ensures: |ret| ret.uses.windows(2).all(|pair| matches!(*pair, [(first, _), (second, _)] if first.start() <= second.start()))
        && ret.uses.iter().all(|&(span, _)| usize::from(span.end()).saturating_sub(usize::from(span.start())) <= ret.widest))]
    pub(super) fn of(
        module: &LoweredModule<'_>,
        arena: &CoreArena,
        unit: &Unit,
        base: ByteOffset,
        patterns: &[(ByteSpan, ConstantIndex, ConstructorTag)],
        hidden: &[ByteSpan],
    ) -> Self
    {
        let origins = module.origins();
        let mut declarations: Vec<(ConstantIndex, Referent)> = module
            .declarations()
            .iter()
            .filter_map(|declaration| {
                let (source, named) = placed(unit, declaration.named())?;
                let (_, extent) = placed(unit, declaration.span())?;
                Some((declaration.constant(), Referent {
                    source,
                    named,
                    extent,
                }))
            })
            .collect();
        declarations.sort_by_key(|&(constant, _)| constant);
        declarations.dedup_by_key(|&mut (constant, _)| constant);
        let declared = |constant: ConstantIndex| {
            declarations
                .binary_search_by_key(&constant, |&(held, _)| held)
                .ok()
                .and_then(|at| declarations.get(at))
                .map(|&(_, referent)| referent)
        };
        // Each family's constructors by tag, where its declaration writes them:
        // the described or native family whose name tile is the declaration's.
        let mut written: BTreeMap<ByteSpan, &[WrittenConstructor]> = BTreeMap::new();
        let descriptions = module.descriptions();
        for described in &descriptions.declarations {
            let _first = written
                .entry(described.named.span)
                .or_insert(described.written.constructors.as_slice());
        }
        for native in &descriptions.natives {
            let _first = written
                .entry(native.named.span)
                .or_insert(native.written.constructors.as_slice());
        }
        // Each declared name, a family's constructors after it; an operation
        // or a loop's words is declared from its family's form and named by it.
        let mut offered: Vec<(Referent, NameKind)> = Vec::new();
        for declaration in module.declarations() {
            if matches!(declaration.role(), Role::Operation | Role::Words) {
                continue;
            }
            let (Some((source, named)), Some((_, extent))) = (
                placed(unit, declaration.named()),
                placed(unit, declaration.span()),
            )
            else {
                continue;
            };
            let constructors = written.get(&declaration.named());
            let declared = if constructors.is_some() {
                NameKind::Family
            }
            else {
                NameKind::Value
            };
            offered.push((
                Referent {
                    source,
                    named,
                    extent,
                },
                declared,
            ));
            for constructor in constructors.copied().unwrap_or_default() {
                if let Some((source, named)) = placed(unit, constructor.named) {
                    offered.push((
                        Referent {
                            source,
                            named,
                            extent,
                        },
                        NameKind::Constructor,
                    ));
                }
            }
        }
        offered.sort_unstable();
        offered.dedup_by_key(|&mut (referent, _)| referent);
        let constructed = |family: ConstantIndex, tag: ConstructorTag| {
            let declaration = module
                .declarations()
                .iter()
                .find(|declaration| declaration.constant() == family)?;
            let named = written
                .get(&declaration.named())?
                .get(usize::from(tag))?
                .named;
            let (source, named) = placed(unit, named)?;
            let (_, extent) = placed(unit, declaration.span())?;
            Some(Referent {
                source,
                named,
                extent,
            })
        };
        let mut uses: Vec<(ByteSpan, Target)> = Vec::new();
        let mut keep = |span: ByteSpan, referent: Option<Referent>, family: bool| {
            let Some(referent) = referent
            else {
                return;
            };
            if hidden
                .iter()
                .any(|form| form.start() <= span.start() && span.end() <= form.end())
            {
                return;
            }
            if let Some(span) = moved(span, base) {
                uses.push((span, Target { referent, family }));
            }
        };
        for &(variable, binder) in origins.bindings() {
            let Maybe::Present(origin) = origins.value(variable)
            else {
                continue;
            };
            if origin.provenance() != Provenance::Written {
                continue;
            }
            let referent = placed(unit, binder).map(|(source, named)| Referent {
                source,
                named,
                extent: named,
            });
            keep(origin.span(), referent, false);
        }
        for &(value, origin) in origins.values() {
            if origin.provenance() != Provenance::Written {
                continue;
            }
            match arena.value(value) {
                Some(&Value::Constant(constant)) => keep(origin.span(), declared(constant), false),
                Some(&Value::Constructor { datatype, tag, .. }) => {
                    if let Some(&ValueType::Data { declaration, .. }) = arena.value_type(datatype) {
                        keep(origin.span(), constructed(declaration, tag), false);
                    }
                },
                Some(_) | None => {},
            }
        }
        for &(ty, origin) in origins.value_types() {
            if origin.provenance() != Provenance::Written {
                continue;
            }
            if let Some(&ValueType::Data { declaration, .. }) = arena.value_type(ty) {
                keep(origin.span(), declared(declaration), true);
            }
        }
        for &(span, family, tag) in patterns {
            keep(span, constructed(family, tag), false);
        }
        uses.sort_by_key(|&(span, _)| (span.start(), span.end()));
        uses.dedup_by_key(|&mut (span, _)| span);
        let widest = uses
            .iter()
            .map(|&(span, _)| usize::from(span.end()).saturating_sub(usize::from(span.start())))
            .max()
            .unwrap_or(0_usize);
        Self {
            uses,
            widest,
            declarations,
            offered,
        }
    }

    /// Each name the unit declares, a family's constructors included, with
    /// what it names, ascending by referent.
    ///
    /// # Specification
    /// trivial.
    pub(super) fn offered(&self) -> &[(Referent, NameKind)]
    {
        &self.offered
    }

    /// The innermost use holding `offset`, and what it refers to.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: among the uses whose span starts at or before `offset` and
    ///   ends after it, the narrowest, the earliest among equals; none when no
    ///   use holds it.
    /// - provides: the use a reader pointing at `offset` means.
    /// - fails: never.
    /// - panics: none.
    /// - intension: a binary search for the uses starting at or before
    ///   `offset`, then a walk back over those no wider than the widest use.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a constructor nested inside another's arguments
    ///   answers itself, and the outer one answers at its own name.
    /// - witness: `typed::tests::a_use_refers_to_its_binder_and_its_declaration_795`
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            spec_clause_traversal,
            reason = "parity: the body walks the uses that can hold the offset once; the check walks every use once"
        )
    )]
    #[spec(ensures: |ret| {
        let holding = |span: ByteSpan| span.start() <= offset && offset < span.end();
        let width = |span: ByteSpan| usize::from(span.end()).saturating_sub(usize::from(span.start()));
        match ret {
            Some(&(span, _)) => holding(span)
                && self.uses.iter().filter(|&&(other, _)| holding(other)).all(|&(other, _)| width(other) >= width(span)),
            None => !self.uses.iter().any(|&(span, _)| holding(span)),
        }
    })]
    pub(super) fn at(
        &self,
        offset: ByteOffset,
    ) -> Option<&(ByteSpan, Target)>
    {
        let after = self
            .uses
            .partition_point(|&(span, _)| span.start() <= offset);
        let mut best: Option<&(ByteSpan, Target)> = None;
        for held in self.uses.get(.. after)?.iter().rev() {
            let (span, _) = *held;
            if usize::from(span.start()).saturating_add(self.widest) <= usize::from(offset) {
                break;
            }
            if offset < span.end()
                && best.is_none_or(|&(chosen, _)| {
                    usize::from(span.end()).saturating_sub(usize::from(span.start()))
                        <= usize::from(chosen.end()).saturating_sub(usize::from(chosen.start()))
                })
            {
                best = Some(held);
            }
        }
        best
    }

    /// The referent of the declaration admitting `constant`.
    ///
    /// # Specification
    /// trivial.
    pub(super) fn declared(
        &self,
        constant: ConstantIndex,
    ) -> Option<Referent>
    {
        self.declarations
            .binary_search_by_key(&constant, |&(held, _)| held)
            .ok()
            .and_then(|at| self.declarations.get(at))
            .map(|&(_, referent)| referent)
    }
}
