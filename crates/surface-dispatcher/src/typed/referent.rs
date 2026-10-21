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
//! - **A declaration written in two halves**, a signature and a definition,
//!   refers by the half written first; the other half's name tile is kept as a
//!   use of it, and [`Referents::half`] answers either half's own site.
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
use gandr_surface_lowering::DeclarationOutcome;
use gandr_surface_lowering::HalfAt;
use gandr_surface_lowering::LoweredModule;
use gandr_surface_lowering::LoweringRefusal;
use gandr_surface_lowering::Provenance;
use gandr_surface_lowering::Resolution;
use gandr_surface_lowering::Role;
use gandr_surface_lowering::SourceIndex;
use gandr_surface_lowering::Unit;
use gandr_surface_lowering::described::DescribedUse;
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

/// Which half of a declared name a request asks for.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum DeclaredHalf
{
    /// The signature: where the name's type is declared.
    Signature,
    /// The definition: where the name's body is given.
    Definition,
}

/// The sites of a declaration's halves, each named by its own name tile and
/// extended by its own form.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
struct Halved
{
    /// The signature's site, when the name has one.
    signature: Option<Referent>,
    /// The definition's site, when the name has one.
    definition: Option<Referent>,
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
///   `widest` is at least the width of every use; `by_referent` holds the
///   narrowest use per written name and start, ascending by the name's source
///   and span then the use's; the declarations ascend by constant; the offered
///   names ascend by referent.
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
    /// The narrowest use per written name and start, by that name.
    by_referent: Vec<(Referent, ByteSpan)>,
    /// Each declaration's referent, by the constant it admits.
    declarations: Vec<(ConstantIndex, Referent)>,
    /// Each name the unit declares, a family's constructors included, with
    /// what it names.
    offered: Vec<(Referent, NameKind)>,
    /// The sites of each declaration's halves, by the declaration's referent.
    halves: Vec<(Referent, Halved)>,
    /// Each name the lowering refused as naming nothing, where its refusal of
    /// a declaration stands, ascending.
    unresolved: Vec<ByteSpan>,
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
    ///   it, `hidden` the forms whose sites answer nothing, and `members` each
    ///   theory member's written use the description reading kept.
    /// - ensures: a use is kept when the source wrote it at or past `base` and
    ///   inside no `hidden` form, at its span moved back by `base`: each
    ///   written variable the origin table records a binder for, referring to
    ///   that binder; each written value that is a constant, and each written
    ///   type naming a data family, referring to the declaration admitting the
    ///   constant, by its name tile and its declaring form; each written
    ///   constructor value and each of `patterns`, referring to the name tile
    ///   the family's declaration writes for the tag, extended by the family's
    ///   form; and each name the lowering's resolution record holds, a name of
    ///   a declaration it refused included, referring as the origin it would
    ///   have left does; the name tile of a declaration's half written after
    ///   the one introducing it, referring to the declaration; and each of
    ///   `members`, a theory member's written use, referring to the member's
    ///   name tile. A use both name at one span is kept once. Each
    ///   declaration's halves are kept at their own name tiles and forms. A
    ///   referent's spans are in the text of the source holding it. A use whose
    ///   referent no record places is not kept. Each declaration the lowering
    ///   refused for a name nothing declares or binds (`UnresolvedName`,
    ///   `UnresolvedTypeHead`) keeps that refusal's span, moved back by `base`
    ///   and inside no `hidden` form, as unresolved, ascending.
    /// - provides: the index a definition request answers from.
    /// - fails: never.
    /// - panics: none.
    /// - intension: one pass over each origin record, each resolution and each
    ///   declaration.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a parameter's use, a declaration's use, a family
    ///   written in a signature, a constructor in a term and in a pattern, and
    ///   an imported declaration's use each refer to their own site; a position
    ///   in no use refers to nothing; a constructor and a call's head in a
    ///   declaration the lowering refused refer to their sites. A declaration
    ///   refused as shadowing an import refers nowhere inside it while a use
    ///   after it still refers, and a written variable refers to its binder, a
    ///   recursive call's head to the name it calls. A name nothing declares
    ///   beside a form refused as shadowing is kept as unresolved.
    /// - witness: `typed::tests::a_use_refers_to_its_binder_and_its_declaration_795`
    /// - witness: `typed::tests::an_imported_name_refers_to_its_sibling_795`
    /// - witness: `typed::tests::a_refused_declaration_s_uses_refer_to_their_sites_836`
    /// - witness: `typed::tests::a_declaration_refused_as_shadowing_answers_at_no_site_677`
    /// - witness: `typed::tests::a_name_ends_where_it_is_written`
    /// - witness: `typed::tests::a_recursive_call_s_head_refers_to_the_name_it_calls`
    /// - witness: `typed::tests::a_name_nothing_declares_is_kept_beside_a_form_refused_as_shadowing`
    #[spec(ensures: |ret| ret.uses.windows(2).all(|pair| matches!(*pair, [(first, _), (second, _)] if first.start() <= second.start()))
        && ret.uses.iter().all(|&(span, _)| usize::from(span.end()).saturating_sub(usize::from(span.start())) <= ret.widest))]
    pub(super) fn of(
        module: &LoweredModule<'_>,
        arena: &CoreArena,
        unit: &Unit,
        base: ByteOffset,
        patterns: &[(ByteSpan, ConstantIndex, ConstructorTag)],
        hidden: &[ByteSpan],
        members: &[DescribedUse],
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
        // Each declaration's halves at their own sites, and the name tile of a
        // half written after the one that introduced the name, kept below as a
        // use of the declaration.
        let site = |half: Maybe<HalfAt, _>| {
            let Maybe::Present(half) = half
            else {
                return None;
            };
            let (source, named) = placed(unit, half.named)?;
            let (_, extent) = placed(unit, half.span)?;
            Some(Referent {
                source,
                named,
                extent,
            })
        };
        let mut halves: Vec<(Referent, Halved)> = Vec::new();
        let mut seconds: Vec<(ByteSpan, ConstantIndex)> = Vec::new();
        for declaration in module.declarations() {
            let Some(referent) = declared(declaration.constant())
            else {
                continue;
            };
            let written = declaration.halves();
            for half in [written.signature, written.definition] {
                if let Maybe::Present(half) = half
                    && half.named != declaration.named()
                {
                    seconds.push((half.named, declaration.constant()));
                }
            }
            halves.push((referent, Halved {
                signature: site(written.signature),
                definition: site(written.definition),
            }));
        }
        halves.sort_unstable_by_key(|&(referent, _)| referent);
        halves.dedup_by_key(|&mut (referent, _)| referent);
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
        // A constructor's result names its family at its head, and each
        // argument repeating a parameter names that parameter's binder; the
        // lowering mints neither, the family being the constructor's own.
        for declaration in module.declarations() {
            let Some(constructors) = written.get(&declaration.named())
            else {
                continue;
            };
            for constructor in *constructors {
                keep(constructor.head, declared(declaration.constant()), true);
                for repeated in &constructor.parameters {
                    let binder = placed(unit, repeated.named).map(|(source, named)| Referent {
                        source,
                        named,
                        extent: named,
                    });
                    keep(repeated.span, binder, false);
                }
            }
        }
        // A name the lowering resolved keeps its use though the declaration
        // holding it was refused and emitted no origin for it.
        for &(span, resolution) in module.resolutions() {
            let referent = match resolution {
                Resolution::Binder(binder) => {
                    placed(unit, binder).map(|(source, named)| Referent {
                        source,
                        named,
                        extent: named,
                    })
                },
                Resolution::Declaration(constant) => declared(constant),
                Resolution::Constructor { named, family } => placed(unit, named)
                    .zip(declared(family))
                    .map(|((source, named), family)| Referent {
                        source,
                        named,
                        extent: family.extent,
                    }),
            };
            keep(span, referent, false);
        }
        for &(span, constant) in &seconds {
            keep(span, declared(constant), false);
        }
        // A theory member's use, by the member's name tile.
        for member in members {
            let referent = placed(unit, member.named).map(|(source, named)| Referent {
                source,
                named,
                extent: named,
            });
            keep(member.span, referent, false);
        }
        // A name nothing declares or binds, where the lowering's refusal of the
        // declaration writing it stands.
        let mut unresolved: Vec<ByteSpan> = module
            .declarations()
            .iter()
            .filter_map(|declaration| {
                if let DeclarationOutcome::Refused(
                    LoweringRefusal::UnresolvedName { span, .. }
                    | LoweringRefusal::UnresolvedTypeHead { span, .. },
                ) = declaration.outcome()
                    && !hidden
                        .iter()
                        .any(|form| form.start() <= span.start() && span.end() <= form.end())
                {
                    moved(span, base)
                }
                else {
                    None
                }
            })
            .collect();
        unresolved.sort_unstable();
        unresolved.dedup();
        uses.sort_by_key(|&(span, _)| (span.start(), span.end()));
        uses.dedup_by_key(|&mut (span, _)| span);
        let widest = uses
            .iter()
            .map(|&(span, _)| usize::from(span.end()).saturating_sub(usize::from(span.start())))
            .max()
            .unwrap_or(0_usize);
        let mut by_referent: Vec<(Referent, ByteSpan)> = uses
            .iter()
            .map(|&(span, target)| (target.referent, span))
            .collect();
        // A constructor applied keeps its name and its application as two uses
        // starting together; the narrower, kept first, is the name.
        by_referent.sort_unstable_by_key(|&(referent, span)| {
            (referent.source, referent.named, span.start(), span.end())
        });
        by_referent
            .dedup_by_key(|&mut (referent, span)| (referent.source, referent.named, span.start()));
        Self {
            uses,
            widest,
            by_referent,
            declarations,
            offered,
            halves,
            unresolved,
        }
    }

    /// The span of every use referring to the name written at `named` of
    /// `source`, one per start, ascending.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the narrowest of the uses starting at each offset whose
    ///   referent's source and name are `source` and `named`, ascending by
    ///   start: a recursive declaration's call refers to its name as a binder,
    ///   every other use as the declaration, and both are the one name; none
    ///   for a name no use refers to.
    /// - provides: what a highlight, a reference search and a rename read.
    /// - fails: never.
    /// - panics: none.
    /// - intension: two binary searches.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a parameter's uses, a recursive declaration's call
    ///   and a constructor's uses in a term and in a pattern are each found
    ///   once, and no use of another name is.
    /// - witness: `typed::tests::each_name_is_found_with_every_use_referring_to_it`
    #[spec(ensures: |ret| ret.iter().all(|&(held, _)| (held.source, held.named) == (source, named))
        && ret.windows(2).all(|pair| matches!(pair, [(_, earlier), (_, later)] if earlier.start() < later.start())))]
    pub(super) fn uses_of(
        &self,
        source: SourceIndex,
        named: ByteSpan,
    ) -> &[(Referent, ByteSpan)]
    {
        let key = (source, named);
        let first = self
            .by_referent
            .partition_point(|&(held, _)| (held.source, held.named) < key);
        let rest = self.by_referent.get(first ..).unwrap_or_default();
        let taken = rest.partition_point(|&(held, _)| (held.source, held.named) == key);
        rest.get(.. taken).unwrap_or_default()
    }

    /// The spans of the names the lowering refused as naming nothing, in the
    /// source's own text, ascending.
    ///
    /// # Specification
    /// trivial.
    pub(super) fn unresolved(&self) -> &[ByteSpan]
    {
        &self.unresolved
    }

    /// The referent whose name, written in `source`, holds `offset`: a
    /// declaration's, a constructor's, or a binder some use refers to.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a referent written in `source` whose name starts at or before
    ///   `offset` and ends after it, among the offered names and the referents
    ///   of the uses; none when no such name holds it.
    /// - provides: what a request at a declaring name means.
    /// - fails: never.
    /// - panics: none.
    /// - intension: a binary search in each of two sorted lists.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a declaration's name, a constructor's name and a used
    ///   parameter's name each answer themselves; a use answers nothing here; a
    ///   name holds no byte past its end.
    /// - witness: `typed::tests::each_name_is_found_with_every_use_referring_to_it`
    /// - witness: `typed::tests::a_name_ends_where_it_is_written`
    #[spec(ensures: |ret| ret.is_none_or(|found| found.source == source
        && found.named.start() <= offset && offset < found.named.end()))]
    pub(super) fn named_at(
        &self,
        source: SourceIndex,
        offset: ByteOffset,
    ) -> Option<Referent>
    {
        let holding = |referent: &Referent| {
            referent.source == source
                && referent.named.start() <= offset
                && offset < referent.named.end()
        };
        let before =
            |referent: &Referent| (referent.source, referent.named.start()) <= (source, offset);
        let offered = self
            .offered
            .partition_point(|&(referent, _)| before(&referent));
        let used = self
            .by_referent
            .partition_point(|&(referent, _)| before(&referent));
        offered
            .checked_sub(1_usize)
            .and_then(|at| self.offered.get(at))
            .map(|&(referent, _)| referent)
            .filter(holding)
            .or_else(|| {
                used.checked_sub(1_usize)
                    .and_then(|at| self.by_referent.get(at))
                    .map(|&(referent, _)| referent)
                    .filter(holding)
            })
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
    ///   answers itself, and the outer one answers at its own name; a use holds
    ///   no byte past its end, where what encloses it answers.
    /// - witness: `typed::tests::a_use_refers_to_its_binder_and_its_declaration_795`
    /// - witness: `typed::tests::a_name_ends_where_it_is_written`
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

    /// Every use lying wholly inside `within`, ascending by start, each with
    /// what it refers to.
    ///
    /// # Specification
    /// trivial.
    pub(super) fn within(
        &self,
        within: ByteSpan,
    ) -> impl Iterator<Item = &(ByteSpan, Target)>
    {
        let first = self
            .uses
            .partition_point(|&(span, _)| span.start() < within.start());
        self.uses
            .get(first ..)
            .unwrap_or_default()
            .iter()
            .take_while(move |&&(span, _)| span.start() < within.end())
            .filter(move |&&(span, _)| span.end() <= within.end())
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

    /// The site of the `half` of the declaration `referent` names: its own
    /// name tile and form; `referent` itself when it names no declaration or
    /// one with no such half.
    ///
    /// # Specification
    /// trivial.
    pub(super) fn half(
        &self,
        referent: Referent,
        half: DeclaredHalf,
    ) -> Referent
    {
        self.halves
            .binary_search_by_key(&referent, |&(held, _)| held)
            .ok()
            .and_then(|at| self.halves.get(at))
            .and_then(|&(_, halved)| match half {
                DeclaredHalf::Signature => halved.signature,
                DeclaredHalf::Definition => halved.definition,
            })
            .unwrap_or(referent)
    }
}
