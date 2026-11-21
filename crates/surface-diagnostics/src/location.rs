//! What a report reads of a checker refusal through the origin table, read
//! while a composition holds the arena.
//!
//! # A key names a node, and the arena locates it
//!
//! A report outlives the arena that its checker judged over. Its refusal and
//! its failure name each node by its content key, so two sessions that judge
//! one text report alike. Two nodes of one content share a key, so a key does
//! not locate a node in the source. A composition locates each refused
//! declaration while it holds the arena form and the origin table: the loci
//! that the refusal marks, the binder names and the locus of each frame of
//! its failure, the call whose implicit it names and the law that it names.
//! A report reads the located record, and never the origin table.
//!
//! The alternative was an origin table keyed by content key. Two nodes of one
//! content can stand at two places, so that table would hold one place for
//! both.

use alloc::collections::BTreeMap;
use alloc::string::String;
use alloc::vec::Vec;

use anodized::spec;
use gandr_core_checker::CheckRefusal;
use gandr_core_checker::Failure;
use gandr_core_checker::ModuleReport;
use gandr_kernel_term::ConstantIndex;
use gandr_surface_corpus::DeclarationReport;
use gandr_surface_corpus::Refusal;
use gandr_surface_corpus::RefusalOf;
use gandr_surface_corpus::SettleReport;
use gandr_surface_corpus::checker_refusal;
use gandr_surface_lowering::Omitted;
use gandr_surface_lowering::OriginTable;
use gandr_surface_syntax::ByteSpan;
use gandr_surface_syntax::SourceText;
use quenchant_shape::shape::Maybe;

use crate::frame::framed;
use crate::frame::opened;
use crate::locus::Annotations;
use crate::locus::node;
use crate::model::Locus;
use crate::model::binding;
use crate::model::context_locus;
use crate::report::report_span;

quenchant_shape::reason_enum! {
    /// Why a declaration has no located record, or a record names no call or
    /// law.
    pub mod locating {
        /// The reason nothing is located.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The declaration produced no checker refusal.
            Unrefused,
            /// The refusal names no such call or law, or the origin table
            /// records none for the node it names.
            Unrecorded,
        }
    }
}

/// One frame of a failure, located: the names of the binders that its rule
/// opened, and where its node stands in the source.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Frame
{
    /// The names of the binders the rule opened, outermost first, as
    /// [`opened`] reads them.
    pub binders: Vec<Maybe<String, binding::Absent>>,
    /// Where the node of the rule stands in the source.
    pub locus: Maybe<Locus, context_locus::Absent>,
}

/// What a report reads of one checker refusal through the origin table.
///
/// # Specification
/// - requires: built by [`Located::of`] from the arena form of the refusal and
///   of its failure.
/// - ensures: as [`Located::of`].
/// - panics: none.
/// - executable: none — this data type has no call boundary; [`Located::of`]
///   carries the predicates.
///
/// # Adequacy
/// - hypothesis: L3 — as [`Located::of`].
/// - witness: `tests::diagnostics::a_refused_declaration_is_located`
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Located
{
    /// The loci that the refusal marks.
    pub annotations: Annotations,
    /// The names of the binders that the failure stood under before its
    /// frames opened any, as [`framed`] reads them.
    pub framed: Vec<Maybe<String, binding::Absent>>,
    /// Each frame of the failure, outermost first; none when the body kept no
    /// failure.
    pub frames: Vec<Frame>,
    /// The call whose omitted implicit the refusal names.
    pub omitted: Maybe<Omitted, locating::Absent>,
    /// The law that the refusal names, as the source writes it.
    pub law: Maybe<gandr_theory_levitation::Name, locating::Absent>,
}

impl Located
{
    /// Locate `refusal` and its `failure` in the declaration that spans
    /// `declaration`, through `origins` over `text`.
    ///
    /// # Specification
    /// - requires: `refusal` and `failure` name nodes of the arena that
    ///   `origins` records; `text` is the source that `origins` measures.
    /// - ensures: the annotations are [`Annotations::refusal`] of `refusal`;
    ///   the hypotheses' names are [`framed`] of the failure, and each frame
    ///   holds [`opened`] of its obligation and the locus of its node, in the
    ///   order of the failure's obligations; the call is the one the origin
    ///   table records at the node an implicit or model refusal names, and the
    ///   law the one it records at a handler refusal's scope and rule.
    /// - provides: everything a report reads of the refusal through the origin
    ///   table.
    /// - fails: never; an unrecorded node leaves its part absent.
    /// - panics: none.
    ///
    /// # Cost
    /// - allocation: the omitted call and the frames, diagnostic
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a refused declaration's report marks the loci, the
    ///   contexts and the binder names that a report through the origin table
    ///   marked.
    /// - witness: `tests::diagnostics::a_refused_declaration_is_located`
    /// - witness: `tests::diagnostics::a_mismatch_under_a_binder_names_it`
    #[spec(ensures: |ret| ret.frames.len()
        == failure.as_ref().map_or(0_usize, |failure| failure.obligations().len()))]
    #[inline]
    #[must_use]
    pub fn of(
        refusal: CheckRefusal,
        failure: Option<&Failure>,
        declaration: ByteSpan,
        (origins, text): (&OriginTable, SourceText<'_>),
    ) -> Self
    {
        let omitted = if let CheckRefusal::ImplicitUnsolved { at, .. }
        | CheckRefusal::ModelUnanswered { at, .. }
        | CheckRefusal::ModelAmbiguous { at, .. } = refusal
        {
            match origins.omitted(at) {
                Maybe::Present(omitted) => Maybe::Present(omitted.clone()),
                Maybe::Absent(_) => Maybe::Absent(locating::Absent::Unrecorded),
            }
        }
        else {
            Maybe::Absent(locating::Absent::Unrecorded)
        };
        let law = if let CheckRefusal::HandlerUnlawful { at, rule, .. } = refusal {
            match origins.scope_law(at, rule) {
                Maybe::Present(law) => Maybe::Present(law.clone()),
                Maybe::Absent(_) => Maybe::Absent(locating::Absent::Unrecorded),
            }
        }
        else {
            Maybe::Absent(locating::Absent::Unrecorded)
        };
        let (named, frames) = failure.map_or_else(
            || (Vec::new(), Vec::new()),
            |failure| {
                let frames = failure
                    .obligations()
                    .iter()
                    .map(|obligation| Frame {
                        binders: opened(obligation, origins, text),
                        locus: match node(origins, obligation.at()) {
                            Maybe::Present(span) => match Locus::of(text, span) {
                                Maybe::Present(locus) => Maybe::Present(locus),
                                Maybe::Absent(_) => {
                                    Maybe::Absent(context_locus::Absent::OutsideText)
                                },
                            },
                            Maybe::Absent(_) => Maybe::Absent(context_locus::Absent::Unrecorded),
                        },
                    })
                    .collect();
                (framed(failure, origins), frames)
            },
        );
        Self {
            annotations: Annotations::refusal(RefusalOf::Checking(refusal), declaration, origins),
            framed: named,
            frames,
            omitted,
            law,
        }
    }

    /// The call whose omitted implicit the refusal names.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub const fn omitted(&self) -> Maybe<&Omitted, locating::Absent>
    {
        match self.omitted {
            Maybe::Present(ref omitted) => Maybe::Present(omitted),
            Maybe::Absent(reason) => Maybe::Absent(reason),
        }
    }

    /// The law that the refusal names, as the source writes it.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub const fn law(&self) -> Maybe<&gandr_theory_levitation::Name, locating::Absent>
    {
        match self.law {
            Maybe::Present(ref law) => Maybe::Present(law),
            Maybe::Absent(reason) => Maybe::Absent(reason),
        }
    }
}

/// The located record of each declaration of a module whose produced refusal
/// is a checker refusal, by the declaration's admission position.
///
/// # Specification
/// - requires: built by [`Locations::of`] or [`Locations::after`].
/// - ensures: each position keyed is a declaration whose produced refusal is a
///   checker refusal.
/// - panics: none.
/// - executable: none — this data type has no call boundary; [`Locations::of`]
///   carries the predicates.
///
/// # Adequacy
/// - hypothesis: L3 — as [`Located::of`].
/// - witness: `tests::diagnostics::a_refused_declaration_is_located`
#[repr(transparent)]
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Locations(BTreeMap<ConstantIndex, Located>);

impl Locations
{
    /// Locate each checker refusal that `report` settled, of the verdicts
    /// `verdicts`, and its failure, through `origins` over `text`.
    ///
    /// # Specification
    /// - requires: `report` settled `verdicts`, and `origins` records the arena
    ///   that `verdicts` judged over; `text` is the source that `origins`
    ///   measures.
    /// - ensures: one record per declaration whose produced refusal is a
    ///   checker refusal, [`Located::of`] the refusal that [`checker_refusal`]
    ///   gives and the failure that `verdicts` keeps.
    /// - provides: the located records a report reads in place of the origin
    ///   table.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Located::of`].
    /// - witness: `tests::diagnostics::a_refused_declaration_is_located`
    #[spec(ensures: |ret| ret.0.keys().all(|constant| report.declarations().iter().any(|declaration|
        declaration.constant() == *constant
            && matches!(declaration.produced().refusal(), Maybe::Present(Refusal::Checking(_))))))]
    #[inline]
    #[must_use]
    pub fn of(
        module: &gandr_surface_lowering::LoweredModule<'_>,
        report: &SettleReport<'_>,
        verdicts: &ModuleReport,
        (origins, text): (&OriginTable, SourceText<'_>),
    ) -> Self
    {
        Self(located(
            module,
            report.declarations(),
            verdicts,
            (origins, text),
        ))
    }

    /// [`Self::of`], `earlier` the records of a module whose declarations lead
    /// `module`'s, below `boundary`: only the declarations from `boundary` on
    /// are located.
    ///
    /// # Specification
    /// - requires: as [`Self::of`]; `earlier` is [`Self::of`] over the leading
    ///   module's report, and `boundary` its first position past them.
    /// - ensures: `earlier`'s records, and a record per declaration from
    ///   `boundary` on as [`Self::of`] makes it.
    /// - provides: a document's records at the cost of its own refusals.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Cost
    /// - allocation: the located refusals, diagnostic
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a document judged after a closure judged once locates
    ///   as on a fresh judgement of the closure.
    /// - witness: `tests::diagnostics::a_document_judged_after_its_closure_spells_as_the_whole_unit_776`
    #[spec(ensures: |ret| earlier.0.range(.. boundary).all(|(constant, record)| ret.0.get(constant) == Some(record)))]
    #[inline]
    #[must_use]
    pub fn after(
        earlier: &Self,
        boundary: ConstantIndex,
        module: &gandr_surface_lowering::LoweredModule<'_>,
        (report, verdicts): (&SettleReport<'_>, &ModuleReport),
        (origins, text): (&OriginTable, SourceText<'_>),
    ) -> Self
    {
        let declarations = report.declarations();
        let mut later = located(
            module,
            declarations
                .get(
                    declarations
                        .partition_point(|declaration| declaration.constant() < boundary) ..,
                )
                .unwrap_or_default(),
            verdicts,
            (origins, text),
        );
        later.extend(
            earlier
                .0
                .range(.. boundary)
                .map(|(&constant, record)| (constant, record.clone())),
        );
        Self(later)
    }

    /// The record of the declaration at `constant`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn get(
        &self,
        constant: ConstantIndex,
    ) -> Maybe<&Located, locating::Absent>
    {
        let Some(record) = self.0.get(&constant)
        else {
            return Maybe::Absent(locating::Absent::Unrefused);
        };
        Maybe::Present(record)
    }
}

/// The bytes that `refusal`, a checker refusal of the declaration that spans
/// `declaration`, blames, through `origins`.
///
/// # Specification
/// - requires: `refusal` names nodes of the arena that `origins` records.
/// - ensures: the span of the primary locus [`Annotations::refusal`] gives the
///   refusal, or the reason it gives none.
/// - provides: the site a formatter compares two refusals of one declaration
///   at.
/// - fails: never.
/// - panics: none.
/// - executable: none — the site is what the walk of the refusal's loci
///   answers, which a predicate would walk again.
///
/// # Adequacy
/// - hypothesis: L3 — as [`Annotations::refusal`].
/// - witness: `locus::tests::refusal_locations_keep_origin_families_and_missing_nodes_distinct`
#[inline]
pub fn blamed(
    refusal: CheckRefusal,
    declaration: ByteSpan,
    origins: &OriginTable,
) -> Maybe<ByteSpan, report_span::Absent>
{
    match Annotations::refusal(RefusalOf::Checking(refusal), declaration, origins).primary {
        Maybe::Present(annotation) => Maybe::Present(annotation.span),
        Maybe::Absent(reason) => Maybe::Absent(reason),
    }
}

/// [`Locations::of`] over `declarations`.
///
/// # Specification
/// - requires: as [`Locations::of`].
/// - ensures: as [`Locations::of`], of the declarations among `declarations`.
/// - fails: never.
/// - panics: none.
///
/// # Cost
/// - allocation: the located refusals, diagnostic
///
/// # Adequacy
/// - hypothesis: L3 — as [`Located::of`].
/// - witness: `tests::diagnostics::a_refused_declaration_is_located`
#[spec(ensures: |ret| ret.keys().all(|constant| declarations.iter().any(|declaration| declaration.constant() == *constant)))]
fn located(
    module: &gandr_surface_lowering::LoweredModule<'_>,
    declarations: &[DeclarationReport<'_>],
    verdicts: &ModuleReport,
    (origins, text): (&OriginTable, SourceText<'_>),
) -> BTreeMap<ConstantIndex, Located>
{
    declarations
        .iter()
        .filter(|declaration| {
            matches!(
                declaration.produced().refusal(),
                Maybe::Present(Refusal::Checking(_))
            )
        })
        .filter_map(|declaration| {
            let constant = declaration.constant();
            match checker_refusal(module, verdicts, constant) {
                Maybe::Present(refusal) => Some((
                    constant,
                    Located::of(
                        refusal,
                        verdicts.failures().get(&constant),
                        declaration.span(),
                        (origins, text),
                    ),
                )),
                Maybe::Absent(_) => None,
            }
        })
        .collect()
}
