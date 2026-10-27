//! The failures a module's refused bodies kept, and the spelling of every type
//! they and its checker refusals name, made while the arena they name is at
//! hand.
//!
//! # Spelled once, at the judgement
//!
//! A checker refusal and the failure the checking machine built for it name
//! type nodes of the arena the module was judged over, and the composition
//! moves that arena into the kernel admission once the module is judged. A
//! diagnostic is built before the admission runs or after it has consumed the
//! arena, so it cannot read the arena; the composition spells every type the
//! module's produced checker refusals compare and every type their failures
//! name — what each rule's term was checked against, the binders each rule
//! opened, the hypotheses in scope — through `gandr-surface-pretty` on a
//! [`SPELLING_WIDTH`]-column page, constants by their paths from the top
//! level, and carries the spellings beside the origin table. A type the
//! printer cannot lay out on one line is left unspelled, since it stands in a
//! one-line label. A module that refuses nothing spells nothing. A document
//! judged after its import closure spells its own refusals and failures and
//! keeps the closure's spellings ([`TypeSpellings::after`]).
//!
//! The alternatives were keeping the arena in the composition, which costs a
//! copy of the whole arena per revision or makes the admission borrow what a
//! face also reads, and spelling from a cloned arena at the diagnostic, which
//! costs the same copy. Reversal: a diagnostic that needs a type no failure
//! names needs the arena, or a richer table built at the judgement.
//!
//! # Spelled in both spellings
//!
//! Each type is spelled twice, once in each [`Spelling`]: the arena is gone
//! by the time a face asks, and the face, not the judgement, knows which
//! spelling its reader chose. [`TypeSpellings`] holds both, and a face reads
//! one through [`TypeSpellings::spelled`]. The alternative, the reader's
//! spelling threaded into the judgement, would judge a document once per
//! spelling where a shared session serves editors that chose differently.
//! The second pass spells only the types a refusal names. Reversal: a profile
//! that shows the second pass, at which point the judgement spells the one
//! spelling each face it serves asked for.
//!
//! # Spelled under the binders in scope
//!
//! A type a failure names stands under the binders its run had opened up to
//! where the type is read: an obligation's expected type under those opened
//! before it, a binder's type under those before the binder, a compared type
//! under them all. Each is spelled under the names the source wrote for them,
//! read as a context's binders are ([`crate::frame::contexts`]), so a mismatch
//! between `counted_at(presented)` and `counted_at(other)` reads so rather than
//! as `counted_at(?)` twice. A failure whose obligations do not account for
//! every hypothesis spells its types under no name. A type stands in the
//! regions its run had opened the same way, one per capability scope and hold
//! the checker entered, outermost first, each named as the source writes the
//! capability or the held slot, so a kept type reads `at c` rather than
//! `at ?`. A region the failing definition abstracts, `@[r : Region]`, is
//! named as its telescope writes it, by the lowering's
//! [`LoweredModule::region_names`]. The alternative, a spelling per
//! diagnostic, is the arena copy the section above declines.
//!
//! # A failure is kept by position
//!
//! The checker's module report keeps each refused body's [`Failure`] by its
//! admission position, which a settled declaration report names. The
//! composition copies them out as [`Failures`] before the report moves into
//! the admission, so a diagnostic finds a refusal's failure without the
//! checker's report.

use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use alloc::string::String;
use alloc::vec::Vec;

use anodized::spec;
use gandr_core_checker::Failure;
use gandr_core_checker::FrameRole;
use gandr_core_checker::ModuleReport;
use gandr_core_checker::TypeNode;
use gandr_core_term::CompTypeId;
use gandr_core_term::ComputationId;
use gandr_core_term::CoreArena;
use gandr_core_term::ValueTypeId;
use gandr_kernel_term::ConstantIndex;
use gandr_surface_corpus::DeclarationReport;
use gandr_surface_corpus::Refusal;
use gandr_surface_corpus::SettleReport;
use gandr_surface_lowering::ConstructorSpelling;
use gandr_surface_lowering::DeclarationOutcome;
use gandr_surface_lowering::LoweredModule;
use gandr_surface_lowering::Origin;
use gandr_surface_lowering::OriginTable;
use gandr_surface_lowering::Role;
use gandr_surface_lowering::SurfaceName;
use gandr_surface_pretty::Arity;
use gandr_surface_pretty::Constructors;
use gandr_surface_pretty::CoreNode;
use gandr_surface_pretty::CoreSource;
use gandr_surface_pretty::FamilyKey;
use gandr_surface_pretty::Form;
use gandr_surface_pretty::ModelSlot;
use gandr_surface_pretty::Modelled;
use gandr_surface_pretty::Name;
use gandr_surface_pretty::Presentation;
use gandr_surface_pretty::Spelling;
use gandr_surface_pretty::Style;
use gandr_surface_pretty::present_type_line;
use gandr_surface_syntax::SourceFragment;
use gandr_surface_syntax::SourceText;
use quenchant_shape::shape::Maybe;

use crate::frame::opened;
use crate::frame::written_binder;

quenchant_shape::reason_enum! {
    /// Why a type node has no spelling.
    pub mod spelling {
        /// The reason no spelling is held.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// No refusal or failure of the module names the node, or the
            /// printer could not lay it out on one line.
            Unspelled,
        }
    }
}

quenchant_shape::reason_enum! {
    /// Why a declaration has no failure.
    pub mod kept {
        /// The reason no failure is kept.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The body was not refused by the checking machine: it checked,
            /// was not judged, or was refused before the machine ran.
            Unrefused,
        }
    }
}

/// The page a spelled type is laid out on: one line beside a source locus, as
/// wide as the transcript a session prints.
const SPELLING_WIDTH: u32 = 100;

/// Where a type a failure names stands: the failure's hypotheses and regions,
/// by its position among the failures spelled, and how many of each, outermost
/// first, it stands under.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Scoped
{
    /// The failure's position among those spelled.
    scope: usize,
    /// How many of its hypotheses the type stands under.
    depth: usize,
    /// How many of its regions the type stands in.
    regions: usize,
}

impl Scoped
{
    /// A type standing under no binder and in no region.
    const CLOSED: Self = Self {
        scope: usize::MAX,
        depth: 0_usize,
        regions: 0_usize,
    };
}

/// The failure each refused body of a module kept, by the declaration's
/// admission position.
///
/// # Specification
/// - requires: built by [`Failures::of`] from the checker's report.
/// - ensures: each position keyed is a body the checking machine refused.
/// - panics: none.
/// - executable: none — this data type has no call boundary; [`Failures::of`]
///   carries the predicates.
///
/// # Adequacy
/// - hypothesis: L3 — a refused body keeps its failure under its position and a
///   module that refuses nothing keeps none.
/// - witness: `tests::diagnostics::a_refusal_keeps_its_failure_and_spells_its_types`
#[repr(transparent)]
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Failures(BTreeMap<ConstantIndex, Failure>);

impl Failures
{
    /// The failures the checker's `report` keeps.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: exactly the report's failures, by position.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a refused body's failure is read back under its
    ///   position.
    /// - witness: `tests::diagnostics::a_refusal_keeps_its_failure_and_spells_its_types`
    #[spec(ensures: |ret| &ret.0 == report.failures())]
    #[inline]
    #[must_use]
    pub fn of(report: &ModuleReport) -> Self
    {
        Self(report.failures().clone())
    }

    /// The failure the body at `constant` was refused with.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn get(
        &self,
        constant: ConstantIndex,
    ) -> Maybe<&Failure, kept::Absent>
    {
        self.0
            .get(&constant)
            .map_or(Maybe::Absent(kept::Absent::Unrefused), Maybe::Present)
    }
}

/// The spelling of every type a module's checker refusals compare and its
/// failures name, keyed by its node, in one spelling.
///
/// # Specification
/// - requires: read from a [`TypeSpellings`] built over the arena the refusals
///   were judged over.
/// - ensures: each node keyed is one a refusal of the module compares, or one a
///   failure names, spelled by the shared printer.
/// - panics: none.
/// - executable: none — this data type has no call boundary;
///   [`TypeSpellings::of`] carries the predicates.
///
/// # Adequacy
/// - hypothesis: L3 — a mismatch spells both of its types, a failure the type
///   its outer rule was checked against, and a module that refuses nothing
///   spells none.
/// - witness: `tests::diagnostics::a_refusal_keeps_its_failure_and_spells_its_types`
#[repr(transparent)]
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Spellings(BTreeMap<TypeNode, Presentation>);

/// A module's [`Spellings`] in each [`Spelling`].
///
/// # Specification
/// - requires: built by [`TypeSpellings::of`].
/// - ensures: both spellings key the same nodes but where the printer lays one
///   out on more lines than the other.
/// - panics: none.
/// - executable: none — this data type has no call boundary;
///   [`TypeSpellings::of`] carries the predicates.
///
/// # Adequacy
/// - hypothesis: L3 — a mismatch between relations spells each side with its
///   glyph in Unicode and its ASCII spelling in ASCII.
/// - witness: `tests::diagnostics::a_refusal_spells_its_types_in_either_spelling_782`
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct TypeSpellings
{
    /// The types in [`Spelling::Unicode`].
    unicode: Spellings,
    /// The types in [`Spelling::Ascii`].
    ascii: Spellings,
}

impl TypeSpellings
{
    /// Spell every type the checker refusals `report` settled compare, and
    /// every type `failures` name, their nodes read from `arena`, their
    /// constants named by `module` and their binders by `origins` over `text`.
    ///
    /// # Specification
    /// - requires: `report` settled the verdicts judged over `arena`, of the
    ///   declarations `module` lowered into it, and `failures` holds those
    ///   verdicts' failures; `origins` is `module`'s origin table with the
    ///   judgement's elaborated nodes carried, and `text` the source it
    ///   measures.
    /// - ensures: each type a produced checker refusal compares, as
    ///   [`gandr_core_checker::CheckRefusal::compared`] names it, and each type
    ///   [`Failure::types`] names, is keyed by its node and spelled on one line
    ///   through [`present_type_line`] in its sugared form, once in each
    ///   spelling, constants by their paths from the top level, so a member of
    ///   a module, a sealed abstract type among them, reads as it is written
    ///   outside it; a dependent arrow's binder is named as the source writes
    ///   it, where it captures nothing; a type a failure names is spelled under
    ///   the hypotheses it stands under, each by the name
    ///   [`crate::frame::contexts`] gives it, and in the regions it stands in,
    ///   each by its scope's capability or its hold's slot as written, and at
    ///   its definition's region binders, each by its name in the telescope, a
    ///   failure's first naming of a node winning; a type the printer cannot
    ///   spell, or whose line is wider than a page of [`SPELLING_WIDTH`]
    ///   columns, is left unkeyed, and is never laid out; nothing else is
    ///   keyed.
    /// - provides: the spellings a diagnostic reads a refusal's types from once
    ///   the arena is gone.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a value mismatch spells its expected and found types
    ///   apart; a failure spells the types its rules were checked against; a
    ///   module whose declarations all check spells none; a sealed abstract
    ///   type is spelled by its module's path; a mismatch between types over
    ///   two parameters spells each by its name, and a hypothesis's type the
    ///   parameters before it; a type kept at a scope or a hold names it, and
    ///   one kept at a definition's region binder names the binder.
    /// - witness: `tests::diagnostics::a_refusal_keeps_its_failure_and_spells_its_types`
    /// - witness: `tests::diagnostics::a_sealed_type_is_spelled_by_its_path`
    /// - witness: `tests::diagnostics::a_refusal_spells_its_binders_by_name_418`
    /// - witness: `tests::diagnostics::a_trace_spells_a_kept_region_by_its_name_1494`
    /// - witness: `tests::diagnostics::a_mismatch_between_two_region_binders_names_both_2138`
    #[spec(ensures: |ret| [&ret.unicode, &ret.ascii].iter().all(|spelled| spelled.0.iter().all(|(node, presentation)| !presentation.as_ref().contains('\n')
        && (report.declarations().iter().any(|declaration|
            matches!(declaration.produced().refusal(), Maybe::Present(Refusal::Checking(refusal))
                if [refusal.compared().expected, refusal.compared().found].contains(&Maybe::Present(*node))))
            || failures.0.values().any(|failure| failure.types().contains(node))))))]
    #[inline]
    #[must_use]
    pub fn of(
        arena: &CoreArena,
        module: &LoweredModule<'_>,
        report: &SettleReport<'_>,
        failures: &Failures,
        (origins, text): (&OriginTable, SourceText<'_>),
    ) -> Self
    {
        spell(
            (arena, module),
            (report.declarations(), failures.0.iter()),
            (origins, text),
        )
    }

    /// [`Self::of`], `earlier` the spellings of a module whose declarations
    /// lead `module`'s, below `boundary`: only the refusals and failures of
    /// the declarations from `boundary` on are spelled, and a node `earlier`
    /// spells keeps that spelling.
    ///
    /// # Specification
    /// - requires: as [`Self::of`]; `earlier` is [`Self::of`] over the leading
    ///   module's report and failures, judged over an arena `arena` extends,
    ///   and `boundary` its first position past them.
    /// - ensures: `earlier`'s spellings, with each type the refusals and
    ///   failures from `boundary` on name spelled as [`Self::of`] spells it,
    ///   where `earlier` keys no spelling of it.
    /// - provides: a document's spellings at the cost of its own refusals.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the clause names [`Self::of`]'s spelling of each
    ///   node; the witness compares the joined spellings with a fresh one's.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a document judged after a closure judged once spells
    ///   as on a fresh judgement of the closure.
    /// - witness: `tests::diagnostics::a_document_judged_after_its_closure_spells_as_the_whole_unit_776`
    #[inline]
    #[must_use]
    pub fn after(
        earlier: &Self,
        boundary: ConstantIndex,
        (arena, module): (&CoreArena, &LoweredModule<'_>),
        (report, failures): (&SettleReport<'_>, &Failures),
        (origins, text): (&OriginTable, SourceText<'_>),
    ) -> Self
    {
        let mut later = spell(
            (arena, module),
            (
                report
                    .declarations()
                    .get(
                        report
                            .declarations()
                            .partition_point(|declaration| declaration.constant() < boundary) ..,
                    )
                    .unwrap_or_default(),
                failures.0.range(boundary ..),
            ),
            (origins, text),
        );
        for (into, from) in [
            (&mut later.unicode, &earlier.unicode),
            (&mut later.ascii, &earlier.ascii),
        ] {
            into.0.extend(
                from.0
                    .iter()
                    .map(|(&node, spelled)| (node, spelled.clone())),
            );
        }
        later
    }

    /// The types in `spelling`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn spelled(
        &self,
        spelling: Spelling,
    ) -> &Spellings
    {
        match spelling {
            Spelling::Unicode => &self.unicode,
            Spelling::Ascii => &self.ascii,
        }
    }
}

/// [`TypeSpellings::of`] over `declarations`' checker refusals and
/// `failures`.
///
/// # Specification
/// - requires: as [`TypeSpellings::of`].
/// - ensures: as [`TypeSpellings::of`], of the refusals among `declarations`
///   and of `failures`, in their order; every spelling kept is one line.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — as [`TypeSpellings::of`], and a split opening two binders
///   at once, the second's type naming the first.
/// - witness: `tests::diagnostics::a_refusal_keeps_its_failure_and_spells_its_types`
/// - witness: `tests::diagnostics::a_later_binder_of_one_split_spells_under_the_earlier`
#[spec(ensures: |ret| [&ret.unicode, &ret.ascii].iter().all(|spelled|
    spelled.0.values().all(|presentation| !presentation.as_ref().contains('\n'))))]
fn spell<'failure>(
    (arena, module): (&CoreArena, &LoweredModule<'_>),
    (declarations, failures): (
        &[DeclarationReport<'_>],
        impl Iterator<Item = (&'failure ConstantIndex, &'failure Failure)>,
    ),
    (origins, text): (&OriginTable, SourceText<'_>),
) -> TypeSpellings
{
    let mut unicode = BTreeMap::new();
    let mut ascii = BTreeMap::new();
    let mut seen = BTreeSet::new();
    // Each failure's hypotheses, named where the source wrote their
    // binders, and each type it names with how many of them it stands
    // under.
    let mut scopes: Vec<Vec<Option<String>>> = Vec::new();
    // Each failure's regions, outermost first: the checker opens one at a
    // capability scope's subject and one at a hold's body, each named as the
    // source writes the binder it opens, the capability or the held slot.
    let mut regions: Vec<Vec<Option<String>>> = Vec::new();
    // Each failure's definition's region binders, by ordinal, named as its
    // telescope writes them.
    let mut bindings: Vec<Vec<Option<Name<'_>>>> = Vec::new();
    let mut named: Vec<(TypeNode, Scoped)> = Vec::new();
    for (&constant, failure) in failures {
        bindings.push(
            module
                .region_names(constant)
                .iter()
                .map(|name| name.map(|name| Name::from(<&str>::from(SourceFragment::from(name)))))
                .collect(),
        );
        let scope = scopes.len();
        let first = named.len();
        let mut names: Vec<Option<String>> = Vec::with_capacity(failure.hypotheses().len());
        let mut around: Vec<Option<String>> = Vec::new();
        for obligation in failure.obligations() {
            let standing = Scoped {
                scope,
                depth: names.len(),
                regions: around.len(),
            };
            if let Maybe::Present(expected) = obligation.expected() {
                named.push((expected, standing));
            }
            if matches!(
                obligation.role(),
                FrameRole::ScopeSubject | FrameRole::HoldBody
            ) {
                around.push(match written_binder(obligation.at(), origins, text) {
                    Maybe::Present(name) => Some(name),
                    Maybe::Absent(_) => None,
                });
            }
            let binders = opened(obligation, origins, text);
            for (name, &ty) in binders.into_iter().zip(obligation.binders()) {
                named.push((TypeNode::Value(ty), Scoped {
                    depth: names.len(),
                    ..standing
                }));
                names.push(match name {
                    Maybe::Present(name) => Some(name),
                    Maybe::Absent(_) => None,
                });
            }
        }
        if names.len() != failure.hypotheses().len() {
            // The obligations do not account for every hypothesis, so
            // no name is known to stand at its position.
            names.clear();
            for &mut (_, ref mut scoped) in named.get_mut(first ..).into_iter().flatten() {
                scoped.depth = 0;
            }
        }
        let full = names.len();
        let enclosed = around.len();
        let compared = failure.refusal().compared();
        let pursued = match failure.pursuit().expected() {
            Maybe::Present(node) => Some(node),
            Maybe::Absent(_) => None,
        };
        named.extend(
            [compared.expected, compared.found]
                .into_iter()
                .filter_map(|side| match side {
                    Maybe::Present(node) => Some(node),
                    Maybe::Absent(_) => None,
                })
                .chain(pursued)
                .chain(
                    failure
                        .endpoints()
                        .iter()
                        .map(|live| TypeNode::Value(live.state)),
                )
                .map(|node| {
                    (node, Scoped {
                        scope,
                        depth: full,
                        regions: enclosed,
                    })
                }),
        );
        // A region's depth counts from the outermost, so a hypothesis spelled
        // under every region the failure stands in names the ones it was
        // formed in as they were.
        named.extend(failure.hypotheses().iter().enumerate().map(|(at, &ty)| {
            (TypeNode::Value(ty), Scoped {
                scope,
                depth: at.min(full),
                regions: enclosed,
            })
        }));
        scopes.push(names);
        regions.push(around);
    }
    named.extend(
        declarations
            .iter()
            .filter_map(|declaration| match declaration.produced().refusal() {
                Maybe::Present(Refusal::Checking(refusal)) => Some(refusal.compared()),
                Maybe::Present(Refusal::Lowering(_) | Refusal::Corpus(_)) | Maybe::Absent(_) => {
                    None
                },
            })
            .flat_map(|compared| [compared.expected, compared.found])
            .filter_map(|side| match side {
                Maybe::Present(node) => Some((node, Scoped::CLOSED)),
                Maybe::Absent(_) => None,
            }),
    );
    if named.is_empty() {
        return TypeSpellings::default();
    }
    let paths = constant_names(module);
    let names: Vec<Name<'_>> = paths.iter().map(|path| Name::from(path.as_str())).collect();
    let families = Families::of(module);
    let constructors = families.naming();
    let contexts = printed_names(&scopes);
    let enclosing = printed_names(&regions);
    let arrows: Vec<(CompTypeId, Name<'_>)> = written_names(origins.arrows(), text);
    let pairs: Vec<(ValueTypeId, Name<'_>)> = written_names(origins.pairs(), text);
    let seconds: Vec<(ValueTypeId, Name<'_>)> = written_names(origins.seconds(), text);
    let mut relations = origins.relations().to_vec();
    relations.sort_by_key(|&(related, _)| related);
    let mut models: Vec<(ValueTypeId, Modelled<'_>)> = origins
        .models()
        .iter()
        .map(|&(modelled, ref model)| {
            (modelled, Modelled {
                theory: Name::from(model.theory.as_ref()),
                sorts: model
                    .sorts
                    .iter()
                    .map(|&(ref sort, carrier)| {
                        (Name::from(sort.as_ref()), CoreNode::ValueType(carrier))
                    })
                    .collect(),
            })
        })
        .collect();
    models.sort_by_key(|&(modelled, _)| modelled);
    let implicits = telescopes(module);
    let slots = model_slots(module);
    let source = CoreSource::new(arena, &names)
        .naming(&constructors)
        .naming_arrows(&arrows)
        .naming_pairs(&pairs, &seconds)
        .relating(&relations)
        .modeling(&models)
        .naming_implicits(&implicits)
        .flattening(&slots);
    for (
        node,
        Scoped {
            scope,
            depth,
            regions: within,
        },
    ) in named
    {
        if !seen.insert(node) {
            continue;
        }
        let root = match node {
            TypeNode::Value(id) => CoreNode::ValueType(id),
            TypeNode::Computation(id) => CoreNode::CompType(id),
        };
        let context = contexts
            .get(scope)
            .and_then(|context| context.get(.. depth))
            .unwrap_or_default();
        let around = enclosing
            .get(scope)
            .and_then(|around| around.get(.. within))
            .unwrap_or_default();
        let bound = bindings.get(scope).map(Vec::as_slice).unwrap_or_default();
        for (spelling, spelled) in [
            (Spelling::Unicode, &mut unicode),
            (Spelling::Ascii, &mut ascii),
        ] {
            let style = Style {
                form: Form::Sugared,
                spelling,
            };
            // The one-line spelling is the page's layout wherever it fits,
            // and a type laid out over more lines is not kept, so one whose
            // line does not fit is never laid out.
            if let Ok(presentation) = present_type_line(
                &source.within(context).scoped(around).bounding(bound),
                root,
                style,
            ) && !presentation.as_ref().contains('\n')
                && u32::try_from(presentation.as_ref().chars().count())
                    .is_ok_and(|width| width <= SPELLING_WIDTH)
            {
                let _fresh = spelled.insert(node, presentation);
            }
        }
    }
    TypeSpellings {
        unicode: Spellings(unicode),
        ascii: Spellings(ascii),
    }
}

/// Each node of `named` with the name `text` writes at its origin, in
/// `named`'s order; a node whose origin falls outside `text` is left out.
///
/// # Specification
/// trivial.
fn written_names<'text, Id>(
    named: &[(Id, Origin)],
    text: SourceText<'text>,
) -> Vec<(Id, Name<'text>)>
where
    Id: Copy,
{
    let text: &str = text.into();
    named
        .iter()
        .filter_map(|&(node, origin)| {
            let span = origin.span();
            text.get(usize::from(span.start()) .. usize::from(span.end()))
                .map(|name| (node, Name::from(name)))
        })
        .collect()
}

impl Spellings
{
    /// The spelling of `node`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn get(
        &self,
        node: TypeNode,
    ) -> Maybe<&Presentation, spelling::Absent>
    {
        self.0
            .get(&node)
            .map_or(Maybe::Absent(spelling::Absent::Unspelled), Maybe::Present)
    }
}

/// The names `held` keeps for each failure, outermost first, as the printer
/// reads them: a binder or region the source names by its name, any other as
/// unnamed.
///
/// # Specification
/// - requires: nothing.
/// - ensures: one list per failure of `held`, each as long as its own, each
///   name the one `held` keeps at its position.
/// - provides: the contexts and regions [`spell`] prints a failure's types in.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — as [`TypeSpellings::of`].
/// - witness: `tests::diagnostics::a_refusal_spells_its_binders_by_name_418`
#[spec(ensures: |ret| ret.len() == held.len()
    && ret.iter().zip(held).all(|(printed, kept)| printed.len() == kept.len()))]
fn printed_names(held: &[Vec<Option<String>>]) -> Vec<Vec<Option<Name<'_>>>>
{
    held.iter()
        .map(|names| {
            names
                .iter()
                .map(|name| name.as_deref().map(Name::from))
                .collect()
        })
        .collect()
}

/// The name a printer writes for each constant of `module`, by admission
/// position.
///
/// A name is the declaration's path from the top level, its segments joined
/// by `.`; a position no declaration holds is the empty name. The words of a
/// family's loops are named by the path type they read as, `Path(Circle,
/// Base, Base)`, so a word's type spells as it is written and its letters are
/// not looked up under its family's name.
///
/// # Specification
/// - requires: nothing.
/// - ensures: one name per position up to the highest declared one; each
///   declared position holds its declaration's path, so a member of a module, a
///   sealed abstract type among them, reads as it is written outside it, and
///   the words of a family's loops hold the path type at their point.
/// - provides: the constant names a [`CoreSource`] reads to spell a type that
///   mentions a declaration.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a refusal comparing two declared types spells the names
///   of the declarations it mentions, and a sealed abstract type is spelled by
///   its module's path rather than its bare name; a word spells by its letters,
///   which only a words family named apart from its sort finds.
/// - witness: `tests::diagnostics::a_refusal_keeps_its_failure_and_spells_its_types`
/// - witness: `tests::diagnostics::a_sealed_type_is_spelled_by_its_path`
/// - witness: `tests::diagnostics::a_word_spells_by_its_letters`
#[spec(ensures: |ret| module.declarations().iter().all(|declaration|
    ret.get(usize::from(declaration.constant())).is_some()))]
#[inline]
#[must_use]
pub fn constant_names(module: &LoweredModule<'_>) -> Vec<String>
{
    let positions = module
        .declarations()
        .iter()
        .map(|declaration| usize::from(declaration.constant()).saturating_add(1))
        .max()
        .unwrap_or_default();
    let mut paths = alloc::vec![String::new(); positions];
    for declaration in module.declarations() {
        if let Some(slot) = paths.get_mut(usize::from(declaration.constant())) {
            slot.clear();
            for (index, segment) in module.path_of(declaration).iter().enumerate() {
                if index > 0 {
                    slot.push('.');
                }
                slot.push_str(<&str>::from(SourceFragment::from(*segment)));
            }
        }
    }
    for declaration in module.declarations() {
        if let Maybe::Present((sort, point)) = words_point(module, declaration) {
            let family = paths.get(usize::from(sort)).cloned().unwrap_or_default();
            if let Some(slot) = paths.get_mut(usize::from(declaration.constant())) {
                *slot = alloc::format!("Path({family}, {point}, {point})");
            }
        }
    }
    paths
}

/// The telescope of each function of `module` that writes an implicit.
///
/// Ascending by its constant, as [`CoreSource::naming_implicits`] reads it:
/// one entry per parameter in the merged order, an implicit's name and none
/// for an explicit one.
///
/// # Specification
/// trivial.
#[inline]
#[must_use]
pub fn telescopes<'module>(
    module: &'module LoweredModule<'_>
) -> Vec<(ConstantIndex, Vec<Option<Name<'module>>>)>
{
    let mut telescopes: Vec<(ConstantIndex, Vec<Option<Name<'module>>>)> = module
        .declarations()
        .iter()
        .filter_map(|declaration| {
            let constant = declaration.constant();
            let held = module.implicits(constant);
            (!held.is_empty()).then(|| {
                (
                    constant,
                    held.iter()
                        .map(|name| name.as_ref().map(|name| Name::from(name.as_ref())))
                        .collect(),
                )
            })
        })
        .collect();
    telescopes.sort_by_key(|&(constant, _)| constant);
    telescopes.dedup_by_key(|&mut (constant, _)| constant);
    telescopes
}

/// The model implicits of each function of `module` whose telescope writes
/// one.
///
/// Ascending by its constant, as [`CoreSource::flattening`] reads them: each
/// slot in telescope order, its components and its fixed sorts by name.
///
/// # Specification
/// trivial.
#[inline]
#[must_use]
pub fn model_slots<'module>(
    module: &'module LoweredModule<'_>
) -> Vec<(ConstantIndex, Vec<ModelSlot<'module, CoreNode>>)>
{
    let mut slots: Vec<(ConstantIndex, Vec<ModelSlot<'module, CoreNode>>)> = module
        .declarations()
        .iter()
        .filter_map(|declaration| {
            let constant = declaration.constant();
            let held = module.model_slots(constant);
            (!held.is_empty()).then(|| {
                (
                    constant,
                    held.iter()
                        .map(|slot| ModelSlot {
                            at: slot.at,
                            name: Name::from(slot.name.as_ref()),
                            theory: Name::from(slot.theory.as_ref()),
                            components: slot
                                .components
                                .iter()
                                .map(|&(ref component, sort)| {
                                    (Name::from(component.as_ref()), sort)
                                })
                                .collect(),
                            fixed: slot
                                .fixed
                                .iter()
                                .map(|&(ref sort, ty)| {
                                    (Name::from(sort.as_ref()), CoreNode::ValueType(ty))
                                })
                                .collect(),
                        })
                        .collect(),
                )
            })
        })
        .collect();
    slots.sort_by_key(|&(constant, _)| constant);
    slots.dedup_by_key(|&mut (constant, _)| constant);
    slots
}

quenchant_shape::reason_enum! {
    /// Why a declaration names no words' point.
    pub mod words_point {
        /// The reason no point is spelled.
        #[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
        pub enum Absent {
            /// The declaration is no words of a family's loops, or its family
            /// is not among the module's data declarations.
            Unworded,
        }
    }
}

/// The sort the words `declaration` declares are over, and the point their
/// loops are at, spelled by the sort's constructor names.
///
/// # Specification
/// - requires: nothing.
/// - ensures: for the words of a family's loops whose family the module holds,
///   the family's admission position and the closed term its loops are at, each
///   constructor by its name, applied to its fields when it has any.
/// - fails: [`words_point::Absent::Unworded`] for any other declaration.
/// - panics: none.
///
/// # Termination
/// - reason: one pass over the point's pre-order nodes, last to first.
/// - measure: the point's nodes still to spell.
///
/// # Adequacy
/// - hypothesis: L3 — as [`constant_names`], and points whose constructors take
///   one argument and two.
/// - witness: `tests::diagnostics::a_word_spells_by_its_letters`
/// - witness: `tests::diagnostics::a_words_point_spells_its_constructors_arguments`
#[spec(ensures: |ret| match ret {
    Maybe::Present((_, ref point)) => !point.is_empty(),
    Maybe::Absent(_) => true,
})]
fn words_point(
    module: &LoweredModule<'_>,
    declaration: &gandr_surface_lowering::LoweredDeclaration<'_>,
) -> Maybe<(ConstantIndex, String), words_point::Absent>
{
    let unworded = Maybe::Absent(words_point::Absent::Unworded);
    if declaration.role() != Role::Words {
        return unworded;
    }
    let DeclarationOutcome::Data(index) = declaration.outcome()
    else {
        return unworded;
    };
    let Maybe::Present(cells) = module
        .data(index)
        .map(|signature| signature.presentation().cells())
    else {
        return unworded;
    };
    let Some(cells) = cells
    else {
        return unworded;
    };
    let Some(family) = module
        .declarations()
        .iter()
        .find_map(|held| match held.outcome() {
            DeclarationOutcome::Data(family) if held.constant() == cells.sort() => Some(family),
            DeclarationOutcome::Completed { .. }
            | DeclarationOutcome::Uncompleted { .. }
            | DeclarationOutcome::Bodied { .. }
            | DeclarationOutcome::Data(_)
            | DeclarationOutcome::Codata(_)
            | DeclarationOutcome::Abstract(_)
            | DeclarationOutcome::World
            | DeclarationOutcome::Refused(_) => None,
        })
    else {
        return unworded;
    };
    let Maybe::Present(signature) = module.data(family)
    else {
        return unworded;
    };
    let names = module.constructors(family);
    let mut spelled: Vec<String> = Vec::new();
    for node in cells.point().iter().rev() {
        let gandr_kernel_term::RuleNode::Constructor(tag) = *node
        else {
            return unworded;
        };
        let tag = usize::from(tag);
        let (Some(name), Some(fields)) = (names.get(tag), signature.constructors().get(tag))
        else {
            return unworded;
        };
        let start = spelled.len().saturating_sub(fields.len());
        let mut text = name.clone();
        if start < spelled.len() {
            text.push('(');
            for (index, argument) in spelled.drain(start ..).rev().enumerate() {
                if index > 0 {
                    text.push_str(", ");
                }
                text.push_str(&argument);
            }
            text.push(')');
        }
        spelled.push(text);
    }
    match (spelled.pop(), spelled.is_empty()) {
        (Some(point), true) => Maybe::Present((cells.sort(), point)),
        _ => unworded,
    }
}

/// The constructors of every data declaration of a module, each family by
/// its constant's admission position, and the family each data case of its
/// bodies eliminates.
///
/// Each constructor is kept by its name and field count in tag order, and
/// a family records whether it is the words of a family's loops, whose empty
/// word is spelled `here(a)` at their point `a` as a value and `here` as a
/// pattern, and whose letters cons onto the rest of a word. The core names a
/// constructor by its family and its tag, and a data case matches by tag
/// alone, so a printer reads the names here, owned so a table outliving the
/// lowered module keeps them.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Families
{
    /// Each data declaration's constructors.
    families: Vec<Family>,
    /// Each data case, with the constant of the family it eliminates.
    cases: Vec<(ComputationId, ConstantIndex)>,
}

/// One data declaration's constructors, as [`Families`] keeps them.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Eq, PartialEq)]
struct Family
{
    /// The family's constant.
    constant: ConstantIndex,
    /// Each constructor's name and field count, in tag order.
    constructors: Vec<(String, usize)>,
    /// The empty word as a value is written, `here(a)`, when the family is
    /// the words of a family's loops.
    empty: Option<String>,
    /// The names of the family's loops, in the order a data case over the
    /// family takes their branches after its constructors'.
    loops: Vec<String>,
}

impl Families
{
    /// The constructors of every data declaration of `module`, and the
    /// family each data case of its arena eliminates.
    ///
    /// A case is named by its node in the module's own arena, so a table
    /// made here names the cases of that arena alone; a source over another
    /// arena, such as a run's value read back, takes [`Self::declared`].
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the families [`Self::declared`] holds, and one case per data
    ///   case the module's origins record a family for, at that family's
    ///   position.
    /// - provides: the constructor names a [`CoreSource`] over the module's
    ///   arena spells a constructor value and a data case's patterns with.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a body's match names each branch by its constructor;
    ///   a case left out spells `?`, which the test fails on.
    /// - witness: `tests::diagnostics::a_body_names_its_match_arms_by_their_constructors_809`
    #[spec(ensures: |ret| ret.families.len() <= module.declarations().len()
        && ret.cases.len() == module.origins().eliminations().len())]
    #[inline]
    #[must_use]
    pub fn of(module: &LoweredModule<'_>) -> Self
    {
        let cases = module.origins().eliminations().collect();
        Self {
            cases,
            ..Self::declared(module)
        }
    }

    /// The constructors of every data declaration of `module`, naming no
    /// data case.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: one family per data declaration whose signature the module
    ///   holds, at its constant's position, its constructors named as written
    ///   in tag order with the field count the signature gives each, a
    ///   constructor whose bare name the module reports shadowed qualified by
    ///   its family's path, `Theory.App`; then its loops named as written, the
    ///   words declaring them in module order; the words of a family's loops
    ///   are consed, their empty word written `here(a)` as a value at their
    ///   point `a`; no case.
    /// - provides: the constructor names a [`CoreSource`] over any arena spells
    ///   a constructor value with.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a refusal whose type mentions a constructor value
    ///   spells it by its declared name; a family left out spells `?`, which
    ///   the test fails on.
    /// - witness: `tests::diagnostics::a_mismatch_spells_the_constructors_its_type_mentions`
    /// - witness: `tests::diagnostics::a_word_spells_by_its_letters`
    /// - witness: `tests::diagnostics::a_loop_arm_is_named_by_its_loop_823`
    /// - witness: `tests::diagnostics::a_shadowed_constructor_spells_by_its_family_2428`
    #[spec(ensures: |ret| ret.families.len() <= module.declarations().len() && ret.cases.is_empty())]
    #[inline]
    #[must_use]
    pub fn declared(module: &LoweredModule<'_>) -> Self
    {
        let mut looped: BTreeMap<ConstantIndex, Vec<String>> = BTreeMap::new();
        for declaration in module.declarations() {
            if declaration.role() != Role::Words {
                continue;
            }
            let DeclarationOutcome::Data(index) = declaration.outcome()
            else {
                continue;
            };
            let Maybe::Present(Some(cells)) = module
                .data(index)
                .map(|signature| signature.presentation().cells())
            else {
                continue;
            };
            // A word's constructors are the empty word, then a letter and its
            // inverse per loop: the letters, at the odd tags, name the loops.
            let letters = module
                .constructors(index)
                .iter()
                .skip(1)
                .step_by(2)
                .take(cells.cells().len())
                .cloned();
            looped.entry(cells.sort()).or_default().extend(letters);
        }
        let mut qualifier = alloc::string::String::new();
        let families = module
            .declarations()
            .iter()
            .filter_map(|declaration| {
                let DeclarationOutcome::Data(index) = declaration.outcome()
                else {
                    return None;
                };
                let Maybe::Present(signature) = module.data(index)
                else {
                    return None;
                };
                let point = words_point(module, declaration);
                let names = module.constructors(index);
                let family = declaration.constant();
                qualifier.clear();
                let constructors = names
                    .iter()
                    .zip(signature.constructors())
                    .map(|(name, fields)| {
                        let spelled = if module
                            .constructor_spelling(family, SurfaceName::from(name.as_str()))
                            == ConstructorSpelling::Qualified
                        {
                            if qualifier.is_empty() {
                                for segment in module.path_of(declaration) {
                                    if !qualifier.is_empty() {
                                        qualifier.push('.');
                                    }
                                    qualifier.push_str(<&str>::from(SourceFragment::from(segment)));
                                }
                            }
                            alloc::format!("{qualifier}.{name}")
                        }
                        else {
                            name.clone()
                        };
                        (spelled, fields.len())
                    })
                    .collect();
                let empty = match point {
                    Maybe::Present((_, ref point)) => {
                        names.first().map(|name| alloc::format!("{name}({point})"))
                    },
                    Maybe::Absent(_) => None,
                };
                Some(Family {
                    constant: family,
                    constructors,
                    empty,
                    loops: looped.remove(&family).unwrap_or_default(),
                })
            })
            .collect();
        Self {
            families,
            cases: Vec::new(),
        }
    }

    /// The constructor table these families make, each family and each data
    /// case over it under the family's declaration.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: each family answers its constructors by tag under its
    ///   declaration, whichever other family shares its name; each case answers
    ///   its family's declaration.
    /// - provides: the [`Constructors`] a [`CoreSource`] names through.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — a clause would traverse every family the receiver
    ///   holds, which `spec_clause_traversal` refuses.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::of`]; a family keyed by its name instead
    ///   answers a namesake's constructors, which the driver's
    ///   `cli::a_run_spells_its_value_by_its_own_type_past_a_namesake_3125`
    ///   fails on.
    /// - witness: `tests::diagnostics::a_mismatch_spells_the_constructors_its_type_mentions`
    /// - witness: `tests::diagnostics::a_body_names_its_match_arms_by_their_constructors_809`
    #[inline]
    #[must_use]
    pub fn naming(&self) -> Constructors<'_>
    {
        let mut constructors = Constructors::default();
        for family in &self.families {
            let declared = FamilyKey::Declared(family.constant);
            let members = family
                .constructors
                .iter()
                .map(|&(ref name, fields)| (Name::from(name.as_str()), Arity::from(fields)));
            match family.empty {
                Some(ref empty) => {
                    constructors.words(declared, members, Name::from(empty.as_str()));
                },
                None => constructors.family(declared, members),
            }
            if !family.loops.is_empty() {
                constructors.loops(
                    declared,
                    family.loops.iter().map(|name| Name::from(name.as_str())),
                );
            }
        }
        for &(case, family) in &self.cases {
            constructors.case(case, FamilyKey::Declared(family));
        }
        constructors
    }
}
