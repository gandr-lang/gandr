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
//! [`SPELLING_WIDTH`]-column page, constants by their declared names, and
//! carries the spellings beside the origin table. A type the printer cannot
//! lay out on one line is left unspelled, since it stands in a one-line
//! label. A module that refuses nothing spells nothing.
//!
//! The alternatives were keeping the arena in the composition, which costs a
//! copy of the whole arena per revision or makes the admission borrow what a
//! face also reads, and spelling from a cloned arena at the diagnostic, which
//! costs the same copy. Reversal: a diagnostic that needs a type no failure
//! names needs the arena, or a richer table built at the judgement.
//!
//! # A failure is kept by position
//!
//! The checker's module report keeps each refused body's [`Failure`] by its
//! admission position, which a settled declaration report names. The
//! composition copies them out as [`Failures`] before the report moves into
//! the admission, so a diagnostic finds a refusal's failure without the
//! checker's report.

use alloc::collections::BTreeMap;
use alloc::vec::Vec;

use anodized::spec;
use gandr_core_checker::Failure;
use gandr_core_checker::ModuleReport;
use gandr_core_checker::TypeNode;
use gandr_core_term::CoreArena;
use gandr_kernel_term::ConstantIndex;
use gandr_surface_corpus::Refusal;
use gandr_surface_corpus::SettleReport;
use gandr_surface_lowering::LoweredModule;
use gandr_surface_pretty::CoreNode;
use gandr_surface_pretty::CoreSource;
use gandr_surface_pretty::Name;
use gandr_surface_pretty::PageWidth;
use gandr_surface_pretty::Presentation;
use gandr_surface_pretty::present_type;
use gandr_surface_syntax::SourceFragment;
use quenchant_shape::shape::Maybe;

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
/// - witness: `diagnostics::diagnostics::a_refusal_keeps_its_failure_and_spells_its_types`
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
    /// - witness: `diagnostics::diagnostics::a_refusal_keeps_its_failure_and_spells_its_types`
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
/// failures name, keyed by its node.
///
/// # Specification
/// - requires: built by [`Spellings::of`] over the arena the refusals were
///   judged over.
/// - ensures: each node keyed is one a refusal of the module compares, or one a
///   failure names, spelled by the shared printer.
/// - panics: none.
/// - executable: none — this data type has no call boundary; [`Spellings::of`]
///   carries the predicates.
///
/// # Adequacy
/// - hypothesis: L3 — a mismatch spells both of its types, a failure the type
///   its outer rule was checked against, and a module that refuses nothing
///   spells none.
/// - witness: `diagnostics::diagnostics::a_refusal_keeps_its_failure_and_spells_its_types`
#[repr(transparent)]
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Spellings(BTreeMap<TypeNode, Presentation>);

impl Spellings
{
    /// Spell every type the checker refusals `report` settled compare, and
    /// every type `failures` name, their nodes read from `arena` and their
    /// constants named by `module`.
    ///
    /// # Specification
    /// - requires: `report` settled the verdicts judged over `arena`, of the
    ///   declarations `module` lowered into it, and `failures` holds those
    ///   verdicts' failures.
    /// - ensures: each type a produced checker refusal compares, as
    ///   [`gandr_core_checker::CheckRefusal::compared`] names it, and each type
    ///   [`Failure::types`] names, is keyed by its node and spelled through
    ///   [`present_type`] on a page of [`SPELLING_WIDTH`] columns, constants by
    ///   their declared names; a type the printer cannot lay out, or lays out
    ///   over more than one line, is left unkeyed; nothing else is keyed.
    /// - provides: the spellings a diagnostic reads a refusal's types from once
    ///   the arena is gone.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a value mismatch spells its expected and found types
    ///   apart; a failure spells the types its rules were checked against; a
    ///   module whose declarations all check spells none.
    /// - witness: `diagnostics::diagnostics::a_refusal_keeps_its_failure_and_spells_its_types`
    #[spec(ensures: |ret| ret.0.iter().all(|(node, presentation)| !presentation.as_ref().contains('\n')
        && (report.declarations().iter().any(|declaration|
            matches!(declaration.produced().refusal(), Maybe::Present(Refusal::Checking(refusal))
                if [refusal.compared().expected, refusal.compared().found].contains(&Maybe::Present(*node))))
            || failures.0.values().any(|failure| failure.types().contains(node)))))]
    #[inline]
    #[must_use]
    pub fn of(
        arena: &CoreArena,
        module: &LoweredModule<'_>,
        report: &SettleReport<'_>,
        failures: &Failures,
    ) -> Self
    {
        let mut spelled = BTreeMap::new();
        let named: Vec<TypeNode> = report
            .declarations()
            .iter()
            .filter_map(|declaration| match declaration.produced().refusal() {
                | Maybe::Present(Refusal::Checking(refusal)) => Some(refusal.compared()),
                | Maybe::Present(Refusal::Lowering(_) | Refusal::Corpus(_)) | Maybe::Absent(_) => {
                    None
                },
            })
            .flat_map(|compared| [compared.expected, compared.found])
            .filter_map(|side| match side {
                | Maybe::Present(node) => Some(node),
                | Maybe::Absent(_) => None,
            })
            .chain(failures.0.values().flat_map(Failure::types))
            .collect();
        if named.is_empty() {
            return Self(spelled);
        }
        let positions = module
            .declarations()
            .iter()
            .map(|declaration| usize::from(declaration.constant()).saturating_add(1))
            .max()
            .unwrap_or_default();
        let mut names = alloc::vec![Name::from(""); positions];
        for declaration in module.declarations() {
            if let Some(slot) = names.get_mut(usize::from(declaration.constant())) {
                *slot = Name::from(<&str>::from(SourceFragment::from(declaration.name())));
            }
        }
        let source = CoreSource::new(arena, &names);
        for node in named {
            if spelled.contains_key(&node) {
                continue;
            }
            let root = match node {
                | TypeNode::Value(id) => CoreNode::ValueType(id),
                | TypeNode::Computation(id) => CoreNode::CompType(id),
            };
            if let Ok(presentation) = present_type(&source, root, PageWidth::from(SPELLING_WIDTH))
                && !presentation.as_ref().contains('\n')
            {
                let _fresh = spelled.insert(node, presentation);
            }
        }
        Self(spelled)
    }

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
