//! The types a module's checker refusals compare, and the judgements each
//! refused body stood inside, kept while the arena they were judged over is
//! at hand.
//!
//! # Spelled once, at the judgement
//!
//! A checker refusal names type nodes of the arena the module was judged over,
//! and that arena moves into the kernel admission once the module is judged. A
//! face renders the composition before the admission runs and after it is
//! gone, so it cannot read the arena; the types a refusal compares, and the
//! types the judgements it stood inside were checked against, are spelled here
//! instead, through the printer every face shares, and the composition
//! carries the spellings beside the origin table its loci are read through. A
//! module that refuses nothing spells nothing.
//!
//! A checker refusal names type nodes of the arena its module was judged over,
//! and `judge` moves that arena into the `Admission`, so a face rendering the
//! composition — before the admission runs, or after it has consumed the arena
//! — has no node to read. `judge` therefore spells every type a produced
//! checker refusal compares, as `CheckRefusal::compared` names them, through
//! `gandr-surface-pretty` on a 100-column page, and `Composed::Settled` carries
//! them as `spellings` beside the origin table, keyed by node; `Spellings::get`
//! answers a node with its spelling or `spelling::Absent::Unspelled`. A type
//! the printer cannot lay out on one line is left unspelled, since its spelling
//! stands in a one-line label. A module that refuses nothing spells nothing, so
//! a clean run pays one scan of its reports.
//!
//! The alternatives were keeping the arena in the composition, which costs a
//! copy of the whole arena per revision or makes the admission borrow what the
//! face also reads, and spelling in the renderer from a cloned arena, which
//! costs the same copy. The choice reverses when a face needs a type the
//! refusal does not name — a binder's in the typing context at the failure, say
//! — which needs the arena or a richer table at the judgement.
//!
//! The judgements a refused body stood inside are a refusal's nested reasons,
//! and they name nodes of the same arena. `judge` copies the checker's trails
//! out of its report as `Trails` before the report moves into the `Admission`,
//! keyed by admission position, which each settled `DeclarationReport` names,
//! and spells the type each judgement was checked against into the same
//! `Spellings`. A clean module copies an empty map. The alternative was reading
//! the trails off the admission's report, which a face rendering after the
//! admission ran does not hold; the choice reverses with the arena's, when the
//! face keeps the judgement's report.
//!
//! # A refusal's trail is kept by position
//!
//! The checker traces each refused body: the value and computation judgements
//! the refusal stood inside, outermost first, each a term node and the type it
//! was checked against. The composition keeps them by the declaration's
//! admission position, which a settled declaration report names, so a face
//! finds a refusal's nested reasons without the checker's report.

use alloc::collections::BTreeMap;
use alloc::vec::Vec;

use anodized::spec;
use gandr_core_checker::ModuleReport;
use gandr_core_checker::Pending;
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
            /// No refusal of the module compares the node, or the printer
            /// could not lay it out on one line.
            Unspelled,
        }
    }
}

/// The page a spelled type is laid out on: one line beside a source locus, as
/// wide as the transcript a session prints.
const SPELLING_WIDTH: u32 = 100;

/// The spelling of every type a module's checker refusals compare, keyed by
/// its node.
///
/// # Specification
/// - requires: built by [`Spellings::of`] over the arena the refusals were
///   judged over.
/// - ensures: each node keyed is one a refusal of the module compares, or one a
///   judgement its trail holds was checked against, spelled by the shared
///   printer.
/// - panics: none.
/// - executable: none — this data type has no call boundary; [`Spellings::of`]
///   carries the predicates.
///
/// # Adequacy
/// - hypothesis: L3 — a mismatch spells both of its types and a module that
///   refuses nothing spells none.
/// - witness: `spelled::tests::a_refusal_spells_the_types_it_compares`
/// - witness: `spelled::tests::a_refusal_keeps_the_judgements_it_stood_inside`
#[repr(transparent)]
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Spellings(BTreeMap<TypeNode, Presentation>);

impl Spellings
{
    /// Spell every type the checker refusals `report` settled compare, and
    /// every type a judgement of `trails` was checked against, their nodes read
    /// from `arena` and their constants named by `module`.
    ///
    /// # Specification
    /// - requires: `report` settled the verdicts judged over `arena`, of the
    ///   declarations `module` lowered into it, and `trails` holds those
    ///   verdicts' trails.
    /// - ensures: each type a produced checker refusal compares, as
    ///   [`gandr_core_checker::CheckRefusal::compared`] names it, and each type
    ///   a trail's judgement was checked against, is keyed by its node and
    ///   spelled through [`present_type`] on a page of [`SPELLING_WIDTH`]
    ///   columns, constants by their declared names; a type the printer cannot
    ///   lay out, or lays out over more than one line, is left unkeyed, since
    ///   its spelling stands in a one-line label; nothing else is keyed.
    /// - provides: the spellings a face reads a refusal's types from once the
    ///   arena is gone.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a value mismatch spells its expected and found types
    ///   apart; a trail spells the type its outer judgement was checked
    ///   against; a module whose declarations all check spells none.
    /// - witness: `spelled::tests::a_refusal_spells_the_types_it_compares`
    /// - witness: `spelled::tests::a_refusal_keeps_the_judgements_it_stood_inside`
    #[spec(ensures: |ret| ret.0.iter().all(|(node, presentation)| !presentation.as_ref().contains('\n')
        && (report.declarations().iter().any(|declaration|
            matches!(declaration.produced().refusal(), Maybe::Present(Refusal::Checking(refusal))
                if [refusal.compared().expected, refusal.compared().found].contains(&Maybe::Present(*node))))
            || trails.0.values().flatten().any(|pending| pending.expected == Maybe::Present(*node)))))]
    #[inline]
    #[must_use]
    pub fn of(
        arena: &CoreArena,
        module: &LoweredModule<'_>,
        report: &SettleReport<'_>,
        trails: &Trails,
    ) -> Self
    {
        let mut spelled = BTreeMap::new();
        let compared: Vec<TypeNode> = report
            .declarations()
            .iter()
            .filter_map(|declaration| match declaration.produced().refusal() {
                | Maybe::Present(Refusal::Checking(refusal)) => Some(refusal.compared()),
                | Maybe::Present(
                    Refusal::Lowering(_) | Refusal::Corpus(_) | Refusal::Readmission { .. },
                )
                | Maybe::Absent(_) => None,
            })
            .flat_map(|compared| [compared.expected, compared.found])
            .filter_map(|side| match side {
                | Maybe::Present(node) => Some(node),
                | Maybe::Absent(_) => None,
            })
            .chain(
                trails
                    .0
                    .values()
                    .flatten()
                    .filter_map(|pending| match pending.expected {
                        | Maybe::Present(node) => Some(node),
                        | Maybe::Absent(_) => None,
                    }),
            )
            .collect();
        if compared.is_empty() {
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
        for node in compared {
            let root = match node {
                | TypeNode::Value(id) => CoreNode::ValueType(id),
                | TypeNode::Computation(id) => CoreNode::CompType(id),
            };
            if let Ok(presentation) = present_type(&source, root, PageWidth::from(SPELLING_WIDTH))
                && !presentation.as_ref().contains('\n')
            {
                let _replaced = spelled.insert(node, presentation);
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

/// The judgements each refused body of a module stood inside, outermost first,
/// by the declaration's admission position.
///
/// # Specification
/// - requires: built by [`Trails::of`] from the checker's report.
/// - ensures: each position keyed is a refused body's, its trail non-empty.
/// - panics: none.
/// - executable: none — this data type has no call boundary; [`Trails::of`]
///   carries the predicates.
///
/// # Adequacy
/// - hypothesis: L3 — a refused body keeps its trail under its position and a
///   module that refuses nothing keeps none.
/// - witness: `spelled::tests::a_refusal_keeps_the_judgements_it_stood_inside`
#[repr(transparent)]
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Trails(BTreeMap<ConstantIndex, Vec<Pending>>);

impl Trails
{
    /// The trails the checker's `report` holds.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: exactly the report's trails, by position.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a refused body's trail is read back under its
    ///   position.
    /// - witness: `spelled::tests::a_refusal_keeps_the_judgements_it_stood_inside`
    #[spec(ensures: |ret| &ret.0 == report.pending())]
    #[inline]
    #[must_use]
    pub fn of(report: &ModuleReport) -> Self
    {
        Self(report.pending().clone())
    }

    /// The judgements the body at `constant` was refused inside, outermost
    /// first; none when it was not refused or not judged.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn get(
        &self,
        constant: ConstantIndex,
    ) -> &[Pending]
    {
        self.0.get(&constant).map_or(&[], Vec::as_slice)
    }
}

#[cfg(test)]
mod tests
{
    use gandr_core_checker::CheckRefusal;
    use gandr_core_checker::Mismatch;
    use gandr_core_checker::TypeNode;
    use gandr_surface_corpus::CorpusRoot;
    use gandr_surface_corpus::Refusal;
    use gandr_surface_grammar::built_in;
    use gandr_surface_syntax::SourceText;
    use quenchant_shape::shape::Maybe;

    use crate::compose::Composed;
    use crate::compose::LoweringCount;
    use crate::compose::compose;

    #[test]
    fn a_refusal_spells_the_types_it_compares()
    {
        let grammar = built_in().expect("the built-in grammar builds");
        let mut lowerings = LoweringCount::default();
        let Ok(Composed::Settled {
            report, spellings, ..
        }) = compose(
            &grammar,
            CorpusRoot::Fixture,
            SourceText::from("def wrong : Integer ;\ndef wrong = \"text\" ;\n"),
            &mut lowerings,
        )
        else {
            panic!("the module settles");
        };
        let [ref declaration] = *report.declarations()
        else {
            panic!("one declaration");
        };
        let Maybe::Present(Refusal::Checking(CheckRefusal::TypeMismatch(Mismatch::Value {
            synthesised,
            expected,
            ..
        }))) = declaration.produced().refusal()
        else {
            panic!("the declaration is a value mismatch");
        };
        let spelled = |node| match spellings.get(node) {
            | Maybe::Present(presentation) => presentation.as_ref().to_owned(),
            | Maybe::Absent(reason) => format!("{reason:?}"),
        };
        assert_eq!(spelled(TypeNode::Value(expected)), "Integer");
        assert_eq!(spelled(TypeNode::Value(synthesised)), "String");

        let Ok(Composed::Settled {
            spellings, trails, ..
        }) = compose(
            &grammar,
            CorpusRoot::Fixture,
            SourceText::from("def right : Integer ;\ndef right = 1 ;\n"),
            &mut lowerings,
        )
        else {
            panic!("the module settles");
        };
        assert_eq!(
            spellings,
            super::Spellings::default(),
            "a module that refuses nothing spells nothing"
        );
        assert_eq!(
            trails,
            super::Trails::default(),
            "a module that refuses nothing keeps no trail"
        );
    }

    #[test]
    fn a_refusal_keeps_the_judgements_it_stood_inside()
    {
        let grammar = built_in().expect("the built-in grammar builds");
        let mut lowerings = LoweringCount::default();
        let Ok(Composed::Settled {
            report,
            spellings,
            trails,
            ..
        }) = compose(
            &grammar,
            CorpusRoot::Fixture,
            SourceText::from("def a : +U (-F Integer) ;\ndef a = thunk { become force 1 } ;\n"),
            &mut lowerings,
        )
        else {
            panic!("the module settles");
        };
        let [ref declaration] = *report.declarations()
        else {
            panic!("one declaration");
        };
        let trail = trails.get(declaration.constant());
        let spelled: Vec<String> = trail
            .iter()
            .map(|pending| match pending.expected {
                | Maybe::Present(node) => match spellings.get(node) {
                    | Maybe::Present(presentation) => presentation.as_ref().to_owned(),
                    | Maybe::Absent(reason) => format!("{reason:?}"),
                },
                | Maybe::Absent(reason) => format!("{reason:?}"),
            })
            .collect();
        assert_eq!(
            spelled,
            ["+U (-F Integer)", "-F Integer"],
            "the thunk was checked against its declared type and the force inside it \
             against the thunk's computation type: {trail:?}"
        );
    }
}
