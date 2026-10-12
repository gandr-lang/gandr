//! The types a module's checker refusals compare, spelled while the arena they
//! were judged over is at hand.
//!
//! # Spelled once, at the judgement
//!
//! A checker refusal names type nodes of the arena the module was judged over,
//! and that arena moves into the kernel admission once the module is judged. A
//! face renders the composition before the admission runs and after it is
//! gone, so it cannot read the arena; the types a refusal compares are spelled
//! here instead, through the printer every face shares, and the composition
//! carries the spellings beside the origin table its loci are read through. A
//! module that refuses nothing spells nothing.

use alloc::collections::BTreeMap;
use alloc::vec::Vec;

use anodized::spec;
use gandr_core_checker::TypeNode;
use gandr_core_term::CoreArena;
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
/// - ensures: each node keyed is one a refusal of the module compares, spelled
///   by the shared printer.
/// - panics: none.
/// - executable: none — this data type has no call boundary; [`Spellings::of`]
///   carries the predicates.
///
/// # Adequacy
/// - hypothesis: L3 — a mismatch spells both of its types and a module that
///   refuses nothing spells none.
/// - witness: `spelled::tests::a_refusal_spells_the_types_it_compares`
#[repr(transparent)]
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Spellings(BTreeMap<TypeNode, Presentation>);

impl Spellings
{
    /// Spell every type the checker refusals `report` settled compare, their
    /// nodes read from `arena` and their constants named by `module`.
    ///
    /// # Specification
    /// - requires: `report` settled the verdicts judged over `arena`, of the
    ///   declarations `module` lowered into it.
    /// - ensures: each type a produced checker refusal compares, as
    ///   [`gandr_core_checker::CheckRefusal::compared`] names it, is keyed by
    ///   its node and spelled through [`present_type`] on a page of
    ///   [`SPELLING_WIDTH`] columns, constants by their declared names; a type
    ///   the printer cannot lay out, or lays out over more than one line, is
    ///   left unkeyed, since its spelling stands in a one-line label; nothing
    ///   else is keyed.
    /// - provides: the spellings a face reads a refusal's types from once the
    ///   arena is gone.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a value mismatch spells its expected and found types
    ///   apart; a module whose declarations all check spells none.
    /// - witness: `spelled::tests::a_refusal_spells_the_types_it_compares`
    #[spec(ensures: |ret| ret.0.iter().all(|(node, presentation)| !presentation.as_ref().contains('\n')
        && report.declarations().iter().any(|declaration|
        matches!(declaration.produced().refusal(), Maybe::Present(Refusal::Checking(refusal))
            if [refusal.compared().expected, refusal.compared().found].contains(&Maybe::Present(*node))))))]
    #[inline]
    #[must_use]
    pub fn of(
        arena: &CoreArena,
        module: &LoweredModule<'_>,
        report: &SettleReport<'_>,
    ) -> Self
    {
        let mut spelled = BTreeMap::new();
        let compared: Vec<TypeNode> = report
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

        let Ok(Composed::Settled { spellings, .. }) = compose(
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
    }
}
