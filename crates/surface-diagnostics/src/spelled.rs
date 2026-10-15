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
//! one-line label. A module that refuses nothing spells nothing.
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
use alloc::string::String;
use alloc::vec::Vec;

use anodized::spec;
use gandr_core_checker::Failure;
use gandr_core_checker::ModuleReport;
use gandr_core_checker::TypeNode;
use gandr_core_term::CoreArena;
use gandr_kernel_term::ConstantIndex;
use gandr_surface_corpus::Refusal;
use gandr_surface_corpus::SettleReport;
use gandr_surface_lowering::DeclarationOutcome;
use gandr_surface_lowering::LoweredModule;
use gandr_surface_lowering::Role;
use gandr_surface_pretty::Arity;
use gandr_surface_pretty::Constructors;
use gandr_surface_pretty::CoreNode;
use gandr_surface_pretty::CoreSource;
use gandr_surface_pretty::Form;
use gandr_surface_pretty::Name;
use gandr_surface_pretty::PageWidth;
use gandr_surface_pretty::Placement;
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
    ///   [`present_type`] in its sugared form on a page of [`SPELLING_WIDTH`]
    ///   columns, constants by their paths from the top level, so a member of a
    ///   module, a sealed abstract type among them, reads as it is written
    ///   outside it; a type the printer cannot lay out, or lays out over more
    ///   than one line, is left unkeyed; nothing else is keyed.
    /// - provides: the spellings a diagnostic reads a refusal's types from once
    ///   the arena is gone.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a value mismatch spells its expected and found types
    ///   apart; a failure spells the types its rules were checked against; a
    ///   module whose declarations all check spells none; a sealed abstract
    ///   type is spelled by its module's path.
    /// - witness: `diagnostics::diagnostics::a_refusal_keeps_its_failure_and_spells_its_types`
    /// - witness: `diagnostics::diagnostics::a_sealed_type_is_spelled_by_its_path`
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
                Maybe::Present(Refusal::Checking(refusal)) => Some(refusal.compared()),
                Maybe::Present(Refusal::Lowering(_) | Refusal::Corpus(_)) | Maybe::Absent(_) => {
                    None
                },
            })
            .flat_map(|compared| [compared.expected, compared.found])
            .filter_map(|side| match side {
                Maybe::Present(node) => Some(node),
                Maybe::Absent(_) => None,
            })
            .chain(failures.0.values().flat_map(Failure::types))
            .collect();
        if named.is_empty() {
            return Self(spelled);
        }
        let paths = constant_names(module);
        let names: Vec<Name<'_>> = paths.iter().map(|path| Name::from(path.as_str())).collect();
        let families = Families::of(module);
        let constructors = families.naming(&names);
        let source = CoreSource::new(arena, &names).naming(&constructors);
        for node in named {
            if spelled.contains_key(&node) {
                continue;
            }
            let root = match node {
                TypeNode::Value(id) => CoreNode::ValueType(id),
                TypeNode::Computation(id) => CoreNode::CompType(id),
            };
            if let Ok(presentation) = present_type(
                &source,
                root,
                PageWidth::from(SPELLING_WIDTH),
                Form::Sugared,
            ) && !presentation.as_ref().contains('\n')
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
/// - witness: `diagnostics::diagnostics::a_refusal_keeps_its_failure_and_spells_its_types`
/// - witness: `diagnostics::diagnostics::a_sealed_type_is_spelled_by_its_path`
/// - witness: `diagnostics::diagnostics::a_word_spells_by_its_letters`
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
            *slot = module
                .path_of(declaration)
                .iter()
                .map(|segment| <&str>::from(SourceFragment::from(*segment)))
                .collect::<Vec<_>>()
                .join(".");
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
/// - hypothesis: L3 — as [`constant_names`].
/// - witness: `diagnostics::diagnostics::a_word_spells_by_its_letters`
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
            | DeclarationOutcome::Abstract(_)
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
        let arguments: Vec<String> = spelled
            .drain(spelled.len().saturating_sub(fields.len()) ..)
            .rev()
            .collect();
        spelled.push(if arguments.is_empty() {
            name.clone()
        }
        else {
            alloc::format!("{name}({})", arguments.join(", "))
        });
    }
    match (spelled.pop(), spelled.is_empty()) {
        (Some(point), true) => Maybe::Present((cells.sort(), point)),
        _ => unworded,
    }
}

/// The constructors of every data declaration of a module, each family by
/// its constant's admission position.
///
/// Each constructor is kept by its name and field count in tag order, and
/// a family records whether it is the words of a family's loops, whose empty
/// word is spelled `here(a)` at their point `a` and whose letters cons onto
/// the rest of a word. The core names a constructor by its family and its
/// tag, so a printer reads the names here, owned so a table outliving the
/// lowered module keeps them.
#[repr(transparent)]
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Families(Vec<Family>);

/// One data declaration's constructors, as [`Families`] keeps them.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Eq, PartialEq)]
struct Family
{
    /// The admission position of the family's constant.
    constant: usize,
    /// Each constructor's name and field count, in tag order.
    constructors: Vec<(String, usize)>,
    /// Where each constructor's name stands to its fields.
    placement: Placement,
}

impl Families
{
    /// The constructors of every data declaration of `module`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: one family per data declaration whose signature the module
    ///   holds, at its constant's position, its constructors named as written
    ///   in tag order with the field count the signature gives each; the words
    ///   of a family's loops are consed, their empty word named `here(a)` at
    ///   their point `a`.
    /// - provides: the constructor names a [`CoreSource`] spells a constructor
    ///   value and a data case's patterns with.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a refusal whose type mentions a constructor value
    ///   spells it by its declared name; a family left out spells `?`, which
    ///   the test fails on.
    /// - witness: `diagnostics::diagnostics::a_mismatch_spells_the_constructors_its_type_mentions`
    /// - witness: `diagnostics::diagnostics::a_word_spells_by_its_letters`
    #[spec(ensures: |ret| ret.0.len() <= module.declarations().len())]
    #[inline]
    #[must_use]
    pub fn of(module: &LoweredModule<'_>) -> Self
    {
        Self(
            module
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
                    let constructors = module
                        .constructors(index)
                        .iter()
                        .zip(signature.constructors())
                        .enumerate()
                        .map(|(tag, (name, fields))| match point {
                            Maybe::Present((_, ref point)) if tag == 0 => {
                                (alloc::format!("{name}({point})"), fields.len())
                            },
                            Maybe::Present(_) | Maybe::Absent(_) => (name.clone(), fields.len()),
                        })
                        .collect();
                    let placement = match point {
                        Maybe::Present(_) => Placement::Consed,
                        Maybe::Absent(_) => Placement::Applied,
                    };
                    Some(Family {
                        constant: usize::from(declaration.constant()),
                        constructors,
                        placement,
                    })
                })
                .collect(),
        )
    }

    /// The constructor table these families make, each family under the
    /// name `names` gives its constant.
    ///
    /// # Specification
    /// - requires: `names` are the module's constant names by admission
    ///   position, as [`constant_names`] spells them.
    /// - ensures: each family whose constant `names` holds answers its
    ///   constructors by tag, the first family under a name winning.
    /// - provides: the [`Constructors`] a [`CoreSource`] names through.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the table keeps the first family under a name and
    ///   lists none, so a predicate over every family would re-derive the
    ///   shadowing the table itself defines.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::of`].
    /// - witness: `diagnostics::diagnostics::a_mismatch_spells_the_constructors_its_type_mentions`
    #[inline]
    #[must_use]
    pub fn naming<'names>(
        &'names self,
        names: &[Name<'names>],
    ) -> Constructors<'names>
    {
        let mut constructors = Constructors::default();
        for family in &self.0 {
            if let Some(&named) = names.get(family.constant) {
                let members = family
                    .constructors
                    .iter()
                    .map(|&(ref name, fields)| (Name::from(name.as_str()), Arity::from(fields)));
                match family.placement {
                    Placement::Applied => constructors.family(named, members),
                    Placement::Consed => constructors.words(named, members),
                }
            }
        }
        constructors
    }
}
