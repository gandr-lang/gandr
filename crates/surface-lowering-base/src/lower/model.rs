//! The records of the model types that the lowering's context holds.
//!
//! The classification reads a theory's models as a type, a module packed at
//! its model type and a flattened model implicit into these records. The mint
//! sweep reads them back, and `gandr-surface-lowering` names each one at its
//! old path.

use alloc::vec::Vec;

use anodized::spec;
use gandr_surface_syntax::NodeIndex;
use gandr_theory_levitation::FreeTerm;
use gandr_theory_levitation::Name;
use gandr_theory_levitation::TermView;

use super::arity;
use crate::model::Dependent;
use crate::model::ModelComponent;
use crate::model::ModelForm;
use crate::model::ModelSignature;
use crate::model::SortTerm;
use crate::module::StructureIndex;

pub mod flattened;
pub use self::flattened::ComponentPlace;
pub use self::flattened::Flattened;
pub use self::flattened::ModelSlot;
pub use self::flattened::PlannedModel;
pub use self::flattened::Supplied;
pub use self::flattened::WrittenSlot;

/// A theory's models as a type.
///
/// It holds the signature of each theory that its bundled record reads, the
/// outermost first. Each signature stands beside the places of the theories
/// that its nested components name. It also holds the name that the type is
/// written over.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Bundled
{
    /// The theories, the outermost first; a nested theory stands after the
    /// one nesting it. The outermost holds no component its manifest sorts
    /// fix.
    pub theories: Vec<BundledTheory>,
    /// The theory's name, `T` in `Model(T)`, where every node below the type
    /// is located.
    pub named: NodeIndex,
    /// The outermost theory's manifest sorts, `with sort x = A`: each sort's
    /// name beside the type it is.
    pub manifests: Vec<(Name, NodeIndex)>,
}

impl Bundled
{
    /// Whether the outermost theory's record nests: some component reads one
    /// before it, so it mints as dependent pairs rather than a record keyed by
    /// its labels. A bundle with no theory is not keyed.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn dependent(&self) -> arity::Dependent
    {
        arity::Dependent(self.theories.first().is_none_or(|theory| {
            bundle_dependence(&theory.signature)
                .iter()
                .any(|binds| binds.0)
        }))
    }

    /// The signature of the outermost theory: the one the type is written
    /// over, less the sorts its manifests fix.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn outermost(&self) -> Option<&ModelSignature>
    {
        self.theories.first().map(|theory| &theory.signature)
    }
}

/// One theory of a [`Bundled`] record.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct BundledTheory
{
    /// The signature the theory derives.
    pub signature: ModelSignature,
    /// The place of each nested component's theory, in the order the
    /// components stand.
    pub nested: Vec<usize>,
}

/// A module packed at its model type: the theories of the bundle, as
/// [`Bundled`] reads them, each beside the module giving its members.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Packed
{
    /// The bundle's theories, the outermost first.
    pub theories: Vec<BundledTheory>,
    /// The module giving each theory's members, place for place: the packed
    /// module first, then the member module each nested component names.
    pub modules: Vec<StructureIndex>,
}

/// Whether each component of `signature` is named by a later one, and so its
/// link in the bundled record binds.
///
/// # Specification
/// - requires: nothing.
/// - ensures: one flag per component, in order: affirmative exactly when a
///   later component's sort terms name it or a later law's terms apply it.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the toggle's carrier binds and its operations do not; a
///   law-bearing theory's operations bind.
/// - witness: `gandr-surface-lowering::tests::modules::models::a_model_type_is_the_record_its_theory_derives`
/// - witness: `gandr-surface-lowering::tests::modules::models::a_law_bearing_model_type_reads_its_operations`
#[spec(ensures: |ret| ret.len() == signature.components.len())]
#[cfg_attr(
    dylint_lib = "quenchant_dylints",
    expect(
        linear_search_in_loop,
        reason = "bounded: `named` holds the names one signature's components read"
    )
)]
#[inline]
#[must_use]
pub fn bundle_dependence(signature: &ModelSignature) -> Vec<Dependent>
{
    let mut named: Vec<&Name> = Vec::new();
    let mut flags = Vec::with_capacity(signature.components.len());
    for component in signature.components.iter().rev() {
        flags.push(Dependent(named.contains(&&component.name)));
        component_reads(component, &mut named);
    }
    flags.reverse();

    flags
}

/// Push every name `component` reads onto `into`: the sorts its sort terms
/// name and the operations its terms apply.
///
/// # Specification
/// - requires: nothing.
/// - ensures: one entry per sort term's sort and per application's head, in the
///   order the component states them.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — as [`bundle_dependence`].
/// - witness: `gandr-surface-lowering::tests::modules::models::a_law_bearing_model_type_reads_its_operations`
#[spec(
    captures: before = into.len(),
    ensures: into.len() >= before,
)]
fn component_reads<'form>(
    component: &'form ModelComponent,
    into: &mut Vec<&'form Name>,
)
{
    match component.form {
        Ok(ModelForm::Sort { ref indices, .. }) => {
            for binder in indices {
                sort_reads(&binder.sort, into);
            }
        },
        Ok(ModelForm::Operation {
            ref telescope,
            ref results,
        }) => {
            for binder in telescope {
                for variable in &binder.over {
                    sort_reads(&variable.sort, into);
                }
                sort_reads(&binder.sort, into);
            }
            for result in results {
                sort_reads(result, into);
            }
        },
        Ok(ModelForm::Constant(ref sort)) => sort_reads(sort, into),
        Ok(ModelForm::Law {
            ref telescope,
            ref hypotheses,
            ref carrier,
            ref left,
            ref right,
        }) => {
            for binder in telescope {
                sort_reads(&binder.sort, into);
            }
            for hypothesis in hypotheses {
                sort_reads(&hypothesis.carrier, into);
                term_heads(&hypothesis.left, into);
                term_heads(&hypothesis.right, into);
            }
            sort_reads(carrier, into);
            term_heads(left, into);
            term_heads(right, into);
        },
        Ok(ModelForm::Nested(_)) | Err(_) => {},
    }
}

/// Push the sort `sort` names and the heads its index terms apply onto
/// `into`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the sort's name, then each index term's heads in order.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — as [`bundle_dependence`].
/// - witness: `gandr-surface-lowering::tests::modules::models::a_model_type_is_the_record_its_theory_derives`
#[spec(
    captures: before = into.len(),
    ensures: into.len() > before,
)]
fn sort_reads<'form>(
    sort: &'form SortTerm,
    into: &mut Vec<&'form Name>,
)
{
    into.push(&sort.sort);
    for index in &sort.indices {
        term_heads(index, into);
    }
}

/// Push the head of every application in `term` onto `into`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: one entry per operation application of the term.
/// - fails: never.
/// - panics: none.
///
/// # Termination
/// Each node of the finite term is pushed once and popped once.
///
/// # Adequacy
/// - hypothesis: L3 — as [`bundle_dependence`].
/// - witness: `gandr-surface-lowering::tests::modules::models::a_law_bearing_model_type_reads_its_operations`
#[spec(
    captures: before = into.len(),
    ensures: into.len() >= before,
)]
fn term_heads<'term>(
    term: &'term FreeTerm,
    into: &mut Vec<&'term Name>,
)
{
    let mut pending = Vec::from([term.to_node()]);
    while let Some(node) = pending.pop() {
        match node.view() {
            TermView::Var(_) | TermView::Atom(_) | TermView::Bound(_) => {},
            TermView::Op { name, args } => {
                into.push(name);
                pending.extend(args);
            },
            TermView::Ctor { args, .. }
            | TermView::Results { args }
            | TermView::Inst { args, .. }
            | TermView::Abs { args, .. }
            | TermView::Lam { args, .. } => {
                pending.extend(args);
            },
        }
    }
}
