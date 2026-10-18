//! `Model(S)`: the signature of a `theory` block's models, derived from what
//! the block presents.
//!
//! # `theory` presents, `Model(S)` structures
//!
//! A `theory` block presents a shape: sorts, some indexed by a telescope of
//! earlier sorts, operations between them, and rules relating operation terms.
//! Its models are ordinary modules, and the signature they are checked against
//! is computed from the presentation rather than written by hand: one type
//! component per sort, an indexed sort a type family over its index telescope;
//! one value component per operation, whose type binds every sort variable the
//! operation's ports leave free as a dependent parameter before the ports
//! themselves; and one `Path`-typed law per rule, quantified over the rule's
//! variables, between the operation terms it relates. This is Lawvere's
//! reading of a theory — a model is a structure-preserving interpretation, and
//! `Model(S)` the signature of such interpretations into the value universe —
//! with the sorts, operations and equations laid out as one telescope, as
//! Kaposi and Kovács read a signature off a presentation. Laws are identity-
//! typed fields, so two models with equal operations and different laws are
//! different models (Ahrens, North, Shulman and Tsementzis).
//!
//! - Choice: derive the signature from the block's `Theory` value
//!   (`gandr_theory_levitation::TheoryValue`), the presentation the block
//!   defines — each port's sort a sort name over index terms, each rule with
//!   its name — read beside the name tiles that place its members.
//!   Alternatives: deriving from the elaborated cell store, which keeps no rule
//!   names and declines a law over an indexed sort whose producer side applies
//!   an operation to a composite, so `Model` would inherit a cell gate that
//!   says nothing about the law; and reading the description's sort spellings
//!   back as text. Reversal: a cell store that keeps names and composites would
//!   let `Model` read the cells, one source for both.
//! - Choice: `Model` is an elaboration-stage function of the value a theory
//!   block defines, not a core function `Theory -> Type`. A model signature is
//!   a telescope whose components are types, families and laws, large
//!   components no first-order code computation states, so the derivation reads
//!   the value's normal form where the block writes it. Alternatives: a core
//!   `Model` by large elimination over `Theory`, which the code universe rules
//!   out. Reversal: normal forms of computed `Theory` values at elaboration
//!   time, which would let `Model` read a value no block writes.
//! - Choice: every rule reads as a `Path` — the invertible overlay — whatever
//!   its arrow. Alternatives: a directed reading of rules as rewrites, which
//!   needs a directed identity the value universe does not have. Reversal:
//!   directed models.
//!
//! # Clauses bind their free sort variables
//!
//! `oper comp : (f : Hom(a, b), g : Hom(b, c)) --> Hom(a, c)` leaves `a`, `b`
//! and `c` free; their sorts are inferred by unification against the index
//! telescope of the sorts they index (`Hom(dom : Ob, cod : Ob)` makes each an
//! `Ob`), and the operation's type binds them first, in the order a walk of
//! the ports meets them, each sort's own variables before it:
//! `(a : Ob, b : Ob, c : Ob, f : Hom(a, b), g : Hom(b, c)) => Hom(a, c)`. A
//! rule's variables are inferred the same way from the terms it relates, each
//! application elaborated with the implicit arguments its operation binds, so
//! `comp(id(a), f) ==> f` is the law
//! `(a : Ob, b : Ob, f : Hom(a, b)) => Path(Hom(a, b), comp(a, a, b, id(a), f),
//! f)`: the variables standing in another variable's sort first, in the order a
//! walk of the rule's written variables meets them, each sort before its
//! variable, then the rest in order of first occurrence. A variable a rule
//! leaves unnamed takes the first letter the rule does not write.
//!
//! - Choice: first-order unification over index terms, run as one explicit
//!   worklist. Alternatives: requiring every implicit argument written, which
//!   makes the presentation restate what its ports already say. Reversal: a
//!   theory that writes higher-order index terms.
//!
//! A component the derivation cannot state is kept with its fault, so the
//! module ascribed to `Model(S)` refuses that component by name and keeps the
//! others: a rule relating a many-out operation's results, a circuit rule, a
//! variable no occurrence sorts, and an ill-sorted term.
//!
//! # References
//!
//! - F. William Lawvere. "Functorial Semantics of Algebraic Theories."
//!   _Proceedings of the National Academy of Sciences_ 50(5) (1963).
//!   <https://doi.org/10.1073/pnas.50.5.869>
//! - Ambrus Kaposi and András Kovács. "Signatures and Induction Principles for
//!   Higher Inductive-Inductive Types." _Logical Methods in Computer Science_
//!   16(1) (2020). <https://doi.org/10.23638/LMCS-16(1:10)2020>
//! - Benedikt Ahrens, Paige Randall North, Michael Shulman and Dimitris
//!   Tsementzis. "The Univalence Principle." arXiv:2102.06275 (2021).
//! - J. A. Robinson. "A Machine-Oriented Logic Based on the Resolution
//!   Principle." _Journal of the ACM_ 12(1) (1965).
//!   <https://doi.org/10.1145/321250.321253> — first-order unification.

use alloc::collections::BTreeMap;
use alloc::format;
use alloc::vec::Vec;

use anodized::spec;
use gandr_surface_syntax::ByteSpan;
use gandr_theory_levitation::FreeTerm;
use gandr_theory_levitation::Name;
use gandr_theory_levitation::TheoryDesc;
use gandr_theory_levitation::TheoryFault;
use gandr_theory_levitation::TheoryPort;
use gandr_theory_levitation::TheoryValue;
use quenchant_shape::shape::Maybe;

use crate::description::DescriptionGrade;
use crate::form::Placed;

mod infer;
#[cfg(test)]
mod tests;

quenchant_shape::reason_enum! {
    /// Why a described declaration presents no model signature.
    pub mod presentation {
        /// The reason a declaration has no presentation.
        #[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
        pub enum Absent {
            /// A `data` or `codata` family, which is a type of its own rather
            /// than a shape with models.
            Family,
            /// A top-level `oper`, one operation outside any theory.
            Circuit,
        }
    }
}

/// The presentation a description route attaches to a declaration.
///
/// # Specification
/// trivial.
pub type Presented = Maybe<Presentation, presentation::Absent>;

/// A sort applied to index terms, as a port or an index states it:
/// `Hom(a, b)`, or `Ob` with no indices.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: the sort's name and its index terms in written order; a derived
///   sort term carries every index its sort binds, implicit ones first.
/// - executable: none — a sort term is data the derivation reads.
///
/// # Adequacy
/// - hypothesis: L3 — the `CatShape` presentation's port sorts and their
///   derived forms are asserted whole.
/// - witness: `model::tests::the_cat_shape_operations_bind_their_free_sorts_first`
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SortTerm
{
    /// The sort's name.
    pub sort: Name,
    /// Its index terms, left to right.
    pub indices: Vec<FreeTerm>,
}

/// A named port: an operation's input or output, or a sort's index.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: the port's name — for an unnamed one, the placeholder `_i` its
///   position `i` among its member's ports gives it — its sort, and the
///   variables it binds, outermost first.
/// - executable: none — a port is data the derivation reads.
///
/// # Adequacy
/// - hypothesis: L3 — as [`SortTerm`].
/// - witness: `model::tests::the_cat_shape_operations_bind_their_free_sorts_first`
/// - witness: `model::tests::an_underivable_component_keeps_its_fault`
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Port
{
    /// The port's name.
    pub name: Name,
    /// Its sort.
    pub sort: SortTerm,
    /// The `pi+` binders over it, each a named variable of a representable
    /// sort; empty for a first-order port.
    pub binders: Vec<Binder>,
}

/// A sort a theory declares, with its index telescope.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: the sort's name, name tile and written indices.
/// - executable: none — a presented sort is data the derivation reads.
///
/// # Adequacy
/// - hypothesis: L3 — the `CatShape` sorts derive their components.
/// - witness: `model::tests::the_cat_shape_sorts_are_a_type_and_a_family`
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PresentedSort
{
    /// The sort's name.
    pub name: Name,
    /// Its name tile.
    pub named: Placed,
    /// Its written index telescope.
    pub indices: Vec<Port>,
}

/// An operation a theory declares, with its boundary.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: the operation's name, name tile, and its input and output ports
///   in written order.
/// - executable: none — a presented operation is data the derivation reads.
///
/// # Adequacy
/// - hypothesis: L3 — as [`SortTerm`].
/// - witness: `model::tests::the_cat_shape_operations_bind_their_free_sorts_first`
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PresentedOperation
{
    /// The operation's name.
    pub name: Name,
    /// Its name tile.
    pub named: Placed,
    /// Its input ports.
    pub inputs: Vec<Port>,
    /// Its output ports.
    pub outputs: Vec<Port>,
}

/// A rule a theory writes as a face between two terms.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: the rule's name, name tile and the two terms it relates, as
///   written.
/// - executable: none — a presented law is data the derivation reads.
///
/// # Adequacy
/// - hypothesis: L3 — the three `CatShape` laws derive their components.
/// - witness: `model::tests::the_cat_shape_laws_relate_elaborated_terms`
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PresentedLaw
{
    /// The rule's name.
    pub name: Name,
    /// Its name tile.
    pub named: Placed,
    /// The term it rewrites from.
    pub left: FreeTerm,
    /// The term it rewrites to.
    pub right: FreeTerm,
}

/// A circuit rule a theory wires, kept by name.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: the rule's name and name tile.
/// - executable: none — a presented circuit is data the derivation reads.
///
/// # Adequacy
/// - hypothesis: L3 — a circuit rule derives a component refused by name.
/// - witness: `model::tests::an_underivable_component_keeps_its_fault`
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PresentedCircuit
{
    /// The rule's name.
    pub name: Name,
    /// Its name tile.
    pub named: Placed,
}

/// What a `theory` block presents: its `Theory` value, where each member the
/// value codes is written, and the circuit rules `Theory` does not code yet.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: the value is the one source of the presented sorts, operations
///   and faces; the placement holds one name tile per member it codes, in the
///   value's order.
/// - executable: none — a presentation is data the derivation reads.
///
/// # Adequacy
/// - hypothesis: L3 — the `CatShape` presentation derives the `CatShape` model.
/// - witness: `model::tests::the_cat_shape_sorts_are_a_type_and_a_family`
/// - witness: `model::tests::a_presentation_reads_its_members_off_its_value`
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Presentation
{
    /// The presentation as a value of `Theory`.
    pub value: TheoryValue,
    /// Where each member the value codes is written.
    pub placement: Placement,
    /// The rules wired as circuits, kept beside the value.
    pub circuits: Vec<PresentedCircuit>,
}

/// Where the members a presentation's value codes are written: one name tile
/// per sort, per operation and per face, in the value's order, and each
/// face's whole member.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: each list in written order.
/// - executable: none — a placement is provenance beside a value.
///
/// # Adequacy
/// - hypothesis: L3 — as [`Presentation`].
/// - witness: `model::tests::a_presentation_reads_its_members_off_its_value`
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Placement
{
    /// Each sort's name tile.
    pub sorts: Vec<Placed>,
    /// Each operation's name tile.
    pub operations: Vec<Placed>,
    /// Each face's name tile.
    pub laws: Vec<Placed>,
    /// Each face's whole member.
    pub faces: Vec<ByteSpan>,
}

/// The members a presentation's value codes, each at its name tile.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: sorts, operations and faces, each in written order.
/// - executable: none — members are data the derivation reads.
///
/// # Adequacy
/// - hypothesis: L3 — as [`Presentation::members`].
/// - witness: `model::tests::a_presentation_reads_its_members_off_its_value`
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Members
{
    /// The declared sorts.
    pub sorts: Vec<PresentedSort>,
    /// The declared operations.
    pub operations: Vec<PresentedOperation>,
    /// The rules written as faces.
    pub laws: Vec<PresentedLaw>,
}

/// Why a presentation's members cannot be read.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: the value's own fault, or a member no tile places.
/// - executable: none — a fault is data.
///
/// # Adequacy
/// - hypothesis: L3 — as [`Presentation::members`].
/// - witness: `model::tests::a_presentation_reads_its_members_off_its_value`
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum PresentationFault
{
    /// The value codes no presentation.
    Value(TheoryFault),
    /// The value codes a member its placement holds no tile for.
    Unplaced,
}

impl Presentation
{
    /// The members the value codes, each at its tile; an unnamed port reads
    /// as the placeholder its position names.
    ///
    /// # Specification
    /// - ensures: one presented sort, operation and face per member the value
    ///   codes, in its order, each at the placement's tile of the same
    ///   position.
    /// - fails: [`PresentationFault::Value`] for a value that codes no
    ///   presentation; [`PresentationFault::Unplaced`] when the value codes
    ///   more members of a kind than the placement places.
    /// - panics: none.
    ///
    /// # Errors
    /// As stated.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a presentation with an unnamed port reads back its
    ///   members, the port at its placeholder, and a placement one sort,
    ///   operation or law tile short is refused; the `CatShape` derivation
    ///   reads its members this way.
    /// - witness: `model::tests::a_presentation_reads_its_members_off_its_value`
    /// - witness: `model::tests::the_cat_shape_sorts_are_a_type_and_a_family`
    #[inline]
    #[spec(ensures: |ref ret| ret.as_ref().map_or(true, |members| {
        members.sorts.len() <= self.placement.sorts.len()
            && members.operations.len() <= self.placement.operations.len()
            && members.laws.len() <= self.placement.laws.len()
    }))]
    pub fn members(&self) -> Result<Members, PresentationFault>
    {
        let parts = self.value.decode().map_err(PresentationFault::Value)?;
        if parts.sorts.len() > self.placement.sorts.len()
            || parts.operations.len() > self.placement.operations.len()
            || parts.rules.len() > self.placement.laws.len()
        {
            return Err(PresentationFault::Unplaced);
        }
        let mut members = Members::default();
        for (sort, &named) in parts.sorts.into_iter().zip(&self.placement.sorts) {
            let names = presented_names(&sort.indices, &[]);
            members.sorts.push(PresentedSort {
                name: sort.name,
                named,
                indices: ports(sort.indices, names),
            });
        }
        for (operation, &named) in parts.operations.into_iter().zip(&self.placement.operations) {
            let mut names = presented_names(&operation.inputs, &operation.outputs).into_iter();
            members.operations.push(PresentedOperation {
                name: operation.name,
                named,
                inputs: ports(operation.inputs, names.by_ref()),
                outputs: ports(operation.outputs, names),
            });
        }
        for (law, &named) in parts.rules.into_iter().zip(&self.placement.laws) {
            members.laws.push(PresentedLaw {
                name: law.name,
                named,
                left: law.left,
                right: law.right,
            });
        }
        Ok(members)
    }
}

/// The ports `coded`, each under the next of `names`, its binders under their
/// own names.
///
/// # Specification
/// trivial.
fn ports<Names>(
    coded: Vec<TheoryPort>,
    names: Names,
) -> Vec<Port>
where
    Names: IntoIterator<Item = Name>,
{
    coded
        .into_iter()
        .zip(names)
        .map(|(port, name)| Port {
            name,
            sort: SortTerm {
                sort: port.sort,
                indices: port.indices,
            },
            binders: port
                .bindings
                .into_iter()
                .map(|binder| Binder {
                    name: binder.name,
                    sort: SortTerm {
                        sort: binder.sort,
                        indices: binder.indices,
                    },
                })
                .collect(),
        })
        .collect()
}

/// The names a member's ports present under, `inputs` then `outputs`: each
/// port's own, or for an unnamed one the placeholder `_position` of its
/// position among all of them, which the named-port normal form reads as
/// anonymous.
///
/// # Specification
/// - ensures: one name per port, in order; a named port's own name.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — an unnamed output after one input presents as `_1`, after
///   two as `_2`, and a named port as itself.
/// - witness: `model::tests::a_presentation_reads_its_members_off_its_value`
#[spec(ensures: |ref names| names.len() == inputs.len().saturating_add(outputs.len()))]
pub(crate) fn presented_names(
    inputs: &[TheoryPort],
    outputs: &[TheoryPort],
) -> Vec<Name>
{
    inputs
        .iter()
        .chain(outputs)
        .enumerate()
        .map(|(position, port)| {
            if port.name.as_ref().is_empty() {
                Name::from(format!("_{position}"))
            }
            else {
                port.name.clone()
            }
        })
        .collect()
}

/// One binder of a derived telescope.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: the binder's name and its sort, whose index terms name only the
///   binders before it.
/// - executable: none — a binder is data the lowering mints from.
///
/// # Adequacy
/// - hypothesis: L3 — as [`SortTerm`].
/// - witness: `model::tests::the_cat_shape_operations_bind_their_free_sorts_first`
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Binder
{
    /// The binder's name.
    pub name: Name,
    /// Its sort.
    pub sort: SortTerm,
}

/// What one component of a model signature states.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: a sort's index telescope, an operation's telescope and results,
///   or a law's telescope, carrier and endpoints; every term names only the
///   telescope's binders and the theory's operations, each application carrying
///   every argument its operation binds.
/// - executable: none — a form is data the lowering mints from.
///
/// # Adequacy
/// - hypothesis: L3 — the `CatShape` sorts, operations and laws are asserted as
///   their exact forms.
/// - witness: `model::tests::the_cat_shape_sorts_are_a_type_and_a_family`
/// - witness: `model::tests::the_cat_shape_operations_bind_their_free_sorts_first`
/// - witness: `model::tests::the_cat_shape_laws_relate_elaborated_terms`
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ModelForm
{
    /// A sort: a type, or a type family over its indices.
    Sort
    {
        /// The index telescope; empty for an unindexed sort.
        indices: Vec<Binder>,
    },
    /// An operation: a function over its telescope returning its results.
    Operation
    {
        /// The free sort variables, then the input ports.
        telescope: Vec<Binder>,
        /// One sort per output port.
        results: Vec<SortTerm>,
    },
    /// A law: a path between two terms, quantified over their variables.
    Law
    {
        /// The rule's variables.
        telescope: Vec<Binder>,
        /// The sort both terms inhabit.
        carrier: SortTerm,
        /// The term the rule rewrites from.
        left: FreeTerm,
        /// The term it rewrites to.
        right: FreeTerm,
    },
}

/// Why the derivation cannot state a component.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: each reason is distinct and names no source position; the
///   component carrying it names the member.
/// - executable: none — a fault is data a refusal carries.
///
/// # Adequacy
/// - hypothesis: L3 — an ill-sorted law, an unsorted variable, a circuit rule
///   and a binding operation each keep their own fault.
/// - witness: `model::tests::an_underivable_component_keeps_its_fault`
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum ModelFault
{
    /// A sort or an operation the theory does not declare, or one used where
    /// the other is read.
    UnknownHead,
    /// An application written with other than its head's explicit count.
    Arity,
    /// A term whose sort disagrees with the sort its position reads.
    IllSorted,
    /// A variable no occurrence gives a sort.
    Unsorted,
    /// A term relating the results of a many-out operation.
    ManyOut,
    /// A circuit rule, whose sphere the model does not read yet.
    Circuit,
    /// A constructor term, which a theory does not declare.
    Constructor,
    /// A component naming a sort or an operation whose own derivation
    /// failed.
    Inherited,
    /// An operation one of whose ports binds a variable: a second-order
    /// operation, whose models are the first-order translation's, not a
    /// structure on the value universe.
    Binding,
}

impl core::fmt::Display for ModelFault
{
    /// The reason, as a clause.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result
    {
        f.write_str(match *self {
            Self::UnknownHead => "names a sort or an operation the theory does not declare",
            Self::Arity => "applies a sort or an operation to the wrong number of arguments",
            Self::IllSorted => "relates a term at a sort its position does not read",
            Self::Unsorted => "binds a variable no occurrence gives a sort",
            Self::ManyOut => "relates the results of a many-out operation",
            Self::Circuit => "is a circuit rule, whose sphere a model does not read yet",
            Self::Constructor => "applies a constructor, which a theory does not declare",
            Self::Inherited => "names a component the model cannot state",
            Self::Binding => {
                "binds a variable over a port, whose models are its first-order translation's"
            },
        })
    }
}

/// One component of a model signature.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: the member's name and name tile in the theory, and what it states
///   or why it states nothing.
/// - executable: none — a component is data the lowering reads.
///
/// # Adequacy
/// - hypothesis: L3 — as [`ModelForm`] and [`ModelFault`].
/// - witness: `model::tests::the_cat_shape_sorts_are_a_type_and_a_family`
/// - witness: `model::tests::an_underivable_component_keeps_its_fault`
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ModelComponent
{
    /// The member's name.
    pub name: Name,
    /// Its name tile in the theory.
    pub named: Placed,
    /// What it states.
    pub form: Result<ModelForm, ModelFault>,
}

/// The signature of a theory's models: its sorts, then its operations, then its
/// laws, each in written order.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: every type component precedes the value components naming it, and
///   every operation precedes the laws naming it.
/// - executable: none — the signature is data the lowering reads.
///
/// # Adequacy
/// - hypothesis: L3 — the `CatShape` signature lists its five components in
///   order.
/// - witness: `model::tests::the_cat_shape_sorts_are_a_type_and_a_family`
#[repr(transparent)]
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct ModelSignature
{
    /// The components, in signature order.
    pub components: Vec<ModelComponent>,
}

/// Derive the model signature of what a theory presents, reading its members
/// off its value.
///
/// # Specification
/// - requires: nothing.
/// - ensures: [`derive_members`] of the value's members and the circuit rules
///   kept beside it.
/// - fails: a value whose members cannot be read, as [`Presentation::members`];
///   any other fault is kept on its component.
/// - panics: none.
/// - executable: none — as [`derive_members`].
///
/// # Errors
/// As [`Presentation::members`].
///
/// # Adequacy
/// - hypothesis: L3 — as [`derive_members`].
/// - witness: `model::tests::the_cat_shape_sorts_are_a_type_and_a_family`
/// - witness: `model::tests::an_underivable_component_keeps_its_fault`
#[inline]
pub fn derive(presentation: &Presentation) -> Result<ModelSignature, PresentationFault>
{
    let members = presentation.members()?;
    Ok(derive_members(&members, &presentation.circuits))
}

/// Derive the model signature of a presentation's members and its circuit
/// rules.
///
/// # Specification
/// - requires: nothing.
/// - ensures: one component per presented sort, operation, face and circuit
///   rule, in that order and each group in written order; a sort's or an
///   operation's telescope binds its free sort variables before its ports, a
///   law's binds the variables in another variable's sort first, and every
///   application carries every argument its operation binds; a component that
///   cannot be stated keeps its fault, an operation one of whose ports binds a
///   variable keeps [`ModelFault::Binding`], and one naming such a component is
///   [`ModelFault::Inherited`].
/// - fails: never; a fault is kept on its component.
/// - panics: none.
/// - executable: none — the inference the components result from is the
///   derivation itself.
///
/// # Adequacy
/// - hypothesis: L3 — the `CatShape` presentation and an ill-sorted, an
///   unsorted, a circuit and a binding member, each asserted as the exact
///   components.
/// - witness: `model::tests::the_cat_shape_sorts_are_a_type_and_a_family`
/// - witness: `model::tests::the_cat_shape_operations_bind_their_free_sorts_first`
/// - witness: `model::tests::the_cat_shape_laws_relate_elaborated_terms`
/// - witness: `model::tests::an_underivable_component_keeps_its_fault`
#[must_use]
pub(crate) fn derive_members(
    members: &Members,
    circuits: &[PresentedCircuit],
) -> ModelSignature
{
    let mut heads: BTreeMap<Name, Result<infer::Head, ModelFault>> = BTreeMap::new();
    let mut components = Vec::new();
    for sort in &members.sorts {
        let head = infer::derive_head(&heads, infer::HeadKind::Sort, &sort.indices, &[]);
        let form = head.clone().map(|derived| ModelForm::Sort {
            indices: derived.binders,
        });
        let _first = heads.insert(sort.name.clone(), head);
        components.push(ModelComponent {
            name: sort.name.clone(),
            named: sort.named,
            form,
        });
    }
    for operation in &members.operations {
        let binds = operation
            .inputs
            .iter()
            .chain(&operation.outputs)
            .any(|port| !port.binders.is_empty());
        let head = if binds {
            Err(ModelFault::Binding)
        }
        else {
            infer::derive_head(
                &heads,
                infer::HeadKind::Operation,
                &operation.inputs,
                &operation.outputs,
            )
        };
        let form = head.clone().map(|derived| ModelForm::Operation {
            telescope: derived.binders,
            results: derived.results,
        });
        let _first = heads.insert(operation.name.clone(), head);
        components.push(ModelComponent {
            name: operation.name.clone(),
            named: operation.named,
            form,
        });
    }
    for law in &members.laws {
        components.push(ModelComponent {
            name: law.name.clone(),
            named: law.named,
            form: infer::derive_law(&heads, law),
        });
    }
    for circuit in circuits {
        components.push(ModelComponent {
            name: circuit.name.clone(),
            named: circuit.named,
            form: Err(ModelFault::Circuit),
        });
    }

    ModelSignature { components }
}

/// Whether a telescope binder is named after it, and so binds.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub(crate) struct Dependent(pub bool);

/// The tail of a derived value component's telescope.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug)]
pub(crate) enum Tail<'form>
{
    /// An operation's results.
    Results(&'form [SortTerm]),
    /// A law's carrier and endpoints.
    Path(&'form SortTerm, &'form FreeTerm, &'form FreeTerm),
}

/// Whether each binder of `telescope` is named by a later binder's sort or
/// by `tail`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: one flag per binder, in order: affirmative exactly when the
///   binder's name is a variable of a later binder's index terms or of the
///   tail's sorts and terms.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — `comp`'s sort binders bind and its morphisms do not;
///   every binder of `unitL` binds.
/// - witness: `tests::modules::models::a_derived_signature_states_what_the_written_one_does`
#[spec(ensures: |ret| ret.len() == telescope.len())]
pub(crate) fn dependence(
    telescope: &[Binder],
    tail: Tail<'_>,
) -> Vec<Dependent>
{
    let mut named: Vec<&Name> = Vec::new();
    match tail {
        Tail::Results(results) => {
            for result in results {
                sort_vars(result, &mut named);
            }
        },
        Tail::Path(carrier, left, right) => {
            sort_vars(carrier, &mut named);
            named.extend(left.to_node().vars());
            named.extend(right.to_node().vars());
        },
    }
    let mut flags = Vec::with_capacity(telescope.len());
    for binder in telescope.iter().rev() {
        flags.push(Dependent(named.contains(&&binder.name)));
        sort_vars(&binder.sort, &mut named);
    }
    flags.reverse();

    flags
}

/// Push every variable of `sort`'s index terms onto `into`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: one entry per variable leaf of each index term, in order.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — as [`dependence`].
/// - witness: `tests::modules::models::a_derived_signature_states_what_the_written_one_does`
#[spec(
    captures: before = into.len(),
    ensures: into.len() >= before,
)]
fn sort_vars<'term>(
    sort: &'term SortTerm,
    into: &mut Vec<&'term Name>,
)
{
    for index in &sort.indices {
        into.extend(index.to_node().vars());
    }
}

/// A `theory` block a module declares, as the lowering read it: its checked
/// description — the species whose sorts and operations generate its models —
/// beside the presentation `Model(S)` derives from.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: the description and the presentation are one declaration's.
/// - executable: none — the handle borrows the module's description report.
///
/// # Adequacy
/// - hypothesis: L3 — a module declaring `CatShape` beside a family hands back
///   one theory, its two sorts and two operations, and the model its instance
///   checks against.
/// - witness: `tests::modules::models::a_lowered_theory_exposes_its_description_and_its_model`
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct LoweredTheory<'module>
{
    /// The theory's name tile.
    pub named: Placed,
    /// Its checked description: the sorts, and the operations as generators.
    pub description: &'module TheoryDesc<DescriptionGrade>,
    /// What it presents to the signature of its models.
    pub presentation: &'module Presentation,
}

impl LoweredTheory<'_>
{
    /// The signature of the theory's models, derived from its presentation's
    /// value.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// As [`derive()`].
    #[inline]
    pub fn model(&self) -> Result<ModelSignature, PresentationFault>
    {
        derive(self.presentation)
    }
}
