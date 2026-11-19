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
//! themselves, and per constant (`oper zero : T`), whose type is its own, a
//! sort of the theory or a builtin type; and one `Path`-typed law per rule,
//! quantified over the rule's variables, between the operation terms it
//! relates. This is Lawvere's reading of a theory — a model is a
//! structure-preserving interpretation, and `Model(S)` the signature of such
//! interpretations into the value universe —
//! with the sorts, operations and equations laid out as one telescope, as
//! Kaposi and Kovács read a signature off a presentation. Laws are identity-
//! typed fields, so two models with equal operations and different laws are
//! different models (Ahrens, North, Shulman and Tsementzis).
//!
//! A rule is a cell its theory decides by conversion, and its law is the cell
//! the model carries: `here` where the carrier converts the two sides, a
//! written path otherwise. The checker reads the same law at two more sites. A
//! fold out of the presented type rests on it (`gandr-core-checker`'s
//! `respect`), and a handler of the theory owes it by conversion
//! (`gandr-core-checker`'s `handler`).
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
//! `(a : Ob, b : Ob, c : Ob, f : Hom(a, b), g : Hom(b, c)) -> Hom(a, c)`. A
//! rule's variables are inferred the same way from the terms it relates, each
//! application elaborated with the implicit arguments its operation binds, so
//! `comp(id(a), f) ==> f` is the law
//! `(a : Ob, b : Ob, f : Hom(a, b)) => Path[.A = Hom(a, b)](comp(a, a, b,
//! id(a), f), f)`: the variables standing in another variable's sort first, in
//! the order a walk of the rule's written variables meets them, each sort
//! before its variable, then the rest in order of first occurrence. A variable
//! a rule leaves unnamed takes the first letter the rule does not write.
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
//! - `vault:01a178aa-a07b-7a23-bbcd-cf3893ccc160` — background: the
//!   effect-modalities design (§ The declaration) — a sort indexed by the
//!   host's types derives its family over `Type`, and a `Type[-]` sort's family
//!   lands in the computation types.

use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use alloc::vec::Vec;

use anodized::spec;
use gandr_core_term::builtin::TypeAtom;
use gandr_kernel_term::GroundSort;
use gandr_surface_syntax::ByteSpan;
use gandr_surface_syntax::NodeIndex;
use gandr_theory_circuit_algebras::SpiderCanon;
use gandr_theory_levitation::FreeTerm;
use gandr_theory_levitation::Name;
use gandr_theory_levitation::NameId;
use gandr_theory_levitation::Names;
use gandr_theory_levitation::NominalId;
use gandr_theory_levitation::OperationKind;
use gandr_theory_levitation::Representability;
use gandr_theory_levitation::TermName;
use gandr_theory_levitation::TheoryBinder;
use gandr_theory_levitation::TheoryDesc;
use gandr_theory_levitation::TheoryFault;
use gandr_theory_levitation::TheoryInclusion;
use gandr_theory_levitation::TheoryPort;
use gandr_theory_levitation::TheoryValue;
use gandr_theory_levitation::name_mint;
use gandr_theory_levitation::name_text;
use gandr_theory_levitation::presented_ids;
use quenchant_shape::shape::Maybe;

use crate::description::DescriptionGrade;
use crate::description::written::WrittenCircuit;
use crate::form::Placed;
use crate::resolve::SurfaceName;
use crate::resolve::type_atom;

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
pub struct SortTerm<N = Name>
{
    /// The sort's name.
    pub sort: N,
    /// Its index terms, left to right.
    pub indices: Vec<FreeTerm<N>>,
}

quenchant_shape::reason_enum! {
    /// Why a sort term names no builtin of the host.
    pub mod builtin_sort {
        /// The reason a sort term names no builtin.
        #[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
        pub enum Absent {
            /// The term applies its head to index terms.
            Indexed,
            /// The term's name is neither `Type` nor a builtin type.
            Named,
        }
    }
}

/// A builtin of the host a sort term names: a builtin type, or the universe of
/// the host's types at a ground sort.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: the atom a builtin type's name spells, or the ground sort a bare
///   `Type` ranges over.
/// - executable: none — a builtin sort is data its readers match on.
///
/// # Adequacy
/// - hypothesis: L3 — as [`SortTerm::builtin`].
/// - witness: `model::tests::a_sort_indexed_by_host_types_is_a_family_over_the_universe_2114`
/// - witness: `model::tests::a_sort_indexed_by_a_builtin_type_is_a_family_over_it_3079`
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum BuiltinSort
{
    /// A builtin type: `Integer`, `String`.
    Atom(TypeAtom),
    /// The universe of the host's types at a ground sort: `Type`.
    Universe(GroundSort),
}

impl<N> SortTerm<N>
where
    N: TermName,
{
    /// The builtin of the host the term names, its name read in `names`: the
    /// value types for a bare `Type`, the sort an index of a sort indexed by
    /// host types ranges over, or the builtin type an unindexed name spells.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: [`BuiltinSort::Universe`] at the value sort exactly when the
    ///   term is `Type` applied to no index term; [`BuiltinSort::Atom`] when it
    ///   is a builtin type's name applied to none.
    /// - fails: never; every other term, and a name `names` does not hold, is
    ///   an absence.
    /// - panics: none.
    /// - executable: none — the clause would read the name again, which is the
    ///   comparison the body makes.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a sort indexed at `Type` derives its family over the
    ///   universe, and a theory sort beside it keeps its own head; a sort
    ///   indexed at a builtin type derives its family over that type.
    /// - witness: `model::tests::a_sort_indexed_by_host_types_is_a_family_over_the_universe_2114`
    /// - witness: `model::tests::a_sort_indexed_by_a_builtin_type_is_a_family_over_it_3079`
    #[inline]
    pub fn builtin_in(
        &self,
        names: &Names,
    ) -> Maybe<BuiltinSort, builtin_sort::Absent>
    {
        if !self.indices.is_empty() {
            return Maybe::Absent(builtin_sort::Absent::Indexed);
        }
        let Maybe::Present(spelled) = self.sort.spelled(names)
        else {
            return Maybe::Absent(builtin_sort::Absent::Named);
        };
        if spelled.as_ref() == crate::form::TileName::UNIVERSE.as_ref() {
            return Maybe::Present(BuiltinSort::Universe(GroundSort::Value));
        }
        match type_atom(SurfaceName::from(spelled.as_ref())) {
            Maybe::Present(atom) => Maybe::Present(BuiltinSort::Atom(atom)),
            Maybe::Absent(_) => Maybe::Absent(builtin_sort::Absent::Named),
        }
    }
}

impl SortTerm
{
    /// The builtin of the host a text sort term names, as
    /// [`SortTerm::builtin_in`] reads it: a text name reads itself.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn builtin(&self) -> Maybe<BuiltinSort, builtin_sort::Absent>
    {
        self.builtin_in(&Names::new())
    }
}

impl<N> SortTerm<N>
{
    /// The sort term with each name replaced by its image under `name`.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Cost
    /// - allocation: the mapped index terms, durable by the term it maps
    ///
    /// # Errors
    /// The first error `name` returns.
    #[inline]
    pub fn map_names<M, E, F>(
        &self,
        name: &mut F,
    ) -> Result<SortTerm<M>, E>
    where
        F: FnMut(&N) -> Result<M, E>,
    {
        let sort = name(&self.sort)?;
        let mut indices = Vec::with_capacity(self.indices.len());
        for index in &self.indices {
            indices.push(index.map_names(&mut *name)?);
        }
        Ok(SortTerm { sort, indices })
    }
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
pub struct Port<N = Name>
{
    /// The port's name.
    pub name: N,
    /// Its sort.
    pub sort: SortTerm<N>,
    /// The restricted binders over it, each a named variable of a representable
    /// sort; empty for a first-order port.
    pub binders: Vec<Binder<N>>,
    /// The atoms `bind` abstracts over it, outside its binders, each of an
    /// atom sort; empty for a port that abstracts none.
    pub abstractions: Vec<Binder<N>>,
}

/// A sort a theory declares, with its index telescope and the ground sort its
/// model lands in.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: the sort's name, name tile, written indices, and the computation
///   types for a `Type[-]` sort and the value types for any other.
/// - executable: none — a presented sort is data the derivation reads.
///
/// # Adequacy
/// - hypothesis: L3 — the `CatShape` sorts derive their components, and a
///   `Type[-]` sort derives a family into computation types.
/// - witness: `model::tests::the_cat_shape_sorts_are_a_type_and_a_family`
/// - witness: `model::tests::a_computation_sort_derives_a_family_into_computation_types`
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PresentedSort<N = Name>
{
    /// The sort's name.
    pub name: N,
    /// Its name tile.
    pub named: Placed,
    /// Its written index telescope.
    pub indices: Vec<Port<N>>,
    /// The ground sort its model lands in.
    pub ground: GroundSort,
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
pub struct PresentedOperation<N = Name>
{
    /// The operation's name.
    pub name: N,
    /// Its name tile.
    pub named: Placed,
    /// An operation, an observation or a constant.
    pub kind: OperationKind,
    /// Its input ports.
    pub inputs: Vec<Port<N>>,
    /// Its output ports.
    pub outputs: Vec<Port<N>>,
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
pub struct PresentedLaw<N = Name>
{
    /// The rule's name.
    pub name: N,
    /// Its name tile.
    pub named: Placed,
    /// The term it rewrites from.
    pub left: FreeTerm<N>,
    /// The term it rewrites to.
    pub right: FreeTerm<N>,
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

/// A circuit rule a theory reads as a diagram, kept with its spider canon.
///
/// Its body merges or splits a wire of a sort that the theory marks
/// `@[ frobenius ]`. No term reads a spider, so the value does not code it.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: the rule's name and name tile, and the canon of its wiring modulo
///   the Frobenius laws.
/// - executable: none — a presented diagram is data that the checks read.
///
/// # Adequacy
/// - hypothesis: L3 — a marked merge is kept with its canon, and the merge in
///   the other association has the same canon.
/// - witness: `description::theory::tests::a_marked_merge_is_a_diagram_of_its_presentation_5763`
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PresentedDiagram
{
    /// The rule's name and name tile.
    pub circuit: PresentedCircuit,
    /// The canon of its wiring modulo the Frobenius laws of its spiders.
    pub canon: SpiderCanon,
}

/// What a `theory` block presents.
///
/// Its `Theory` value, where each member the value codes is written, the
/// circuit rules `Theory` does not code yet, the inclusion of each theory the
/// block includes, and the laws it states.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: the value is the one source of the presented sorts, operations
///   and faces; the placement holds one name tile per member it codes, in the
///   value's order; the value restricts along each inclusion to the value of
///   the theory it includes. A stated law stands beside the value, which the
///   rule decision reads, so it takes no part in the theory's rewriting.
/// - executable: none — a presentation is data the derivation reads.
///
/// # Adequacy
/// - hypothesis: L3 — the `CatShape` presentation derives the `CatShape` model;
///   a block that includes another restricts to it.
/// - witness: `model::tests::the_cat_shape_sorts_are_a_type_and_a_family`
/// - witness: `model::tests::a_presentation_reads_its_members_off_its_value`
/// - witness: `description::theory::tests::an_included_theory_is_the_extension_restricted`
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Presentation
{
    /// The presentation as a value of `Theory`.
    pub value: TheoryValue,
    /// Where each member the value codes is written.
    pub placement: Placement,
    /// The rules wired as circuits whose boundaries derive, kept beside the
    /// value.
    pub circuits: Vec<PresentedCircuit>,
    /// The rules wired as diagrams, an included theory's first.
    pub diagrams: Vec<PresentedDiagram>,
    /// The theories the block includes, each with its inclusion, in written
    /// order.
    pub inclusions: Vec<Included>,
    /// The laws the block states, `law name : …`, in written order, an
    /// included theory's first.
    pub laws: Vec<StatedLaw>,
    /// The operations the block marks `@[ inert ]`, an included theory's
    /// among them: fields the manifest step reads and no other declaration
    /// does.
    pub inert: BTreeSet<Name>,
    /// The sorts the block marks `@[ frobenius ]`, an included theory's among
    /// them. Each sort carries a special commutative Frobenius algebra. A
    /// circuit rule may merge and split its wires.
    pub frobenius: BTreeSet<Name>,
    /// Each port whose sort names no sort of the signature and no index, in
    /// written order: a name that the scope of the declaring source resolves
    /// once it stands (#8139).
    pub ported: Vec<PortedName>,
}

/// A port's sort that a theory's signature does not declare, kept as written
/// until the scope of the declaring source resolves it: `Integer` in `oper
/// read : () --> Integer`.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PortedName
{
    /// The operation whose port it is.
    pub operation: Name,
    /// The sort as written.
    pub sort: Name,
    /// Where the sort is written.
    pub span: ByteSpan,
}

/// A law a theory states as the path type a model proves it at: `law sym :
/// (a : Carrier, b : Carrier) => Path[.A = Bool](eq(a, b), eq(b, a))`, an
/// equation no rule orients.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: the sort binders in written order, then the path hypotheses, then
///   the path the law states; every term names only the binders and the
///   theory's operations, or is a `Bool` literal standing as a whole side.
/// - executable: none — a stated law is data the derivation reads.
///
/// # Adequacy
/// - hypothesis: L3 — `refl`, `sym` and `trans` derive the components their
///   binders, hypotheses and paths spell; a law naming an unbound variable or
///   at the wrong sort is refused.
/// - witness: `model::tests::a_stated_law_binds_its_written_variables_2356`
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct StatedLaw<N = Name>
{
    /// The law's name.
    pub name: N,
    /// Its name tile.
    pub named: Placed,
    /// The variables it quantifies over, each at its written sort.
    pub binders: Vec<Binder<N>>,
    /// The paths it assumes, after every variable.
    pub hypotheses: Vec<Hypothesis<N>>,
    /// The sort both sides inhabit.
    pub carrier: SortTerm<N>,
    /// The path's left side.
    pub left: FreeTerm<N>,
    /// Its right side.
    pub right: FreeTerm<N>,
}

/// A path a law assumes, `p : Path[.A = Bool](eq(a, b), true)`: an argument of
/// the law's proof no later type names.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: the hypothesis' name, carrier and sides, each side naming only
///   the law's variables.
/// - executable: none — a hypothesis is data the lowering mints from.
///
/// # Adequacy
/// - hypothesis: L3 — the two hypotheses of `trans` follow its variables, each
///   a path over them.
/// - witness: `model::tests::a_stated_law_binds_its_written_variables_2356`
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Hypothesis<N = Name>
{
    /// The hypothesis' name.
    pub name: N,
    /// The sort both sides inhabit.
    pub carrier: SortTerm<N>,
    /// The path's left side.
    pub left: FreeTerm<N>,
    /// Its right side.
    pub right: FreeTerm<N>,
}

/// One theory a block includes, and where the `include` names it.
///
/// The inclusion is the theory morphism the block's models restrict along.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: nothing beyond its fields.
/// - executable: none — a morphism is data the derivation reads.
///
/// # Adequacy
/// - hypothesis: L3 — as [`Presentation`].
/// - witness: `description::theory::tests::an_included_theory_is_the_extension_restricted`
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Included
{
    /// The included theory's declaration.
    pub theory: NominalId,
    /// Where each of its members stands in the including presentation.
    pub inclusion: TheoryInclusion,
    /// The tile the `include` member names the theory by.
    pub named: Placed,
    /// The included `theory` block.
    pub block: Placed,
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

/// The members a presentation's value codes, each at its name tile, their
/// names `N`: the ids of the members' table, or the text a text consumer reads
/// back.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: sorts, operations and faces, each in written order; each id reads
///   its text in the table. A text form's names are their own text, and its
///   table is empty.
/// - executable: none — members are data the derivation reads.
///
/// # Adequacy
/// - hypothesis: L3 — as [`Presentation::members`].
/// - witness: `model::tests::a_presentation_reads_its_members_off_its_value`
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Members<N = NameId>
{
    /// The table of the members' names: each id below reads its text here.
    pub names: Names,
    /// The declared sorts.
    pub sorts: Vec<PresentedSort<N>>,
    /// The declared operations.
    pub operations: Vec<PresentedOperation<N>>,
    /// The rules written as faces.
    pub laws: Vec<PresentedLaw<N>>,
}

impl Members
{
    /// The members read back as text, for a consumer that holds text: a
    /// boundary of the lowering's text, which #7663 moves to ids.
    ///
    /// # Specification
    /// - ensures: the same members, each name the text its id reads in the
    ///   table; the text form's table is empty.
    /// - fails: [`name_text::Absent::Unminted`] for an id the table did not
    ///   mint.
    /// - panics: none.
    /// - executable: none — the reading is the table's, name by name.
    ///
    /// # Cost
    /// - allocation: each name's text and member, durable by the text form
    ///
    /// # Errors
    /// As the fails clause.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a presentation's members read back as the text its
    ///   value codes, an unnamed port at its placeholder.
    /// - witness: `model::tests::a_presentation_reads_its_members_off_its_value`
    #[inline]
    pub fn spelled(&self) -> Result<Members<Name>, name_text::Absent>
    {
        let mut spell = speller(&self.names);
        let mut sorts = Vec::with_capacity(self.sorts.len());
        for sort in &self.sorts {
            sorts.push(sort.map_names(&mut spell)?);
        }
        let mut operations = Vec::with_capacity(self.operations.len());
        for operation in &self.operations {
            operations.push(operation.map_names(&mut spell)?);
        }
        let mut laws = Vec::with_capacity(self.laws.len());
        for law in &self.laws {
            laws.push(law.map_names(&mut spell)?);
        }
        Ok(Members {
            names: Names::new(),
            sorts,
            operations,
            laws,
        })
    }
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
    /// The derivation holds a name that its table did not mint.
    Unminted,
}

impl Presentation
{
    /// Every circuit rule the block wires: the rules whose boundaries derive,
    /// then the rules it reads as diagrams.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn wired(&self) -> impl Iterator<Item = &PresentedCircuit>
    {
        self.circuits
            .iter()
            .chain(self.diagrams.iter().map(|diagram| &diagram.circuit))
    }

    /// The members the value codes, each at its tile and each name minted
    /// into the members' table; an unnamed port reads as the placeholder its
    /// position names.
    ///
    /// # Specification
    /// - ensures: one presented sort, operation and face per member the value
    ///   codes, in its order, each at the placement's tile of the same
    ///   position.
    /// - fails: [`PresentationFault::Value`] for a value that codes no
    ///   presentation, or names more than a table holds;
    ///   [`PresentationFault::Unplaced`] when the value codes more members of a
    ///   kind than the placement places.
    /// - panics: none.
    ///
    /// # Cost
    /// - allocation: the table and the members, durable by the members
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
        let mut names = Names::new();
        let parts = self
            .value
            .decode_into(&mut names)
            .map_err(PresentationFault::Value)?;
        if parts.sorts.len() > self.placement.sorts.len()
            || parts.operations.len() > self.placement.operations.len()
            || parts.rules.len() > self.placement.laws.len()
        {
            return Err(PresentationFault::Unplaced);
        }
        let full = PresentationFault::Value(TheoryFault::Full);
        let mut sorts = Vec::with_capacity(parts.sorts.len());
        for (sort, &named) in parts.sorts.into_iter().zip(&self.placement.sorts) {
            let Maybe::Present(presented) = presented_ids(&sort.indices, &[], &mut names)
            else {
                return Err(full);
            };
            let ground = match sort.representability {
                Representability::Computation => GroundSort::Computation,
                Representability::Ordinary
                | Representability::Representable
                | Representability::Atom => GroundSort::Value,
            };
            sorts.push(PresentedSort {
                name: sort.name,
                named,
                indices: ports(sort.indices, presented),
                ground,
            });
        }
        let mut operations = Vec::with_capacity(parts.operations.len());
        for (operation, &named) in parts.operations.into_iter().zip(&self.placement.operations) {
            let Maybe::Present(presented) =
                presented_ids(&operation.inputs, &operation.outputs, &mut names)
            else {
                return Err(full);
            };
            let mut presented = presented.into_iter();
            operations.push(PresentedOperation {
                name: operation.name,
                named,
                kind: operation.kind,
                inputs: ports(operation.inputs, presented.by_ref()),
                outputs: ports(operation.outputs, presented),
            });
        }
        let laws = parts
            .rules
            .into_iter()
            .zip(&self.placement.laws)
            .map(|(law, &named)| PresentedLaw {
                name: law.name,
                named,
                left: law.left,
                right: law.right,
            })
            .collect();
        Ok(Members {
            names,
            sorts,
            operations,
            laws,
        })
    }

    /// The members the value codes, read back as text for a consumer that
    /// holds text, as [`Members::spelled`] reads them.
    ///
    /// # Specification
    /// - ensures: [`Self::members`], each name its text.
    /// - fails: as [`Self::members`]; [`PresentationFault::Unminted`] for an id
    ///   the table did not mint.
    /// - panics: none.
    /// - executable: none — as [`Members::spelled`].
    ///
    /// # Cost
    /// - allocation: the members on ids, setup
    /// - allocation: their text form, durable by the text form
    ///
    /// # Errors
    /// As the fails clause.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::members`].
    /// - witness: `model::tests::a_presentation_reads_its_members_off_its_value`
    #[inline]
    pub fn spelled_members(&self) -> Result<Members<Name>, PresentationFault>
    {
        self.members()?
            .spelled()
            .map_err(|_unminted| PresentationFault::Unminted)
    }
}

impl Members
{
    /// The sort of each wire of `circuit` that a reading reaches.
    ///
    /// # Specification
    /// - ensures: a wire's sort is the first one that its ports, its rewrite
    ///   port or an operation's port give it. That sort is one the theory
    ///   declares unindexed, read back as text: the circuit is written text.
    /// - fails: never; a wire that no sort reaches has no entry.
    /// - panics: none.
    /// - executable: none — each sort is read off the receiver's sorts, which a
    ///   predicate would walk again for each wire.
    ///
    /// # Cost
    /// - allocation: the text of each wire's sort, durable by the wires
    ///
    /// # Termination
    /// Each round over the node lines sorts a wire or stops, and there are
    /// finitely many wires.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a wire that only a later reading reaches, a rewrite
    ///   side read off the side it rewrites, and an output read off its
    ///   operation's result each take their sort.
    /// - witness: `tests::described::a_circuit_wire_takes_its_sort_from_whichever_reading_reaches_it`
    /// - witness: `description::theory::tests::a_marked_merge_is_a_diagram_of_its_presentation_5763`
    pub(crate) fn wire_sorts(
        &self,
        circuit: &WrittenCircuit,
    ) -> BTreeMap<Name, Name>
    {
        let spelled = |id: NameId| match self.names.text(id) {
            Maybe::Present(text) => Some(Name::from(text)),
            Maybe::Absent(_) => None,
        };
        let declared = |sort: &Name| {
            self.sorts.iter().any(|held| {
                held.indices.is_empty()
                    && self.names.text(held.name) == Maybe::Present(sort.as_name_ref())
            })
        };
        let declared_id = |sort: NameId| {
            self.sorts
                .iter()
                .any(|held| held.name == sort && held.indices.is_empty())
        };
        let mut wires: BTreeMap<Name, Name> = BTreeMap::new();
        for port in &circuit.ports {
            if declared(&port.sort) {
                let _first = wires.insert(port.name.clone(), port.sort.clone());
            }
        }
        let mut rewrites: BTreeMap<Name, (&Name, &Name)> = BTreeMap::new();
        for rewrite in &circuit.rewrites {
            let _first = rewrites.insert(
                rewrite.named.name.clone(),
                (&rewrite.left.name, &rewrite.right.name),
            );
        }
        let mut operations: BTreeMap<&str, &PresentedOperation<NameId>> = BTreeMap::new();
        for operation in &self.operations {
            if let Maybe::Present(text) = self.names.text(operation.name) {
                let _first = operations.entry(<&str>::from(text)).or_insert(operation);
            }
        }
        for _round in 0 ..= circuit.frames.len().saturating_add(circuit.rewrites.len()) {
            let before = wires.len();
            for &(left, right) in rewrites.values() {
                let shared = wires.get(left).or_else(|| wires.get(right)).cloned();
                if let Some(sort) = shared {
                    for side in [left, right] {
                        if !declared(side) {
                            let _held = wires.entry(side.clone()).or_insert_with(|| sort.clone());
                        }
                    }
                }
            }
            for frame in &circuit.frames {
                let reads: Vec<Option<Name>> =
                    if let Some(&(left, right)) = rewrites.get(&frame.head.name) {
                        let sort = if declared(left) {
                            Some(left.clone())
                        }
                        else {
                            wires
                                .get(left)
                                .or_else(|| wires.get(right))
                                .cloned()
                                .or_else(|| {
                                    frame
                                        .arguments
                                        .iter()
                                        .chain(&frame.outputs)
                                        .find_map(|wire| wires.get(&wire.name).cloned())
                                })
                        };
                        frame
                            .arguments
                            .iter()
                            .chain(&frame.outputs)
                            .map(|_| sort.clone())
                            .collect()
                    }
                    else if let Some(operation) = operations.get(frame.head.name.as_ref()) {
                        operation
                            .inputs
                            .iter()
                            .chain(&operation.outputs)
                            .map(|port| {
                                (port.sort.indices.is_empty() && declared_id(port.sort.sort))
                                    .then(|| spelled(port.sort.sort))
                                    .flatten()
                            })
                            .collect()
                    }
                    else {
                        Vec::new()
                    };
                for (wire, sort) in frame.arguments.iter().chain(&frame.outputs).zip(reads) {
                    if let Some(sort) = sort {
                        let _held = wires.entry(wire.name.clone()).or_insert(sort);
                    }
                }
            }
            if wires.len() == before {
                break;
            }
        }
        wires
    }
}

/// The ports `coded`, each under the next of `names`, its binders under their
/// own names.
///
/// # Specification
/// trivial.
///
/// # Adequacy
/// - hypothesis: L3 — operations with plain, bound and abstracting ports read
///   back their ports, each refused by the fault its ports name, so a port list
///   emptied, padded or stripped of its binders or atoms shows.
/// - witness: `model::tests::an_underivable_component_keeps_its_fault`
/// - witness: `model::tests::a_presentation_reads_its_members_off_its_value`
fn ports<N, Presented>(
    coded: Vec<TheoryPort<N>>,
    names: Presented,
) -> Vec<Port<N>>
where
    Presented: IntoIterator<Item = N>,
{
    let binders = |list: Vec<TheoryBinder<N>>| {
        list.into_iter()
            .map(|binder| Binder {
                name: binder.name,
                over: Vec::new(),
                sort: SortTerm {
                    sort: binder.sort,
                    indices: binder.indices,
                },
            })
            .collect()
    };
    coded
        .into_iter()
        .zip(names)
        .map(|(port, name)| Port {
            name,
            sort: SortTerm {
                sort: port.sort,
                indices: port.indices,
            },
            binders: binders(port.bindings),
            abstractions: binders(port.abstractions),
        })
        .collect()
}

impl<N> Port<N>
{
    /// The port with each name replaced by its image under `name`.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Cost
    /// - allocation: the mapped sort and binders, durable by the port
    ///
    /// # Errors
    /// The first error `name` returns.
    #[inline]
    pub fn map_names<M, E, F>(
        &self,
        name: &mut F,
    ) -> Result<Port<M>, E>
    where
        F: FnMut(&N) -> Result<M, E>,
    {
        let port = name(&self.name)?;
        let sort = self.sort.map_names(name)?;
        let mut binders = Vec::with_capacity(self.binders.len());
        for binder in &self.binders {
            binders.push(binder.map_names(name)?);
        }
        let mut abstractions = Vec::with_capacity(self.abstractions.len());
        for abstraction in &self.abstractions {
            abstractions.push(abstraction.map_names(name)?);
        }
        Ok(Port {
            name: port,
            sort,
            binders,
            abstractions,
        })
    }
}

impl<N> PresentedSort<N>
{
    /// The sort with each name replaced by its image under `name`.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Cost
    /// - allocation: the mapped index ports, durable by the sort
    ///
    /// # Errors
    /// The first error `name` returns.
    #[inline]
    pub fn map_names<M, E, F>(
        &self,
        name: &mut F,
    ) -> Result<PresentedSort<M>, E>
    where
        F: FnMut(&N) -> Result<M, E>,
    {
        let sort = name(&self.name)?;
        let mut indices = Vec::with_capacity(self.indices.len());
        for index in &self.indices {
            indices.push(index.map_names(name)?);
        }
        Ok(PresentedSort {
            name: sort,
            named: self.named,
            indices,
            ground: self.ground,
        })
    }
}

impl<N> PresentedOperation<N>
{
    /// The operation with each name replaced by its image under `name`.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Cost
    /// - allocation: the mapped ports, durable by the operation
    ///
    /// # Errors
    /// The first error `name` returns.
    #[inline]
    pub fn map_names<M, E, F>(
        &self,
        name: &mut F,
    ) -> Result<PresentedOperation<M>, E>
    where
        F: FnMut(&N) -> Result<M, E>,
    {
        let operation = name(&self.name)?;
        let mut inputs = Vec::with_capacity(self.inputs.len());
        for input in &self.inputs {
            inputs.push(input.map_names(name)?);
        }
        let mut outputs = Vec::with_capacity(self.outputs.len());
        for output in &self.outputs {
            outputs.push(output.map_names(name)?);
        }
        Ok(PresentedOperation {
            name: operation,
            named: self.named,
            kind: self.kind,
            inputs,
            outputs,
        })
    }
}

impl<N> Variable<N>
{
    /// The variable with each name replaced by its image under `name`.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Cost
    /// - allocation: the mapped sort, durable by the variable it maps
    ///
    /// # Errors
    /// The first error `name` returns.
    #[inline]
    pub fn map_names<M, E, F>(
        &self,
        name: &mut F,
    ) -> Result<Variable<M>, E>
    where
        F: FnMut(&N) -> Result<M, E>,
    {
        Ok(Variable {
            name: name(&self.name)?,
            sort: self.sort.map_names(name)?,
        })
    }
}

impl<N> Binder<N>
{
    /// The binder with each name replaced by its image under `name`.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Cost
    /// - allocation: the mapped variables and sort, durable by the binder
    ///
    /// # Errors
    /// The first error `name` returns.
    #[inline]
    pub fn map_names<M, E, F>(
        &self,
        name: &mut F,
    ) -> Result<Binder<M>, E>
    where
        F: FnMut(&N) -> Result<M, E>,
    {
        let binder = name(&self.name)?;
        let mut over = Vec::with_capacity(self.over.len());
        for variable in &self.over {
            over.push(variable.map_names(name)?);
        }
        Ok(Binder {
            name: binder,
            over,
            sort: self.sort.map_names(name)?,
        })
    }
}

impl<N> Hypothesis<N>
{
    /// The hypothesis with each name replaced by its image under `name`.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Cost
    /// - allocation: the mapped carrier and sides, durable by the hypothesis
    ///
    /// # Errors
    /// The first error `name` returns.
    #[inline]
    pub fn map_names<M, E, F>(
        &self,
        name: &mut F,
    ) -> Result<Hypothesis<M>, E>
    where
        F: FnMut(&N) -> Result<M, E>,
    {
        Ok(Hypothesis {
            name: name(&self.name)?,
            carrier: self.carrier.map_names(name)?,
            left: self.left.map_names(&mut *name)?,
            right: self.right.map_names(&mut *name)?,
        })
    }
}

impl<N> StatedLaw<N>
{
    /// The law with each name replaced by its image under `name`.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Cost
    /// - allocation: the mapped parts, durable by the law it maps
    ///
    /// # Errors
    /// The first error `name` returns.
    #[inline]
    pub fn map_names<M, E, F>(
        &self,
        name: &mut F,
    ) -> Result<StatedLaw<M>, E>
    where
        F: FnMut(&N) -> Result<M, E>,
    {
        let law = name(&self.name)?;
        let mut binders = Vec::with_capacity(self.binders.len());
        for binder in &self.binders {
            binders.push(binder.map_names(name)?);
        }
        let mut hypotheses = Vec::with_capacity(self.hypotheses.len());
        for hypothesis in &self.hypotheses {
            hypotheses.push(hypothesis.map_names(name)?);
        }
        Ok(StatedLaw {
            name: law,
            named: self.named,
            binders,
            hypotheses,
            carrier: self.carrier.map_names(name)?,
            left: self.left.map_names(&mut *name)?,
            right: self.right.map_names(&mut *name)?,
        })
    }
}

impl<N> PresentedLaw<N>
{
    /// The law with each name replaced by its image under `name`.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Cost
    /// - allocation: the mapped sides, durable by the law it maps
    ///
    /// # Errors
    /// The first error `name` returns.
    #[inline]
    pub fn map_names<M, E, F>(
        &self,
        name: &mut F,
    ) -> Result<PresentedLaw<M>, E>
    where
        F: FnMut(&N) -> Result<M, E>,
    {
        Ok(PresentedLaw {
            name: name(&self.name)?,
            named: self.named,
            left: self.left.map_names(&mut *name)?,
            right: self.right.map_names(&mut *name)?,
        })
    }
}

impl<N> ModelForm<N>
{
    /// The form with each name replaced by its image under `name`: a text
    /// consumer reads a form of ids back this way at its boundary.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Cost
    /// - allocation: the mapped parts, durable by the form it maps
    ///
    /// # Errors
    /// The first error `name` returns.
    #[inline]
    pub fn map_names<M, E, F>(
        &self,
        name: &mut F,
    ) -> Result<ModelForm<M>, E>
    where
        F: FnMut(&N) -> Result<M, E>,
    {
        let binders = |list: &[Binder<N>], name: &mut F| -> Result<Vec<Binder<M>>, E> {
            let mut mapped = Vec::with_capacity(list.len());
            for binder in list {
                mapped.push(binder.map_names(name)?);
            }
            Ok(mapped)
        };
        Ok(match *self {
            Self::Sort {
                ref indices,
                ground,
            } => ModelForm::Sort {
                indices: binders(indices, name)?,
                ground,
            },
            Self::Operation {
                ref telescope,
                ref results,
            } => {
                let telescope = binders(telescope, name)?;
                let mut mapped = Vec::with_capacity(results.len());
                for result in results {
                    mapped.push(result.map_names(name)?);
                }
                ModelForm::Operation {
                    telescope,
                    results: mapped,
                }
            },
            Self::Constant(ref sort) => ModelForm::Constant(sort.map_names(name)?),
            Self::Nested(ref theory) => ModelForm::Nested(name(theory)?),
            Self::Law {
                ref telescope,
                ref hypotheses,
                ref carrier,
                ref left,
                ref right,
            } => {
                let telescope = binders(telescope, name)?;
                let mut assumed = Vec::with_capacity(hypotheses.len());
                for hypothesis in hypotheses {
                    assumed.push(hypothesis.map_names(name)?);
                }
                ModelForm::Law {
                    telescope,
                    hypotheses: assumed,
                    carrier: carrier.map_names(name)?,
                    left: left.map_names(&mut *name)?,
                    right: right.map_names(&mut *name)?,
                }
            },
        })
    }
}

/// One binder of a derived telescope.
///
/// A binder that takes variables is a binding port's: in a model over host
/// types its port is the thunked function from those variables to its sort,
/// `+U ((x : R) -> -F C)`, the standard model of a second-order signature, in
/// which a representable sort's binder is an exponential.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: the binder's name, the variables it takes, outermost first, each
///   at a representable sort, and its sort under them; every index term names
///   only the binders before it and, in its sort, its own variables.
/// - executable: none — a binder is data the lowering mints from.
///
/// # Adequacy
/// - hypothesis: L3 — as [`SortTerm`].
/// - witness: `model::tests::the_cat_shape_operations_bind_their_free_sorts_first`
/// - witness: `model::tests::a_binding_port_derives_the_function_from_its_variables_765`
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Binder<N = Name>
{
    /// The binder's name.
    pub name: N,
    /// The variables it takes, outermost first; empty for a value binder.
    pub over: Vec<Variable<N>>,
    /// Its sort, under the variables it takes.
    pub sort: SortTerm<N>,
}

/// One variable a binding port's binder takes.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: the variable's name and its representable sort, whose index terms
///   name the binders before its binder and the variables before it.
/// - executable: none — a variable is data the lowering mints from.
///
/// # Adequacy
/// - hypothesis: L3 — as [`Binder`].
/// - witness: `model::tests::a_binding_port_derives_the_function_from_its_variables_765`
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Variable<N = Name>
{
    /// The variable's name.
    pub name: N,
    /// Its sort.
    pub sort: SortTerm<N>,
}

/// What one component of a model signature states.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: a sort's index telescope, an operation's telescope and results,
///   or a law's telescope, hypotheses, carrier and endpoints; every term names
///   only the telescope's binders and the theory's operations, each application
///   carrying every argument its operation binds, or is a `Bool` literal.
/// - executable: none — a form is data the lowering mints from.
///
/// # Adequacy
/// - hypothesis: L3 — the `CatShape` sorts, operations and laws are asserted as
///   their exact forms.
/// - witness: `model::tests::the_cat_shape_sorts_are_a_type_and_a_family`
/// - witness: `model::tests::the_cat_shape_operations_bind_their_free_sorts_first`
/// - witness: `model::tests::the_cat_shape_laws_relate_elaborated_terms`
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ModelForm<N = Name>
{
    /// A sort: a type, or a type family over its indices, landing in its
    /// ground sort.
    Sort
    {
        /// The index telescope; empty for an unindexed sort.
        indices: Vec<Binder<N>>,
        /// The ground sort its model lands in: the computation types for a
        /// `Type[-]` sort, the value types for any other.
        ground: GroundSort,
    },
    /// An operation: a function over its telescope returning its results.
    Operation
    {
        /// The free sort variables, then the input ports.
        telescope: Vec<Binder<N>>,
        /// One sort per output port.
        results: Vec<SortTerm<N>>,
    },
    /// A constant: a value of its type, a sort term that binds no variable —
    /// a sort of the theory, or a builtin type it does not declare.
    Constant(SortTerm<N>),
    /// A nested model: a module ascribed the model signature of the theory
    /// this name declares, `oper inner : Model(T)`.
    Nested(N),
    /// A law: a path between two terms, quantified over their variables and
    /// assuming its hypotheses — a rule's, with none, or a stated law's.
    Law
    {
        /// The law's variables.
        telescope: Vec<Binder<N>>,
        /// The paths it assumes, after every variable.
        hypotheses: Vec<Hypothesis<N>>,
        /// The sort both terms inhabit.
        carrier: SortTerm<N>,
        /// The left term: the one a rule rewrites from.
        left: FreeTerm<N>,
        /// The right term: the one a rule rewrites to.
        right: FreeTerm<N>,
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
///   and a law at a binding port each keep their own fault.
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
    /// A law relating a term at a port that binds a variable: its two sides
    /// are host functions, whose path the derivation does not state.
    Binding,
    /// An operation one of whose ports abstracts an atom: a nominal
    /// operation, whose models are nominal sets', not a structure on the
    /// value universe.
    Abstraction,
    /// A stated law naming a variable it does not bind, or binding one twice.
    Unbound,
    /// A sort indexed by, or an operation with a port at, a computation sort:
    /// a computation type, which a model's binders do not range over yet.
    Computation,
    /// A component whose derivation names more names than its description's
    /// table holds.
    Full,
}

impl core::fmt::Display for ModelFault
{
    /// The reason, as a clause.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — every fault renders a clause no other fault renders,
    ///   so an empty or fixed text shows.
    /// - witness: `model::tests::each_model_fault_reads_as_its_own_clause`
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
                "relates a term at a port that binds a variable, a path between host functions"
            },
            Self::Abstraction => "abstracts an atom over a port, whose models are nominal sets'",
            Self::Unbound => "names a variable its statement does not bind once",
            Self::Computation => {
                "has a port at a computation sort, which a model does not read yet"
            },
            Self::Full => "names more names than its description's table holds",
        })
    }
}

/// Why a theory's member cannot stand in the effect interface a capability
/// scope handles the theory as.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: each reason is distinct and names no source position; the refusal
///   carrying it names the member.
/// - executable: none — a fault is data a refusal carries.
///
/// # Adequacy
/// - hypothesis: L3 — each fault reads as a clause of its own.
/// - witness: `model::tests::each_interface_fault_reads_as_its_own_clause`
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum InterfaceFault
{
    /// A member other than an operation returning the carrier, the one
    /// unindexed sort every operation returns.
    Carrier,
    /// An operation whose last input is no continuation: a port at the
    /// carrier, abstracting no atom, whose binders read sorts the manifest
    /// fixes.
    Continuation,
    /// An operation with more than one input at the carrier: it takes one
    /// continuation or none.
    Continuations(ContinuationCount),
    /// An operation one of whose inputs before its continuation is no value
    /// of a sort the manifest fixes.
    Payload,
    /// A sort with an index telescope, which no one type fixes.
    Indexed,
    /// A sort other than the carrier that the manifest does not fix.
    Unfixed,
    /// The carrier, which the manifest fixes: the handler's answer is.
    Fixed,
    /// A law no handler's clauses read: one naming a constructor, an atom or
    /// a variable outside the position its sort takes.
    Law,
    /// A value operation, every input and the output at a sort the manifest
    /// fixes, which a scope writing its clauses has no clause for: only a
    /// model the scope names answers it.
    Value,
}

impl core::fmt::Display for InterfaceFault
{
    /// The reason, as a clause.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — every fault renders a clause no other fault renders,
    ///   so an empty or fixed text shows.
    /// - witness: `model::tests::each_interface_fault_reads_as_its_own_clause`
    #[inline]
    fn fmt(
        &self,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result
    {
        let reason = match *self {
            Self::Carrier => "is no operation returning the sort every operation returns",
            Self::Continuation => "takes no continuation at that sort as its last input",
            Self::Continuations(count) => {
                return write!(
                    f,
                    "takes {} inputs at the sort the operations return, and an operation takes one continuation or none",
                    count.0
                );
            },
            Self::Payload => "takes an input before its continuation at no sort the manifest fixes",
            Self::Indexed => "is an indexed sort, which no one type fixes",
            Self::Unfixed => {
                "is a sort the operations do not return, which the manifest leaves unfixed"
            },
            Self::Fixed => "is the sort the operations return, which the handler's answer fixes",
            Self::Law => "is a law no handler's clauses read",
            Self::Value => "is a value operation, which only a model the scope names answers",
        };
        f.write_str(reason)
    }
}

/// The count of the inputs of an operation at its theory's carrier.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ContinuationCount(usize);

impl From<usize> for ContinuationCount
{
    /// Wrap a count of inputs.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(count: usize) -> Self
    {
        Self(count)
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
pub struct ModelComponent<N = Name>
{
    /// The member's name.
    pub name: N,
    /// Its name tile in the theory.
    pub named: Placed,
    /// What it states.
    pub form: Result<ModelForm<N>, ModelFault>,
    /// Whether the member is an operation its theory marks `@[ inert ]`.
    pub inert: bool,
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
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ModelSignature
{
    /// The components, in signature order.
    pub components: Vec<ModelComponent>,
    /// The written declaration of the theory the signature derives from,
    /// whose port sorts the scope of its source resolves (#8139).
    pub theory: Maybe<NodeIndex, signature_theory::Absent>,
}

impl Default for ModelSignature
{
    /// No components, from no theory.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn default() -> Self
    {
        Self {
            components: Vec::new(),
            theory: Maybe::Absent(signature_theory::Absent::Unwritten),
        }
    }
}

quenchant_shape::reason_enum! {
    /// Why a model signature names no written theory.
    pub mod signature_theory {
        /// The reason a model signature names no written theory.
        #[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
        pub enum Absent {
            /// The presentation stands in no theory block of a collection.
            Unwritten,
        }
    }
}

/// The model signature of a presentation's members on ids: each component,
/// and the table its names read their text in.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: as [`ModelSignature`]; each id reads its text in the table.
/// - executable: none — a derivation is data its readers read back.
///
/// # Adequacy
/// - hypothesis: L3 — as [`derive_members`].
/// - witness: `model::tests::the_cat_shape_sorts_are_a_type_and_a_family`
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct Derivation
{
    /// The table of the components' names: each id below reads its text here.
    names: Names,
    /// The components, in signature order.
    components: Vec<ModelComponent<NameId>>,
}

impl Derivation
{
    /// The signature read back as text, for the consumers that hold text: the
    /// boundary of the lowering's text, which #7663 moves to ids.
    ///
    /// # Specification
    /// - ensures: one component per component, in order, each name the text its
    ///   id reads in the table.
    /// - fails: [`PresentationFault::Unminted`] for an id the table did not
    ///   mint.
    /// - panics: none.
    /// - executable: none — as [`Members::spelled`], component by component.
    ///
    /// # Cost
    /// - allocation: each name's text and form, durable by the signature
    ///
    /// # Errors
    /// As the fails clause.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`derive_members`].
    /// - witness: `model::tests::the_cat_shape_sorts_are_a_type_and_a_family`
    pub(crate) fn spelled(&self) -> Result<ModelSignature, PresentationFault>
    {
        let unminted = |_absent| PresentationFault::Unminted;
        let mut spell = speller(&self.names);
        let mut components = Vec::with_capacity(self.components.len());
        for component in &self.components {
            let form = match component.form {
                Ok(ref form) => Ok(form.map_names(&mut spell).map_err(unminted)?),
                Err(fault) => Err(fault),
            };
            components.push(ModelComponent {
                name: spell(&component.name).map_err(unminted)?,
                named: component.named,
                form,
                inert: component.inert,
            });
        }
        Ok(ModelSignature {
            components,
            theory: Maybe::Absent(signature_theory::Absent::Unwritten),
        })
    }
}

/// Derive the model signature of what a theory presents, reading its members
/// off its value.
///
/// # Specification
/// - requires: nothing.
/// - ensures: [`derive_members`] of the value's members, the circuit rules and
///   the stated laws kept beside it, each component inert exactly when the
///   presentation marks its name inert.
/// - fails: a value whose members cannot be read, as [`Presentation::members`];
///   [`PresentationFault::Value`] and [`PresentationFault::Unminted`] as
///   [`derive_members`] and [`Derivation::spelled`]; any other fault is kept on
///   its component.
/// - panics: none.
/// - executable: none — as [`derive_members`].
///
/// # Cost
/// - allocation: the members and the derivation on ids, setup
/// - allocation: the signature's text, durable by the signature
///
/// # Errors
/// As the fails clause.
///
/// # Adequacy
/// - hypothesis: L3 — as [`derive_members`].
/// - witness: `model::tests::the_cat_shape_sorts_are_a_type_and_a_family`
/// - witness: `model::tests::an_underivable_component_keeps_its_fault`
#[inline]
pub fn derive(
    presentation: &Presentation,
    theory: Maybe<NodeIndex, signature_theory::Absent>,
) -> Result<ModelSignature, PresentationFault>
{
    let members = presentation.members()?;
    let mut signature =
        derive_members(&members, presentation.wired(), &presentation.laws)?.spelled()?;
    signature.theory = theory;
    for component in &mut signature.components {
        component.inert = presentation.inert.contains(&component.name);
    }
    Ok(signature)
}

/// Derive the model signature of a presentation's members, its wired circuit
/// rules and the laws it states.
///
/// # Specification
/// - requires: nothing.
/// - ensures: one component per presented sort, operation, face, stated law and
///   wired circuit rule, in that order and each group in written order; a
///   circuit rule's component keeps [`ModelFault::Circuit`], whether its
///   boundaries derive or the block reads it as a diagram; a sort's or an
///   operation's telescope binds its free sort variables before its ports, a
///   law's binds the variables in another variable's sort first, and every
///   application carries every argument its operation binds; a stated law's
///   telescope is its written binders and its hypotheses its written ones; a
///   port at a builtin type the theory does not declare reads it as a closed
///   sort; a constant whose type leaves no variable free derives that type
///   alone, and one whose type does derives as an operation of no inputs; a
///   binding port's binder takes its bound variables; a sort lands in the
///   ground sort it is presented at; a component that cannot be stated keeps
///   its fault, a sort or an operation with a port at a computation sort keeps
///   [`ModelFault::Computation`], a law relating a term at a binding port keeps
///   [`ModelFault::Binding`], and one naming such a component is
///   [`ModelFault::Inherited`].
/// - fails: [`PresentationFault::Value`] when the table cannot mint the name of
///   a stated law or a circuit rule; any other fault is kept on its component.
/// - panics: none.
/// - executable: none — the inference the components result from is the
///   derivation itself.
///
/// # Cost
/// - allocation: the table and the components, durable by the derivation
///
/// # Errors
/// As the fails clause.
///
/// # Adequacy
/// - hypothesis: L3 — the `CatShape` presentation and an ill-sorted, an
///   unsorted, a circuit and a binding member, each asserted as the exact
///   components; a `Type[-]` sort's family and an operation at it, each
///   asserted as its form or fault.
/// - witness: `model::tests::the_cat_shape_sorts_are_a_type_and_a_family`
/// - witness: `model::tests::the_cat_shape_operations_bind_their_free_sorts_first`
/// - witness: `model::tests::the_cat_shape_laws_relate_elaborated_terms`
/// - witness: `model::tests::an_underivable_component_keeps_its_fault`
/// - witness: `model::tests::a_binding_port_derives_the_function_from_its_variables_765`
/// - witness: `model::tests::a_constant_derives_its_type_alone`
/// - witness: `model::tests::a_computation_sort_derives_a_family_into_computation_types`
pub(crate) fn derive_members<'wired>(
    members: &Members,
    circuits: impl IntoIterator<Item = &'wired PresentedCircuit>,
    stated: &[StatedLaw],
) -> Result<Derivation, PresentationFault>
{
    let full = PresentationFault::Value(TheoryFault::Full);
    let mut names = members.names.clone();
    let mut minted = Vec::with_capacity(stated.len());
    for law in stated {
        minted.push(
            law.map_names(&mut minter(&mut names))
                .map_err(|_full| full)?,
        );
    }
    let (heads, mut components) = derive_heads(members, &mut names);
    for law in &members.laws {
        components.push(ModelComponent {
            name: law.name,
            named: law.named,
            form: infer::derive_law(&heads, law, &mut names),
            inert: false,
        });
    }
    for law in &minted {
        components.push(ModelComponent {
            name: law.name,
            named: law.named,
            form: infer::derive_stated(&heads, law, &mut names),
            inert: false,
        });
    }
    for circuit in circuits {
        let Maybe::Present(name) = names.mint(circuit.name.as_name_ref())
        else {
            return Err(full);
        };
        components.push(ModelComponent {
            name,
            named: circuit.named,
            form: Err(ModelFault::Circuit),
            inert: false,
        });
    }

    Ok(Derivation { names, components })
}

/// The map that mints each text name into `names`: the map a text form takes
/// to reach the ids of a description's table.
///
/// # Specification
/// trivial.
///
/// # Cost
/// - allocation: each new name's text, growth within the table
fn minter(names: &mut Names) -> impl FnMut(&Name) -> Result<NameId, name_mint::Absent>
{
    |name| match names.mint(name.as_name_ref()) {
        Maybe::Present(id) => Ok(id),
        Maybe::Absent(absent) => Err(absent),
    }
}

/// The map that reads each id of `names` back as text: the map a text
/// consumer reads a form of ids by, at its boundary.
///
/// # Specification
/// trivial.
///
/// # Cost
/// - allocation: each name's text, durable by the text form it builds
pub(crate) fn speller(names: &Names)
-> impl FnMut(&NameId) -> Result<Name, name_text::Absent> + '_
{
    |&id| match names.text(id) {
        Maybe::Present(text) => Ok(Name::from(text)),
        Maybe::Absent(absent) => Err(absent),
    }
}

/// Derive the law each of `laws` states over the sorts and operations of
/// `members`, as a law the theory writes derives, without adding it to the
/// theory.
///
/// # Specification
/// - requires: nothing.
/// - ensures: one form per law, in order, each the form [`derive_members`]
///   gives a law of `members` written with the same sides, read back as text.
/// - fails: never; a fault is kept on its law, and a law whose names the table
///   cannot mint keeps [`ModelFault::Full`].
/// - panics: none.
/// - executable: none — as [`derive_members`].
///
/// # Cost
/// - allocation: the table copy and each law's forms, durable by the forms
///
/// # Adequacy
/// - hypothesis: L3 — a rule a group's completion derives states its telescope
///   and endpoints over the group's own operations.
/// - witness: `derive::tests::a_derived_rule_states_its_law_over_the_theory`
#[must_use]
#[inline]
pub fn derive_laws(
    members: &Members,
    laws: &[PresentedLaw],
) -> Vec<Result<ModelForm, ModelFault>>
{
    let mut names = members.names.clone();
    let (heads, _components) = derive_heads(members, &mut names);
    laws.iter()
        .map(|law| {
            let minted = law
                .map_names(&mut minter(&mut names))
                .map_err(|_full| ModelFault::Full)?;
            let form = infer::derive_law(&heads, &minted, &mut names)?;
            form.map_names(&mut speller(&names))
                .map_err(|_unminted| ModelFault::Full)
        })
        .collect()
}

/// Derive the law each of `stated` states over the sorts and operations of
/// `members`, as [`derive_members`] derives a law the theory states.
///
/// # Specification
/// - requires: nothing.
/// - ensures: one form per stated law, in order, each the form
///   [`derive_members`] gives it.
/// - fails: never; a fault is kept on its law, and a law whose names the table
///   cannot mint keeps [`ModelFault::Full`].
/// - panics: none.
/// - executable: none — as [`derive_members`].
///
/// # Cost
/// - allocation: the table copy and each law's id form, durable by the forms
///
/// # Adequacy
/// - hypothesis: L3 — a stated law naming a variable it does not bind keeps its
///   fault, which the theory refuses at the law.
/// - witness: `description::theory::tests::a_stated_law_naming_an_unbound_variable_is_refused_at_its_theory_4115`
#[must_use]
pub(crate) fn derive_stated(
    members: &Members,
    stated: &[StatedLaw],
) -> Vec<Result<ModelForm<NameId>, ModelFault>>
{
    let mut names = members.names.clone();
    let (heads, _components) = derive_heads(members, &mut names);
    stated
        .iter()
        .map(|law| {
            let minted = law
                .map_names(&mut minter(&mut names))
                .map_err(|_full| ModelFault::Full)?;
            infer::derive_stated(&heads, &minted, &mut names)
        })
        .collect()
}

/// The heads of `members`' sorts and operations, each beside its derived
/// component, as [`derive_members`] states them before the laws; each fresh
/// name minted into `names`.
///
/// # Specification
/// - requires: `names` holds the members' names.
/// - ensures: one component per presented sort and operation, in that order,
///   each group in written order, and each one's head by its name, every
///   builtin a sort's index or a port names — the host universe or a builtin
///   type — held as a closed sort.
/// - fails: never; a fault is kept on its component.
/// - panics: none.
/// - executable: none — as [`derive_members`].
///
/// # Cost
/// - allocation: the heads and the components, durable by the signature
///
/// # Adequacy
/// - hypothesis: L3 — as [`derive_members`].
/// - witness: `model::tests::the_cat_shape_sorts_are_a_type_and_a_family`
fn derive_heads(
    members: &Members,
    names: &mut Names,
) -> (infer::Heads, Vec<ModelComponent<NameId>>)
{
    /// Hold the bare sort `term` names as a closed sort, once, when no sort
    /// of the members declares it: the type universe or a port sort that the
    /// scope of the theory's source resolves (#8139).
    ///
    /// # Specification
    /// trivial.
    fn close(
        heads: &mut infer::Heads,
        names: &mut Names,
        declared: &[PresentedSort<NameId>],
        term: &SortTerm<NameId>,
    )
    {
        if term.indices.is_empty()
            && !declared.iter().any(|sort| sort.name == term.sort)
            && heads.get(term.sort).is_none()
        {
            let closed = infer::derive_head(heads, infer::HeadKind::Sort, (&[], &[]), names);
            heads.insert(term.sort, closed);
        }
    }
    let mut heads = infer::Heads::default();
    let mut components =
        Vec::with_capacity(members.sorts.len().saturating_add(members.operations.len()));
    let computations: Vec<NameId> = members
        .sorts
        .iter()
        .filter(|sort| sort.ground == GroundSort::Computation)
        .map(|sort| sort.name)
        .collect();
    let computational = |port: &Port<NameId>| computations.contains(&port.sort.sort);
    for sort in &members.sorts {
        for index in &sort.indices {
            close(&mut heads, names, &members.sorts, &index.sort);
        }
        let head = if sort.indices.iter().any(computational) {
            Err(ModelFault::Computation)
        }
        else {
            infer::derive_head(&heads, infer::HeadKind::Sort, (&sort.indices, &[]), names)
        };
        let form = match head {
            Ok(ref derived) => Ok(ModelForm::Sort {
                indices: derived.binders.clone(),
                ground: sort.ground,
            }),
            Err(fault) => Err(fault),
        };
        heads.insert(sort.name, head);
        components.push(ModelComponent {
            name: sort.name,
            named: sort.named,
            form,
            inert: false,
        });
    }
    let ports = members
        .operations
        .iter()
        .flat_map(|operation| operation.inputs.iter().chain(&operation.outputs));
    for port in ports {
        close(&mut heads, names, &members.sorts, &port.sort);
    }
    for operation in &members.operations {
        let head = if operation
            .inputs
            .iter()
            .chain(&operation.outputs)
            .any(|port| !port.abstractions.is_empty())
        {
            Err(ModelFault::Abstraction)
        }
        else if operation
            .inputs
            .iter()
            .chain(&operation.outputs)
            .any(computational)
        {
            Err(ModelFault::Computation)
        }
        else {
            infer::derive_head(
                &heads,
                infer::HeadKind::Operation,
                (&operation.inputs, &operation.outputs),
                names,
            )
        };
        let form = match (operation.kind, &head) {
            (OperationKind::Constant, &Ok(ref derived)) if derived.binders.is_empty() => {
                match *derived.results.as_slice() {
                    [ref sort] => Ok(ModelForm::Constant(sort.clone())),
                    _ => Err(ModelFault::ManyOut),
                }
            },
            (OperationKind::Nested, _) => match *operation.outputs.as_slice() {
                [ref port] if port.sort.indices.is_empty() => Ok(ModelForm::Nested(port.sort.sort)),
                _ => Err(ModelFault::ManyOut),
            },
            (
                OperationKind::Operation | OperationKind::Observation | OperationKind::Constant,
                &Ok(ref derived),
            ) => Ok(ModelForm::Operation {
                telescope: derived.binders.clone(),
                results: derived.results.clone(),
            }),
            (
                OperationKind::Operation | OperationKind::Observation | OperationKind::Constant,
                &Err(fault),
            ) => Err(fault),
        };
        heads.insert(operation.name, head);
        components.push(ModelComponent {
            name: operation.name,
            named: operation.named,
            form,
            inert: false,
        });
    }

    (heads, components)
}

/// Whether a telescope binder is named after it, and so binds.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Dependent(pub bool);

/// The tail of a derived value component's telescope.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug)]
pub enum Tail<'form>
{
    /// An operation's results.
    Results(&'form [SortTerm]),
    /// A law's hypotheses, carrier and endpoints.
    Path(
        &'form [Hypothesis],
        &'form SortTerm,
        &'form FreeTerm,
        &'form FreeTerm,
    ),
}

/// Whether each binder of `telescope` is named by a later binder's sort or
/// by `tail`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: one flag per binder, in order: affirmative exactly when the
///   binder's name is a variable of a later binder's index terms — its own or
///   its variables', less the names those variables bind — or of the tail's
///   hypotheses, sorts and terms.
/// - fails: never.
/// - panics: none.
///
/// # Cost
/// - allocation: the flags, durable by the list
/// - allocation: the names seen, setup
///
/// # Adequacy
/// - hypothesis: L3 — `comp`'s sort binders bind and its morphisms do not;
///   every binder of `unitL` binds.
/// - witness: `gandr-surface-lowering::tests::modules::models::a_derived_signature_states_what_the_written_one_does`
#[spec(ensures: |ret| ret.len() == telescope.len())]
#[cfg_attr(
    dylint_lib = "quenchant_dylints",
    expect(
        linear_search_in_loop,
        reason = "bounded: `named` holds the variables one operation's telescope and result mention"
    )
)]
#[inline]
#[must_use]
pub fn dependence(
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
        Tail::Path(hypotheses, carrier, left, right) => {
            for hypothesis in hypotheses {
                sort_vars(&hypothesis.carrier, &mut named);
                named.extend(hypothesis.left.to_node().vars());
                named.extend(hypothesis.right.to_node().vars());
            }
            sort_vars(carrier, &mut named);
            named.extend(left.to_node().vars());
            named.extend(right.to_node().vars());
        },
    }
    let mut flags = Vec::with_capacity(telescope.len());
    for binder in telescope.iter().rev() {
        flags.push(Dependent(named.contains(&&binder.name)));
        binder_vars(binder, &mut named);
    }
    flags.reverse();

    flags
}

/// Whether each of `variables`, the variables one binder takes, is named by
/// a later variable's sort or by `result`, the binder's sort under them.
///
/// # Specification
/// - requires: nothing.
/// - ensures: one flag per variable, in order: affirmative exactly when the
///   variable's name is a variable of a later variable's index terms or of
///   `result`'s.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — `get`'s state is named by no sort, so its function is an
///   arrow.
/// - witness: `model::tests::a_binding_port_derives_the_function_from_its_variables_765`
#[spec(ensures: |ret| ret.len() == variables.len())]
#[cfg_attr(
    dylint_lib = "quenchant_dylints",
    expect(
        linear_search_in_loop,
        reason = "bounded: `named` holds the variables one port's sorts mention"
    )
)]
#[inline]
#[must_use]
pub fn variable_dependence(
    variables: &[Variable],
    result: &SortTerm,
) -> Vec<Dependent>
{
    let mut named: Vec<&Name> = Vec::new();
    sort_vars(result, &mut named);
    let mut flags = Vec::with_capacity(variables.len());
    for variable in variables.iter().rev() {
        flags.push(Dependent(named.contains(&&variable.name)));
        sort_vars(&variable.sort, &mut named);
    }
    flags.reverse();

    flags
}

/// Push every variable `binder`'s sort and its variables' sorts name, less
/// the names those variables bind, onto `into`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: for a value binder, as [`sort_vars`] over its sort; for one that
///   takes variables, every variable of its sort's and its variables' index
///   terms that none of its variables is named.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — as [`dependence`].
/// - witness: `model::tests::a_binding_port_derives_the_function_from_its_variables_765`
#[spec(
    captures: before = into.len(),
    ensures: into.len() >= before,
)]
fn binder_vars<'term>(
    binder: &'term Binder,
    into: &mut Vec<&'term Name>,
)
{
    if binder.over.is_empty() {
        sort_vars(&binder.sort, into);
        return;
    }
    let mut mentioned = Vec::new();
    sort_vars(&binder.sort, &mut mentioned);
    for variable in &binder.over {
        sort_vars(&variable.sort, &mut mentioned);
    }
    into.extend(
        mentioned
            .into_iter()
            .filter(|&name| binder.over.iter().all(|variable| variable.name != *name)),
    );
}

/// Push every variable of `sort`'s index terms onto `into`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: one entry per variable leaf of each index term, in order.
/// - fails: never.
/// - panics: none.
///
/// # Cost
/// - allocation: the names pushed, growth within `into`
///
/// # Adequacy
/// - hypothesis: L3 — as [`dependence`].
/// - witness: `gandr-surface-lowering::tests::modules::models::a_derived_signature_states_what_the_written_one_does`
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
/// - witness: `gandr-surface-lowering::tests::modules::models::a_lowered_theory_exposes_its_description_and_its_model`
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct LoweredTheory<'module>
{
    /// The theory's name tile.
    pub named: Placed,
    /// Its checked description: the sorts, and the operations as generators.
    pub description: &'module TheoryDesc<DescriptionGrade>,
    /// What it presents to the signature of its models.
    pub presentation: &'module Presentation,
    /// Its written declaration, which its signature names as its theory.
    pub declaration: NodeIndex,
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
        derive(self.presentation, Maybe::Present(self.declaration))
    }
}
