//! The name-free declaration input: what one declaration offers the judgement.
//!
//! # Name-free, and owned here
//!
//! A [`Declaration`] carries an admission position, an optional declared type,
//! an optional body and an [`OriginToken`]. It carries no name, no span and no
//! syntax node: the producer of the terms resolves names to positions and keeps
//! the origins, and the checker echoes the token back beside every verdict so
//! the driver can resolve it. This crate owns the type; a producer is adapted
//! to it downstream of both, so the two never agree on more than this one small
//! shape.
//!
//! # Each half is present or absent for a stated reason
//!
//! A missing declared type means the author wrote a definition with no
//! signature, so the body must synthesise. A missing body is a hole: no
//! definition supplies it. Both halves are independent, so the hole's rule is
//! read in both directions — under a signature it absorbs the declared type
//! and owes it, and with no signature it is refused, because nothing hands it a
//! type.
//!
//! A [`DeclarationContent`] distinguishes the optional value halves from a
//! complete native `DataSignature` and from a sealed [`AbstractType`]. Reading
//! a lowering's outcome type directly would couple independent layers; the
//! adapter is revisited only if a shared producer-neutral declaration
//! vocabulary replaces it. Names enter only at export, through
//! `bridge::Readmission::export`.
//!
//! # A sealed abstract type
//!
//! Opaque ascription declares each abstract component as an atom at its own
//! admission position, before the members that implement it: its kind, its
//! representation, how many positions after it stay inside the seal, and the
//! site that minted it. The atom's identity is the position; the extent says
//! where the representation stops being visible, so the module's own members
//! check at the representation and every later declaration sees the atom
//! alone.
//!
//! # A world and an entry
//!
//! A world declaration takes a position and carries nothing else: the
//! position is the world's identity, as an atom's is. A value declaration
//! may carry an [`Entry`], the world its body is judged at and the
//! capabilities its host hands it; one carrying none takes the host's
//! ([`crate::worlds`]).

use alloc::vec::Vec;

use anodized::spec;
use gandr_core_term::ValueId;
use gandr_core_term::ValueTypeId;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::SealExtent;
use quenchant_shape::shape::Maybe;

use crate::seal::SealSite;
use crate::worlds::Entry;
use crate::worlds::Mobility;

quenchant_shape::reason_enum! {
    /// Why a declaration carries no declared type.
    pub mod signature {
        /// The reason the declared type is absent.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The author wrote a definition and no signature, so the body
            /// must synthesise its own type.
            Unsigned,
            /// The declaration is a source's run target, its final
            /// expression: no signature can be written, and a body that
            /// suspends a computation has the thunk type of the computation
            /// type it synthesises.
            RunTarget,
        }
    }
}

quenchant_shape::reason_enum! {
    /// Why a declaration carries no body.
    pub mod body {
        /// The reason the body is absent.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The body is a hole: no definition supplies it.
            Hole,
            /// The host asserts the declared type, a law of one of its
            /// primitives: no definition supplies it, and it is owed only
            /// when it converts with a statement the host's law table holds.
            Hosted,
        }
    }
}

quenchant_shape::reason_enum! {
    /// Why a declaration states no entry.
    pub mod entry {
        /// The reason the entry is absent.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The source states none: the host's entry applies.
            Unstated,
        }
    }
}

/// The opaque handle a producer attaches to a declaration, echoed back with its
/// verdict.
///
/// The checker never interprets the index it wraps; the driver resolves it to
/// the declaration's name and span through whatever table issued it.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct OriginToken(usize);

impl From<usize> for OriginToken
{
    /// The token wrapping `index`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(index: usize) -> Self
    {
        Self(index)
    }
}

impl From<OriginToken> for usize
{
    /// The index `token` wraps.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(token: OriginToken) -> Self
    {
        token.0
    }
}

quenchant_shape::reason_enum! {
    /// Why a sealed atom's interface states no identity-system law.
    pub mod law {
        /// The reason an interface states no law.
        #[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
        pub enum Absent {
            /// The declaration states none: an identity at the atom is refused.
            Unstated,
        }
    }
}

quenchant_shape::reason_enum! {
    /// Why a sealed atom carries no element interface.
    pub mod interface {
        /// The reason an atom states no element relation.
        #[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
        pub enum Absent {
            /// The declaration states none: the atom's identity is its own
            /// neutral fibre.
            Unstated,
        }
    }
}

/// What a sealed atom's elements are related by: a relation, its reflexivity
/// and, when stated, the law that makes the relation its identity.
///
/// Over the representation `R` at the kind's level `l`: `relation` at `U(R →
/// R → F U_l)`, `reflexivity` at `U(Π (x : R). F El(⟨relation x x⟩))`, and
/// `law` at `U(Π (a b : R). Π (r : El(⟨relation a b⟩)). F Path(Σ (y : R).
/// El(⟨relation a y⟩), (b, r), (a, ⟨reflexivity a⟩)))`, every element of the
/// singleton at `a` its centre. Each is a closed value.
///
/// # Specification
/// - requires: nothing; the atom's judgement checks each value at its type.
/// - ensures: retains every value verbatim.
/// - panics: none.
/// - executable: none — data declaration, not a callable boundary.
///
/// # Adequacy
/// - hypothesis: L3 — a lawful atom's relation is its identity in the checker
///   and in the kernel.
/// - witness: `bridge::tests::a_lawful_atom_reads_its_relation_as_its_identity_in_both_checkers`
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct AtomInterface
{
    /// The relation between two elements, a code-valued binary function.
    relation: ValueId,
    /// The relation's reflexivity, one witness per element.
    reflexivity: ValueId,
    /// The singleton's contraction onto its centre, when stated.
    law: Maybe<ValueId, law::Absent>,
}

impl AtomInterface
{
    /// The interface relating elements by `relation`, reflexive by
    /// `reflexivity`, stating no law.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn new(
        relation: ValueId,
        reflexivity: ValueId,
    ) -> Self
    {
        Self {
            relation,
            reflexivity,
            law: Maybe::Absent(law::Absent::Unstated),
        }
    }

    /// This interface with `law` as its identity-system law.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the same atom with and without its law reads the
    ///   relation's evidence as an identity only with it, and refuses it by
    ///   name without.
    /// - witness: `bridge::tests::a_lawful_atom_reads_its_relation_as_its_identity_in_both_checkers`
    /// - witness: `bridge::tests::an_atom_stating_no_law_refuses_the_relation_s_evidence_by_name`
    #[inline]
    #[must_use]
    pub const fn lawful(
        self,
        law: ValueId,
    ) -> Self
    {
        Self {
            law: Maybe::Present(law),
            ..self
        }
    }

    /// The relation between two elements.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the relation is checked at its own type and read as
    ///   the atom's identity, so another value in its place refuses the atom or
    ///   the evidence.
    /// - witness: `bridge::tests::a_lawful_atom_reads_its_relation_as_its_identity_in_both_checkers`
    /// - witness: `bridge::tests::an_interface_member_named_at_another_member_s_type_refuses_the_atom`
    #[inline]
    #[must_use]
    pub const fn relation(&self) -> ValueId
    {
        self.relation
    }

    /// The relation's reflexivity.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the reflexivity is checked at its own type, so
    ///   another value in its place refuses the atom.
    /// - witness: `bridge::tests::a_lawful_atom_reads_its_relation_as_its_identity_in_both_checkers`
    /// - witness: `bridge::tests::an_interface_member_named_at_another_member_s_type_refuses_the_atom`
    #[inline]
    #[must_use]
    pub const fn reflexivity(&self) -> ValueId
    {
        self.reflexivity
    }

    /// The identity-system law, when stated.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a stated law makes the relation's evidence an
    ///   identity, and its absence refuses that evidence by name.
    /// - witness: `bridge::tests::a_lawful_atom_reads_its_relation_as_its_identity_in_both_checkers`
    /// - witness: `bridge::tests::an_atom_stating_no_law_refuses_the_relation_s_evidence_by_name`
    #[inline]
    pub const fn law(&self) -> Maybe<ValueId, law::Absent>
    {
        self.law
    }
}

/// A sealed abstract type: an atom of a universe, the representation it
/// stands for inside its seal, the reach of that seal, and the interface its
/// elements are related by, when stated.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct AbstractType
{
    /// The universe the atom inhabits.
    kind: ValueTypeId,
    /// The type the atom stands for inside its seal.
    representation: ValueTypeId,
    /// How many admission positions after the atom's own stay inside the
    /// seal.
    extent: SealExtent,
    /// The sealing site that mints the atom.
    site: SealSite,
    /// Whether the signature marks the atom as crossing worlds.
    mobility: Mobility,
    /// The relation, reflexivity and law the atom's elements are related by.
    interface: Maybe<AtomInterface, interface::Absent>,
}

impl AbstractType
{
    /// The atom of `kind` standing for `representation` for the `extent`
    /// positions after its own, minted at `site`, stating no interface.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn new(
        kind: ValueTypeId,
        representation: ValueTypeId,
        extent: SealExtent,
        site: SealSite,
    ) -> Self
    {
        Self {
            kind,
            representation,
            extent,
            site,
            mobility: Mobility::Immobile,
            interface: Maybe::Absent(interface::Absent::Unstated),
        }
    }

    /// This abstract type with its elements related by `interface`.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an interfaced atom reads its relation as its
    ///   identity, which a plain atom does not.
    /// - witness: `bridge::tests::a_lawful_atom_reads_its_relation_as_its_identity_in_both_checkers`
    #[inline]
    #[must_use]
    pub const fn interfaced(
        self,
        interface: AtomInterface,
    ) -> Self
    {
        Self {
            interface: Maybe::Present(interface),
            ..self
        }
    }

    /// The interface the atom's elements are related by, when stated.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the interface read back is the one the evidence is
    ///   checked through, so an absent one keeps the atom's own fibre.
    /// - witness: `bridge::tests::a_lawful_atom_reads_its_relation_as_its_identity_in_both_checkers`
    #[inline]
    pub const fn interface(&self) -> Maybe<AtomInterface, interface::Absent>
    {
        self.interface
    }

    /// This abstract type with the signature's mark `mobility`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn marked(
        self,
        mobility: Mobility,
    ) -> Self
    {
        Self { mobility, ..self }
    }

    /// Whether the signature marks the atom as crossing worlds.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn mobility(&self) -> Mobility
    {
        self.mobility
    }

    /// The universe the atom inhabits.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn kind(&self) -> ValueTypeId
    {
        self.kind
    }

    /// The type the atom stands for inside its seal.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn representation(&self) -> ValueTypeId
    {
        self.representation
    }

    /// How many admission positions after the atom's own stay inside the
    /// seal.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn extent(&self) -> SealExtent
    {
        self.extent
    }

    /// The sealing site that mints the atom.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn site(&self) -> SealSite
    {
        self.site
    }
}

/// The five disjoint declaration judgments.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum DeclarationContent
{
    /// An optionally ascribed value or an explicit hole.
    Value
    {
        /// The declared value type, if any.
        signature: Maybe<ValueTypeId, signature::Absent>,
        /// The defining value, or an explicit hole.
        body: Maybe<ValueId, body::Absent>,
    },
    /// A native nominal signature; it is neither a value body nor a hole.
    Data(alloc::sync::Arc<gandr_core_term::DataSignature>),
    /// A codata signature: its telescope and its observations.
    Codata(alloc::sync::Arc<gandr_core_term::CodataSignature>),
    /// A sealed abstract type; an atom, neither a value nor an assumption.
    Abstract(AbstractType),
    /// A world: its position is its identity, and it carries nothing.
    World,
}
/// One declaration, as the judgement reads it.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct Declaration
{
    /// The admission position the declaration takes.
    constant: ConstantIndex,
    /// The value declaration or native nominal signature.
    content: DeclarationContent,
    /// The producer's handle, echoed back.
    origin: OriginToken,
    /// The laws a definition's folds rest on, one per rule of the folded
    /// type in written order; empty for every other declaration.
    laws: Vec<ConstantIndex>,
    /// The rules of the operation a value declaration lowered from, over
    /// module positions; none for every other declaration. The judgement
    /// reads none of them: the kernel decides them where the declaration
    /// crosses.
    operation_rules: gandr_kernel_term::OperationRules,
    /// The stage binders a value declaration is quantified over, each with
    /// its bound; none for every other declaration. Its declared type names
    /// each binder's stage by the binder's ordinal.
    stages: Vec<gandr_kernel_term::StageBound>,
    /// The stages a value declaration's calls supply their callees' binders
    /// at, `f[i = j]`, each at the value its call forces; none for every
    /// other declaration. The kernel never reads them.
    supplies: Vec<gandr_core_term::staged::Supply>,
    /// The model slots a value declaration's calls omit, each with the
    /// models in scope that may answer it; none for every other declaration.
    /// The kernel never reads them: each is resolved before the body crosses.
    models: Vec<gandr_core_term::model::ModelSlot>,
    /// The laws a value declaration's capability scopes owe the theories they
    /// handle, each read through its scope's clauses; none for every other
    /// declaration. The kernel never reads them: no handler crosses.
    handler_laws: Vec<gandr_core_term::handler::HandlerLaw>,
    /// The entry a value declaration states, or why none.
    entry: Maybe<Entry, entry::Absent>,
}

impl Declaration
{
    /// The declaration at `constant` with these halves and this origin.
    ///
    /// # Specification
    /// - requires: nothing; judgement checks arena membership and admission
    ///   order rather than trusting the producer.
    /// - ensures: the accessors return exactly the arguments.
    /// - provides: the one constructor; every combination of present and absent
    ///   halves is representable, the body-less, signature-less one included,
    ///   because the hole rule answers it.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — over all four combinations of declaration halves,
    ///   module verdicts distinguish checking, synthesis and the two hole
    ///   directions; their origins separate lost provenance. Arena membership
    ///   and admission order are obligations of judgement, not construction.
    /// - witness: `module::tests::each_combination_of_halves_gets_its_verdict`
    /// - witness: `module::tests::an_admission_out_of_order_is_refused`
    #[spec(ensures: |ret| ret.constant == constant && ret.origin == origin
        && matches!(ret.content, DeclarationContent::Value { signature: declared, body: defined } if declared == signature && defined == body))]
    #[inline]
    #[must_use]
    pub fn new(
        constant: ConstantIndex,
        signature: Maybe<ValueTypeId, signature::Absent>,
        body: Maybe<ValueId, body::Absent>,
        origin: OriginToken,
    ) -> Self
    {
        Self {
            constant,
            content: DeclarationContent::Value { signature, body },
            origin,
            laws: Vec::new(),
            operation_rules: gandr_kernel_term::OperationRules::default(),
            stages: Vec::new(),
            supplies: Vec::new(),
            models: Vec::new(),
            handler_laws: Vec::new(),
            entry: Maybe::Absent(entry::Absent::Unstated),
        }
    }

    /// The admission position the declaration takes.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn constant(&self) -> ConstantIndex
    {
        self.constant
    }

    /// The value declaration or native nominal signature.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn content(&self) -> &DeclarationContent
    {
        &self.content
    }

    /// A nominal declaration at its own admission position.
    ///
    /// The shared immutable signature is retained by the declaration, context
    /// and report without copying its parameter and constructor telescopes.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn data(
        constant: ConstantIndex,
        signature: alloc::sync::Arc<gandr_core_term::DataSignature>,
        origin: OriginToken,
    ) -> Self
    {
        Self {
            constant,
            origin,
            content: DeclarationContent::Data(signature),
            laws: Vec::new(),
            operation_rules: gandr_kernel_term::OperationRules::default(),
            stages: Vec::new(),
            supplies: Vec::new(),
            models: Vec::new(),
            handler_laws: Vec::new(),
            entry: Maybe::Absent(entry::Absent::Unstated),
        }
    }

    /// A codata declaration at its own admission position.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn codata(
        constant: ConstantIndex,
        signature: alloc::sync::Arc<gandr_core_term::CodataSignature>,
        origin: OriginToken,
    ) -> Self
    {
        Self {
            constant,
            origin,
            content: DeclarationContent::Codata(signature),
            laws: Vec::new(),
            operation_rules: gandr_kernel_term::OperationRules::default(),
            stages: Vec::new(),
            supplies: Vec::new(),
            models: Vec::new(),
            handler_laws: Vec::new(),
            entry: Maybe::Absent(entry::Absent::Unstated),
        }
    }

    /// A sealed abstract type at its own admission position.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn abstract_type(
        constant: ConstantIndex,
        sealed: AbstractType,
        origin: OriginToken,
    ) -> Self
    {
        Self {
            constant,
            origin,
            content: DeclarationContent::Abstract(sealed),
            laws: Vec::new(),
            operation_rules: gandr_kernel_term::OperationRules::default(),
            stages: Vec::new(),
            supplies: Vec::new(),
            models: Vec::new(),
            handler_laws: Vec::new(),
            entry: Maybe::Absent(entry::Absent::Unstated),
        }
    }

    /// A world declaration at its own admission position.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn world(
        constant: ConstantIndex,
        origin: OriginToken,
    ) -> Self
    {
        Self {
            constant,
            origin,
            content: DeclarationContent::World,
            laws: Vec::new(),
            operation_rules: gandr_kernel_term::OperationRules::default(),
            stages: Vec::new(),
            supplies: Vec::new(),
            models: Vec::new(),
            handler_laws: Vec::new(),
            entry: Maybe::Absent(entry::Absent::Unstated),
        }
    }

    /// The producer's handle.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn origin(&self) -> OriginToken
    {
        self.origin
    }

    /// The laws a definition's folds rest on, in its folded type's rule
    /// order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn laws(&self) -> &[ConstantIndex]
    {
        &self.laws
    }

    /// The rules of the operation the declaration lowered from, over module
    /// positions.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn operation_rules(&self) -> &gandr_kernel_term::OperationRules
    {
        &self.operation_rules
    }

    /// The stage binders the declaration is quantified over, each with its
    /// bound, in binder order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn stages(&self) -> &[gandr_kernel_term::StageBound]
    {
        &self.stages
    }

    /// The stages the declaration's calls supply their callees' binders at,
    /// each at the value its call forces.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn supplies(&self) -> &[gandr_core_term::staged::Supply]
    {
        &self.supplies
    }

    /// The model slots the declaration's calls omit, each with its
    /// candidates.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn models(&self) -> &[gandr_core_term::model::ModelSlot]
    {
        &self.models
    }

    /// The laws the declaration's capability scopes owe, each read through
    /// its scope's clauses.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn handler_laws(&self) -> &[gandr_core_term::handler::HandlerLaw]
    {
        &self.handler_laws
    }

    /// The entry the declaration states, or why none.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub const fn entry(&self) -> Maybe<&Entry, entry::Absent>
    {
        match self.entry {
            Maybe::Present(ref stated) => Maybe::Present(stated),
            Maybe::Absent(reason) => Maybe::Absent(reason),
        }
    }

    /// This value declaration carrying `laws` as the laws its folds rest on,
    /// everything else unchanged; any other declaration unchanged.
    ///
    /// # Specification
    /// - requires: nothing — a fold's respect for its type's rules consults law
    ///   `i` only where its two sides of rule `i` do not convert, and checks
    ///   the law's statement against them there.
    /// - ensures: a value declaration carries exactly `laws`; a data or
    ///   abstract declaration is returned unchanged.
    /// - provides: how a producer attaches the laws a `respects` attribute
    ///   names.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a fold over the circle is admitted on its laws and
    ///   refused without them or with a law stating another path.
    /// - witness: `tests::native_formers::a_fold_rests_on_the_laws_of_the_rules_it_computes_apart`
    #[spec(
        captures: entry = (self.constant, self.origin, matches!(self.content, DeclarationContent::Value { .. }), self.laws.len(), laws.len()),
        ensures: |ret| ret.constant == entry.0 && ret.origin == entry.1
            && ret.laws.len() == if entry.2 { entry.4 } else { entry.3 },
    )]
    #[inline]
    #[must_use]
    pub fn lawful(
        self,
        laws: Vec<ConstantIndex>,
    ) -> Self
    {
        match self.content {
            DeclarationContent::Value { .. } => Self { laws, ..self },
            DeclarationContent::Data(_)
            | DeclarationContent::Codata(_)
            | DeclarationContent::Abstract(_)
            | DeclarationContent::World => self,
        }
    }

    /// This value declaration carrying `rules` as the rules of the operation
    /// it lowered from, everything else unchanged; any other declaration
    /// unchanged.
    ///
    /// # Specification
    /// - requires: nothing — the kernel decides at admission that the rules
    ///   converge.
    /// - ensures: a value declaration carries exactly `rules`; any other
    ///   declaration is returned unchanged.
    /// - provides: how a producer attaches the rules an operation was written
    ///   as.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an operation's rules cross to the kernel, which
    ///   admits the corpus's converging operations and refuses a forged pair.
    /// - witness: `bridge::tests::an_operations_rules_cross_at_kernel_positions_and_the_kernel_decides_them`
    #[spec(
        captures: entry = (self.constant, self.origin, matches!(self.content, DeclarationContent::Value { .. }), self.operation_rules.rules().len(), rules.rules().len()),
        ensures: |ret| ret.constant == entry.0 && ret.origin == entry.1
            && ret.operation_rules.rules().len() == if entry.2 { entry.4 } else { entry.3 },
    )]
    #[inline]
    #[must_use]
    pub fn ruled(
        self,
        rules: gandr_kernel_term::OperationRules,
    ) -> Self
    {
        match self.content {
            DeclarationContent::Value { .. } => Self {
                operation_rules: rules,
                ..self
            },
            DeclarationContent::Data(_)
            | DeclarationContent::Codata(_)
            | DeclarationContent::Abstract(_)
            | DeclarationContent::World => self,
        }
    }

    /// This value declaration quantified over `stages`, the stage binders
    /// its declared type names by ordinal, everything else unchanged; any
    /// other declaration unchanged.
    ///
    /// # Specification
    /// - requires: nothing — the judgement refuses a bound naming no earlier
    ///   binder and a stage naming no binder.
    /// - ensures: a value declaration carries exactly `stages`; any other
    ///   declaration is returned unchanged.
    /// - provides: how a producer attaches the binders a `@[i : Size]`
    ///   signature states.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a helper typed at a stage takes a recursion's claim,
    ///   and a call at no stage reads its result plain.
    /// - witness: `quantified::tests::a_helper_at_a_stage_takes_a_recursion_s_claim`
    #[spec(
        captures: entry = (self.constant, self.origin, matches!(self.content, DeclarationContent::Value { .. }), self.stages.len(), stages.len()),
        ensures: |ret| ret.constant == entry.0 && ret.origin == entry.1
            && ret.stages.len() == if entry.2 { entry.4 } else { entry.3 },
    )]
    #[inline]
    #[must_use]
    pub fn staged(
        self,
        stages: Vec<gandr_kernel_term::StageBound>,
    ) -> Self
    {
        match self.content {
            DeclarationContent::Value { .. } => Self { stages, ..self },
            DeclarationContent::Data(_)
            | DeclarationContent::Codata(_)
            | DeclarationContent::Abstract(_)
            | DeclarationContent::World => self,
        }
    }

    /// This value declaration whose calls supply `supplies`, everything else
    /// unchanged; any other declaration unchanged.
    ///
    /// # Specification
    /// - requires: nothing — the judgement holds each supply to the stage its
    ///   call's arguments show.
    /// - ensures: a value declaration carries exactly `supplies`; any other
    ///   declaration is returned unchanged.
    /// - provides: how a producer attaches the stages `f[i = j]` supplies.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a supply the arguments agree with checks, and one
    ///   they do not is refused.
    /// - witness: `quantified::tests::a_supplied_stage_is_held_to_the_arguments_1227`
    #[spec(
        captures: entry = (self.constant, self.origin, matches!(self.content, DeclarationContent::Value { .. }), self.supplies.len(), supplies.len()),
        ensures: |ret| ret.constant == entry.0 && ret.origin == entry.1
            && ret.supplies.len() == if entry.2 { entry.4 } else { entry.3 },
    )]
    #[inline]
    #[must_use]
    pub fn supplied(
        self,
        supplies: Vec<gandr_core_term::staged::Supply>,
    ) -> Self
    {
        match self.content {
            DeclarationContent::Value { .. } => Self { supplies, ..self },
            DeclarationContent::Data(_)
            | DeclarationContent::Codata(_)
            | DeclarationContent::Abstract(_)
            | DeclarationContent::World => self,
        }
    }

    /// This value declaration whose calls omit the model slots `models`,
    /// everything else unchanged; any other declaration unchanged.
    ///
    /// # Specification
    /// - requires: nothing — the judgement resolves each slot whose holes its
    ///   body nominates, and leaves any other unread.
    /// - ensures: a value declaration carries exactly `models`; any other
    ///   declaration is returned unchanged.
    /// - provides: how a producer attaches the candidates an omitted model slot
    ///   is resolved among.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a slot one candidate answers resolves to it.
    /// - witness: `elaboration::tests::a_model_slot_resolves_to_the_candidate_its_sort_admits_739`
    #[spec(
        captures: entry = (self.constant, self.origin, matches!(self.content, DeclarationContent::Value { .. }), self.models.len(), models.len()),
        ensures: |ret| ret.constant == entry.0 && ret.origin == entry.1
            && ret.models.len() == if entry.2 { entry.4 } else { entry.3 },
    )]
    #[inline]
    #[must_use]
    pub fn resolving(
        self,
        models: Vec<gandr_core_term::model::ModelSlot>,
    ) -> Self
    {
        match self.content {
            DeclarationContent::Value { .. } => Self { models, ..self },
            DeclarationContent::Data(_)
            | DeclarationContent::Codata(_)
            | DeclarationContent::Abstract(_)
            | DeclarationContent::World => self,
        }
    }

    /// This value declaration whose capability scopes owe `laws`, everything
    /// else unchanged; any other declaration unchanged.
    ///
    /// # Specification
    /// - requires: nothing — the judgement decides each law's sides once the
    ///   body is judged.
    /// - ensures: a value declaration carries exactly `laws`; any other
    ///   declaration is returned unchanged.
    /// - provides: how a producer attaches the laws a scope over a theory owes.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a law whose sides convert admits the declaration, and
    ///   one whose sides are apart refuses it.
    /// - witness: `module::tests::a_scope_is_checked_as_a_model_of_its_theory_2272`
    #[spec(
        captures: entry = (self.constant, self.origin, matches!(self.content, DeclarationContent::Value { .. }), self.handler_laws.len(), laws.len()),
        ensures: |ret| ret.constant == entry.0 && ret.origin == entry.1
            && ret.handler_laws.len() == if entry.2 { entry.4 } else { entry.3 },
    )]
    #[inline]
    #[must_use]
    pub fn obliged(
        self,
        laws: Vec<gandr_core_term::handler::HandlerLaw>,
    ) -> Self
    {
        match self.content {
            DeclarationContent::Value { .. } => Self {
                handler_laws: laws,
                ..self
            },
            DeclarationContent::Data(_)
            | DeclarationContent::Codata(_)
            | DeclarationContent::Abstract(_)
            | DeclarationContent::World => self,
        }
    }

    /// This value declaration stating `entry`, everything else unchanged;
    /// any other declaration unchanged.
    ///
    /// # Specification
    /// - requires: nothing — the worlds `entry` names are checked when the
    ///   declaration is judged, as is its bound by the host's entry.
    /// - ensures: a value declaration states exactly `entry`; a data, abstract
    ///   or world declaration is returned unchanged.
    /// - provides: how a producer attaches the entry an `entry` attribute
    ///   states.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a declaration entered at the seat's world with one
    ///   capability migrates once and is refused a second migration.
    /// - witness: `worlds::tests::a_migration_consumes_its_capability_visibly`
    #[spec(
        captures: entry_before = (self.constant, self.origin, matches!(self.content, DeclarationContent::Value { .. })),
        ensures: |ret| ret.constant == entry_before.0 && ret.origin == entry_before.1
            && (!entry_before.2 || matches!(ret.entry, Maybe::Present(_))),
    )]
    #[inline]
    #[must_use]
    pub fn entered(
        self,
        entry: Entry,
    ) -> Self
    {
        match self.content {
            DeclarationContent::Value { .. } => Self {
                entry: Maybe::Present(entry),
                ..self
            },
            DeclarationContent::Data(_)
            | DeclarationContent::Codata(_)
            | DeclarationContent::Abstract(_)
            | DeclarationContent::World => self,
        }
    }
}
