//! The laws a derived equality proves: the bodies of `Eq.generic.refl(T)` and
//! `Eq.generic.sym(T)`.
//!
//! For the equality `E` [`super::equality`] derives at the closed, free
//! declaration `T`, the derivation writes
//!
//! ```text
//! refl_T : U (Π a : T. F Path(Bool, ⟨E a a⟩, true))
//! refl_T = thunk (λa. case a as s. F Path(Bool, ⟨E s s⟩, true)
//!            { c_i ↦ λx̄. cong(x̄ ≐ x̄ ↦ true) })
//!
//! sym_T  : U (Π a b : T. F Path(Bool, ⟨E a b⟩, ⟨E b a⟩))
//! sym_T  = thunk (λa b. case a as s. F Path(Bool, ⟨E s b⟩, ⟨E b s⟩)
//!            { c_i ↦ λx̄. case b as t. F Path(Bool, ⟨E (c_i x̄) t⟩, ⟨E t (c_i x̄)⟩)
//!                { c_i ↦ λȳ. cong(x̄ ≐ ȳ ↦ ȳ ≐ x̄)
//!                ; c_k ↦ λz̄. return here(false) } })
//! ```
//!
//! each `case … as` a data case whose motive its branches' goals read, and `E`
//! written in place, as the equality writes another declaration's. A
//! constructor's branch of `E` is the sequential conjunction `K(t̄) = r ← t_1;
//! case r { K(t_2 …) ; return false }` of its fields' comparisons, and
//! `cong(t̄ ↦ s̄)` proves `Path(Bool, ⟨K(t̄)⟩, ⟨K(s̄)⟩)` from a proof `π_j :
//! Path(Bool, ⟨t_j⟩, ⟨s_j⟩)` of each comparison, by congruence, from the last
//! comparison back:
//!
//! ```text
//! cong_j = p ← π_j; q ← cong_{j+1};
//!          a ← transport(λz. Path(Bool, ⟨K_j(t̄)⟩, ⟨case z { K_{j+1}(t̄) ; false }⟩), p, here(⟨K_j(t̄)⟩));
//!          transport(λw. Path(Bool, ⟨K_j(t̄)⟩, ⟨case ⟨s_j⟩ { return w ; false }⟩), q, a)
//! ```
//!
//! The first transport rewrites the comparison and the second the rest of the
//! conjunction. Both rest on conversion: a bind over a stuck comparison meets
//! the case over its returned value, and `return ⟨K⟩` meets `K` in a branch
//! of a stuck case.
//!
//! A comparison's proof reads its field's type: at an integer or a string, the
//! law the host asserts of its equality, which the caller's [`Hosted`]
//! answers; at a unit, `here(true)`; at another covered declaration, that
//! declaration's own derived proof, written in place.
//!
//! # Coverage
//!
//! Every declaration the equality covers whose fields are integers, strings,
//! units and other such declarations, with any number of constructors. A
//! field of a sum or a tuple refuses [`Uncovered::DependentCase`]: its proof
//! cases on the field under a motive, which core's `case` does not carry
//! (#2374). A recursive field refuses [`Uncovered::Inductive`]. Transitivity
//! is not derived: its proof inverts a conjunction, which needs that motive
//! over `Bool`.
//!
//! The laws are untrusted, as the equality is: each is an ordinary declaration
//! the checker judges and the kernel readmits.
//!
//! # Decision
//!
//! - Choice: a proof per declaration, one data case per constructor of each
//!   argument and the conjunction rewritten comparison by comparison with
//!   transport, the primitives' laws the host's own. It needs nothing past the
//!   core the equality already uses: a data case with a motive over a
//!   declaration, and paths over `Bool`.
//! - Alternatives: a generic induction over a description's codes, as the
//!   equality is generic over them, which would cover sums, tuples and
//!   recursion at once but needs a case whose motive reads its scrutinee at
//!   every code; admitting a derived law on the derivation's word, which would
//!   leave a model's laws unchecked.
//! - Reversal: once core's case carries a motive over a sum (#2374), a sum's
//!   and a tuple's fields prove by the same congruence under that case, and
//!   transitivity by inverting the conjunction; a recursive field then wants
//!   the induction, not this per-declaration proof.

use alloc::collections::BTreeMap;
use alloc::vec::Vec;

use anodized::spec;
use gandr_kernel_term::BaseType;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::ConstructorTag;
use gandr_kernel_term::FieldCount;
use gandr_kernel_term::FieldPosition;
use gandr_kernel_term::OccurrenceSite;

use super::Derived;
use super::Deriving;
use super::Signatures;
use super::Uncovered;
use super::count;
use super::plus;
use crate::Binders;
use crate::ComputationId;
use crate::CoreArena;
use crate::ValueId;
use crate::ValueType;
use crate::ValueTypeId;
use crate::primitive::Arguments;
use crate::primitive::Primitive;

#[cfg(test)]
mod tests;

/// A law a derived equality proves.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Statement
{
    /// `(a) => Path(Bool, E(a, a), true)`.
    Reflexive,
    /// `(a, b) => Path(Bool, E(a, b), E(b, a))`.
    Symmetric,
}

/// The law the host asserts of its equality at an integer or a string field,
/// as a value of the law's type: the prelude's admitted law, or none where it
/// states none.
pub type Hosted<'lookup> = dyn Fn(BaseType, Statement) -> Option<ValueId> + 'lookup;

/// Which way a comparison reads its two sides.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Sides
{
    /// Left then right, as the equality compares them.
    Written,
    /// Right then left, as symmetry's target compares them.
    Swapped,
}

/// One field's comparison in a law's proof.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Field
{
    /// Decided by the host's primitive and proved by the law the host asserts.
    Hosted
    {
        /// The primitive the equality calls.
        primitive: Primitive,
        /// The host's law.
        law: ValueId,
    },
    /// A unit, equal to itself.
    Unit,
    /// Another declaration, decided by its derived equality and proved by its
    /// derived law.
    Nested(ConstantIndex),
}

/// One comparison of a constructor's field: the field and the de Bruijn levels
/// of its two sides.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Compared
{
    /// The field compared.
    field: Field,
    /// The left side's level.
    left: Binders,
    /// The right side's level.
    right: Binders,
}

/// What a conjunction's proof by congruence ends at.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Target
{
    /// `true`: each comparison proved reflexive.
    Truth,
    /// The conjunction with each comparison's sides swapped.
    Swapped,
}

/// One law's derivation: the equalities derived, each covered declaration's
/// fields, and each proof derived so far.
struct Proving<'deriving, 'run, 'lookup, 'hosted>
{
    /// The equalities the law is about, and the arena.
    deriving: &'deriving mut Deriving<'run, 'lookup>,
    /// The host's laws.
    hosted: &'deriving Hosted<'hosted>,
    /// The law proved.
    statement: Statement,
    /// Each covered declaration's fields, constructor by constructor.
    fields: BTreeMap<ConstantIndex, Vec<Vec<Field>>>,
    /// Each declaration's derived proof and its declared type.
    proofs: BTreeMap<ConstantIndex, (ValueId, ValueTypeId)>,
}

/// Derive `statement` of the equality of the closed, free data declaration at
/// `position`.
///
/// # Specification
/// - requires: as [`super::equality`]; `hosted` answers a value of the host's
///   law at a base type wherever the prelude states one.
/// - ensures: the declared type and the body the module documentation states,
///   minted into `arena`, each closed.
/// - provides: the body of a definition written `Eq.generic.refl(T)` or
///   `Eq.generic.sym(T)`, judged by the checker and readmitted by the kernel as
///   any declaration.
/// - fails: what [`super::equality`] fails with; [`Uncovered::Field`] at an
///   integer or string field whose law `hosted` does not answer;
///   [`Uncovered::DependentCase`] at a field of a sum or a tuple;
///   [`Uncovered::Inductive`] at a recursive field — each at the first such
///   field of the declaration or of one its fields reach.
/// - panics: none.
///
/// # Errors
/// As `- fails:`.
///
/// # Adequacy
/// - hypothesis: L3 — a point's and a line's laws derive closed proofs of the
///   stated types, a flag and a recursion refuse at their fields, and an
///   integer law the host does not state refuses at the field. The checker's
///   admission of the proofs is witnessed in `gandr_core_checker`'s
///   recursive-data tests.
/// - witness: `generic::law::tests::a_point_and_a_line_derive_closed_laws_2302`
/// - witness: `generic::law::tests::an_uncovered_field_refuses_its_law_at_its_site_2302`
#[spec(ensures: |ret| ret.as_ref().map_or(true, |derived| arena.value_type(derived.declared).is_some() && arena.value(derived.body).is_some()))]
#[inline]
pub fn law(
    arena: &mut CoreArena,
    position: ConstantIndex,
    signatures: &Signatures<'_>,
    statement: Statement,
    hosted: &Hosted<'_>,
) -> Result<Derived, Uncovered>
{
    let (mut deriving, order) = Deriving::start(arena, signatures, position)?;
    let mut proving = Proving {
        deriving: &mut deriving,
        hosted,
        statement,
        fields: BTreeMap::new(),
        proofs: BTreeMap::new(),
    };
    proving.cover(position)?;
    // A declaration's proof is derived after those its fields reach, so each is
    // written in place by the time it is applied.
    for declaration in order {
        if proving.fields.contains_key(&declaration) {
            let proof = match statement {
                Statement::Reflexive => proving.reflexivity(declaration)?,
                Statement::Symmetric => proving.symmetry(declaration)?,
            };
            let _first = proving.proofs.insert(declaration, proof);
        }
    }
    let &(body, declared) = proving
        .proofs
        .get(&position)
        .ok_or(Uncovered::Unknown(position))?;
    Ok(Derived {
        declared,
        body,
        cases: deriving.cases,
    })
}

impl Proving<'_, '_, '_, '_>
{
    /// Read the fields of `position` and of every declaration they reach.
    ///
    /// # Specification
    /// - requires: every declaration `position` reaches is derived.
    /// - ensures: `position` and each declaration a field reaches through
    ///   another declaration's fields have their fields filed.
    /// - fails: as [`Self::field`], at the first field it stops at.
    /// - panics: none.
    ///
    /// # Termination
    /// - reason: a declaration is filed at most once, and the equality's
    ///   derivation has refused every cycle.
    /// - measure: the reached declarations not yet filed.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a line files its point, and a flag refuses.
    /// - witness: `generic::law::tests::a_point_and_a_line_derive_closed_laws_2302`
    /// - witness: `generic::law::tests::an_uncovered_field_refuses_its_law_at_its_site_2302`
    #[spec(ensures: |ret| ret.is_err() || self.fields.contains_key(&position))]
    fn cover(
        &mut self,
        position: ConstantIndex,
    ) -> Result<(), Uncovered>
    {
        let mut pending = Vec::from([position]);
        while let Some(at) = pending.pop() {
            if self.fields.contains_key(&at) {
                continue;
            }
            let rows = self
                .deriving
                .rows
                .get(&at)
                .cloned()
                .ok_or(Uncovered::Unknown(at))?;
            let mut read = Vec::with_capacity(rows.len());
            for (tag, row) in rows.iter().enumerate() {
                let mut fields = Vec::with_capacity(row.len());
                for (place, &ty) in row.iter().enumerate() {
                    let site = OccurrenceSite::Field {
                        tag: ConstructorTag::from(tag),
                        field: FieldPosition::from(place),
                    };
                    let field = self.field(at, site, ty)?;
                    if let Field::Nested(declaration) = field {
                        pending.push(declaration);
                    }
                    fields.push(field);
                }
                read.push(fields);
            }
            let _first = self.fields.insert(at, read);
        }
        Ok(())
    }

    /// The comparison a field of type `ty`, at `site` of the declaration at
    /// `at`, stands for in the law's proof.
    ///
    /// # Specification
    /// - requires: `ty` is closed.
    /// - ensures: an integer or a string compared by its primitive and proved
    ///   by the host's law; a unit; another declaration of no arguments.
    /// - fails: [`Uncovered::Field`] for a base type without its primitive or
    ///   its law, and any type the equality does not compare;
    ///   [`Uncovered::Inductive`] for `at` itself; [`Uncovered::DependentCase`]
    ///   for a sum or a non-empty tuple.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`law`].
    /// - witness: `generic::law::tests::an_uncovered_field_refuses_its_law_at_its_site_2302`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |&field| field != Field::Nested(at)))]
    fn field(
        &self,
        at: ConstantIndex,
        site: OccurrenceSite,
        ty: ValueTypeId,
    ) -> Result<Field, Uncovered>
    {
        let uncovered = Uncovered::Field(at, site);
        match self.deriving.arena.value_type(ty) {
            Some(&ValueType::Base(base @ (BaseType::Integer | BaseType::String))) => {
                let primitive = if base == BaseType::Integer {
                    self.deriving.integer
                }
                else {
                    self.deriving.text
                };
                match (primitive, (self.hosted)(base, self.statement)) {
                    (Some(primitive), Some(law)) => Ok(Field::Hosted { primitive, law }),
                    _ => Err(uncovered),
                }
            },
            Some(&ValueType::Product(ref parts)) if parts.is_empty() => Ok(Field::Unit),
            Some(&ValueType::Data {
                declaration,
                ref arguments,
            }) if arguments.is_empty() => {
                if declaration == at {
                    Err(Uncovered::Inductive(at, site))
                }
                else {
                    Ok(Field::Nested(declaration))
                }
            },
            Some(&(ValueType::Sum(_) | ValueType::Product(_))) => {
                Err(Uncovered::DependentCase(at, site))
            },
            Some(_) | None => Err(uncovered),
        }
    }

    /// The variable at de Bruijn `level`, read `depth` binders deep.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: as [`Deriving::at`].
    /// - fails: as [`Deriving::at`].
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`law`].
    /// - witness: `generic::law::tests::a_point_and_a_line_derive_closed_laws_2302`
    #[spec(ensures: |ret| ret.is_ok() == (u32::from(level) < u32::from(depth)))]
    fn at(
        &mut self,
        depth: Binders,
        level: Binders,
    ) -> Result<ValueId, Uncovered>
    {
        self.deriving.at(depth, level)
    }

    /// `force (E : U (T → T → F Bool)) left right`, the derived equality of
    /// the declaration at `at` applied.
    ///
    /// # Specification
    /// - requires: `at` is derived.
    /// - ensures: the application, as the equality writes another declaration's
    ///   comparison.
    /// - fails: [`Uncovered::Unknown`] for a declaration not derived.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`law`].
    /// - witness: `generic::law::tests::a_point_and_a_line_derive_closed_laws_2302`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |&term| self.deriving.arena.computation(term).is_some()))]
    fn decide(
        &mut self,
        at: ConstantIndex,
        left: ValueId,
        right: ValueId,
    ) -> Result<ComputationId, Uncovered>
    {
        let derived = self
            .deriving
            .derived
            .get(&at)
            .copied()
            .ok_or(Uncovered::Unknown(at))?;
        let ty = self.deriving.predicate(at);
        let arena = &mut *self.deriving.arena;
        let ascribed = arena.value_ascribe(derived, ty);
        let forced = arena.computation_force(ascribed);
        let applied = arena.computation_application(forced, left);
        Ok(arena.computation_application(applied, right))
    }

    /// `⟨decided⟩`, a computation of `F Bool` read as the value it returns:
    /// thunked, ascribed `U (F Bool)` and forced, since a case synthesises no
    /// type.
    ///
    /// # Specification
    /// trivial.
    fn endpoint(
        &mut self,
        decided: ComputationId,
    ) -> ValueId
    {
        let arena = &mut *self.deriving.arena;
        let thunk = arena.value_thunk(decided);
        let verdict = arena.value_type_thunk(self.deriving.answer);
        let ascribed = arena.value_ascribe(thunk, verdict);
        let forced = arena.computation_force(ascribed);
        arena.value_returned(forced)
    }

    /// `compared`'s comparison, `depth` binders deep, its sides read as
    /// `sides` says: the term the equality writes for it.
    ///
    /// # Specification
    /// - requires: `compared`'s levels are below `depth`.
    /// - ensures: the primitive at the two sides, `return true` for a unit, the
    ///   other declaration's equality applied.
    /// - fails: as [`Self::at`] and [`Self::decide`].
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`law`].
    /// - witness: `generic::law::tests::a_point_and_a_line_derive_closed_laws_2302`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |&term| self.deriving.arena.computation(term).is_some()))]
    fn term(
        &mut self,
        compared: Compared,
        sides: Sides,
        depth: Binders,
    ) -> Result<ComputationId, Uncovered>
    {
        let (left, right) = if sides == Sides::Swapped {
            (compared.right, compared.left)
        }
        else {
            (compared.left, compared.right)
        };
        match compared.field {
            Field::Hosted { primitive, .. } => {
                let left = self.at(depth, left)?;
                let right = self.at(depth, right)?;
                Ok(self
                    .deriving
                    .arena
                    .computation_primitive(primitive, Arguments::Binary([left, right])))
            },
            Field::Unit => Ok(self.deriving.arena.computation_return(self.deriving.truth)),
            Field::Nested(at) => {
                let left = self.at(depth, left)?;
                let right = self.at(depth, right)?;
                self.decide(at, left, right)
            },
        }
    }

    /// The sequential conjunction of `comparisons`, the first `depth` binders
    /// deep, as the equality writes a constructor's branch.
    ///
    /// # Specification
    /// - requires: every level in `comparisons` is below `depth`.
    /// - ensures: `return true` for none, the comparison for one, and otherwise
    ///   each bound and cased on in turn, a `false` ending the rest, the i-th
    ///   built `depth + 2i` deep; a unit bound before a later comparison
    ///   thunked, ascribed and forced, as the equality binds it.
    /// - fails: as [`Self::term`]; [`Uncovered::BinderCeiling`] past the
    ///   ceiling.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the proof's endpoints convert with the equality's
    ///   branches.
    /// - witness: `generic::law::tests::a_point_and_a_line_derive_closed_laws_2302`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |&term| self.deriving.arena.computation(term).is_some()))]
    fn conjunction(
        &mut self,
        comparisons: &[Compared],
        depth: Binders,
    ) -> Result<ComputationId, Uncovered>
    {
        let Some((&last, rest)) = comparisons.split_last()
        else {
            return Ok(self.deriving.arena.computation_return(self.deriving.truth));
        };
        let deepest = plus(depth, plus(count(rest)?, count(rest)?)?)?;
        let mut continued = self.term(last, Sides::Written, deepest)?;
        for (place, &compared) in rest.iter().enumerate().rev() {
            let place = count(rest.get(.. place).unwrap_or_default())?;
            let at = plus(depth, plus(place, place)?)?;
            let bound = plus(at, Binders::ONE)?;
            let verdict = self.at(bound, at)?;
            let ended = self.deriving.refuted();
            let case = self
                .deriving
                .arena
                .computation_case(verdict, &[continued, ended]);
            let term = self.term(compared, Sides::Written, at)?;
            let bindable = if compared.field == Field::Unit {
                let thunk = self.deriving.arena.value_thunk(term);
                let verdict = self.deriving.arena.value_type_thunk(self.deriving.answer);
                let ascribed = self.deriving.arena.value_ascribe(thunk, verdict);
                self.deriving.arena.computation_force(ascribed)
            }
            else {
                term
            };
            continued = self.deriving.arena.computation_bind(bindable, case);
        }
        Ok(continued)
    }

    /// The proof of `compared`, `depth` binders deep: `Path(Bool, ⟨t⟩, true)`
    /// for reflexivity, `Path(Bool, ⟨t⟩, ⟨t swapped⟩)` for symmetry.
    ///
    /// # Specification
    /// - requires: `compared`'s levels are below `depth`, and a nested
    ///   declaration's proof is derived.
    /// - ensures: the host's law forced and applied, `return here(true)` for a
    ///   unit, the nested declaration's proof ascribed, forced and applied — to
    ///   the left side for reflexivity, to both for symmetry.
    /// - fails: [`Uncovered::Unknown`] for a nested proof not derived; as
    ///   [`Self::at`].
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`law`].
    /// - witness: `generic::law::tests::a_point_and_a_line_derive_closed_laws_2302`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |&term| self.deriving.arena.computation(term).is_some()))]
    fn proof(
        &mut self,
        compared: Compared,
        depth: Binders,
    ) -> Result<ComputationId, Uncovered>
    {
        let head = match compared.field {
            Field::Unit => {
                // Bound before a later comparison's proof, so ascribed to
                // synthesise, as the equality binds a unit's comparison.
                let truth = self.deriving.truth;
                let arena = &mut *self.deriving.arena;
                let here = arena.value_here(truth);
                let proved = arena.computation_return(here);
                let thunk = arena.value_thunk(proved);
                let path = arena.value_type_path(self.deriving.boolean, truth, truth);
                let returns = arena.comp_type_returner(path);
                let stated = arena.value_type_thunk(returns);
                let ascribed = arena.value_ascribe(thunk, stated);
                return Ok(arena.computation_force(ascribed));
            },
            Field::Hosted { law, .. } => self.deriving.arena.computation_force(law),
            Field::Nested(at) => {
                let &(proof, declared) = self.proofs.get(&at).ok_or(Uncovered::Unknown(at))?;
                let ascribed = self.deriving.arena.value_ascribe(proof, declared);
                self.deriving.arena.computation_force(ascribed)
            },
        };
        let left = self.at(depth, compared.left)?;
        let applied = self.deriving.arena.computation_application(head, left);
        Ok(match self.statement {
            Statement::Reflexive => applied,
            Statement::Symmetric => {
                let right = self.at(depth, compared.right)?;
                self.deriving.arena.computation_application(applied, right)
            },
        })
    }

    /// `Path(Bool, ⟨K(comparisons)⟩, ⟨K(targets)⟩)` by congruence, the
    /// first comparison's proof bound `depth` binders deep.
    ///
    /// # Specification
    /// - requires: every level in `comparisons` is below `depth`.
    /// - ensures: `return here(true)` for no comparisons, the comparison's
    ///   proof for one, and otherwise each step the module documentation
    ///   states, the j-th `depth + j` deep.
    /// - fails: as [`Self::step`].
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`law`].
    /// - witness: `generic::law::tests::a_point_and_a_line_derive_closed_laws_2302`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |&term| self.deriving.arena.computation(term).is_some()))]
    fn cong(
        &mut self,
        comparisons: &[Compared],
        target: Target,
        depth: Binders,
    ) -> Result<ComputationId, Uncovered>
    {
        let Some((&last, rest)) = comparisons.split_last()
        else {
            let here = self.deriving.arena.value_here(self.deriving.truth);
            return Ok(self.deriving.arena.computation_return(here));
        };
        let mut built = self.proof(last, plus(depth, count(rest)?)?)?;
        for place in (0 .. rest.len()).rev() {
            let at = plus(depth, count(rest.get(.. place).unwrap_or_default())?)?;
            let from = comparisons.get(place ..).unwrap_or_default();
            built = self.step(from, target, at, built)?;
        }
        Ok(built)
    }

    /// One step of [`Self::cong`]: the conjunction from `comparisons`' first,
    /// given `rest`, the proof of the conjunction after it, built `depth + 1`
    /// deep.
    ///
    /// # Specification
    /// - requires: at least two comparisons; their levels below `depth`.
    /// - ensures: `p ← π; q ← rest; a ← transport(…, p, here(…)); transport(…,
    ///   q, a)` with the motives the module documentation states, the first
    ///   comparison's proof bound `depth` binders deep.
    /// - fails: as [`Self::conjunction`] and [`Self::proof`].
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`law`].
    /// - witness: `generic::law::tests::a_point_and_a_line_derive_closed_laws_2302`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |&term| self.deriving.arena.computation(term).is_some()))]
    fn step(
        &mut self,
        comparisons: &[Compared],
        target: Target,
        depth: Binders,
        rest: ComputationId,
    ) -> Result<ComputationId, Uncovered>
    {
        let Some((&first, tail)) = comparisons.split_first()
        else {
            return Err(Uncovered::BinderCeiling);
        };
        let boolean = self.deriving.boolean;
        let head = self.proof(first, depth)?;
        // Past `p` and `q`.
        let opened = plus(depth, Binders::from(2_u32))?;
        let rewritten = {
            let inside = plus(opened, Binders::ONE)?;
            let whole = self.conjunction(comparisons, inside)?;
            let left = self.endpoint(whole);
            let z = self.at(inside, opened)?;
            let continued = self.conjunction(tail, plus(inside, Binders::ONE)?)?;
            let ended = self.deriving.refuted();
            let case = self.deriving.arena.computation_case(z, &[continued, ended]);
            let right = self.endpoint(case);
            let motive = self.deriving.arena.value_type_path(boolean, left, right);
            let whole = self.conjunction(comparisons, opened)?;
            let start = self.endpoint(whole);
            let base = self.deriving.arena.value_here(start);
            let p = self.at(opened, depth)?;
            self.deriving
                .arena
                .computation_path_transport(motive, p, base)
        };
        // Past `a`.
        let rewound = plus(opened, Binders::ONE)?;
        let finished = {
            let inside = plus(rewound, Binders::ONE)?;
            let whole = self.conjunction(comparisons, inside)?;
            let left = self.endpoint(whole);
            // `case true { return w ; false }` is `w`, and a case does not
            // synthesise a literal scrutinee, so where the target comparison
            // is `true` — reflexivity's, and a unit's — the motive states `w`.
            let right = match (target, first.field) {
                (Target::Truth, _) | (Target::Swapped, Field::Unit) => self.at(inside, rewound)?,
                (Target::Swapped, Field::Hosted { .. } | Field::Nested(_)) => {
                    let swapped = self.term(first, Sides::Swapped, inside)?;
                    let decided = self.deriving.arena.value_returned(swapped);
                    let w = self.at(plus(inside, Binders::ONE)?, rewound)?;
                    let kept = self.deriving.arena.computation_return(w);
                    let ended = self.deriving.refuted();
                    let case = self
                        .deriving
                        .arena
                        .computation_case(decided, &[kept, ended]);
                    self.endpoint(case)
                },
            };
            let motive = self.deriving.arena.value_type_path(boolean, left, right);
            let q = self.at(rewound, plus(depth, Binders::ONE)?)?;
            let a = self.at(rewound, opened)?;
            self.deriving.arena.computation_path_transport(motive, q, a)
        };
        let arena = &mut *self.deriving.arena;
        let tail_bound = arena.computation_bind(rewritten, finished);
        let rest_bound = arena.computation_bind(rest, tail_bound);
        Ok(arena.computation_bind(head, rest_bound))
    }

    /// `⟨E left right⟩`, the equality of `at` at two variables, `depth`
    /// binders deep.
    ///
    /// # Specification
    /// - requires: `at` is derived; both levels below `depth`.
    /// - ensures: the value the application returns.
    /// - fails: as [`Self::at`] and [`Self::decide`].
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`law`].
    /// - witness: `generic::law::tests::a_point_and_a_line_derive_closed_laws_2302`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |&value| self.deriving.arena.value(value).is_some()))]
    fn decided(
        &mut self,
        at: ConstantIndex,
        depth: Binders,
        (left, right): (Binders, Binders),
    ) -> Result<ValueId, Uncovered>
    {
        let left = self.at(depth, left)?;
        let right = self.at(depth, right)?;
        let decided = self.decide(at, left, right)?;
        Ok(self.deriving.arena.value_returned(decided))
    }

    /// The comparisons of a constructor's fields `fields`, the left sides
    /// bound from level `lefts` and the right from `rights`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: one comparison per field, in order, its sides `lefts + i` and
    ///   `rights + i`.
    /// - fails: [`Uncovered::BinderCeiling`] past the ceiling.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`law`].
    /// - witness: `generic::law::tests::a_point_and_a_line_derive_closed_laws_2302`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |compared| compared.len() == fields.len()))]
    fn compared(
        fields: &[Field],
        (lefts, rights): (Binders, Binders),
    ) -> Result<Vec<Compared>, Uncovered>
    {
        let mut compared = Vec::with_capacity(fields.len());
        let mut step = Binders::NONE;
        for &field in fields {
            compared.push(Compared {
                field,
                left: plus(lefts, step)?,
                right: plus(rights, step)?,
            });
            step = plus(step, Binders::ONE)?;
        }
        Ok(compared)
    }

    /// The reflexivity of the equality of the declaration at `at`, and its
    /// declared type.
    ///
    /// # Specification
    /// - requires: `at`'s fields are filed and every nested proof derived.
    /// - ensures: `refl_T` and its type as the module documentation states.
    /// - fails: as [`Self::cong`].
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`law`].
    /// - witness: `generic::law::tests::a_point_and_a_line_derive_closed_laws_2302`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |&(body, declared)| self.deriving.arena.value(body).is_some() && self.deriving.arena.value_type(declared).is_some()))]
    fn reflexivity(
        &mut self,
        at: ConstantIndex,
    ) -> Result<(ValueId, ValueTypeId), Uncovered>
    {
        let boolean = self.deriving.boolean;
        let truth = self.deriving.truth;
        let carrier = self.deriving.arena.value_type_data(at, Vec::new());
        // Under `a`: `a` is level zero.
        let one = Binders::ONE;
        let declared = {
            let left = self.decided(at, one, (Binders::NONE, Binders::NONE))?;
            let path = self.deriving.arena.value_type_path(boolean, left, truth);
            let returns = self.deriving.arena.comp_type_returner(path);
            let quantified = self.deriving.arena.comp_type_pi(carrier, returns);
            self.deriving.arena.value_type_thunk(quantified)
        };
        // Under `a` and the case's `s`: `s` is level one.
        let motive = {
            let left = self.decided(at, Binders::from(2_u32), (one, one))?;
            let path = self.deriving.arena.value_type_path(boolean, left, truth);
            self.deriving.arena.comp_type_returner(path)
        };
        let rows = self.fields.get(&at).cloned().unwrap_or_default();
        let mut branches = Vec::with_capacity(rows.len());
        let mut arities = Vec::with_capacity(rows.len());
        for row in &rows {
            let width = count(row)?;
            let compared = Self::compared(row, (one, one))?;
            let proof = self.cong(&compared, Target::Truth, plus(one, width)?)?;
            branches.push(self.deriving.abstracted(proof, width));
            arities.push(FieldCount::from(row.len()));
        }
        let scrutinee = self.at(one, Binders::NONE)?;
        let case = self
            .deriving
            .arena
            .computation_data_case(scrutinee, motive, branches, arities);
        self.deriving.cases.push((case, at));
        let body = self.deriving.arena.computation_lambda(case);
        Ok((self.deriving.arena.value_thunk(body), declared))
    }

    /// The symmetry of the equality of the declaration at `at`, and its
    /// declared type.
    ///
    /// # Specification
    /// - requires: `at`'s fields are filed and every nested proof derived.
    /// - ensures: `sym_T` and its type as the module documentation states.
    /// - fails: as [`Self::cong`].
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`law`].
    /// - witness: `generic::law::tests::a_point_and_a_line_derive_closed_laws_2302`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |&(body, declared)| self.deriving.arena.value(body).is_some() && self.deriving.arena.value_type(declared).is_some()))]
    fn symmetry(
        &mut self,
        at: ConstantIndex,
    ) -> Result<(ValueId, ValueTypeId), Uncovered>
    {
        let boolean = self.deriving.boolean;
        let carrier = self.deriving.arena.value_type_data(at, Vec::new());
        // Levels: `a` 0, `b` 1, then the first argument's fields and the
        // second's.
        let (first, second) = (Binders::NONE, Binders::ONE);
        let opened = Binders::from(2_u32);
        let declared = {
            let left = self.decided(at, opened, (first, second))?;
            let right = self.decided(at, opened, (second, first))?;
            let path = self.deriving.arena.value_type_path(boolean, left, right);
            let returns = self.deriving.arena.comp_type_returner(path);
            let inner = self.deriving.arena.comp_type_pi(carrier, returns);
            let outer = self.deriving.arena.comp_type_pi(carrier, inner);
            self.deriving.arena.value_type_thunk(outer)
        };
        // Under `a`, `b` and the case's `s`: `s` is level two.
        let outer_motive = {
            let inside = plus(opened, Binders::ONE)?;
            let left = self.decided(at, inside, (opened, second))?;
            let right = self.decided(at, inside, (second, opened))?;
            let path = self.deriving.arena.value_type_path(boolean, left, right);
            self.deriving.arena.comp_type_returner(path)
        };
        let rows = self.fields.get(&at).cloned().unwrap_or_default();
        let arities: Vec<FieldCount> = rows.iter().map(|row| FieldCount::from(row.len())).collect();
        let mut outer = Vec::with_capacity(rows.len());
        for (tag, own) in rows.iter().enumerate() {
            let width = count(own)?;
            let rights = plus(opened, width)?;
            // Under the fields and the inner case's `t`: `t` is level
            // `rights`, the constructor rebuilt from the fields.
            let inner_motive = {
                let inside = plus(rights, Binders::ONE)?;
                let mut fields = Vec::with_capacity(own.len());
                let mut level = opened;
                for _field in own {
                    fields.push(self.at(inside, level)?);
                    level = plus(level, Binders::ONE)?;
                }
                let built = self.deriving.arena.value_constructor(
                    carrier,
                    ConstructorTag::from(tag),
                    fields,
                );
                let t = self.at(inside, rights)?;
                let left = self.decide(at, built, t)?;
                let left = self.deriving.arena.value_returned(left);
                let right = self.decide(at, t, built)?;
                let right = self.deriving.arena.value_returned(right);
                let path = self.deriving.arena.value_type_path(boolean, left, right);
                self.deriving.arena.comp_type_returner(path)
            };
            let mut inner = Vec::with_capacity(rows.len());
            for (other, across) in rows.iter().enumerate() {
                let reach = count(across)?;
                let proof = if other == tag {
                    let compared = Self::compared(own, (opened, rights))?;
                    self.cong(&compared, Target::Swapped, plus(rights, width)?)?
                }
                else {
                    let here = self.deriving.arena.value_here(self.deriving.falsity);
                    self.deriving.arena.computation_return(here)
                };
                inner.push(self.deriving.abstracted(proof, reach));
            }
            let scrutinee = self.at(rights, second)?;
            let case = self.deriving.arena.computation_data_case(
                scrutinee,
                inner_motive,
                inner,
                arities.clone(),
            );
            self.deriving.cases.push((case, at));
            outer.push(self.deriving.abstracted(case, width));
        }
        let scrutinee = self.at(opened, first)?;
        let case =
            self.deriving
                .arena
                .computation_data_case(scrutinee, outer_motive, outer, arities);
        self.deriving.cases.push((case, at));
        let body = self.deriving.arena.computation_lambda(case);
        let body = self.deriving.arena.computation_lambda(body);
        Ok((self.deriving.arena.value_thunk(body), declared))
    }
}
