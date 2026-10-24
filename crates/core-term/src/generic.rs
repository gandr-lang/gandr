//! Equality derived from a data declaration's constructors: the body of
//! `Eq.generic(T)`.
//!
//! For a closed, free declaration `T` at admission position `p` with
//! constructors `c_i` over fields `F̄_i`, the derivation writes
//!
//! ```text
//! eq_T : U (T → T → F Bool)
//! eq_T = thunk (fix_SD rec. λa. λb. case a of
//!          { c_i ↦ λx̄. case b of
//!              { c_i ↦ λȳ. x_1 ≐ y_1 ∧ … ∧ x_n ≐ y_n
//!              ; c_k ↦ λz̄. return false } })
//! ```
//!
//! where the conjunction is sequential, a `false` ending it, and `≐` reads
//! each field's type: the integer and string primitives' equality, a unit
//! answers true, a product compares its components in order and a sum its
//! injections side by side, a field of `T` itself recurses through `rec` on the
//! first argument's field, and a field of another closed, free declaration
//! applies that declaration's own derived equality, written in place. It is
//! generic equality over a description's codes — the unit, products, sums
//! and the recursive occurrence (Chapman, Dagand, `McBride` and Morris, *The
//! Gentle Art of Levitation*, ICFP 2010, `doi:10.1145/1863543.1863547`) — read
//! off the admitted signature instead of a code.
//!
//! The derivation is untrusted: the equality is an ordinary declaration the
//! checker judges and the kernel readmits, its fixpoint typed by stages in
//! both, as the eliminator a recursive declaration derives is.
//!
//! What it does not cover it refuses by name ([`Uncovered`]): a function,
//! universe, path, list or float field has no structural equality the
//! program decides; a declaration with parameters or indices is no type
//! `Eq.generic` is applied to; a presented declaration is a quotient, which
//! structural equality does not respect; a field reading an earlier field, a
//! cycle through two declarations and a recursive occurrence under a product
//! or a sum each need a recursion the one structural fixpoint does not give.
//!
//! The equality's reflexivity and symmetry are [`law`]'s, the bodies of
//! `Eq.generic.refl(T)` and `Eq.generic.sym(T)`.

use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use alloc::vec::Vec;

use anodized::spec;
use gandr_kernel_term::BaseType;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::ConstructorTag;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::FieldCount;
use gandr_kernel_term::FieldPosition;
use gandr_kernel_term::FixpointEvidence;
use gandr_kernel_term::OccurrenceSite;
use gandr_kernel_term::Summand;
use quenchant_shape::shape::Maybe;

use crate::Binders;
use crate::CompTypeId;
use crate::ComponentCount;
use crate::ComputationId;
use crate::CoreArena;
use crate::DataSignature;
use crate::ValueId;
use crate::ValueType;
use crate::ValueTypeId;
use crate::Zone;
use crate::primitive::Arguments;
use crate::primitive::PRELUDE;
use crate::primitive::Primitive;
use crate::primitive::PrimitiveType;

/// Why no equality derives for a declaration.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: each alternative names the declaration it stopped at, and a
///   field's alternative the constructor and field.
/// - executable: none — the record is data a refusal renders.
///
/// # Adequacy
/// - hypothesis: L3 — a function field, a parameterised declaration, a
///   presented one, a dependent field, a cycle and a nested recursion each
///   refuse with their own alternative and site.
/// - witness: `generic::tests::each_uncovered_declaration_refuses_at_its_site`
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Uncovered
{
    /// The lookup answers no data signature at the position.
    Unknown(ConstantIndex),
    /// The declaration takes parameters or indices.
    Applied(ConstantIndex),
    /// The declaration's terms are presented by rules: a quotient.
    Presented(ConstantIndex),
    /// A field's type has no equality the program decides.
    Field(ConstantIndex, OccurrenceSite),
    /// A field's type reads a field before it.
    Dependent(ConstantIndex, OccurrenceSite),
    /// A field reaches a declaration whose equality is being derived through
    /// another.
    Cycle(ConstantIndex, OccurrenceSite),
    /// The declaration occurs in itself under a product or a sum.
    Nested(ConstantIndex, OccurrenceSite),
    /// A law over a field of a sum or a tuple: its proof cases or splits on
    /// the field under a motive reading the field, which core's `case` does
    /// not carry.
    DependentCase(ConstantIndex, OccurrenceSite),
    /// A law over a declaration that occurs in itself: its proof is an
    /// induction, a recursive proof the derivation does not write.
    Inductive(ConstantIndex, OccurrenceSite),
    /// A binder count passes the representable ceiling.
    BinderCeiling,
}

/// A derived declaration: an equality, or a law [`law::law`] proves of one.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Derived
{
    /// Its declared type: `U (T → T → F Bool)` for an equality, the law's
    /// path type for a law.
    declared: ValueTypeId,
    /// Its body, a thunk.
    body: ValueId,
    /// Each data case the body holds, with the declaration it eliminates.
    cases: Vec<(ComputationId, ConstantIndex)>,
}

impl Derived
{
    /// The declared type.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn declared(&self) -> ValueTypeId
    {
        self.declared
    }

    /// The body.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn body(&self) -> ValueId
    {
        self.body
    }

    /// Each data case the body holds, with the declaration whose
    /// constructors its branches are, in the order they were minted.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn cases(&self) -> &[(ComputationId, ConstantIndex)]
    {
        &self.cases
    }
}

/// The data signatures a derivation reads, by admission position.
pub type Signatures<'lookup> = dyn Fn(ConstantIndex) -> Option<&'lookup DataSignature> + 'lookup;

/// Derive the equality of the closed, free data declaration at `position`.
///
/// # Specification
/// - requires: `signatures` answers the signature the lowering mints for each
///   data declaration it reaches, `position` among them.
/// - ensures: the declared type `U (T → T → F Bool)` and the body the module
///   documentation states, minted into `arena`, each closed; its fixpoint
///   carries structural evidence.
/// - provides: the body of a definition written `Eq.generic(T)`. It is a
///   declaration like any other: the checker judges it, the kernel readmits it,
///   and both type its recursion by stages.
/// - fails: [`Uncovered`], naming what stopped the derivation.
/// - panics: none.
///
/// # Errors
/// As `- fails:`.
///
/// # Adequacy
/// - hypothesis: L3 — a two-integer point, a recursive natural and a
///   declaration whose field is another declaration derive closed equalities of
///   the stated type, and each uncovered shape refuses at its site. The
///   checker's admission of the result, and its decisions, are witnessed in
///   `gandr_core_checker`'s recursive-data tests.
/// - witness: `generic::tests::a_point_derives_a_closed_equality_of_two_points`
/// - witness: `generic::tests::a_recursive_declaration_derives_a_structural_fixpoint`
/// - witness: `generic::tests::a_declaration_s_field_of_another_derives_it_in_place`
/// - witness: `generic::tests::each_uncovered_declaration_refuses_at_its_site`
#[spec(ensures: |ret| ret.as_ref().is_err() || ret.as_ref().is_ok_and(|derived| arena.value_type(derived.declared).is_some() && arena.value(derived.body).is_some()))]
#[inline]
pub fn equality(
    arena: &mut CoreArena,
    position: ConstantIndex,
    signatures: &Signatures<'_>,
) -> Result<Derived, Uncovered>
{
    let (mut deriving, _order) = Deriving::start(arena, signatures, position)?;
    let body = deriving
        .derived
        .get(&position)
        .copied()
        .ok_or(Uncovered::Unknown(position))?;
    let declared = deriving.predicate(position);
    Ok(Derived {
        declared,
        body,
        cases: deriving.cases,
    })
}

/// One derivation's state: the arena it mints into, the signatures it reads,
/// and the declarations read and derived so far.
struct Deriving<'run, 'lookup>
{
    /// Where every node is minted.
    arena: &'run mut CoreArena,
    /// The signatures by position.
    signatures: &'run Signatures<'lookup>,
    /// Each reached declaration's fields, constructor by constructor, each
    /// read outside the fields before it.
    rows: BTreeMap<ConstantIndex, Vec<Vec<ValueTypeId>>>,
    /// Each declaration's derived equality, once derived.
    derived: BTreeMap<ConstantIndex, ValueId>,
    /// Each data case minted so far, with the declaration it eliminates.
    cases: Vec<(ComputationId, ConstantIndex)>,
    /// The declaration whose equality is being written.
    own: ConstantIndex,
    /// `Bool`.
    boolean: ValueTypeId,
    /// `F Bool`.
    answer: CompTypeId,
    /// `true`, the left injection of the unit.
    truth: ValueId,
    /// `false`, the right injection of the unit.
    falsity: ValueId,
    /// Integer equality, which the native table declares by the name a source
    /// calls it by, `int.eq`.
    integer: Option<Primitive>,
    /// String equality, which the native table declares.
    text: Option<Primitive>,
}

/// Whether a comparison stands directly at a field of the declaration's
/// constructor, where a recursive call descends.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Standing
{
    /// At a constructor's field.
    Field,
    /// Under a product or a sum inside one.
    Nested,
}

/// One comparison: where it stands, the type both sides have and the levels
/// of the two variables compared.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Comparison
{
    /// The constructor field it compares, or compares inside.
    site: OccurrenceSite,
    /// The type both sides inhabit, closed.
    ty: ValueTypeId,
    /// The left side's de Bruijn level.
    left: Binders,
    /// The right side's de Bruijn level.
    right: Binders,
}

/// One step of building a conjunction: comparisons to open, or a node to
/// assemble from the terms its children built, the first child's term
/// deepest on the stack of built terms.
#[derive(Clone, Debug)]
enum Step
{
    /// The sequential conjunction of `comparisons`, the first `depth` binders
    /// deep.
    All
    {
        /// The comparisons, in order.
        comparisons: Vec<Comparison>,
        /// The binders the first stands under.
        depth: Binders,
        /// Where each stands.
        standing: Standing,
    },
    /// One comparison, `depth` binders deep.
    Compare
    {
        /// The comparison.
        comparison: Comparison,
        /// The binders it stands under.
        depth: Binders,
        /// Where it stands.
        standing: Standing,
    },
    /// Conjoin the terms `comparisons` built, the first `depth` binders deep.
    Conjoin
    {
        /// The comparisons whose terms are conjoined.
        comparisons: Vec<Comparison>,
        /// The binders the first stands under.
        depth: Binders,
    },
    /// Split both sides of a product around the term its components built.
    Split
    {
        /// The left side.
        left: ValueId,
        /// The right side, read under the left side's components.
        right: ValueId,
        /// The product's width.
        arity: ComponentCount,
    },
    /// Case both sides of a sum around the terms its summands built.
    Sides
    {
        /// The left side.
        left: ValueId,
        /// The right side, read under the left side's payload.
        right: ValueId,
        /// The number of summands.
        summands: ComponentCount,
    },
}

/// `left + right` binders, refused past the ceiling.
///
/// # Specification
/// trivial.
fn plus(
    left: Binders,
    right: Binders,
) -> Result<Binders, Uncovered>
{
    u32::from(left)
        .checked_add(u32::from(right))
        .map(Binders::from)
        .ok_or(Uncovered::BinderCeiling)
}

/// The number of binders `items` opens, one per item, checked against the
/// ceiling.
///
/// # Specification
/// trivial.
fn count<T>(items: &[T]) -> Result<Binders, Uncovered>
{
    u32::try_from(items.len())
        .map(Binders::from)
        .map_err(|_cause| Uncovered::BinderCeiling)
}

impl<'run, 'lookup> Deriving<'run, 'lookup>
{
    /// The derivation of `position`'s equality over `signatures`, with every
    /// declaration it reaches derived, and the order they were derived in.
    ///
    /// # Specification
    /// - requires: as [`equality`].
    /// - ensures: each declaration in the order is derived after every one its
    ///   fields reach, `position` last.
    /// - fails: as [`equality`].
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`equality`].
    /// - witness: `generic::tests::a_declaration_s_field_of_another_derives_it_in_place`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |&(ref deriving, ref order)| order.iter().all(|at| deriving.derived.contains_key(at))))]
    fn start(
        arena: &'run mut CoreArena,
        signatures: &'run Signatures<'lookup>,
        position: ConstantIndex,
    ) -> Result<(Self, Vec<ConstantIndex>), Uncovered>
    {
        let named = |name| {
            PRELUDE
                .iter()
                .copied()
                .find(|primitive| primitive.name().as_ref() == name)
        };
        let boolean = PrimitiveType::Boolean.mint(arena);
        let answer = arena.comp_type_returner(boolean);
        let unit = arena.value_unit();
        let truth = arena.value_injection(Summand::from(0_usize), unit);
        let falsity = arena.value_injection(Summand::from(1_usize), unit);
        let mut deriving = Deriving {
            arena,
            signatures,
            rows: BTreeMap::new(),
            derived: BTreeMap::new(),
            cases: Vec::new(),
            own: position,
            boolean,
            answer,
            truth,
            falsity,
            integer: named("int.eq"),
            text: named("string.eq"),
        };
        // Each declaration a field reaches is derived before the declarations
        // reaching it, so its equality is written in place by the time it is
        // compared.
        let order = deriving.order(position)?;
        for &declaration in &order {
            let body = deriving.derive(declaration)?;
            let _first = deriving.derived.insert(declaration, body);
        }
        Ok((deriving, order))
    }
}

impl Deriving<'_, '_>
{
    /// The variable at de Bruijn `level`, read `depth` binders deep.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the intuitionistic variable `depth - 1 - level` when `level`
    ///   is below `depth`.
    /// - fails: [`Uncovered::BinderCeiling`] when `level` is not below `depth`,
    ///   which the derivation's own bookkeeping rules out.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a point's fields are read three and one binders out.
    /// - witness: `generic::tests::a_point_derives_a_closed_equality_of_two_points`
    #[spec(ensures: |ret| ret.is_ok() == (u32::from(level) < u32::from(depth)))]
    fn at(
        &mut self,
        depth: Binders,
        level: Binders,
    ) -> Result<ValueId, Uncovered>
    {
        let index = u32::from(depth)
            .checked_sub(u32::from(level))
            .and_then(|above| above.checked_sub(1))
            .ok_or(Uncovered::BinderCeiling)?;
        Ok(self
            .arena
            .value_variable(Zone::Intuitionistic, DeBruijnIndex::from(index)))
    }

    /// `return false`.
    ///
    /// # Specification
    /// trivial.
    fn refuted(&mut self) -> ComputationId
    {
        self.arena.computation_return(self.falsity)
    }

    /// `U (T → T → F Bool)` at the declaration at `position`.
    ///
    /// # Specification
    /// trivial.
    fn predicate(
        &mut self,
        position: ConstantIndex,
    ) -> ValueTypeId
    {
        let carrier = self.arena.value_type_data(position, Vec::new());
        let second = self.arena.comp_type_arrow(carrier, self.answer);
        let first = self.arena.comp_type_arrow(carrier, second);
        self.arena.value_type_thunk(first)
    }

    /// `body` under `binders` lambdas.
    ///
    /// # Specification
    /// trivial.
    fn abstracted(
        &mut self,
        mut body: ComputationId,
        binders: Binders,
    ) -> ComputationId
    {
        for _binder in 0 .. u32::from(binders) {
            body = self.arena.computation_lambda(body);
        }
        body
    }

    /// The comparisons of the components bound from level `lefts` and from
    /// level `rights`, each of its type in `types`, at `site`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: one comparison per type, in order, its sides `lefts + i` and
    ///   `rights + i`.
    /// - fails: [`Uncovered::BinderCeiling`] past the ceiling.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a point's two fields are compared in order, each
    ///   against its own counterpart.
    /// - witness: `generic::tests::a_point_derives_a_closed_equality_of_two_points`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |comparisons| comparisons.len() == types.len()))]
    fn pairwise(
        site: impl Fn(FieldPosition) -> OccurrenceSite,
        types: &[ValueTypeId],
        (lefts, rights): (Binders, Binders),
    ) -> Result<Vec<Comparison>, Uncovered>
    {
        let mut comparisons = Vec::with_capacity(types.len());
        let mut step = Binders::NONE;
        for (place, &ty) in types.iter().enumerate() {
            comparisons.push(Comparison {
                site: site(FieldPosition::from(place)),
                ty,
                left: plus(lefts, step)?,
                right: plus(rights, step)?,
            });
            step = plus(step, Binders::ONE)?;
        }
        Ok(comparisons)
    }

    /// Read the declaration at `position`: its fields, each strengthened past
    /// the fields before it.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: `position`'s fields filed by constructor, each closed.
    /// - fails: [`Uncovered::Unknown`] with no signature,
    ///   [`Uncovered::Applied`] with parameters or indices,
    ///   [`Uncovered::Presented`] with rules, and [`Uncovered::Dependent`] at
    ///   the first field reading one before it.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — each refusal names its declaration and field.
    /// - witness: `generic::tests::each_uncovered_declaration_refuses_at_its_site`
    #[spec(ensures: |ret| ret.is_err() || self.rows.contains_key(&position))]
    fn read(
        &mut self,
        position: ConstantIndex,
    ) -> Result<(), Uncovered>
    {
        let signature = (self.signatures)(position).ok_or(Uncovered::Unknown(position))?;
        if !signature.parameters().is_empty() || !signature.indices().is_empty() {
            return Err(Uncovered::Applied(position));
        }
        if !signature.presentation().rules().is_empty() {
            return Err(Uncovered::Presented(position));
        }
        let mut rows = Vec::with_capacity(signature.constructors().len());
        for (tag, row) in signature.constructors().iter().enumerate() {
            let mut read = Vec::with_capacity(row.len());
            let mut earlier = Binders::NONE;
            for (place, &field) in row.iter().enumerate() {
                let Maybe::Present(outside) =
                    crate::strengthen_value_type(self.arena, field, earlier)
                else {
                    return Err(Uncovered::Dependent(position, OccurrenceSite::Field {
                        tag: ConstructorTag::from(tag),
                        field: FieldPosition::from(place),
                    }));
                };
                read.push(outside.settle(self.arena));
                earlier = plus(earlier, Binders::ONE)?;
            }
            rows.push(read);
        }
        let _first = self.rows.insert(position, rows);
        Ok(())
    }

    /// The other declarations the fields of the declaration at `position`
    /// reach, directly or inside a product or a sum, with the field each is
    /// reached at, last field first.
    ///
    /// # Specification
    /// - requires: `position` is read.
    /// - ensures: every declaration of no arguments some field's type holds,
    ///   `position` itself excepted, once per occurrence.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a line's points are reached, and a cycle through two
    ///   declarations is.
    /// - witness: `generic::tests::a_declaration_s_field_of_another_derives_it_in_place`
    /// - witness: `generic::tests::each_uncovered_declaration_refuses_at_its_site`
    #[spec(ensures: |ret| ret.iter().all(|reached| reached.0 != position))]
    fn reached(
        &self,
        position: ConstantIndex,
    ) -> Vec<(ConstantIndex, OccurrenceSite)>
    {
        let mut reached = Vec::new();
        let mut pending: Vec<(ValueTypeId, OccurrenceSite)> = Vec::new();
        for (tag, row) in self.rows.get(&position).into_iter().flatten().enumerate() {
            for (place, &ty) in row.iter().enumerate() {
                pending.push((ty, OccurrenceSite::Field {
                    tag: ConstructorTag::from(tag),
                    field: FieldPosition::from(place),
                }));
            }
        }
        while let Some((ty, site)) = pending.pop() {
            match self.arena.value_type(ty) {
                Some(&ValueType::Data {
                    declaration,
                    ref arguments,
                }) if arguments.is_empty() && declaration != position => {
                    reached.push((declaration, site));
                },
                Some(&ValueType::Product(ref parts) | &ValueType::Sum(ref parts)) => {
                    pending.extend(parts.iter().map(|&part| (part, site)));
                },
                Some(_) | None => {},
            }
        }
        reached
    }

    /// Every declaration whose equality `position`'s needs, each after the
    /// declarations its own fields reach, `position` last.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: each reached declaration read and listed once, after every
    ///   declaration it reaches, `position` last.
    /// - fails: [`Uncovered::Cycle`] at the field of the declaration that
    ///   reaches one still open below it; what reading a declaration fails
    ///   with.
    /// - panics: none.
    ///
    /// # Termination
    /// - reason: a declaration is read and opened at most once, and each
    ///   iteration closes one or consumes one reached occurrence.
    /// - measure: the reached declarations' occurrences not yet consumed, then
    ///   the declarations not yet closed.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a line derives its point first; a cycle through two
    ///   declarations refuses at the second's field.
    /// - witness: `generic::tests::a_declaration_s_field_of_another_derives_it_in_place`
    /// - witness: `generic::tests::each_uncovered_declaration_refuses_at_its_site`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |order| order.last() == Some(&position)))]
    fn order(
        &mut self,
        position: ConstantIndex,
    ) -> Result<Vec<ConstantIndex>, Uncovered>
    {
        self.read(position)?;
        let mut open = Vec::from([(position, self.reached(position))]);
        let mut opened = BTreeSet::from([position]);
        let mut closed: BTreeSet<ConstantIndex> = BTreeSet::new();
        let mut order = Vec::new();
        while let Some(top) = open.last_mut() {
            let at = top.0;
            let Some((next, site)) = top.1.pop()
            else {
                let _done = open.pop();
                let _left = opened.remove(&at);
                let _first = closed.insert(at);
                order.push(at);
                continue;
            };
            if closed.contains(&next) {
                continue;
            }
            if opened.contains(&next) {
                return Err(Uncovered::Cycle(at, site));
            }
            self.read(next)?;
            let reached = self.reached(next);
            let _first = opened.insert(next);
            open.push((next, reached));
        }
        Ok(order)
    }

    /// The closed equality of the declaration at `position`, a thunk of its
    /// fixpoint.
    ///
    /// # Specification
    /// - requires: `position` is read, and every declaration it reaches is
    ///   derived.
    /// - ensures: the body [`equality`] states, closed.
    /// - fails: [`Uncovered`] at the first field it stops at.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`equality`].
    /// - witness: `generic::tests::a_point_derives_a_closed_equality_of_two_points`
    /// - witness: `generic::tests::a_recursive_declaration_derives_a_structural_fixpoint`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |&body| self.arena.value(body).is_some()))]
    fn derive(
        &mut self,
        position: ConstantIndex,
    ) -> Result<ValueId, Uncovered>
    {
        let rows = self
            .rows
            .get(&position)
            .cloned()
            .ok_or(Uncovered::Unknown(position))?;
        self.own = position;
        // Levels: `rec` 0, `a` 1, `b` 2, then the first argument's fields and
        // the second's.
        let first = Binders::ONE;
        let second = Binders::from(2_u32);
        let opened = Binders::from(3_u32);
        let arities: Vec<FieldCount> = rows.iter().map(|row| FieldCount::from(row.len())).collect();
        let mut outer = Vec::with_capacity(rows.len());
        for (tag, own) in rows.iter().enumerate() {
            let width = count(own)?;
            let rights = plus(opened, width)?;
            let depth = plus(rights, width)?;
            let mut inner = Vec::with_capacity(rows.len());
            for (other, across) in rows.iter().enumerate() {
                if other == tag {
                    let comparisons = Self::pairwise(
                        |field| OccurrenceSite::Field {
                            tag: ConstructorTag::from(tag),
                            field,
                        },
                        own,
                        (opened, rights),
                    )?;
                    let body = self.conjunction(comparisons, depth, Standing::Field)?;
                    inner.push(self.abstracted(body, width));
                }
                else {
                    let refused = self.refuted();
                    inner.push(self.abstracted(refused, count(across)?));
                }
            }
            let scrutinee = self.at(rights, second)?;
            let case =
                self.arena
                    .computation_data_case(scrutinee, self.answer, inner, arities.clone());
            self.cases.push((case, position));
            outer.push(self.abstracted(case, width));
        }
        let scrutinee = self.at(opened, first)?;
        let case = self
            .arena
            .computation_data_case(scrutinee, self.answer, outer, arities);
        self.cases.push((case, position));
        let over = self.abstracted(case, Binders::from(2_u32));
        let fixpoint = self
            .arena
            .computation_fixpoint(over, FixpointEvidence::StructuralDescent);
        Ok(self.arena.value_thunk(fixpoint))
    }

    /// The sequential conjunction of `comparisons`, the first read `depth`
    /// binders deep and each standing as `standing` says: `true` for none,
    /// the one comparison for one, and otherwise each bound and cased on in
    /// turn, a `false` ending the rest.
    ///
    /// # Specification
    /// - requires: every level in `comparisons` is below `depth`.
    /// - ensures: a computation of `F Bool` under `depth` binders.
    /// - fails: as [`Self::compare`].
    /// - panics: none.
    ///
    /// # Termination
    /// - reason: each step either builds a term or replaces itself with steps
    ///   over strictly smaller types — a comparison's components or summands —
    ///   and an assembling step that consumes their terms.
    /// - measure: the total size of the types still to compare.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a point's two fields conjoin and a constructor with
    ///   none answers true.
    /// - witness: `generic::tests::a_point_derives_a_closed_equality_of_two_points`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |&term| self.arena.computation(term).is_some()))]
    fn conjunction(
        &mut self,
        comparisons: Vec<Comparison>,
        depth: Binders,
        standing: Standing,
    ) -> Result<ComputationId, Uncovered>
    {
        let mut steps = Vec::from([Step::All {
            comparisons,
            depth,
            standing,
        }]);
        let mut built: Vec<ComputationId> = Vec::new();
        while let Some(step) = steps.pop() {
            match step {
                Step::All {
                    comparisons,
                    depth,
                    standing,
                } => {
                    if comparisons.is_empty() {
                        built.push(self.arena.computation_return(self.truth));
                        continue;
                    }
                    // The i-th comparison stands under the verdicts and units
                    // of the i before it: two binders each.
                    let mut opened = Vec::with_capacity(comparisons.len());
                    let mut at = depth;
                    for &comparison in &comparisons {
                        opened.push(Step::Compare {
                            comparison,
                            depth: at,
                            standing,
                        });
                        at = plus(at, Binders::from(2_u32))?;
                    }
                    steps.push(Step::Conjoin { comparisons, depth });
                    steps.extend(opened.into_iter().rev());
                },
                Step::Compare {
                    comparison,
                    depth,
                    standing,
                } => self.compare(comparison, depth, standing, (&mut steps, &mut built))?,
                Step::Conjoin { comparisons, depth } => {
                    let start = built
                        .len()
                        .checked_sub(comparisons.len())
                        .ok_or(Uncovered::BinderCeiling)?;
                    let terms = built.split_off(start);
                    let conjoined = self.conjoin(&comparisons, &terms, depth)?;
                    built.push(conjoined);
                },
                Step::Split { left, right, arity } => {
                    let body = built.pop().ok_or(Uncovered::BinderCeiling)?;
                    let split_right = self.arena.computation_split(right, arity, body);
                    built.push(self.arena.computation_split(left, arity, split_right));
                },
                Step::Sides {
                    left,
                    right,
                    summands,
                } => {
                    let start = built
                        .len()
                        .checked_sub(usize::from(summands))
                        .ok_or(Uncovered::BinderCeiling)?;
                    let compared = built.split_off(start);
                    let sided = self.sides(left, right, &compared);
                    built.push(sided);
                },
            }
        }
        built.pop().ok_or(Uncovered::BinderCeiling)
    }

    /// `terms`, the terms of `comparisons` in order, conjoined: each but the
    /// last bound, cased on and continued by the rest, the first `depth`
    /// binders deep.
    ///
    /// # Specification
    /// - requires: one term per comparison, the i-th built `depth + 2i` binders
    ///   deep; at least one.
    /// - ensures: `r ← t_1; case r { _ ↦ … ; _ ↦ return false }`, the verdict
    ///   bound at level `depth + 2i` and each branch binding the unit it
    ///   carries; the last term itself.
    /// - fails: [`Uncovered::BinderCeiling`] for no terms or past the ceiling.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a point's two fields conjoin by one bind, its second
    ///   field's comparison in the true branch.
    /// - witness: `generic::tests::a_point_derives_a_closed_equality_of_two_points`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |&term| self.arena.computation(term).is_some()))]
    fn conjoin(
        &mut self,
        comparisons: &[Comparison],
        terms: &[ComputationId],
        depth: Binders,
    ) -> Result<ComputationId, Uncovered>
    {
        let Some((&last, rest)) = terms.split_last()
        else {
            return Err(Uncovered::BinderCeiling);
        };
        let mut continued = last;
        for (place, (&term, comparison)) in rest.iter().zip(comparisons).enumerate().rev() {
            let twice = u32::try_from(place)
                .ok()
                .and_then(|place| place.checked_mul(2))
                .ok_or(Uncovered::BinderCeiling)?;
            let at = plus(depth, Binders::from(twice))?;
            let bound = plus(at, Binders::ONE)?;
            let ended = self.refuted();
            let verdict = self.at(bound, at)?;
            let case = self.arena.computation_case(verdict, &[continued, ended]);
            let compared = self.bindable(term, comparison.ty);
            continued = self.arena.computation_bind(compared, case);
        }
        Ok(continued)
    }

    /// `compared`, the comparison of two values of `ty`, as the head of a
    /// bind: a case or a split synthesises no type, so one over a sum or a
    /// product is thunked, ascribed `U (F Bool)` and forced.
    ///
    /// # Specification
    /// - requires: `compared` is a computation of `F Bool`.
    /// - ensures: `compared` itself for a type of any other former; else `force
    ///   (thunk compared : U (F Bool))`, which synthesises `F Bool`.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a line's flag and pair, compared before later fields,
    ///   are each thunked, ascribed and forced.
    /// - witness: `generic::tests::a_declaration_s_field_of_another_derives_it_in_place`
    #[spec(ensures: |ret| self.arena.computation(ret).is_some())]
    fn bindable(
        &mut self,
        compared: ComputationId,
        ty: ValueTypeId,
    ) -> ComputationId
    {
        if !matches!(
            self.arena.value_type(ty),
            Some(&(ValueType::Sum(_) | ValueType::Product(_)))
        ) {
            return compared;
        }
        let thunk = self.arena.value_thunk(compared);
        let verdict = self.arena.value_type_thunk(self.answer);
        let ascribed = self.arena.value_ascribe(thunk, verdict);
        self.arena.computation_force(ascribed)
    }

    /// `case a { inj_k u ↦ case b { inj_k v ↦ u ≐ v ; _ ↦ false } }` over
    /// `left` and `right`, `compared` the k-th summand's `u ≐ v` in order.
    ///
    /// # Specification
    /// - requires: `compared` holds one term per summand.
    /// - ensures: a case on `left` with one branch per summand, each a case on
    ///   `right` whose matching branch is that summand's term and every other
    ///   `return false`.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a line's flag is compared by its injections.
    /// - witness: `generic::tests::a_declaration_s_field_of_another_derives_it_in_place`
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            allocation_in_repeated_body,
            reason = "each summand's case owns its branch table, which the arena keeps"
        )
    )]
    #[spec(ensures: |ret| self.arena.computation(ret).is_some())]
    fn sides(
        &mut self,
        left: ValueId,
        right: ValueId,
        compared: &[ComputationId],
    ) -> ComputationId
    {
        let mut sides = Vec::with_capacity(compared.len());
        for (place, &term) in compared.iter().enumerate() {
            let mut matched = Vec::with_capacity(compared.len());
            for other in 0 .. compared.len() {
                matched.push(if other == place { term } else { self.refuted() });
            }
            sides.push(self.arena.computation_case(right, &matched));
        }
        self.arena.computation_case(left, &sides)
    }

    /// Open `comparison`, read `depth` binders deep and standing as
    /// `standing` says, in the declaration being derived: build its term onto
    /// `built`, or push the steps that build it onto `steps`.
    ///
    /// # Specification
    /// - requires: `comparison`'s levels are below `depth`, its type closed,
    ///   and every other declaration it reaches derived.
    /// - ensures: a computation of `F Bool` under `depth` binders, by the
    ///   type's former as the module documentation states, or the steps that
    ///   build it.
    /// - fails: [`Uncovered::Field`] for a type with no equality,
    ///   [`Uncovered::Nested`] for a recursive occurrence under a product or a
    ///   sum, [`Uncovered::Cycle`] for a declaration not yet derived.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — integers, booleans, a recursive field, another
    ///   declaration's field, and a function field each take their own way.
    /// - witness: `generic::tests::a_point_derives_a_closed_equality_of_two_points`
    /// - witness: `generic::tests::a_declaration_s_field_of_another_derives_it_in_place`
    /// - witness: `generic::tests::each_uncovered_declaration_refuses_at_its_site`
    #[spec(
        captures: [ready = built.len(), pending = steps.len()],
        ensures: |ret| ret.is_err() || built.len() == ready.saturating_add(1) || steps.len() > pending,
    )]
    fn compare(
        &mut self,
        comparison: Comparison,
        depth: Binders,
        standing: Standing,
        (steps, built): (&mut Vec<Step>, &mut Vec<ComputationId>),
    ) -> Result<(), Uncovered>
    {
        let own = self.own;
        let site = comparison.site;
        let uncovered = Uncovered::Field(own, site);
        let left = self.at(depth, comparison.left)?;
        match self.arena.value_type(comparison.ty) {
            Some(&ValueType::Base(BaseType::Integer)) => {
                let primitive = self.integer.ok_or(uncovered)?;
                let right = self.at(depth, comparison.right)?;
                built.push(
                    self.arena
                        .computation_primitive(primitive, Arguments::Binary([left, right])),
                );
            },
            Some(&ValueType::Base(BaseType::String)) => {
                let primitive = self.text.ok_or(uncovered)?;
                let right = self.at(depth, comparison.right)?;
                built.push(
                    self.arena
                        .computation_primitive(primitive, Arguments::Binary([left, right])),
                );
            },
            Some(&ValueType::Data {
                declaration,
                ref arguments,
            }) if arguments.is_empty() => {
                let head = if declaration == own {
                    if standing == Standing::Nested {
                        return Err(Uncovered::Nested(own, site));
                    }
                    let recursive = self.at(depth, Binders::NONE)?;
                    self.arena.computation_force(recursive)
                }
                else {
                    // A thunk synthesises nothing; ascribed, it is forced.
                    let derived = self
                        .derived
                        .get(&declaration)
                        .copied()
                        .ok_or(Uncovered::Cycle(own, site))?;
                    let ty = self.predicate(declaration);
                    let ascribed = self.arena.value_ascribe(derived, ty);
                    self.arena.computation_force(ascribed)
                };
                let right = self.at(depth, comparison.right)?;
                let applied = self.arena.computation_application(head, left);
                built.push(self.arena.computation_application(applied, right));
            },
            Some(&ValueType::Product(ref components)) if components.is_empty() => {
                built.push(self.arena.computation_return(self.truth));
            },
            Some(&ValueType::Product(ref components)) => {
                // `split a as x̄ in split b as ȳ in x_1 ≐ y_1 ∧ …`.
                let components: Vec<ValueTypeId> = components.to_vec();
                let width = count(&components)?;
                let rights = plus(depth, width)?;
                let inside = plus(rights, width)?;
                let comparisons = Self::pairwise(|_place| site, &components, (depth, rights))?;
                let right = self.at(rights, comparison.right)?;
                steps.push(Step::Split {
                    left,
                    right,
                    arity: ComponentCount::from(components.len()),
                });
                steps.push(Step::All {
                    comparisons,
                    depth: inside,
                    standing: Standing::Nested,
                });
            },
            Some(&ValueType::Sum(ref summands)) => {
                // Each summand's payloads are bound at `depth` and `depth +
                // 1`, its comparison two binders deeper.
                let summands: Vec<ValueTypeId> = summands.to_vec();
                let payload = depth;
                let inside = plus(depth, Binders::ONE)?;
                let compared = plus(inside, Binders::ONE)?;
                let right = self.at(inside, comparison.right)?;
                steps.push(Step::Sides {
                    left,
                    right,
                    summands: ComponentCount::from(summands.len()),
                });
                steps.extend(summands.iter().rev().map(|&ty| Step::Compare {
                    comparison: Comparison {
                        site,
                        ty,
                        left: payload,
                        right: inside,
                    },
                    depth: compared,
                    standing: Standing::Nested,
                }));
            },
            Some(_) | None => return Err(uncovered),
        }
        Ok(())
    }
}

pub mod law;

#[cfg(test)]
mod tests;
