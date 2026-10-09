//! The tagged description table: [`SignDesc`] is the declaration table.
//!
//! A [`SignDesc`] bundles the minted [`NominalId`], the declared [`SortDesc`]
//! sort set (the description universe's index), the graded and attributed
//! [`ParamDesc`]s and [`CtorDesc`]s (the σ tag over constructors, each with a
//! first-order [`Code`] and a result sort), the reserved [`OperDesc`]
//! operations, the [`RuleFace`] 2-cells and the [`CircuitRule`] members, and
//! the [`DeclPolarity`]. Every extension point a declaration table needs —
//! sorts, grades, attributes, operations and faces — is a field here, so
//! adding one never retrofits the table.

use alloc::boxed::Box;
use alloc::format;
use alloc::vec;
use alloc::vec::Vec;

use anodized::spec;

use crate::arity::BridgeArity;
use crate::arity::SortRef;
use crate::boundary::NominalSerial;
use crate::boundary::RecursiveStatus;
use crate::boundary::SurfaceByteOffset;
use crate::circuit::CircuitRule;
use crate::code::Attrs;
use crate::code::Code;
use crate::code::CodeNode;
use crate::code::CodeView;
use crate::code::Name;
use crate::rule::RuleFace;

/// The minted 0-cell identity of a datatype; content addressing keys on it.
///
/// It carries a per-elaboration serial, assigned in declaration order, and
/// the datatype's name, so the identity is both distinct and
/// self-describing. Equality reads both, so two descriptions are equal only
/// when they name the same minted datatype.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct NominalId
{
    /// The monotone serial assigned in declaration order within one
    /// elaboration.
    pub serial: NominalSerial,
    /// The datatype's declared name.
    pub name: Name,
}

impl NominalId
{
    /// Mint an identity with the given serial and name.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn new<N>(
        serial: NominalSerial,
        name: N,
    ) -> Self
    where
        N: Into<Name>,
    {
        Self {
            serial,
            name: name.into(),
        }
    }
}

/// A surface span `[start, end)` in source bytes: provenance for a
/// description element.
#[derive(Clone, Copy, Debug, Default, Eq, Hash, PartialEq)]
pub struct SurfaceSpan
{
    /// The start byte, inclusive.
    pub start: SurfaceByteOffset,
    /// The end byte, exclusive.
    pub end: SurfaceByteOffset,
}

impl SurfaceSpan
{
    /// A span over the half-open byte range `[start, end)`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn new(
        start: SurfaceByteOffset,
        end: SurfaceByteOffset,
    ) -> Self
    {
        Self { start, end }
    }
}

/// The polarity of a declared sort or degenerate block: which fixpoint the
/// declaration names.
///
/// Two independent statements, deliberately not fused.
///
/// * **Which fixpoint decodes it.** [`DeclPolarity::Data`] is μ-decoded:
///   constructors are producers, eliminated by patterns.
///   [`DeclPolarity::Codata`] is ν-decoded: members read as observations,
///   introduced by copatterns. Both decoders read one code grammar.
/// * **Where the decoded type lands.** In a call-by-push-value core the μ
///   decoder targets the positive value universe and the ν decoder the negative
///   computation universe. That placement is a design choice correlated with
///   the fixpoint, not entailed by it: calculi exist that carry both fixpoints
///   in one universe, so universe placement is never read off the flag, nor the
///   flag off placement.
///
/// The flag only names the fixpoint. The polarity-specific obligations —
/// positivity for μ-sorts, productivity for ν-sorts — are discharged by the
/// sorting discipline over the declared sort set ([`check_desc`]), never by
/// the tag itself.
///
/// [`check_desc`]: crate::check_desc
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum DeclPolarity
{
    /// `data`: the μ fixpoint.
    Data,
    /// `codata`: the ν fixpoint.
    Codata,
}

/// A declared sort of a signature (a 0-cell), with the fixpoint its
/// declaration names.
///
/// The sort set is the index of the description universe: a multi-sorted
/// signature is one description over a sort set, each constructor targeting a
/// sort through [`CtorDesc::result`] and each recursive occurrence naming its
/// sort at [`Code::var`]. A degenerate `data` or `codata` block declares
/// exactly one sort, named by the block. The index is genuine: a sort is never
/// itself a description, and only finitely many declarations are importable,
/// which is what keeps code equality decidable.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct SortDesc
{
    /// The sort's name.
    pub name: Name,
    /// The fixpoint the sort's declaration names.
    pub polarity: DeclPolarity,
    /// The sort's index telescope, empty for an unindexed sort.
    ///
    /// `sort Hom(dom : Ob, cod : Ob) : Type` declares a sort family, and a
    /// description with nowhere to put `dom` and `cod` describes a different
    /// theory, one whose homs are not indexed by their endpoints. Nothing
    /// downstream can recover the indices, because the surface member is the
    /// only place they are written. The telescope is also the first clause of
    /// the theory's model: `sort X(Δ)` becomes `type X : Δ → Type`, and `Δ` is
    /// exactly this.
    pub indices: Box<[SortIndex]>,
}

impl SortDesc
{
    /// A sort of the given name and polarity, with no indices.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn new<N>(
        name: N,
        polarity: DeclPolarity,
    ) -> Self
    where
        N: Into<Name>,
    {
        Self {
            name: name.into(),
            polarity,
            indices: Box::default(),
        }
    }

    /// A sort family of the given name, polarity and index telescope.
    ///
    /// # Specification
    /// - requires: each index's sort is declared by the same signature, and the
    ///   indices are in declaration order.
    /// - ensures: polarity is retained and the telescope is carried verbatim;
    ///   nothing derives or defaults it, because an index the surface wrote and
    ///   the description dropped is a claim about a theory not presented.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — homogeneous and contrasting sort families are
    ///   observed through checker acceptance and typed polarity diagnostics,
    ///   rejecting a flipped tag. Index order and membership remain a boundary:
    ///   the generic consuming conversion provides no pre-conversion borrowed
    ///   telescope.
    /// - witness: `wellformed::tests::the_sorting_discipline_indexes_the_description`
    #[spec(ensures: |ref family| family.polarity == polarity)]
    #[inline]
    #[must_use]
    pub fn family<N, I>(
        name: N,
        polarity: DeclPolarity,
        indices: I,
    ) -> Self
    where
        N: Into<Name>,
        I: Into<Box<[SortIndex]>>,
    {
        Self {
            name: name.into(),
            polarity,
            indices: indices.into(),
        }
    }
}

/// One binder of a sort's index telescope: `dom : Ob` in
/// `sort Hom(dom : Ob, cod : Ob)`.
///
/// An index ranges over a sort, never over a type: the description universe
/// is indexed by the signature's sort set, and admitting an arbitrary type
/// would let a description mention something its signature does not declare.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct SortIndex
{
    /// The binder's name, in scope in the indices that follow it.
    pub name: Name,
    /// The sort it ranges over, which the same signature declares.
    pub sort: Name,
}

impl SortIndex
{
    /// An index binder of the given name, ranging over `sort`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn new<N, S>(
        name: N,
        sort: S,
    ) -> Self
    where
        N: Into<Name>,
        S: Into<Name>,
    {
        Self {
            name: name.into(),
            sort: sort.into(),
        }
    }
}

/// A datatype parameter with its grade and attribute Σ.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct ParamDesc<G>
{
    /// The parameter's name (`a` in `Maybe(a)`).
    pub name: Name,
    /// The parameter's grade, the consumer's; erased by value decoding.
    pub grade: G,
    /// The parameter's attribute Σ.
    pub attrs: Attrs,
}

impl<G> ParamDesc<G>
{
    /// A parameter with the given name, grade and attribute Σ.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn new<N>(
        name: N,
        grade: G,
        attrs: Attrs,
    ) -> Self
    where
        N: Into<Name>,
    {
        Self {
            name: name.into(),
            grade,
            attrs,
        }
    }
}

/// A constructor (a 1-cell): its name, payload [`Code`], result sort and
/// attribute Σ.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct CtorDesc<G>
{
    /// The constructor's name.
    pub name: Name,
    /// The constructor's payload code: `1` when nullary, a right-nested
    /// product of field codes otherwise.
    pub code: Code<G>,
    /// The constructor's result sort, the declared sort it targets.
    ///
    /// In a degenerate single-sort block this is the block's own sort; a
    /// sign-block `data` member writes it as its output port's sort; a
    /// generalized constructor result names the annotation's head.
    /// Membership in the declared sort set is checked by [`check_desc`].
    ///
    /// [`check_desc`]: crate::check_desc
    pub result: Name,
    /// The constructor's attribute Σ.
    pub attrs: Attrs,
}

impl<G> CtorDesc<G>
{
    /// A constructor with the given name, payload code, result sort and
    /// attribute Σ.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn new<N, R>(
        name: N,
        code: Code<G>,
        result: R,
        attrs: Attrs,
    ) -> Self
    where
        N: Into<Name>,
        R: Into<Name>,
    {
        Self {
            name: name.into(),
            code,
            result: result.into(),
            attrs,
        }
    }

    /// The constructor read as a single-output operation over the sort set:
    /// the container view under which the constructor layer and
    /// [`BridgeArity`] carry one shape.
    ///
    /// The payload code denotes a polynomial over sorts and symbolic types:
    /// products multiply factors into a monomial, inline sums contribute one
    /// monomial per summand, an atom-abstraction contributes its body's
    /// factors, and every leaf becomes one input port — a [`Code::var`] at its
    /// sort, a [`Code::field`] at its symbolic type's head, a [`Code::unit`]
    /// contributing no port. Every monomial feeds the one output port, which
    /// reads at the result sort.
    ///
    /// # Specification
    /// - ensures: the returned arity composes — every `source` index lies in
    ///   `inputs`, every `dest` index is `0`, one factor count per monomial;
    ///   input ports are positionally named `x0, x1, …` in leaf order, and the
    ///   output port is `result` at the result sort.
    /// - panics: none.
    /// - intension: the monomials are computed by an explicit worklist; a walk
    ///   frame pushes a former's sub-codes, a finish frame combines the operand
    ///   stack's top two monomial sets — cross-concatenation for a product,
    ///   union for an inline sum.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — unit, product, sum and abstraction payloads are
    ///   observed through exact ports and maps, including a product of sums; a
    ///   missing nullary monomial, swapped factors, omitted Cartesian pairs or
    ///   leaking a binder changes those records.
    /// - witness: `wellformed::tests::the_constructor_layer_agrees_with_the_bridge_shape`
    /// - witness: `desc::tests::constructor_arities_distribute_products_over_sums_and_erase_binders`
    #[inline]
    #[must_use]
    #[spec(ensures: |ref arity| arity.outputs.len() == 1
        && arity.outputs.first().is_some_and(|port| port.name.as_ref() == "result" && port.sort == self.result)
        && arity.factors.len() == arity.dest.len()
        && arity.dest.iter().all(|dest| *dest == 0)
        && arity.source.iter().enumerate().all(|(index, source)| usize::try_from(*source) == Ok(index))
        && arity.source.len() == arity.inputs.len()
        && arity.factors.iter().fold(0_u64, |total, count| total.saturating_add(u64::from(*count)))
            == u64::try_from(arity.source.len()).unwrap_or(u64::MAX))]
    pub fn arity(&self) -> BridgeArity
    {
        /// One step of the monomial worklist.
        enum MonomialFrame<'code, G>
        {
            /// Read a sub-code's monomials onto the operand stack.
            Walk(CodeNode<'code, G>),
            /// Multiply the top two operands.
            FinishProd,
            /// Add the top two operands.
            FinishSum,
        }

        let mut stack = vec![MonomialFrame::Walk(self.code.to_node())];
        let mut operands: Vec<Vec<Vec<Name>>> = Vec::new();
        while let Some(frame) = stack.pop() {
            match frame {
                | MonomialFrame::Walk(node) => match node.view() {
                    | CodeView::Unit => operands.push(vec![Vec::new()]),
                    | CodeView::Var(sort) => operands.push(vec![vec![sort.clone()]]),
                    | CodeView::Field { ty, .. } => operands.push(vec![vec![ty.head_name()]]),
                    | CodeView::Prod(factors) => {
                        stack.push(MonomialFrame::FinishProd);
                        let factors: Vec<CodeNode<'_, G>> = factors.collect();
                        stack.extend(factors.into_iter().rev().map(MonomialFrame::Walk));
                    },
                    | CodeView::Sum(summands) => {
                        stack.push(MonomialFrame::FinishSum);
                        let summands: Vec<CodeNode<'_, G>> = summands.collect();
                        stack.extend(summands.into_iter().rev().map(MonomialFrame::Walk));
                    },
                    | CodeView::Bind { body, .. } => {
                        stack.extend(body.map(MonomialFrame::Walk));
                    },
                },
                | MonomialFrame::FinishProd => {
                    let rights = operands.pop().unwrap_or_default();
                    let lefts = operands.pop().unwrap_or_default();
                    let combined = lefts
                        .into_iter()
                        .flat_map(|left_monomial| {
                            rights.iter().map(move |right_monomial| {
                                let mut joined = left_monomial.clone();
                                joined.extend(right_monomial.iter().cloned());
                                joined
                            })
                        })
                        .collect();
                    operands.push(combined);
                },
                | MonomialFrame::FinishSum => {
                    let rights = operands.pop().unwrap_or_default();
                    let mut lefts = operands.pop().unwrap_or_default();
                    lefts.extend(rights);
                    operands.push(lefts);
                },
            }
        }

        let monomials = operands.pop().unwrap_or_default();
        let mut inputs = Vec::new();
        let mut factors = Vec::new();
        let mut source = Vec::new();
        for monomial in &monomials {
            factors.push(u32::try_from(monomial.len()).unwrap_or(u32::MAX));
            for sort in monomial {
                let index = u32::try_from(inputs.len()).unwrap_or(u32::MAX);
                inputs.push(SortRef::new(format!("x{}", inputs.len()), sort.clone()));
                source.push(index);
            }
        }
        let dest = vec![0_u32; monomials.len()];
        BridgeArity::new(inputs, factors, source, dest, [SortRef::new(
            "result",
            self.result.clone(),
        )])
    }
}

/// A reserved operation member (`op f(…) -> R`): its name, multi-output
/// [`BridgeArity`] and attribute Σ.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct OperDesc
{
    /// The operation's name.
    pub name: Name,
    /// The operation's multi-output arity.
    pub arity: BridgeArity,
    /// The operation's attribute Σ.
    pub attrs: Attrs,
}

impl OperDesc
{
    /// An operation with the given name, arity and attribute Σ.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn new<N>(
        name: N,
        arity: BridgeArity,
        attrs: Attrs,
    ) -> Self
    where
        N: Into<Name>,
    {
        Self {
            name: name.into(),
            arity,
            attrs,
        }
    }
}

/// The tagged description: the declaration table for one signature.
///
/// `id` keys content addressing; `sorts` is the declared sort set, one entry
/// per declared sort; `params` are the graded and attributed parameters;
/// `ctors` are the constructors, the σ tag, each with a first-order [`Code`]
/// and a result sort; `opers` and `rules` are the reserved operations and
/// 2-cell faces; `circuits` are the 2-cell members whose boundaries are
/// derived from a wiring; `polarity` selects the μ or ν decoder; `attrs` is
/// the datatype's own attribute Σ. There is no parallel structure: the
/// description is the declaration table. `G` is the grade parameters and
/// fields carry, the consumer's own.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct SignDesc<G>
{
    /// The minted 0-cell identity.
    pub id: NominalId,
    /// The declared sort set, the description universe's index. A degenerate
    /// `data` or `codata` block declares exactly one sort, named by the block;
    /// a sign block declares its `sort` members.
    pub sorts: Box<[SortDesc]>,
    /// The datatype parameters, each graded and attributed.
    pub params: Box<[ParamDesc<G>]>,
    /// The constructors: the σ tag over the code grammar, the 1-cells.
    pub ctors: Box<[CtorDesc<G>]>,
    /// The reserved operations.
    pub opers: Box<[OperDesc]>,
    /// The reserved 2-cell rule faces.
    pub rules: Box<[RuleFace]>,
    /// The circuit rule members: a declared sphere with the wiring that must
    /// derive it. The declaration table checks the derived pair against the
    /// declared sphere ([`check_desc`]).
    ///
    /// [`check_desc`]: crate::check_desc
    pub circuits: Box<[CircuitRule]>,
    /// The declaration's polarity, `Data` (μ) or `Codata` (ν).
    ///
    /// The whole-declaration tag of the polarity-homogeneous reading: every
    /// entry of `sorts` agrees with it, which [`check_desc`] enforces. Sorts
    /// of differing polarity in one signature are the growth the per-sort
    /// tags carry; polarity alternation within one sort is a separate
    /// universe change, not taken.
    ///
    /// [`check_desc`]: crate::check_desc
    pub polarity: DeclPolarity,
    /// The datatype's own attribute Σ.
    pub attrs: Attrs,
}

impl<G> SignDesc<G>
{
    /// A description from its minted id, parts and polarity.
    ///
    /// The sort set defaults to the degenerate single sort: one entry named by
    /// the declaration, at the declaration's polarity, the `data` and `codata`
    /// blocks' reading. A multi-sorted sign block replaces it through
    /// [`Self::with_sorts`]. The constructor checks nothing: an ill-formed
    /// description is representable so [`check_desc`](crate::check_desc) can
    /// decline it with a diagnostic, and a caller needing the guarantee runs
    /// [`check_desc`](crate::check_desc).
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn new<Pa, Ct, Op, Ru>(
        id: NominalId,
        params: Pa,
        ctors: Ct,
        opers: Op,
        rules: Ru,
        polarity: DeclPolarity,
        attrs: Attrs,
    ) -> Self
    where
        Pa: Into<Box<[ParamDesc<G>]>>,
        Ct: Into<Box<[CtorDesc<G>]>>,
        Op: Into<Box<[OperDesc]>>,
        Ru: Into<Box<[RuleFace]>>,
    {
        let sorts = Box::from([SortDesc::new(id.name.clone(), polarity)]);
        Self {
            id,
            sorts,
            params: params.into(),
            ctors: ctors.into(),
            opers: opers.into(),
            rules: rules.into(),
            circuits: Box::default(),
            polarity,
            attrs,
        }
    }

    /// The same description carrying `sorts` as its declared sort set.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn with_sorts<So>(
        self,
        sorts: So,
    ) -> Self
    where
        So: Into<Box<[SortDesc]>>,
    {
        Self {
            sorts: sorts.into(),
            ..self
        }
    }

    /// The same description carrying `circuits` as its circuit rule members.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn with_circuits<Ci>(
        self,
        circuits: Ci,
    ) -> Self
    where
        Ci: Into<Box<[CircuitRule]>>,
    {
        Self {
            circuits: circuits.into(),
            ..self
        }
    }

    /// Whether any constructor's payload is recursive.
    ///
    /// # Specification
    /// - ensures: positive exactly when some constructor's code contains a
    ///   [`Code::var`].
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — empty and non-recursive tables, and a recursive
    ///   constructor first or last, distinguish a missed endpoint, inverted
    ///   answer and requiring every constructor rather than any constructor.
    /// - witness: `builtin::tests::list_is_recursive`
    /// - witness: `desc::tests::description_recursion_scans_both_constructor_boundaries`
    #[inline]
    #[must_use]
    #[spec(ensures: |recursive| bool::from(recursive)
        == self.ctors.iter().any(|ctor| ctor.code.recursive_sorts().next().is_some()))]
    pub fn is_recursive(&self) -> RecursiveStatus
    {
        RecursiveStatus::from(
            self.ctors
                .iter()
                .any(|ctor| bool::from(ctor.code.is_recursive())),
        )
    }
}

#[cfg(test)]
mod tests
{
    use super::*;
    use crate::builtin::bool_desc;
    use crate::code::AtomSort;
    use crate::test_support::Grade;

    #[test]
    fn constructor_arities_distribute_products_over_sums_and_erase_binders()
    {
        let nullary = CtorDesc::<Grade>::new("Zero", Code::unit(), "Result", Attrs::empty());
        assert_eq!(
            nullary.arity(),
            BridgeArity::new([], [0], [], [0], [SortRef::new("result", "Result")])
        );
        let payload = Code::bind(
            AtomSort::named("a"),
            Code::prod(
                Code::sum(Code::unit(), Code::var("A")),
                Code::sum(Code::var("B"), Code::var("C")),
            ),
        );
        let ctor = CtorDesc::<Grade>::new("Branches", payload, "Result", Attrs::empty());
        assert_eq!(
            ctor.arity(),
            BridgeArity::new(
                [
                    SortRef::new("x0", "B"),
                    SortRef::new("x1", "C"),
                    SortRef::new("x2", "A"),
                    SortRef::new("x3", "B"),
                    SortRef::new("x4", "A"),
                    SortRef::new("x5", "C")
                ],
                [1, 1, 2, 2],
                [0, 1, 2, 3, 4, 5],
                [0, 0, 0, 0],
                [SortRef::new("result", "Result")],
            )
        );
    }

    #[test]
    fn description_recursion_scans_both_constructor_boundaries()
    {
        let mut desc = bool_desc::<Grade>();
        assert!(!bool::from(desc.is_recursive()));
        desc.ctors = Box::default();
        assert!(!bool::from(desc.is_recursive()));
        let leaf = CtorDesc::new("Leaf", Code::unit(), "Boolean", Attrs::empty());
        let recursive = CtorDesc::new("Rec", Code::var("Boolean"), "Boolean", Attrs::empty());
        desc.ctors = Box::from([leaf.clone(), recursive.clone()]);
        assert!(bool::from(desc.is_recursive()));
        desc.ctors = Box::from([recursive, leaf]);
        assert!(bool::from(desc.is_recursive()));
    }
}
