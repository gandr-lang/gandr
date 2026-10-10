//! Multi-output arities: the bridge diagram `A ←s— J —π→ I —t→ B`.
//!
//! A multi-output operation `(X_a)_{a∈A} ↦ (Y_b)_{b∈B}` with
//! `Y_b = Σ_{i∈I_b} Π_{j∈J_i} X_{s(j)}` is presented by four finite sets and
//! three maps, computed as `Σ_t ∘ Π_π ∘ Δ_s`. The encoding separates the
//! product layer — one operation's named result tuple — from the sum layer —
//! destination aggregation, which independently requires a commutative
//! monoid. It is finite sets and maps, so it stays content-addressable and
//! first-order.

use alloc::boxed::Box;

use anodized::spec;

use crate::boundary::MonomialCount;
use crate::code::Name;
use crate::desc::SortIndex;
use crate::rule::FreeTerm;

/// A named port of an operation's input (`A`) or output (`B`) tuple.
///
/// The port's sort stays symbolic, by name, like the rest of the description
/// surface.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct SortRef
{
    /// The port's name (`q`, `r` in `-> (q: …, r: …)`).
    pub name: Name,
    /// The port's symbolic sort spelling.
    pub sort: Name,
    /// Arguments of the sort family, in telescope order.
    pub arguments: Box<[FreeTerm]>,
    /// Restricted π⁺ domains, outermost first; empty for a first-order port.
    /// Each domain must name a representable sort. This is not atom
    /// abstraction.
    pub bindings: Box<[SortIndex]>,
}

impl SortRef
{
    /// A port of the given name and symbolic sort.
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
            arguments: Box::default(),
            bindings: Box::default(),
        }
    }
    /// Apply this port's sort family to index terms.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn applied<I>(
        self,
        arguments: I,
    ) -> Self
    where
        I: Into<Box<[FreeTerm]>>,
    {
        Self {
            arguments: arguments.into(),
            ..self
        }
    }

    /// Bind representable variables over this port, outermost first.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn pi_plus<I>(
        self,
        bindings: I,
    ) -> Self
    where
        I: Into<Box<[SortIndex]>>,
    {
        Self {
            bindings: bindings.into(),
            ..self
        }
    }
}

/// A multi-output arity as the bridge diagram `A ←s— J —π→ I —t→ B`.
///
/// `inputs` are the input ports `A`; `outputs` the output ports `B`;
/// `factors[i]` is how many factors monomial `i` has (the `J —π→ I` fibers);
/// `source[j]` is `s : J → A`, which input each factor reads; `dest[i]` is
/// `t : I → B`, which output port each monomial feeds. Aggregating several
/// monomials into one output port is the sum layer's monoid-gated combine.
///
/// The maps compose when every `source[j] < inputs.len()`, every
/// `dest[i] < outputs.len()`, `factors.len() == dest.len()` and `source` has
/// one entry per factor. The constructor stores the maps as given, so an
/// ill-formed arity is representable and declined by [`check_desc`] rather
/// than unconstructible.
///
/// [`check_desc`]: crate::check_desc
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct BridgeArity
{
    /// `A`: the input ports, named.
    pub inputs: Box<[SortRef]>,
    /// The `π : J → I` fibers, as the factor count of each monomial `i ∈ I`.
    pub factors: Box<[u32]>,
    /// `s : J → A`: which input each factor reads.
    pub source: Box<[u32]>,
    /// `t : I → B`: which output port each monomial feeds.
    pub dest: Box<[u32]>,
    /// `B`: the output ports, named.
    pub outputs: Box<[SortRef]>,
}

impl BridgeArity
{
    /// A bridge arity from its four sets and three maps, stored as given.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn new<In, Fa, So, De, Ou>(
        inputs: In,
        factors: Fa,
        source: So,
        dest: De,
        outputs: Ou,
    ) -> Self
    where
        In: Into<Box<[SortRef]>>,
        Fa: Into<Box<[u32]>>,
        So: Into<Box<[u32]>>,
        De: Into<Box<[u32]>>,
        Ou: Into<Box<[SortRef]>>,
    {
        Self {
            inputs: inputs.into(),
            factors: factors.into(),
            source: source.into(),
            dest: dest.into(),
            outputs: outputs.into(),
        }
    }

    /// A single-output arity whose one monomial is the product of the given
    /// input ports: the common `op f(a, b, …) -> R` shape.
    ///
    /// # Specification
    /// - ensures: `|I| = 1`, `|B| = 1`, `factors = [|A|]`, `source = [0, 1,
    ///   …]`, `dest = [0]`; the arity composes for any ports.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — zero, one and two input ports distinguish a missing
    ///   nullary monomial, truncated factors, shifted source indices and a
    ///   wrong destination; exact maps and port identities are the observers.
    /// - witness: `arity::tests::single_output_builds_a_composing_arity`
    #[inline]
    #[must_use]
    #[spec(ensures: |ref arity| {
        let factors = u32::try_from(arity.inputs.len()).unwrap_or(u32::MAX);
        arity.factors.as_ref() == [factors]
            && arity.source.iter().copied().eq(0 .. factors)
            && arity.dest.as_ref() == [0_u32]
            && arity.outputs.len() == 1
    })]
    pub fn single_output<In>(
        inputs: In,
        output: SortRef,
    ) -> Self
    where
        In: Into<Box<[SortRef]>>,
    {
        let inputs = inputs.into();
        let factor_count = u32::try_from(inputs.len()).unwrap_or(u32::MAX);
        let source: Box<[u32]> = (0 .. factor_count).collect();
        Self {
            inputs,
            factors: Box::from([factor_count]),
            source,
            dest: Box::from([0_u32]),
            outputs: Box::from([output]),
        }
    }

    /// The number of monomials `|I|`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn monomials(&self) -> MonomialCount
    {
        MonomialCount::from(self.factors.len())
    }
}

#[cfg(test)]
mod tests
{
    use super::*;

    #[test]
    fn single_output_builds_a_composing_arity()
    {
        let ports = [SortRef::new("m", "Dividend"), SortRef::new("n", "Divisor")];
        for (inputs, factors, source) in [
            (&ports[.. 0], [0_u32], &[][..]),
            (&ports[.. 1], [1_u32], &[0_u32][..]),
            (&ports[..], [2_u32], &[0_u32, 1_u32][..]),
        ] {
            let output = SortRef::new("q", "Quotient");
            let arity = BridgeArity::single_output(inputs, output.clone());
            assert_eq!(MonomialCount::from(1), arity.monomials());
            assert_eq!(arity.factors.as_ref(), factors);
            assert_eq!(arity.source.as_ref(), source);
            assert_eq!(arity.dest.as_ref(), [0_u32]);
            assert_eq!(arity.inputs.as_ref(), inputs);
            assert_eq!(arity.outputs.as_ref(), [output]);
        }
    }
}
