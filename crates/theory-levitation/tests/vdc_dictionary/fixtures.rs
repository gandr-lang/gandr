//! Real-structure fixtures: a `Nat` signature with `plus` and `double`
//! rewrite rules, renamed copies for signature morphisms, relation
//! interfaces, clause cells, and the corpora replay-equivalence is decided
//! over.
//!
//! Every description here is field-free and parameter-free, so the grade is
//! the suite's stand-in and never inspected.

use alloc::collections::BTreeMap;
use alloc::sync::Arc;

use anodized::spec;
use gandr_theory_levitation::Attrs;
use gandr_theory_levitation::BridgeArity;
use gandr_theory_levitation::Code;
use gandr_theory_levitation::CtorDesc;
use gandr_theory_levitation::DeclPolarity;
use gandr_theory_levitation::FreeTerm;
use gandr_theory_levitation::Name;
use gandr_theory_levitation::NameRef;
use gandr_theory_levitation::NominalId;
use gandr_theory_levitation::NominalSerial;
use gandr_theory_levitation::OperDesc;
use gandr_theory_levitation::RuleFace;
use gandr_theory_levitation::SignDesc;
use gandr_theory_levitation::SortRef;
use gandr_theory_levitation::SurfaceSpan;
use gandr_theory_levitation::TermView;
use gandr_theory_levitation::derive_cell_var_meta;

use super::harness::BaseInstance;
use super::harness::Cell;
use super::harness::CellClause;
use super::harness::CellKind;
use super::harness::FactorRoute;
use super::harness::LooseArrow;
use super::harness::LooseInstance;
use super::harness::Relation;
use super::harness::SigMorphism;
use super::harness::SigObj;
use super::terms::Binding;
use crate::support::DescriptorFactorIndex;
use crate::support::GeneratorIndex;
use crate::support::Grade;
use crate::support::NumeralCount;

// ----------------------------------------------------------------------
// Ground Nat terms and small term constructors
// ----------------------------------------------------------------------

/// A variable term.
///
/// # Specification
/// trivial.
pub fn var(name: NameRef<'_>) -> FreeTerm
{
    FreeTerm::var(name)
}

/// The `Zero` constructor term.
///
/// # Specification
/// trivial.
pub fn zero() -> FreeTerm
{
    FreeTerm::ctor("Zero", Vec::new())
}

/// `Succ(inner)`.
///
/// # Specification
/// trivial.
pub fn succ(inner: FreeTerm) -> FreeTerm
{
    FreeTerm::ctor("Succ", [inner])
}

/// The numeral `n` as `Succⁿ(Zero)`.
///
/// # Specification
/// - ensures: exactly `n` unary `Succ` constructors ending in nullary `Zero`.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — zero and a multi-successor numeral expose exact
///   constructor trees, rejecting a shifted count, wrong alphabet or missing
///   terminal constructor. The iterative predicate checks every unary edge;
///   allocation exhaustion is outside the domain.
/// - witness: `tests::vdc_dictionary::fixtures::tests::numerals_have_exact_unary_depth_and_terminal`
#[spec(ensures: |ref term| {
    let mut node = term.to_node();
    for _ in 0..usize::from(n) {
        let TermView::Ctor { name, mut args } = node.view() else { return false; };
        if name.as_ref() != "Succ" { return false; }
        let Some(child) = args.next() else { return false; };
        if args.next().is_some() { return false; }
        node = child;
    }
    match node.view() {
        TermView::Ctor { name, args } => name.as_ref() == "Zero" && args.count() == 0,
        _ => false,
    }
})]
pub fn nat(n: NumeralCount) -> FreeTerm
{
    (0 .. usize::from(n)).fold(zero(), |acc, _| succ(acc))
}

/// A face over two terms, with the real derived per-variable metadata and a
/// throwaway provenance span.
///
/// # Specification
/// trivial.
pub fn face(
    lhs: FreeTerm,
    rhs: FreeTerm,
) -> RuleFace
{
    let vars = derive_cell_var_meta(&lhs);
    RuleFace::new(
        lhs,
        rhs,
        vars,
        SurfaceSpan::new(0_usize.into(), 1_usize.into()),
    )
}

// ----------------------------------------------------------------------
// The Nat signature with plus / double rewrite rules
// ----------------------------------------------------------------------

/// The `plus` bridge arity: `plus(m, n) -> q`.
///
/// # Specification
/// trivial.
fn plus_arity() -> BridgeArity
{
    BridgeArity::single_output(
        [SortRef::new("m", "Nat"), SortRef::new("n", "Nat")],
        SortRef::new("q", "Nat"),
    )
}

/// The `double` bridge arity: `double(n) -> q`.
///
/// # Specification
/// trivial.
fn double_arity() -> BridgeArity
{
    BridgeArity::single_output([SortRef::new("n", "Nat")], SortRef::new("q", "Nat"))
}

/// The four symbol names of a `Nat`-shaped signature: two constructors, two
/// operations.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct NatNames
{
    /// The `Zero`-role constructor (payload code `1`).
    pub zero: Name,
    /// The `Succ`-role constructor (payload code `var`).
    pub succ: Name,
    /// The `plus`-role operation (binary arity).
    pub plus: Name,
    /// The `double`-role operation (unary arity).
    pub double: Name,
}

/// The names spelling the real `Nat` signature's symbols (`Zero`, `Succ`,
/// `plus`, `double`), for well-formedness witnesses over in-signature names.
///
/// # Specification
/// trivial.
pub fn real_nat_names() -> NatNames
{
    NatNames {
        zero: "Zero".into(),
        succ: "Succ".into(),
        plus: "plus".into(),
        double: "double".into(),
    }
}

/// A `Nat` name tuple for a tag, role prefixes keeping the four names
/// distinct whatever the tag.
///
/// # Specification
/// trivial.
pub fn nat_names(tag: NameRef<'_>) -> NatNames
{
    NatNames {
        zero: Name::from(format!("Z_{tag}")),
        succ: Name::from(format!("S_{tag}")),
        plus: Name::from(format!("p_{tag}")),
        double: Name::from(format!("d_{tag}")),
    }
}

/// A `Nat`-shaped description with the given symbol names and rules.
/// Constructor codes and operation arities are role-fixed, so any two of
/// these are connected by a valid renaming.
///
/// # Specification
/// trivial.
pub fn nat_from_names(
    names: &NatNames,
    cells: Vec<RuleFace>,
) -> SignDesc<Grade>
{
    SignDesc::new(
        NominalId::new(NominalSerial::from(0_u64), "Nat"),
        Vec::new(),
        [
            CtorDesc::new(names.zero.clone(), Code::unit(), "Nat", Attrs::empty()),
            CtorDesc::new(names.succ.clone(), Code::var("Nat"), "Nat", Attrs::empty()),
        ],
        [
            OperDesc::new(names.plus.clone(), plus_arity(), Attrs::empty()),
            OperDesc::new(names.double.clone(), double_arity(), Attrs::empty()),
        ],
        cells,
        DeclPolarity::Data,
        Attrs::empty(),
    )
}

/// The `Nat` description: `Zero`, `Succ`, operations `plus` and `double`,
/// and three rewrite rules. Passes `check_desc` cleanly.
///
/// # Specification
/// trivial.
pub fn nat_desc() -> SignDesc<Grade>
{
    let rules = vec![
        // plus(Zero, n) ==> n
        face(
            FreeTerm::op("plus", [zero(), var("n".into())]),
            var("n".into()),
        ),
        // plus(Succ(m), n) ==> Succ(plus(m, n))
        face(
            FreeTerm::op("plus", [succ(var("m".into())), var("n".into())]),
            succ(FreeTerm::op("plus", [var("m".into()), var("n".into())])),
        ),
        // double(n) ==> plus(n, n)
        face(
            FreeTerm::op("double", [var("n".into())]),
            FreeTerm::op("plus", [var("n".into()), var("n".into())]),
        ),
    ];
    nat_from_names(&real_nat_names(), rules)
}

/// The single-factor object over [`nat_desc`].
///
/// # Specification
/// trivial.
pub fn nat_sig() -> SigObj
{
    SigObj::single(nat_desc())
}

/// The single-factor object over a named `Nat`-shaped description with no
/// rules.
///
/// # Specification
/// trivial.
pub fn nat_obj(names: &NatNames) -> SigObj
{
    SigObj::single(nat_from_names(names, Vec::new()))
}

/// A small bank of real faces over a named `Nat` signature — a constructor
/// rule, an operation rule, a nested operation rule and an identity-shaped
/// rewrite — for the face-action properties.
///
/// # Specification
/// trivial.
pub fn sample_faces(names: &NatNames) -> Vec<RuleFace>
{
    let zero_term = FreeTerm::ctor(names.zero.clone(), Vec::new());
    let succ_m = FreeTerm::ctor(names.succ.clone(), [var("m".into())]);
    vec![
        // plus(Zero, x) ==> x
        face(
            FreeTerm::op(names.plus.clone(), [zero_term, var("x".into())]),
            var("x".into()),
        ),
        // double(n) ==> plus(n, n)
        face(
            FreeTerm::op(names.double.clone(), [var("n".into())]),
            FreeTerm::op(names.plus.clone(), [var("n".into()), var("n".into())]),
        ),
        // plus(Succ(m), n) ==> Succ(plus(m, n))
        face(
            FreeTerm::op(names.plus.clone(), [succ_m.clone(), var("n".into())]),
            FreeTerm::ctor(names.succ.clone(), [FreeTerm::op(names.plus.clone(), [
                var("m".into()),
                var("n".into()),
            ])]),
        ),
        // Succ(m) ==> Succ(m), exercising constructor renaming
        face(succ_m.clone(), succ_m),
    ]
}

// ----------------------------------------------------------------------
// Renaming signature morphisms
// ----------------------------------------------------------------------

/// The renaming morphism `f : source → target` between two `Nat`-shaped
/// objects: each target symbol sent to its role-matched source symbol.
///
/// # Specification
/// trivial.
pub fn renaming(
    source_names: &NatNames,
    target_names: &NatNames,
) -> SigMorphism
{
    let map: BTreeMap<Name, Name> = [
        (target_names.zero.clone(), source_names.zero.clone()),
        (target_names.succ.clone(), source_names.succ.clone()),
        (target_names.plus.clone(), source_names.plus.clone()),
        (target_names.double.clone(), source_names.double.clone()),
    ]
    .into_iter()
    .collect();
    SigMorphism {
        src: nat_obj(source_names),
        tgt: nat_obj(target_names),
        routes: vec![FactorRoute {
            src_factor: DescriptorFactorIndex::from(0_usize),
            map,
        }],
    }
}

// ----------------------------------------------------------------------
// Relation interfaces, loose arrows and clause cells
// ----------------------------------------------------------------------

/// A single-generator relation over `Nat` whose generating face is
/// `plus(x, Zero) ==> x`, a real in-signature face.
///
/// # Specification
/// trivial.
pub fn unary_relation(name: NameRef<'_>) -> Arc<Relation>
{
    let generator = face(
        FreeTerm::op("plus", [var("x".into()), zero()]),
        var("x".into()),
    );
    Arc::new(Relation {
        name: name.into(),
        src: nat_sig(),
        tgt: nat_sig(),
        gens: vec![generator],
    })
}

/// The loose arrow over a single named relation, framed by identities.
///
/// # Specification
/// trivial.
pub fn loose_of(rel: Arc<Relation>) -> LooseArrow
{
    LooseArrow::of_relation(rel)
}

/// The identity cell on a single loose arrow.
///
/// # Specification
/// trivial.
pub fn ident_cell(loose: LooseArrow) -> Cell
{
    Cell {
        dom: vec![loose.clone()],
        cod: loose,
        left_frame: SigMorphism::identity(&nat_sig()),
        right_frame: SigMorphism::identity(&nat_sig()),
        kind: CellKind::ident(),
    }
}

/// A linear single-clause cell `dom_rel ⇒ cod_rel` matching generator `0`
/// and emitting generator `0` with variable `x` bound to the template (over
/// the namespaced input variable `p0.x`).
///
/// # Specification
/// trivial.
pub fn relabel_cell(
    dom_rel: Arc<Relation>,
    cod_rel: Arc<Relation>,
    template_for_x: FreeTerm,
) -> Cell
{
    let mut emit_templates = Binding::new();
    emit_templates.insert("x".into(), template_for_x);
    Cell {
        dom: vec![loose_of(dom_rel)],
        cod: loose_of(cod_rel),
        left_frame: SigMorphism::identity(&nat_sig()),
        right_frame: SigMorphism::identity(&nat_sig()),
        kind: CellKind::clauses(vec![CellClause {
            matches: vec![GeneratorIndex::from(0_usize)],
            emit: vec![(GeneratorIndex::from(0_usize), emit_templates)],
        }]),
    }
}

// ----------------------------------------------------------------------
// Instances and corpora
// ----------------------------------------------------------------------

/// A single-factor generating instance binding variable `x` to `term`.
///
/// # Specification
/// trivial.
pub fn gen_x(term: FreeTerm) -> LooseInstance
{
    let mut subst = Binding::new();
    subst.insert("x".into(), term);
    LooseInstance {
        per_factor: vec![BaseInstance::Gen {
            generator: GeneratorIndex::from(0_usize),
            subst,
        }],
    }
}

/// The single-input corpus: one input chain per numeral `0 ..= 5`, each a
/// generating instance binding `x` to that numeral.
///
/// # Specification
/// trivial.
pub fn single_input_corpus() -> Vec<Vec<LooseInstance>>
{
    (0 ..= 5_usize)
        .map(|k| vec![gen_x(nat(NumeralCount::from(k)))])
        .collect()
}

#[cfg(test)]
mod tests
{
    use super::*;

    #[test]
    fn numerals_have_exact_unary_depth_and_terminal()
    {
        assert_eq!(nat(NumeralCount::from(0_usize)), FreeTerm::ctor("Zero", []));
        assert_eq!(
            nat(NumeralCount::from(3_usize)),
            FreeTerm::ctor("Succ", [FreeTerm::ctor("Succ", [FreeTerm::ctor(
                "Succ",
                [FreeTerm::ctor("Zero", [])]
            )])])
        );
    }
}
