//! A test-side realization of the virtual double category the rewrite layer
//! is read as: objects, tight arrows, loose arrows with their split
//! restriction, instances, and multi-ary cells with replay.
//!
//! Objects, tight arrows and restriction are built directly on the crate's
//! structures: a [`SigObj`] is a tuple of real `SignDesc`s, a tight arrow
//! renames real constructor and operation symbols and is checked against
//! their real `Code`s and `BridgeArity`s, and restriction recomputes real
//! `RuleFace`s through the real `derive_cell_var_meta`. The cell machinery —
//! [`Cell`], [`replay`], [`graft`] — is a stand-in: the crate has no cell
//! store, and these tests fix what one must satisfy.
//!
//! Every substitution is a `BTreeMap` iterated in key order and every
//! enumeration a left-to-right walk, so replay and equality are
//! reproducible.

use alloc::collections::BTreeMap;
use alloc::sync::Arc;

use anodized::spec;
use gandr_theory_levitation::BridgeArity;
use gandr_theory_levitation::Code;
use gandr_theory_levitation::DiagnosticMessage;
use gandr_theory_levitation::FreeTerm;
use gandr_theory_levitation::Name;
use gandr_theory_levitation::NameRef;
use gandr_theory_levitation::RuleFace;
use gandr_theory_levitation::SignDesc;
use gandr_theory_levitation::derive_cell_var_meta;
use quenchant_shape::shape::Maybe;

use super::terms::Binding;
use super::terms::RewriteStep;
use super::terms::apply_path;
use super::terms::rebuild;
use super::terms::subst_term;
use crate::support::CellEquivalence;
use crate::support::DescriptorFactorCount;
use crate::support::DescriptorFactorIndex;
use crate::support::GeneratorIndex;
use crate::support::Grade;
use crate::support::LooseInstanceEquality;
use crate::support::StepExtent;
use crate::support::StepIndex;
use crate::support::SymbolPresence;

// ----------------------------------------------------------------------
// Objects: tuples of described signatures, the empty tuple terminal
// ----------------------------------------------------------------------

/// An object: a finite product of described signatures.
///
/// The empty tuple is the terminal object `⊤`; the chosen binary product is
/// factor concatenation ([`SigObj::product`]). Object identity is structural
/// equality of the underlying descriptions.
#[repr(transparent)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SigObj
{
    /// The signature factors, left to right.
    pub factors: Vec<SignDesc<Grade>>,
}

impl SigObj
{
    /// A one-factor object over a single description.
    ///
    /// # Specification
    /// trivial.
    pub fn single(desc: SignDesc<Grade>) -> Self
    {
        Self {
            factors: vec![desc],
        }
    }

    /// The terminal object `⊤`, the empty tuple.
    ///
    /// # Specification
    /// trivial.
    pub const fn terminal() -> Self
    {
        Self {
            factors: Vec::new(),
        }
    }

    /// The chosen binary product `A × B`, factor concatenation.
    ///
    /// # Specification
    /// trivial.
    pub fn product(
        left: &Self,
        right: &Self,
    ) -> Self
    {
        let mut factors = left.factors.clone();
        factors.extend(right.factors.iter().cloned());
        Self { factors }
    }

    /// The number of factors, `0` for `⊤`.
    ///
    /// # Specification
    /// trivial.
    pub fn arity(&self) -> DescriptorFactorCount
    {
        DescriptorFactorCount::from(self.factors.len())
    }
}

// ----------------------------------------------------------------------
// Tight arrows: signature morphisms as per-target-factor renamings
// ----------------------------------------------------------------------

/// One target factor's routing: which source factor it is drawn from, and
/// the renaming of that target factor's constructor and operation symbols to
/// symbols of the routed source factor.
///
/// The map sends target symbols to source symbols, the contravariant
/// direction of the term action ([`apply_term`]).
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct FactorRoute
{
    /// The source factor this target factor is routed from.
    pub src_factor: DescriptorFactorIndex,
    /// Every constructor and operation name of the target factor, mapped to a
    /// symbol of the routed source factor.
    pub map: BTreeMap<Name, Name>,
}

/// A tight arrow `f : A → B`: one [`FactorRoute`] per target factor. Its
/// term action sends `B`-terms to `A`-terms.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SigMorphism
{
    /// The source object `A`.
    pub src: SigObj,
    /// The target object `B`.
    pub tgt: SigObj,
    /// One route per target factor of `B`.
    pub routes: Vec<FactorRoute>,
}

/// A single validity failure of a tight arrow.
#[repr(transparent)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct MorphismError
{
    /// A human-readable description of the failure.
    pub message: DiagnosticMessage,
}

impl MorphismError
{
    /// A failure carrying the given description.
    ///
    /// # Specification
    /// trivial.
    fn new(message: String) -> Self
    {
        Self {
            message: DiagnosticMessage::from(message),
        }
    }
}

/// The identity renaming on a description, every symbol to itself.
///
/// # Specification
/// trivial.
fn identity_map(desc: &SignDesc<Grade>) -> BTreeMap<Name, Name>
{
    symbol_names(desc)
        .into_iter()
        .map(|name| (name.clone(), name))
        .collect()
}

/// The constructor and operation names of a description, constructors first,
/// each in declaration order: the symbols a factor's renaming must cover.
///
/// # Specification
/// trivial.
pub fn symbol_names(desc: &SignDesc<Grade>) -> Vec<Name>
{
    desc.ctors
        .iter()
        .map(|ctor| ctor.name.clone())
        .chain(desc.opers.iter().map(|oper| oper.name.clone()))
        .collect()
}

impl SigMorphism
{
    /// The identity tight arrow on an object.
    ///
    /// # Specification
    /// trivial.
    pub fn identity(obj: &SigObj) -> Self
    {
        let routes = obj
            .factors
            .iter()
            .enumerate()
            .map(|(index, desc)| FactorRoute {
                src_factor: DescriptorFactorIndex::from(index),
                map: identity_map(desc),
            })
            .collect();
        Self {
            src: obj.clone(),
            tgt: obj.clone(),
            routes,
        }
    }

    /// The projection `A₀ × … × Aₙ → Aᵢ` onto factor `idx`.
    ///
    /// # Specification
    /// - requires: `idx` is a factor of `product`.
    /// - panics: on an absent factor, a test-author error.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — valid zero-, one- and two-factor products expose
    ///   projection targets, diagonal routing and the projection laws; the
    ///   first absent factor panics. These observations detect routing
    ///   off-by-one, a swapped factor and loss of the terminal boundary, not
    ///   arbitrary product representations.
    /// - witness: `tests::vdc_dictionary::harness::tests::tight_products_observe_zero_and_multiple_factors`
    /// - witness: `tests::vdc_dictionary::law1_tight::the_diagonal_projects_back_to_the_identity`
    #[spec(requires: usize::from(idx) < product.factors.len(),
        ensures: |ref projection| projection.src == *product && projection.tgt.factors.len() == 1
            && projection.tgt.factors.first() == product.factors.get(usize::from(idx))
            && projection.routes.len() == 1 && projection.routes.first().is_some_and(|route|
                route.src_factor == idx && route.map.iter().all(|(name, image)| name == image)))]
    pub fn projection(
        product: &SigObj,
        idx: DescriptorFactorIndex,
    ) -> Self
    {
        let desc = product.factors[usize::from(idx)].clone();
        let route = FactorRoute {
            src_factor: idx,
            map: identity_map(&desc),
        };
        Self {
            src: product.clone(),
            tgt: SigObj::single(desc),
            routes: vec![route],
        }
    }

    /// The diagonal `A → A × A`.
    ///
    /// # Specification
    /// - ensures: target factor `i` is routed from source factor `i mod |A|`
    ///   under the identity renaming.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — terminal, singleton and two-factor objects expose
    ///   exact doubled targets and route indices; composing with either
    ///   projection recovers identity. The observations reject division by
    ///   zero, alternating the wrong width and swapped copies, within finite
    ///   described products.
    /// - witness: `tests::vdc_dictionary::harness::tests::tight_products_observe_zero_and_multiple_factors`
    /// - witness: `tests::vdc_dictionary::law1_tight::the_diagonal_projects_back_to_the_identity`
    #[spec(ensures: |ref diagonal| diagonal.src == *obj
        && diagonal.tgt.factors.iter().eq(obj.factors.iter().chain(&obj.factors))
        && diagonal.routes.len() == diagonal.tgt.factors.len()
        && diagonal.routes.iter().enumerate().all(|(index, route)|
            index.checked_rem(obj.factors.len().max(1)).is_some_and(|factor| usize::from(route.src_factor) == factor)
                && route.map.iter().all(|(name, image)| name == image)))]
    pub fn diagonal(obj: &SigObj) -> Self
    {
        let width = usize::from(obj.arity()).max(1);
        let target = SigObj::product(obj, obj);
        let routes = target
            .factors
            .iter()
            .enumerate()
            .map(|(index, desc)| FactorRoute {
                src_factor: DescriptorFactorIndex::from(
                    index.checked_rem(width).expect("the width is at least one"),
                ),
                map: identity_map(desc),
            })
            .collect();
        Self {
            src: obj.clone(),
            tgt: target,
            routes,
        }
    }

    /// The pairing `⟨f, g⟩ : A → B × C` of two arrows with a shared source.
    ///
    /// # Specification
    /// - requires: both arrows have the same source.
    /// - ensures: target factors and routes are concatenated in left-right
    ///   order.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — same-source finite renamings expose both projections
    ///   of the paired arrow and the terminal case. The beta laws reject
    ///   exchanged routes or target factors; no pairing of different source
    ///   objects is claimed.
    /// - witness: `tests::vdc_dictionary::law1_tight::chosen_product_beta_and_terminal_hold_strictly`
    #[spec(requires: left.src == right.src,
        ensures: |ref paired| paired.src == left.src
            && paired.tgt.factors.iter().eq(left.tgt.factors.iter().chain(&right.tgt.factors))
            && paired.routes.iter().eq(left.routes.iter().chain(&right.routes)))]
    pub fn pairing(
        left: &Self,
        right: &Self,
    ) -> Self
    {
        let mut routes = left.routes.clone();
        routes.extend(right.routes.iter().cloned());
        Self {
            src: left.src.clone(),
            tgt: SigObj::product(&left.tgt, &right.tgt),
            routes,
        }
    }

    /// The terminal arrow `! : A → ⊤`: no target factors, hence no routes.
    ///
    /// # Specification
    /// trivial.
    pub fn terminal(obj: &SigObj) -> Self
    {
        Self {
            src: obj.clone(),
            tgt: SigObj::terminal(),
            routes: Vec::new(),
        }
    }
}

/// Checks that a tight arrow is a valid signature morphism: one route per
/// target factor, and every constructor and operation of each target factor
/// mapped to a same-kind source symbol with a structurally identical payload
/// (`Code` for constructors, `BridgeArity` for operations).
///
/// # Specification
/// - ensures: one error per failure, empty exactly when the arrow is valid; a
///   route-count mismatch is reported alone.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — valid maps and isolated route-count, missing-factor,
///   missing-symbol, alphabet, code and arity failures expose acceptance and
///   exact diagnostic counts. Combined code and arity failures reject
///   short-circuiting; message wording and the well-formedness of whole
///   descriptions are outside this morphism check.
/// - witness: `tests::vdc_dictionary::harness::tests::morphism_checker_distinguishes_structural_failures`
/// - witness: `tests::vdc_dictionary::law1_tight::check_morphism_rejects_code_and_arity_violations`
#[spec(ensures: |ref errors| if morphism.routes.len() == morphism.tgt.factors.len() {
    errors.is_empty() == morphism.routes.iter().zip(&morphism.tgt.factors).all(|(route, target)|
        morphism.src.factors.get(usize::from(route.src_factor)).is_some_and(|source|
            target.ctors.iter().map(|ctor| &ctor.name).chain(target.opers.iter().map(|oper| &oper.name))
                .all(|name| route.map.contains_key(name))
            && route.map.iter().all(|(target_name, source_name)| match ctor_code(target, target_name.as_name_ref()) {
                | Maybe::Present(code) => ctor_code(source, source_name.as_name_ref()) == Maybe::Present(code),
                | Maybe::Absent(_) => bool::from(is_op(target, target_name.as_name_ref()))
                    && op_arity(target, target_name.as_name_ref()) == op_arity(source, source_name.as_name_ref()),
            })))
} else {
    errors.len() == 1
})]
pub fn check_morphism(morphism: &SigMorphism) -> Vec<MorphismError>
{
    let mut errors = Vec::new();
    if morphism.routes.len() != usize::from(morphism.tgt.arity()) {
        errors.push(MorphismError::new(format!(
            "route count {} does not match target arity {}",
            morphism.routes.len(),
            morphism.tgt.arity()
        )));
        return errors;
    }
    for (factor, (route, target)) in morphism
        .routes
        .iter()
        .zip(&morphism.tgt.factors)
        .enumerate()
    {
        let Some(source) = morphism.src.factors.get(usize::from(route.src_factor))
        else {
            errors.push(MorphismError::new(format!(
                "target factor {factor} routes from absent source factor {}",
                route.src_factor
            )));
            continue;
        };
        for symbol in symbol_names(target) {
            if !route.map.contains_key(&symbol) {
                errors.push(MorphismError::new(format!(
                    "target symbol `{symbol}` is unmapped in factor {factor}"
                )));
            }
        }
        for (target_symbol, source_symbol) in &route.map {
            check_symbol_mapping(
                &SymbolMapping {
                    target,
                    source,
                    target_symbol,
                    source_symbol,
                    factor: DescriptorFactorIndex::from(factor),
                },
                &mut errors,
            );
        }
    }
    errors
}

/// One `target_symbol ↦ source_symbol` mapping of a route, with the two
/// descriptions it relates.
struct SymbolMapping<'map>
{
    /// The target factor's description.
    target: &'map SignDesc<Grade>,
    /// The routed source factor's description.
    source: &'map SignDesc<Grade>,
    /// The mapped target symbol.
    target_symbol: &'map Name,
    /// The source symbol it maps to.
    source_symbol: &'map Name,
    /// The target factor, for the message.
    factor: DescriptorFactorIndex,
}

/// Checks one mapping for kind and payload identity.
///
/// # Specification
/// - ensures: one error when the target symbol is a constructor whose source
///   image is not a constructor of the same code, an operation whose source
///   image is not an operation of the same arity, or neither; nothing
///   otherwise.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — constructor and operation mappings with missing,
///   wrong-kind and unequal payload images expose one diagnostic per failed
///   entry and none for a valid entry. Repeated checks reject clearing the
///   collector or appending twice; the observer is failure count, not
///   diagnostic prose.
/// - witness: `tests::vdc_dictionary::harness::tests::morphism_checker_distinguishes_structural_failures`
/// - witness: `tests::vdc_dictionary::law1_tight::check_morphism_rejects_code_and_arity_violations`
#[spec(captures: before = errors.len(), ensures: errors.len() == before.saturating_add(usize::from(
    match ctor_code(mapping.target, mapping.target_symbol.as_name_ref()) {
        | Maybe::Present(code) => ctor_code(mapping.source, mapping.source_symbol.as_name_ref()) != Maybe::Present(code),
        | Maybe::Absent(_) => !bool::from(is_op(mapping.target, mapping.target_symbol.as_name_ref()))
            || op_arity(mapping.target, mapping.target_symbol.as_name_ref()) != op_arity(mapping.source, mapping.source_symbol.as_name_ref()),
    }
)))]
fn check_symbol_mapping(
    mapping: &SymbolMapping<'_>,
    errors: &mut Vec<MorphismError>,
)
{
    let SymbolMapping {
        target,
        source,
        target_symbol,
        source_symbol,
        factor,
    } = *mapping;
    if let Maybe::Present(target_code) = ctor_code(target, target_symbol.as_name_ref()) {
        match ctor_code(source, source_symbol.as_name_ref()) {
            | Maybe::Present(source_code) if source_code == target_code => {},
            | Maybe::Present(_) => errors.push(MorphismError::new(format!(
                "ctor `{target_symbol}` ↦ `{source_symbol}` in factor {factor}: payload codes \
                 differ"
            ))),
            | Maybe::Absent(symbol::Absent::Undeclared) => {
                errors.push(MorphismError::new(format!(
                    "ctor `{target_symbol}` ↦ `{source_symbol}` in factor {factor}: source symbol \
                     is not a constructor with the same code"
                )));
            },
        }
    }
    else if bool::from(is_op(target, target_symbol.as_name_ref())) {
        let target_arity = op_arity(target, target_symbol.as_name_ref());
        let source_arity = op_arity(source, source_symbol.as_name_ref());
        if target_arity != source_arity {
            errors.push(MorphismError::new(format!(
                "op `{target_symbol}` ↦ `{source_symbol}` in factor {factor}: bridge arities \
                 differ or source is not an op"
            )));
        }
    }
    else {
        errors.push(MorphismError::new(format!(
            "mapped symbol `{target_symbol}` in factor {factor} is neither a ctor nor an op of the \
             target"
        )));
    }
}

quenchant_shape::reason_enum! {
    /// Why a symbol lookup finds nothing.
    pub mod symbol {
        /// The reason the symbol has no payload.
        #[derive(Clone, Copy, Debug, Eq, PartialEq)]
        pub enum Absent {
            /// The description declares no symbol of that kind and name.
            Undeclared,
        }
    }
}

/// A constructor's payload code, by name.
///
/// # Specification
/// - ensures: the first constructor's code for the name, or undeclared.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — missing, operation-only and duplicate constructor names
///   expose absence or the first borrowed code. These observations reject
///   crossing symbol alphabets or selecting a later declaration; duplicate
///   declarations are lookup cases, not an endorsement of their
///   well-formedness.
/// - witness: `tests::vdc_dictionary::harness::tests::symbol_lookups_choose_the_first_declaration`
#[spec(ensures: |ref result| match *result {
    | Maybe::Present(code) => desc.ctors.iter().find(|ctor| ctor.name.as_name_ref() == name)
        .is_some_and(|ctor| core::ptr::eq(core::ptr::from_ref(code), &raw const ctor.code)),
    | Maybe::Absent(symbol::Absent::Undeclared) => desc.ctors.iter().all(|ctor| ctor.name.as_name_ref() != name),
})]
fn ctor_code<'desc>(
    desc: &'desc SignDesc<Grade>,
    name: NameRef<'_>,
) -> Maybe<&'desc Code<Grade>, symbol::Absent>
{
    match desc
        .ctors
        .iter()
        .find(|ctor| ctor.name.as_name_ref() == name)
    {
        | Some(ctor) => Maybe::Present(&ctor.code),
        | None => Maybe::Absent(symbol::Absent::Undeclared),
    }
}

/// Whether a name is an operation of a description.
///
/// # Specification
/// trivial.
fn is_op(
    desc: &SignDesc<Grade>,
    name: NameRef<'_>,
) -> SymbolPresence
{
    SymbolPresence::from(
        desc.opers
            .iter()
            .any(|oper| oper.name.as_name_ref() == name),
    )
}

/// An operation's bridge arity, by name.
///
/// # Specification
/// - ensures: the first operation's arity for the name, or undeclared.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — missing, constructor-only and duplicate operation names
///   expose absence or the first borrowed arity. These observations reject
///   crossing symbol alphabets or choosing a later duplicate; lookup does not
///   validate duplicate declarations.
/// - witness: `tests::vdc_dictionary::harness::tests::symbol_lookups_choose_the_first_declaration`
#[spec(ensures: |ref result| match *result {
    | Maybe::Present(arity) => desc.opers.iter().find(|oper| oper.name.as_name_ref() == name)
        .is_some_and(|oper| core::ptr::eq(core::ptr::from_ref(arity), &raw const oper.arity)),
    | Maybe::Absent(symbol::Absent::Undeclared) => desc.opers.iter().all(|oper| oper.name.as_name_ref() != name),
})]
fn op_arity<'desc>(
    desc: &'desc SignDesc<Grade>,
    name: NameRef<'_>,
) -> Maybe<&'desc BridgeArity, symbol::Absent>
{
    match desc
        .opers
        .iter()
        .find(|oper| oper.name.as_name_ref() == name)
    {
        | Some(oper) => Maybe::Present(&oper.arity),
        | None => Maybe::Absent(symbol::Absent::Undeclared),
    }
}

/// Composes two tight arrows: `compose(first, second)` is `second ∘ first`,
/// `first : A → B` then `second : B → C`, giving `A → C`.
///
/// The term action is contravariant, so the composite sends a `C`-symbol
/// through `second`'s map to `B` and then through `first`'s map to `A`.
///
/// # Specification
/// - requires: `first.tgt` is `second.src`, and every second route indexes a
///   first route.
/// - ensures: one route per route of `second`, drawn from the source factor its
///   `first` route names, each symbol mapped through both renamings (a symbol
///   `first` leaves unmapped is kept).
/// - panics: when a route of `second` names a factor `first` does not route, a
///   test-author error.
///
/// # Adequacy
/// - hypothesis: L3 — composable renamings, including unmapped intermediate
///   symbols, expose exact final routes and contravariant term action; an
///   absent routed factor panics. The observations reject reversed map
///   composition, losing unmapped symbols and wrong source factors; global
///   signature validity is a separate check.
/// - witness: `tests::vdc_dictionary::harness::tests::composition_and_term_action_keep_unmapped_heads`
/// - witness: `tests::vdc_dictionary::law1_tight::composition_is_strictly_associative`
/// - witness: `tests::vdc_dictionary::law1_tight::term_action_is_contravariantly_functorial`
#[spec(requires: first.tgt == second.src
    && second.routes.iter().all(|route| usize::from(route.src_factor) < first.routes.len()),
    ensures: |ref composite| composite.src.eq(&first.src) && composite.tgt.eq(&second.tgt)
        && composite.routes.len() == second.routes.len()
        && composite.routes.iter().zip(&second.routes).all(|(route, outer)|
            first.routes.get(usize::from(outer.src_factor)).is_some_and(|inner|
                route.src_factor == inner.src_factor && route.map.len() == outer.map.len()
                    && outer.map.iter().all(|(name, middle)| route.map.get(name) == Some(inner.map.get(middle).unwrap_or(middle))))))]
pub fn compose(
    first: &SigMorphism,
    second: &SigMorphism,
) -> SigMorphism
{
    let routes = second
        .routes
        .iter()
        .map(|outer| {
            let inner = &first.routes[usize::from(outer.src_factor)];
            let map = outer
                .map
                .iter()
                .map(|(c_symbol, b_symbol)| {
                    let a_symbol = inner.map.get(b_symbol).unwrap_or(b_symbol).clone();
                    (c_symbol.clone(), a_symbol)
                })
                .collect();
            FactorRoute {
                src_factor: inner.src_factor,
                map,
            }
        })
        .collect();
    SigMorphism {
        src: first.src.clone(),
        tgt: second.tgt.clone(),
        routes,
    }
}

/// The term action of a tight arrow: renames the constructor and operation
/// symbols of a term over target factor `tgt_factor` into symbols of the
/// routed source factor, leaving variables untouched.
///
/// # Specification
/// - ensures: the term with every application head the factor's route maps
///   replaced by its image; an absent route or an unmapped symbol keeps the
///   head, so the action is total.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — mixed constructor/operation terms with mapped and
///   unmapped heads, variables and an absent route expose exact images. The
///   observations reject renaming variables, changing alphabets, dropping heads
///   or reversing the contravariant action; unknown names are intentionally
///   fixed, not rejected.
/// - witness: `tests::vdc_dictionary::harness::tests::composition_and_term_action_keep_unmapped_heads`
/// - witness: `tests::vdc_dictionary::law1_tight::term_action_is_contravariantly_functorial`
#[spec(ensures: |ref image| image.to_node().vars().eq(term.to_node().vars())
    && (morphism.routes.get(usize::from(tgt_factor)).is_some() || image == term))]
pub fn apply_term(
    morphism: &SigMorphism,
    tgt_factor: DescriptorFactorIndex,
    term: &FreeTerm,
) -> FreeTerm
{
    let route = morphism.routes.get(usize::from(tgt_factor));
    rebuild(
        term,
        |name| FreeTerm::var(name.clone()),
        |name| {
            route
                .and_then(|route| route.map.get(name))
                .unwrap_or(name)
                .clone()
        },
    )
}

/// The face action of a tight arrow: both terms of a face through
/// [`apply_term`], the per-variable metadata recomputed by the real
/// `derive_cell_var_meta`.
///
/// # Specification
/// - ensures: both endpoints are translated, variable metadata is rederived
///   from the translated left endpoint, and provenance is retained.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — well-formed sample faces under role-matched renamings
///   expose translated endpoints, derived metadata and well-formedness. The
///   observations reject translating only one side or carrying stale metadata;
///   this is homogeneous single-signature action, not heterogeneous relation
///   validation.
/// - witness: `tests::vdc_dictionary::law3_restriction::morphism_valid_faces_stay_well_formed_after_translation`
/// - witness: `tests::vdc_dictionary::law3_restriction::a_framed_cell_factors_data_identically_through_its_globular_form`
#[spec(ensures: |ref image| image.provenance == face.provenance
    && image.lhs.to_node().vars().eq(face.lhs.to_node().vars())
    && image.rhs.to_node().vars().eq(face.rhs.to_node().vars()))]
pub fn apply_face(
    morphism: &SigMorphism,
    tgt_factor: DescriptorFactorIndex,
    face: &RuleFace,
) -> RuleFace
{
    let lhs = apply_term(morphism, tgt_factor, &face.lhs);
    let rhs = apply_term(morphism, tgt_factor, &face.rhs);
    let vars = derive_cell_var_meta(&lhs);
    RuleFace::new(lhs, rhs, vars, face.provenance)
}

// ----------------------------------------------------------------------
// Loose arrows: the split representation
// ----------------------------------------------------------------------

/// A named relation interface `R : I ⇸ J`: generating faces between two
/// objects.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Relation
{
    /// The relation's name.
    pub name: Name,
    /// The source object `I`.
    pub src: SigObj,
    /// The target object `J`.
    pub tgt: SigObj,
    /// The generating faces.
    pub gens: Vec<RuleFace>,
}

/// The base of a formal restriction: a named relation, or the rewrite-path
/// relation over a single-description object.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum BaseLoose
{
    /// A named relation interface, shared.
    Named(Arc<Relation>),
    /// The path relation `x ⇝ y` over a single-description object.
    Path
    {
        /// The single-factor object the path relation ranges over.
        sig: SigObj,
    },
}

impl BaseLoose
{
    /// The base's source object.
    ///
    /// # Specification
    /// trivial.
    pub fn src(&self) -> SigObj
    {
        match *self {
            | Self::Named(ref rel) => rel.src.clone(),
            | Self::Path { ref sig } => sig.clone(),
        }
    }

    /// The base's target object.
    ///
    /// # Specification
    /// trivial.
    pub fn tgt(&self) -> SigObj
    {
        match *self {
            | Self::Named(ref rel) => rel.tgt.clone(),
            | Self::Path { ref sig } => sig.clone(),
        }
    }
}

/// A formal restriction `base[left # right]`: a base loose arrow together
/// with the two tight arrows that precompose its faces.
///
/// Restriction never touches the base; it only composes into `left` and
/// `right`. That is what makes restriction split, the tuple construction of
/// Hayato Nasu, *Logical Aspects of Virtual Double Categories*,
/// arXiv:2501.17869, Lemma 3.2.8.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct FormalRestriction
{
    /// The left frame `left : I → base.src`.
    pub left: SigMorphism,
    /// The base loose arrow.
    pub base: BaseLoose,
    /// The right frame `right : J → base.tgt`.
    pub right: SigMorphism,
}

/// A loose arrow `α : I ⇸ J`: a `∧`-tuple of formal restrictions. The empty
/// tuple is `⊤`; concatenation is `∧`.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct LooseArrow
{
    /// The source object `I`.
    pub src: SigObj,
    /// The target object `J`.
    pub tgt: SigObj,
    /// The `∧`-tuple of formal restrictions.
    pub factors: Vec<FormalRestriction>,
}

impl LooseArrow
{
    /// The loose arrow over a single named relation, framed by identities.
    ///
    /// # Specification
    /// trivial.
    pub fn of_relation(rel: Arc<Relation>) -> Self
    {
        let src = rel.src.clone();
        let tgt = rel.tgt.clone();
        let left = SigMorphism::identity(&src);
        let right = SigMorphism::identity(&tgt);
        Self {
            src,
            tgt,
            factors: vec![FormalRestriction {
                left,
                base: BaseLoose::Named(rel),
                right,
            }],
        }
    }

    /// The path loose arrow over a single-description object, framed by
    /// identities: the unit.
    ///
    /// # Specification
    /// - requires: the object has exactly one described factor.
    /// - ensures: the path relation is framed by identities on that object.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a single Nat-shaped description supplies reflexive
    ///   and nonempty paths to path induction. Their replay and beta law reject
    ///   using another base or a nonidentity frame; multi-factor path objects
    ///   are not in the constructor domain.
    /// - witness: `tests::vdc_dictionary::law5_units::path_induction_satisfies_beta_on_refl`
    /// - witness: `tests::vdc_dictionary::law5_units::path_induction_declines_on_a_non_empty_path`
    #[spec(requires: sig.factors.len() == 1)]
    pub fn path(sig: &SigObj) -> Self
    {
        let frame = SigMorphism::identity(sig);
        Self {
            src: sig.clone(),
            tgt: sig.clone(),
            factors: vec![FormalRestriction {
                left: frame.clone(),
                base: BaseLoose::Path { sig: sig.clone() },
                right: frame,
            }],
        }
    }

    /// The terminal loose arrow `⊤ : I ⇸ J`, the empty `∧`-tuple.
    ///
    /// # Specification
    /// trivial.
    pub fn top(
        src: &SigObj,
        tgt: &SigObj,
    ) -> Self
    {
        Self {
            src: src.clone(),
            tgt: tgt.clone(),
            factors: Vec::new(),
        }
    }

    /// The meet `α ∧ β`, factor concatenation; both share their endpoints.
    ///
    /// # Specification
    /// - requires: the arrows share both endpoints.
    /// - ensures: factors are concatenated in left-right order at those
    ///   endpoints.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — same-endpoint named relations expose the factor tuple
    ///   under meet and restriction. The distribution law rejects reversing or
    ///   dropping a factor; no meet across different endpoints is claimed.
    /// - witness: `tests::vdc_dictionary::law3_restriction::restriction_distributes_over_meet`
    /// - witness: `tests::vdc_dictionary::law4_cartesian::projection_pairing_bijection_holds_up_to_replay`
    #[spec(requires: (&left.src, &left.tgt) == (&right.src, &right.tgt),
        ensures: |ref meet| (&meet.src, &meet.tgt) == (&left.src, &left.tgt)
            && meet.factors.iter().eq(left.factors.iter().chain(&right.factors)))]
    pub fn meet(
        left: &Self,
        right: &Self,
    ) -> Self
    {
        let mut factors = left.factors.clone();
        factors.extend(right.factors.iter().cloned());
        Self {
            src: left.src.clone(),
            tgt: left.tgt.clone(),
            factors,
        }
    }
}

/// Restriction `α[s # t]`: `s` composed into every factor's left frame and
/// `t` into every right frame, the base untouched, so restriction is split
/// by construction (Nasu, arXiv:2501.17869, Definition 3.2.6).
///
/// # Specification
/// - requires: well-formed factors and frames, with `s.tgt == alpha.src` and
///   `t.tgt == alpha.tgt`.
/// - ensures: the bases and their order are kept while the two frames compose;
///   the new endpoints are the sources of `s` and `t`.
/// - panics: malformed routed factors can panic during composition.
///
/// # Adequacy
/// - hypothesis: L3 — well-formed named arrows, identity and composed frames,
///   meets and the empty loose arrow expose exact split restrictions. These
///   observations reject mutating a base, reversing composition or losing the
///   empty case; malformed routing is outside this domain.
/// - witness: `tests::vdc_dictionary::law3_restriction::restriction_by_identities_is_the_identity`
/// - witness: `tests::vdc_dictionary::law3_restriction::restriction_composes_by_construction`
/// - witness: `tests::vdc_dictionary::law3_restriction::terminal_loose_arrow_is_restriction_stable`
#[spec(requires: (&s.tgt, &t.tgt) == (&alpha.src, &alpha.tgt),
    ensures: |ref result| (&result.src, &result.tgt) == (&s.src, &t.src)
        && result.factors.len() == alpha.factors.len()
        && result.factors.iter().zip(&alpha.factors).all(|(restricted, original)| restricted.base == original.base))]
pub fn restrict(
    alpha: &LooseArrow,
    s: &SigMorphism,
    t: &SigMorphism,
) -> LooseArrow
{
    let factors = alpha
        .factors
        .iter()
        .map(|factor| FormalRestriction {
            left: compose(s, &factor.left),
            base: factor.base.clone(),
            right: compose(t, &factor.right),
        })
        .collect();
    LooseArrow {
        src: s.src.clone(),
        tgt: t.src.clone(),
        factors,
    }
}

/// Factors a framed cell through its restricted globular form: the frames
/// pushed into the codomain's formal restriction, identity frames left.
///
/// # Specification
/// - requires: the cell has well-formed frames composable with its codomain.
/// - ensures: the same domain and kind, the codomain restricted by the two
///   frames, and identity frames on its endpoints; the kind is kept, so the
///   factorization is data-identical.
/// - panics: malformed routed frames can panic during restriction.
///
/// # Adequacy
/// - hypothesis: L3 — a well-framed cell exposes exact domain, program,
///   restricted codomain and identity endpoint frames. These observers reject
///   altering the program, swapping frames or leaving a nonidentity frame; no
///   normalization of the program itself is claimed.
/// - witness: `tests::vdc_dictionary::law3_restriction::a_framed_cell_factors_data_identically_through_its_globular_form`
#[spec(requires: (&cell.left_frame.tgt, &cell.right_frame.tgt) == (&cell.cod.src, &cell.cod.tgt),
    ensures: |ref result| (&result.dom, &result.kind) == (&cell.dom, &cell.kind)
        && (&result.cod.src, &result.cod.tgt) == (&cell.left_frame.src, &cell.right_frame.src)
        && (&result.left_frame.src, &result.left_frame.tgt) == (&result.cod.src, &result.cod.src)
        && (&result.right_frame.src, &result.right_frame.tgt) == (&result.cod.tgt, &result.cod.tgt))]
pub fn factor_globular(cell: &Cell) -> Cell
{
    let cod = restrict(&cell.cod, &cell.left_frame, &cell.right_frame);
    let left_frame = SigMorphism::identity(&cod.src);
    let right_frame = SigMorphism::identity(&cod.tgt);
    Cell {
        dom: cell.dom.clone(),
        cod,
        left_frame,
        right_frame,
        kind: cell.kind.clone(),
    }
}

// ----------------------------------------------------------------------
// Instances: base and loose instances, boundaries computed on read
// ----------------------------------------------------------------------

/// An instance of a base loose arrow: a generating face under a ground
/// substitution, or a path, a finite reduction sequence.
///
/// Boundaries are computed on read ([`left_endpoint`], [`right_endpoint`]),
/// never stored.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum BaseInstance
{
    /// A generating-face instance.
    Gen
    {
        /// The generator's index into the named relation's faces.
        generator: GeneratorIndex,
        /// The ground substitution for the generator's variables.
        subst: Binding,
    },
    /// A path instance; `refl` is the empty step list.
    Path
    {
        /// The start term of the path.
        start: FreeTerm,
        /// The rewrite steps.
        steps: Vec<RewriteStep>,
    },
}

/// An instance of a loose arrow: one [`BaseInstance`] per factor.
#[repr(transparent)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct LooseInstance
{
    /// One base instance per `∧`-tuple factor.
    pub per_factor: Vec<BaseInstance>,
}

/// Equality of two base instances after boundary normalization: generating
/// instances compare on generator and substitution, paths on start and
/// steps.
///
/// # Specification
/// - ensures: equality exactly on the variant and all its stored payload
///   fields.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — generating instances varying index and substitution, and
///   paths varying start and steps, expose equality and inequality. This
///   rejects ignoring a payload field or equating the two variants; this
///   observer does not quotient paths by their endpoints.
/// - witness: `tests::vdc_dictionary::harness::tests::instance_equality_distinguishes_payloads_and_factor_order`
#[spec(ensures: |equal| bool::from(equal) == (left == right))]
fn base_instance_eq(
    left: &BaseInstance,
    right: &BaseInstance,
) -> LooseInstanceEquality
{
    let equal = match (left, right) {
        | (
            &BaseInstance::Gen {
                generator: left_generator,
                subst: ref left_subst,
            },
            &BaseInstance::Gen {
                generator: right_generator,
                subst: ref right_subst,
            },
        ) => left_generator == right_generator && left_subst == right_subst,
        | (
            &BaseInstance::Path {
                start: ref left_start,
                steps: ref left_steps,
            },
            &BaseInstance::Path {
                start: ref right_start,
                steps: ref right_steps,
            },
        ) => left_start == right_start && left_steps == right_steps,
        | (&BaseInstance::Gen { .. }, &BaseInstance::Path { .. })
        | (&BaseInstance::Path { .. }, &BaseInstance::Gen { .. }) => false,
    };
    LooseInstanceEquality::from(equal)
}

/// Equality of two loose instances, factorwise.
///
/// # Specification
/// - ensures: equality exactly when factor counts and ordered base instances
///   agree.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — empty, singleton and reordered two-factor instances
///   expose exact equality decisions. The observations reject zip-prefix
///   equality, dropping a factor or treating the tuple as a set; equality is of
///   stored instances, not merely their computed boundaries.
/// - witness: `tests::vdc_dictionary::harness::tests::instance_equality_distinguishes_payloads_and_factor_order`
#[spec(ensures: |equal| bool::from(equal) == (left == right))]
pub fn loose_instance_eq(
    left: &LooseInstance,
    right: &LooseInstance,
) -> LooseInstanceEquality
{
    LooseInstanceEquality::from(
        left.per_factor.len() == right.per_factor.len()
            && left
                .per_factor
                .iter()
                .zip(&right.per_factor)
                .all(|(one, other)| bool::from(base_instance_eq(one, other))),
    )
}

quenchant_shape::reason_enum! {
    /// Why an instance has no boundary under a formal restriction.
    pub mod endpoint {
        /// The reason no endpoint is read.
        #[derive(Clone, Copy, Debug, Eq, PartialEq)]
        pub enum Absent {
            /// The instance's shape does not fit the restriction's base: a
            /// generating instance over a path base, or a path over a named
            /// one.
            BaseMismatch,
            /// The instance names a generator the relation does not hold.
            UnknownGenerator,
            /// The path no longer replays.
            PathDeclined,
        }
    }
}

/// The face side a generating instance's endpoint reads.
#[derive(Clone, Copy)]
enum FaceSide
{
    /// The left-hand side.
    Lhs,
    /// The right-hand side.
    Rhs,
}

/// One side of a generating instance's face under its substitution.
///
/// # Specification
/// - ensures: the chosen side of the named generator under `subst`;
///   [`endpoint::Absent::BaseMismatch`] over a path base and
///   [`endpoint::Absent::UnknownGenerator`] for an absent generator.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — both generator sides under a nonidentity substitution
///   expose exact endpoint terms; a path base and first absent generator expose
///   distinct refusals. These observations reject swapping sides, forgetting
///   substitution or conflating absent generators with base mismatch; arbitrary
///   path endpoints use a separate reader.
/// - witness: `tests::vdc_dictionary::harness::tests::endpoint_reading_distinguishes_base_generator_and_path_failures`
/// - witness: `tests::vdc_dictionary::law3_restriction::instance_boundaries_are_computed_from_the_real_face_endpoints`
#[spec(ensures: |ref result| match *base {
    | BaseLoose::Path { .. } => matches!(*result, Maybe::Absent(endpoint::Absent::BaseMismatch)),
    | BaseLoose::Named(ref relation) => match relation.gens.get(usize::from(generator)) {
        | Some(face) => match *result {
            | Maybe::Present(ref image) => {
                let term = match side { FaceSide::Lhs => &face.lhs, FaceSide::Rhs => &face.rhs };
                image.to_node().vars().eq(term.to_node().vars().flat_map(|name| {
                    subst.get(name).into_iter().flat_map(|value| value.to_node().vars())
                        .chain(core::iter::once(name).filter(move |_| !subst.contains_key(name)))
                }))
            },
            | Maybe::Absent(_) => false,
        },
        | None => matches!(*result, Maybe::Absent(endpoint::Absent::UnknownGenerator)),
    },
})]
fn generator_side(
    base: &BaseLoose,
    generator: GeneratorIndex,
    subst: &Binding,
    side: FaceSide,
) -> Maybe<FreeTerm, endpoint::Absent>
{
    let BaseLoose::Named(ref rel) = *base
    else {
        return Maybe::Absent(endpoint::Absent::BaseMismatch);
    };
    let Some(face) = rel.gens.get(usize::from(generator))
    else {
        return Maybe::Absent(endpoint::Absent::UnknownGenerator);
    };
    let term = match side {
        | FaceSide::Lhs => &face.lhs,
        | FaceSide::Rhs => &face.rhs,
    };
    Maybe::Present(subst_term(term, subst))
}

/// The left boundary of a base instance under a formal restriction: the
/// generator's left-hand side under its substitution, or the path's start,
/// translated through the left frame.
///
/// # Specification
/// - ensures: as above; the reasons of the generating case otherwise.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — named generating instances and valid path instances
///   expose exact left endpoints through their left frames; unknown generators
///   and generating instances over path bases expose typed refusal. The
///   observations reject using the right face or frame, while a path left
///   endpoint reads its start rather than replaying its steps.
/// - witness: `tests::vdc_dictionary::harness::tests::endpoint_reading_distinguishes_base_generator_and_path_failures`
/// - witness: `tests::vdc_dictionary::law3_restriction::instance_boundaries_are_computed_from_the_real_face_endpoints`
#[spec(ensures: |ref result| match *instance {
    | BaseInstance::Path { ref start, .. } => match *result {
        | Maybe::Present(ref image) => image.to_node().vars().eq(start.to_node().vars()),
        | Maybe::Absent(_) => false,
    },
    | BaseInstance::Gen { generator, .. } => match factor.base {
        | BaseLoose::Path { .. } => matches!(*result, Maybe::Absent(endpoint::Absent::BaseMismatch)),
        | BaseLoose::Named(ref relation) => if usize::from(generator) < relation.gens.len() {
            matches!(*result, Maybe::Present(_))
        } else {
            matches!(*result, Maybe::Absent(endpoint::Absent::UnknownGenerator))
        },
    },
})]
pub fn left_endpoint(
    factor: &FormalRestriction,
    instance: &BaseInstance,
) -> Maybe<FreeTerm, endpoint::Absent>
{
    let raw = match *instance {
        | BaseInstance::Gen {
            generator,
            ref subst,
        } => generator_side(&factor.base, generator, subst, FaceSide::Lhs),
        | BaseInstance::Path { ref start, .. } => Maybe::Present(start.clone()),
    };
    raw.map(|raw| apply_term(&factor.left, DescriptorFactorIndex::from(0_usize), &raw))
}

/// The right boundary of a base instance under a formal restriction: the
/// generator's right-hand side under its substitution, or the path's
/// endpoint over the path base's rules, translated through the right frame.
///
/// # Specification
/// - ensures: as above; [`endpoint::Absent::BaseMismatch`] for a path over a
///   named base or a terminal path object, and
///   [`endpoint::Absent::PathDeclined`] when the path no longer replays.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — generating instances and empty/nonempty valid paths
///   expose exact right endpoints; wrong bases, terminal path objects, missing
///   generators and invalid paths expose their separate reasons. These
///   observations reject returning the start, using the left frame or
///   conflating refusal classes; multi-factor path semantics are not
///   established.
/// - witness: `tests::vdc_dictionary::harness::tests::endpoint_reading_distinguishes_base_generator_and_path_failures`
/// - witness: `tests::vdc_dictionary::law3_restriction::instance_boundaries_are_computed_from_the_real_face_endpoints`
#[spec(ensures: |ref result| match *result {
    | Maybe::Present(_) => match *instance {
        | BaseInstance::Gen { generator, .. } => matches!(factor.base, BaseLoose::Named(ref relation) if usize::from(generator) < relation.gens.len()),
        | BaseInstance::Path { ref steps, .. } => matches!(factor.base, BaseLoose::Path { ref sig }
            if sig.factors.first().is_some_and(|description| steps.iter().all(|step| usize::from(step.cell) < description.rules.len()))),
    },
    | Maybe::Absent(endpoint::Absent::UnknownGenerator) => matches!(*instance, BaseInstance::Gen { generator, .. }
        if matches!(factor.base, BaseLoose::Named(ref relation) if usize::from(generator) >= relation.gens.len())),
    | Maybe::Absent(endpoint::Absent::PathDeclined) => matches!(*instance, BaseInstance::Path { .. })
        && matches!(factor.base, BaseLoose::Path { ref sig } if !sig.factors.is_empty()),
    | Maybe::Absent(endpoint::Absent::BaseMismatch) => match (instance, &factor.base) {
        | (&BaseInstance::Gen { .. }, &BaseLoose::Path { .. })
        | (&BaseInstance::Path { .. }, &BaseLoose::Named(_)) => true,
        | (&BaseInstance::Path { .. }, &BaseLoose::Path { ref sig }) => sig.factors.is_empty(),
        | (&BaseInstance::Gen { .. }, &BaseLoose::Named(_)) => false,
    },
})]
pub fn right_endpoint(
    factor: &FormalRestriction,
    instance: &BaseInstance,
) -> Maybe<FreeTerm, endpoint::Absent>
{
    let raw = match *instance {
        | BaseInstance::Gen {
            generator,
            ref subst,
        } => generator_side(&factor.base, generator, subst, FaceSide::Rhs),
        | BaseInstance::Path {
            ref start,
            ref steps,
        } => {
            let BaseLoose::Path { ref sig } = factor.base
            else {
                return Maybe::Absent(endpoint::Absent::BaseMismatch);
            };
            let Some(first_factor) = sig.factors.first()
            else {
                return Maybe::Absent(endpoint::Absent::BaseMismatch);
            };
            match apply_path(start, steps, &first_factor.rules) {
                | Maybe::Present(end) => Maybe::Present(end),
                | Maybe::Absent(_) => Maybe::Absent(endpoint::Absent::PathDeclined),
            }
        },
    };
    raw.map(|raw| apply_term(&factor.right, DescriptorFactorIndex::from(0_usize), &raw))
}

// ----------------------------------------------------------------------
// Cells: the stand-in for certificate-backed transformations
// ----------------------------------------------------------------------

/// A clause of a clause-program cell: the expected generator at each input
/// position, and the generator and variable templates to emit at each
/// codomain factor.
///
/// A template is a term over namespaced input variables spelled `p{i}.{v}`
/// — input `i`'s bound variable `v` — instantiated at replay.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CellClause
{
    /// The expected generator per input position.
    pub matches: Vec<GeneratorIndex>,
    /// Per codomain factor: the emitted generator and its variable
    /// templates.
    pub emit: Vec<(GeneratorIndex, Binding)>,
}

/// One step of a cell program.
#[derive(Clone, Debug, Eq, PartialEq)]
enum CellOp
{
    /// The identity on a single loose arrow.
    Ident,
    /// A clause program: the first matching clause emits the output.
    Clauses(Vec<CellClause>),
    /// The pairing of the two subprograms before it, sharing a domain.
    Pair,
    /// The projection onto a codomain factor.
    Proj
    {
        /// The factor projected out.
        idx: DescriptorFactorIndex,
    },
    /// The unique cell into `⊤`.
    Bang,
    /// Path induction over the subprogram before it: `(a, refl, b) ↦
    /// base(a, b)`, declining on a non-empty path.
    PathInd,
}

/// One entry of a cell program: its step and the extent of the subprogram
/// it roots.
#[derive(Clone, Debug, Eq, PartialEq)]
struct CellStep
{
    /// The step.
    op: CellOp,
    /// The steps the subprogram rooted here spans, itself included.
    extent: StepExtent,
}

/// The kind of a multi-ary cell, held as a flat program: each composite
/// step follows the subprograms of its parts, the root last.
///
/// Flat, so a cell owns no cell and a composite of any depth is built,
/// compared and replayed without recursion.
#[repr(transparent)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CellKind
{
    /// The program in post-order.
    steps: Vec<CellStep>,
}

/// The root step of a cell program, read without its parts.
#[derive(Clone, Copy, Debug)]
pub enum CellView<'kind>
{
    /// The identity.
    Ident,
    /// A clause program.
    Clauses(&'kind [CellClause]),
    /// A pairing.
    Pair,
    /// A projection.
    Proj
    {
        /// The factor projected out.
        idx: DescriptorFactorIndex,
    },
    /// The cell into `⊤`.
    Bang,
    /// A path induction.
    PathInd,
}

impl CellKind
{
    /// A one-step program.
    ///
    /// # Specification
    /// trivial.
    fn single(op: CellOp) -> Self
    {
        Self {
            steps: vec![CellStep {
                op,
                extent: StepExtent::from(1_usize),
            }],
        }
    }

    /// A composite step over the given parts' programs, in order.
    ///
    /// # Specification
    /// - ensures: the parts' programs concatenated, then `op` spanning them all
    ///   and itself.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — nested pair and unary programs expose child root
    ///   indices and replayed ordered outputs. These observations reject
    ///   reversing concatenation, omitting a root or recording the wrong
    ///   subtree extent; the evidence is for finite programs, not the
    ///   no-recursion space claim.
    /// - witness: `tests::vdc_dictionary::harness::tests::cell_program_parts_follow_nested_extents`
    /// - witness: `tests::vdc_dictionary::law4_cartesian::projection_pairing_bijection_holds_up_to_replay`
    #[spec(captures: tag = core::mem::discriminant(&op),
        ensures: |ref program| program.steps.last().is_some_and(|root|
            usize::from(root.extent) == program.steps.len() && core::mem::discriminant(&root.op) == tag)
            && program.steps.iter().take(program.steps.len().saturating_sub(1))
                .eq(parts.iter().flat_map(|part| &part.steps)))]
    fn over(
        op: CellOp,
        parts: &[&Self],
    ) -> Self
    {
        let mut steps: Vec<CellStep> = parts
            .iter()
            .flat_map(|part| part.steps.iter().cloned())
            .collect();
        let extent = StepExtent::from(steps.len().saturating_add(1));
        steps.push(CellStep { op, extent });
        Self { steps }
    }

    /// The identity cell's kind.
    ///
    /// # Specification
    /// trivial.
    pub fn ident() -> Self
    {
        Self::single(CellOp::Ident)
    }

    /// A clause program.
    ///
    /// # Specification
    /// trivial.
    pub fn clauses(clauses: Vec<CellClause>) -> Self
    {
        Self::single(CellOp::Clauses(clauses))
    }

    /// The pairing of two cells sharing a domain (cartesian introduction).
    ///
    /// # Specification
    /// - requires: both cells have the same domain chain.
    /// - ensures: the left program precedes the right under a pairing root.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — same-domain cells expose both projection beta laws
    ///   and ordered paired replay. These observations reject exchanging the
    ///   two parts or giving them different inputs; the constructor does not
    ///   establish pairing for different domains.
    /// - witness: `tests::vdc_dictionary::law4_cartesian::projection_pairing_bijection_holds_up_to_replay`
    /// - witness: `tests::vdc_dictionary::harness::tests::cell_program_parts_follow_nested_extents`
    #[spec(requires: left.dom == right.dom,
        ensures: |ref program| matches!(program.view(), CellView::Pair)
            && program.steps.len() == left.kind.steps.len().saturating_add(right.kind.steps.len()).saturating_add(1))]
    pub fn pair(
        left: &Cell,
        right: &Cell,
    ) -> Self
    {
        Self::over(CellOp::Pair, &[&left.kind, &right.kind])
    }

    /// The projection onto codomain factor `idx`.
    ///
    /// # Specification
    /// trivial.
    pub fn proj(idx: DescriptorFactorIndex) -> Self
    {
        Self::single(CellOp::Proj { idx })
    }

    /// The unique cell into `⊤`.
    ///
    /// # Specification
    /// trivial.
    pub fn bang() -> Self
    {
        Self::single(CellOp::Bang)
    }

    /// Path induction over a base cell.
    ///
    /// # Specification
    /// trivial.
    pub fn path_ind(base: &Cell) -> Self
    {
        Self::over(CellOp::PathInd, &[&base.kind])
    }

    /// The root step.
    ///
    /// # Specification
    /// trivial.
    pub fn view(&self) -> CellView<'_>
    {
        self.view_at(self.root())
    }

    /// The step at `at`.
    ///
    /// # Specification
    /// - requires: `at` indexes the program.
    /// - panics: otherwise, a harness error.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — valid nested program roots expose their operation
    ///   variants through replay, while the first index beyond a one-step
    ///   program panics. The observations reject treating every root as a leaf
    ///   or indexing the wrong step; the input index must belong to this
    ///   program.
    /// - witness: `tests::vdc_dictionary::harness::tests::cell_program_parts_follow_nested_extents`
    /// - witness: `tests::vdc_dictionary::harness::tests::replay_distinguishes_arity_projection_pairing_and_path_refusals`
    #[spec(requires: usize::from(at) < self.steps.len())]
    fn view_at(
        &self,
        at: StepIndex,
    ) -> CellView<'_>
    {
        match self.steps[usize::from(at)].op {
            | CellOp::Ident => CellView::Ident,
            | CellOp::Clauses(ref clauses) => CellView::Clauses(clauses),
            | CellOp::Pair => CellView::Pair,
            | CellOp::Proj { idx } => CellView::Proj { idx },
            | CellOp::Bang => CellView::Bang,
            | CellOp::PathInd => CellView::PathInd,
        }
    }

    /// The root step's index.
    ///
    /// # Specification
    /// trivial.
    fn root(&self) -> StepIndex
    {
        StepIndex::from(self.steps.len().saturating_sub(1))
    }

    /// The root of the subprogram ending just before `at`, and the root of
    /// the one before that.
    ///
    /// # Specification
    /// - requires: `at` roots a composite with two parts.
    /// - ensures: `(first, second)`: the parts' roots in program order.
    /// - panics: on a malformed program, a harness error.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — left- and right-nested pairs expose exact child roots
    ///   and ordered replay. Their different right-subtree extents distinguish
    ///   fixed-offset guesses, reversed roots and subtracting the left extent;
    ///   only well-formed binary composite roots are in the domain.
    /// - witness: `tests::vdc_dictionary::harness::tests::cell_program_parts_follow_nested_extents`
    #[spec(requires: usize::from(at) >= 2
        && self.steps.get(usize::from(at)).is_some_and(|root| matches!(root.op, CellOp::Pair))
        && self.steps.get(usize::from(at).saturating_sub(1)).is_some_and(|right|
            usize::from(right.extent) > 0 && usize::from(right.extent) < usize::from(at)),
        ensures: |roots| usize::from(roots.1).checked_add(1) == Some(usize::from(at))
            && usize::from(roots.0) < usize::from(roots.1)
            && self.steps.get(usize::from(roots.1)).is_some_and(|right|
                usize::from(roots.0).checked_add(usize::from(right.extent)) == Some(usize::from(roots.1))))]
    fn two_parts(
        &self,
        at: StepIndex,
    ) -> (StepIndex, StepIndex)
    {
        let second = usize::from(at)
            .checked_sub(1)
            .expect("a composite follows its parts");
        let first = second
            .checked_sub(usize::from(self.steps[second].extent))
            .expect("a pairing follows two parts");
        (StepIndex::from(first), StepIndex::from(second))
    }

    /// The root of the subprogram ending just before `at`.
    ///
    /// # Specification
    /// - requires: `at` roots a composite with one part.
    /// - panics: on a malformed program, a harness error.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a unary root over a nested program exposes the
    ///   immediately preceding child root and its replay; zero refuses. These
    ///   observations reject an off-by-one result and saturating zero; the
    ///   index alone cannot validate the surrounding program shape.
    /// - witness: `tests::vdc_dictionary::harness::tests::cell_program_parts_follow_nested_extents`
    /// - witness: `tests::vdc_dictionary::law5_units::path_induction_satisfies_beta_on_refl`
    #[spec(requires: usize::from(at) > 0,
        ensures: |part| usize::from(part).checked_add(1) == Some(usize::from(at)))]
    fn one_part(at: StepIndex) -> StepIndex
    {
        StepIndex::from(
            usize::from(at)
                .checked_sub(1)
                .expect("a composite follows its part"),
        )
    }
}

/// A multi-ary cell `dom ⇒ cod` framed by two tight arrows.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Cell
{
    /// The domain chain of loose arrows.
    pub dom: Vec<LooseArrow>,
    /// The codomain loose arrow.
    pub cod: LooseArrow,
    /// The left frame.
    pub left_frame: SigMorphism,
    /// The right frame.
    pub right_frame: SigMorphism,
    /// The cell's kind.
    pub kind: CellKind,
}

quenchant_shape::reason_enum! {
    /// Why a replay produces nothing.
    pub mod replay_outcome {
        /// The reason the cell declined.
        #[derive(Clone, Copy, Debug, Eq, PartialEq)]
        pub enum Absent {
            /// The inputs do not fit the cell: a wrong input count, no
            /// matching clause, an absent projected factor, or a non-empty
            /// path under path induction.
            Declined,
        }
    }
}

/// One pending frame of a replay.
enum ReplayFrame
{
    /// Replay the subprogram rooted at `at` on the inputs.
    Eval
    {
        /// The subprogram's root.
        at: StepIndex,
        /// The inputs it is replayed on.
        inputs: Vec<LooseInstance>,
    },
    /// The left part of a pairing has replayed; replay the right part.
    PairRight
    {
        /// The right part's root.
        right: StepIndex,
        /// The shared inputs.
        inputs: Vec<LooseInstance>,
    },
    /// Both parts of a pairing have replayed; concatenate them.
    PairCombine
    {
        /// The left part's output.
        left_out: LooseInstance,
    },
}

/// Replays a cell on a chain of input instances: the checker. Partial: a
/// decline is data, not an error.
///
/// # Specification
/// - ensures: the identity passes its one input through; the cell into `⊤`
///   emits the empty instance; a projection emits its factor of the first
///   input; a clause program emits what its first matching clause emits; a
///   pairing emits the concatenated outputs of its parts, each replayed on the
///   shared inputs; path induction replays its base on the outer inputs when
///   the middle input is `refl`. Every other case is
///   [`replay_outcome::Absent::Declined`].
/// - panics: none.
/// - intension: an explicit frame stack over the flat program, so a composite
///   of any depth replays without recursion.
///
/// # Adequacy
/// - hypothesis: L3 — well-formed identity, terminal, projection, paired and
///   path-induction programs expose exact outputs or typed refusal for wrong
///   arity, missing factors and nonreflexive paths. Nested pairs reject swapped
///   output order or failure masking; these observations concern replay, not
///   validation of declared cell boundaries.
/// - witness: `tests::vdc_dictionary::harness::tests::replay_distinguishes_arity_projection_pairing_and_path_refusals`
/// - witness: `tests::vdc_dictionary::harness::tests::clause_replay_uses_first_match_and_namespaced_bindings`
/// - witness: `tests::vdc_dictionary::harness::tests::cell_program_parts_follow_nested_extents`
/// - witness: `tests::vdc_dictionary::law5_units::path_induction_satisfies_beta_on_refl`
#[spec(ensures: |ref result| match cell.kind.view() {
    | CellView::Ident => if inputs.len() == 1 {
        matches!(*result, Maybe::Present(ref output) if Some(output) == inputs.first())
    } else { matches!(*result, Maybe::Absent(replay_outcome::Absent::Declined)) },
    | CellView::Bang => matches!(*result, Maybe::Present(ref output) if output.per_factor.is_empty()),
    | CellView::Proj { idx } => match inputs.first().and_then(|input| input.per_factor.get(usize::from(idx))) {
        | Some(factor) => matches!(*result, Maybe::Present(ref output) if output.per_factor.len() == 1 && output.per_factor.first() == Some(factor)),
        | None => matches!(*result, Maybe::Absent(replay_outcome::Absent::Declined)),
    },
    | CellView::PathInd => !matches!(*result, Maybe::Present(_))
        || (inputs.len() >= 3 && inputs.get(1).and_then(|middle| middle.per_factor.first())
            .is_some_and(|middle| matches!(*middle, BaseInstance::Path { ref steps, .. } if steps.is_empty()))),
    | CellView::Clauses(_) | CellView::Pair => true,
})]
pub fn replay(
    cell: &Cell,
    inputs: &[LooseInstance],
) -> Maybe<LooseInstance, replay_outcome::Absent>
{
    let declined = Maybe::Absent(replay_outcome::Absent::Declined);
    let kind = &cell.kind;
    let mut stack = vec![ReplayFrame::Eval {
        at: kind.root(),
        inputs: inputs.to_vec(),
    }];
    let mut last: Maybe<LooseInstance, replay_outcome::Absent> = declined.clone();
    while let Some(frame) = stack.pop() {
        match frame {
            | ReplayFrame::Eval { at, inputs } => match kind.view_at(at) {
                | CellView::Ident => {
                    last = match *inputs.as_slice() {
                        | [ref only] => Maybe::Present(only.clone()),
                        | _ => declined.clone(),
                    };
                },
                | CellView::Bang => {
                    last = Maybe::Present(LooseInstance {
                        per_factor: Vec::new(),
                    });
                },
                | CellView::Proj { idx } => {
                    last = match inputs
                        .first()
                        .and_then(|instance| instance.per_factor.get(usize::from(idx)))
                    {
                        | Some(factor) => Maybe::Present(LooseInstance {
                            per_factor: vec![factor.clone()],
                        }),
                        | None => declined.clone(),
                    };
                },
                | CellView::Clauses(clauses) => last = replay_clauses(clauses, &inputs),
                | CellView::Pair => {
                    let (left, right) = kind.two_parts(at);
                    stack.push(ReplayFrame::PairRight {
                        right,
                        inputs: inputs.clone(),
                    });
                    stack.push(ReplayFrame::Eval { at: left, inputs });
                },
                | CellView::PathInd => {
                    let refl_middle = inputs.get(1).and_then(|middle| middle.per_factor.first());
                    match (inputs.first(), refl_middle, inputs.get(2)) {
                        | (
                            Some(left_input),
                            Some(&BaseInstance::Path { ref steps, .. }),
                            Some(right_input),
                        ) if steps.is_empty() => {
                            stack.push(ReplayFrame::Eval {
                                at: CellKind::one_part(at),
                                inputs: vec![left_input.clone(), right_input.clone()],
                            });
                        },
                        | _ => last = declined.clone(),
                    }
                },
            },
            | ReplayFrame::PairRight { right, inputs } => {
                let Maybe::Present(left_out) = core::mem::replace(&mut last, declined.clone())
                else {
                    continue;
                };
                stack.push(ReplayFrame::PairCombine { left_out });
                stack.push(ReplayFrame::Eval { at: right, inputs });
            },
            | ReplayFrame::PairCombine { left_out } => {
                let Maybe::Present(right_out) = core::mem::replace(&mut last, declined.clone())
                else {
                    continue;
                };
                let mut per_factor = left_out.per_factor;
                per_factor.extend(right_out.per_factor);
                last = Maybe::Present(LooseInstance { per_factor });
            },
        }
    }
    last
}

/// Replays a clause program: the first clause whose expected generators
/// agree with the inputs' leading instances fires.
///
/// # Specification
/// - ensures: one generating instance per codomain factor of the firing clause,
///   its templates instantiated over the inputs' bindings namespaced
///   `p{i}.{v}`; [`replay_outcome::Absent::Declined`] when no clause fires.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — zero- and two-input clauses, repeated matching clauses
///   and disjoint namespaced bindings expose exact emitted generators and
///   instantiated templates. Wrong count, missing factors, path inputs and
///   generator mismatch refuse; these observations reject choosing the last
///   clause or conflating identically named variables across inputs, without
///   validating relation boundaries.
/// - witness: `tests::vdc_dictionary::harness::tests::clause_replay_uses_first_match_and_namespaced_bindings`
#[spec(ensures: |ref result| {
    let eligible = clauses.iter().find(|clause| clause.matches.len() == inputs.len()
        && clause.matches.iter().zip(inputs).all(|(expected, input)| matches!(input.per_factor.first(),
            Some(&BaseInstance::Gen { generator, .. }) if generator == *expected)));
    match *result {
        | Maybe::Present(ref output) => eligible.is_some_and(|clause|
            output.per_factor.len() == clause.emit.len()
                && output.per_factor.iter().zip(&clause.emit).all(|(factor, emitted)| match *factor {
                    | BaseInstance::Gen { generator, ref subst } => generator == emitted.0 && subst.keys().eq(emitted.1.keys()),
                    | BaseInstance::Path { .. } => false,
                })),
        | Maybe::Absent(replay_outcome::Absent::Declined) => eligible.is_none(),
    }
})]
fn replay_clauses(
    clauses: &[CellClause],
    inputs: &[LooseInstance],
) -> Maybe<LooseInstance, replay_outcome::Absent>
{
    'clauses: for clause in clauses {
        if clause.matches.len() != inputs.len() {
            continue;
        }
        let mut env = Binding::new();
        for (position, (instance, &expected)) in inputs.iter().zip(&clause.matches).enumerate() {
            match instance.per_factor.first() {
                | Some(&BaseInstance::Gen {
                    generator,
                    ref subst,
                }) if generator == expected => {
                    for (variable, term) in subst {
                        env.insert(Name::from(format!("p{position}.{variable}")), term.clone());
                    }
                },
                | _ => continue 'clauses,
            }
        }
        let per_factor = clause
            .emit
            .iter()
            .map(|&(generator, ref templates)| BaseInstance::Gen {
                generator,
                subst: templates
                    .iter()
                    .map(|(variable, template)| (variable.clone(), subst_term(template, &env)))
                    .collect(),
            })
            .collect();
        return Maybe::Present(LooseInstance { per_factor });
    }
    Maybe::Absent(replay_outcome::Absent::Declined)
}

/// Replay-level composition: each inner cell replayed on its own inputs,
/// then the outer cell on their outputs. Always available, whether or not
/// [`graft`] supports the shapes symbolically.
///
/// # Specification
/// - requires: every inner cell has one corresponding input chain.
/// - ensures: the outer cell's replay on the inner outputs in order;
///   [`replay_outcome::Absent::Declined`] when any replay declines.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — matched inner/input lists expose exact staged outputs,
///   including a shape unsupported by symbolic grafting; either an inner or the
///   outer can decline. These observations reject dropping an inner or masking
///   its refusal; unmatched lists are outside the replay-composition domain.
/// - witness: `tests::vdc_dictionary::harness::tests::replay_composition_propagates_inner_and_outer_refusal`
/// - witness: `tests::vdc_dictionary::law2_cells::symbolic_graft_agrees_with_replay_composition`
/// - witness: `tests::vdc_dictionary::law2_cells::unsupported_shapes_decline_symbolically_but_replay_composes`
#[spec(requires: inners.len() == inner_inputs.len())]
pub fn replay_compose(
    outer: &Cell,
    inners: &[&Cell],
    inner_inputs: &[Vec<LooseInstance>],
) -> Maybe<LooseInstance, replay_outcome::Absent>
{
    let mut middle = Vec::new();
    for (inner, inputs) in inners.iter().zip(inner_inputs) {
        match replay(inner, inputs) {
            | Maybe::Present(output) => middle.push(output),
            | Maybe::Absent(reason) => return Maybe::Absent(reason),
        }
    }
    replay(outer, &middle)
}

/// Replay-equivalence over a supplied corpus of input chains: the identity of
/// cells.
///
/// # Specification
/// - ensures: positive exactly when, on every corpus entry, both cells decline
///   or both fire with factorwise-equal outputs.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — empty and finite input corpora expose vacuous agreement,
///   equal outputs, unequal outputs, two refusals and one-sided refusal. These
///   observations reject equating success with failure or ignoring a differing
///   factor; corpus agreement is not universal cell equality.
/// - witness: `tests::vdc_dictionary::harness::tests::sample_equality_observes_disagreement_and_vacuity`
/// - witness: `tests::vdc_dictionary::law2_cells::grafting_is_associative_up_to_replay`
/// - witness: `tests::vdc_dictionary::law5_units::distinct_bases_give_distinct_inductions_at_refl`
#[spec(ensures: |equal| !(corpus.is_empty() || left == right) || bool::from(equal))]
pub fn cells_equal(
    left: &Cell,
    right: &Cell,
    corpus: &[Vec<LooseInstance>],
) -> CellEquivalence
{
    CellEquivalence::from(corpus.iter().all(|inputs| {
        match (replay(left, inputs), replay(right, inputs)) {
            | (Maybe::Absent(_), Maybe::Absent(_)) => true,
            | (Maybe::Present(ref one), Maybe::Present(ref other)) => {
                bool::from(loose_instance_eq(one, other))
            },
            | (Maybe::Present(_), Maybe::Absent(_)) | (Maybe::Absent(_), Maybe::Present(_)) => {
                false
            },
        }
    }))
}

quenchant_shape::reason_enum! {
    /// Why a symbolic graft is not produced.
    pub mod graft_outcome {
        /// The reason the graft declined.
        #[derive(Clone, Copy, Debug, Eq, PartialEq)]
        pub enum Absent {
            /// The shapes are outside the supported ones; replay-level
            /// composition still carries the composite.
            Unsupported,
        }
    }
}

/// Symbolic grafting, multicategorical composition: the inner cells
/// substituted for the outer cell's inputs.
///
/// # Specification
/// - ensures: the sole inner under an identity outer; the outer over
///   all-identity inners; the composed clause over a linear single-clause
///   chain; [`graft_outcome::Absent::Unsupported`] for every other shape.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — identity and linear clause grafts expose replay equal to
///   staged composition; empty, nonlinear and unsupported program shapes expose
///   refusal. These observations reject losing a unit, reversing template
///   substitution or accepting unsupported shapes; no symbolic graft for
///   general programs is claimed.
/// - witness: `tests::vdc_dictionary::law2_cells::grafting_is_unital_up_to_replay`
/// - witness: `tests::vdc_dictionary::law2_cells::symbolic_graft_agrees_with_replay_composition`
/// - witness: `tests::vdc_dictionary::harness::tests::graft_refuses_each_unsupported_clause_shape`
#[spec(ensures: |ref result| if matches!(outer.kind.view(), CellView::Ident) && inners.len() == 1 {
    matches!(*result, Maybe::Present(ref cell) if Some(cell) == inners.first())
} else if !inners.is_empty() && inners.iter().all(|inner| matches!(inner.kind.view(), CellView::Ident)) {
    matches!(*result, Maybe::Present(ref cell) if cell == outer)
} else {
    match *result {
        | Maybe::Present(ref cell) => inners.len() == 1
            && matches!(outer.kind.view(), CellView::Clauses(_))
            && inners.first().is_some_and(|inner| matches!(inner.kind.view(), CellView::Clauses(_))
                && cell.dom.eq(&inner.dom) && cell.cod.eq(&outer.cod)),
        | Maybe::Absent(graft_outcome::Absent::Unsupported) => true,
    }
})]
pub fn graft(
    outer: &Cell,
    inners: &[Cell],
) -> Maybe<Cell, graft_outcome::Absent>
{
    let view = outer.kind.view();
    if matches!(view, CellView::Ident)
        && let [ref only] = *inners
    {
        return Maybe::Present(only.clone());
    }
    if !inners.is_empty()
        && inners
            .iter()
            .all(|inner| matches!(inner.kind.view(), CellView::Ident))
    {
        return Maybe::Present(outer.clone());
    }
    if let CellView::Clauses(outer_clauses) = view
        && let [ref inner] = *inners
        && let CellView::Clauses(inner_clauses) = inner.kind.view()
    {
        return graft_linear_clause(outer, outer_clauses, inner, inner_clauses);
    }
    Maybe::Absent(graft_outcome::Absent::Unsupported)
}

/// Grafts a single-clause, single-input outer over a single-clause inner
/// with one output, composing the emit templates through the matched middle
/// generator.
///
/// # Specification
/// - ensures: one clause matching the inner's inputs and emitting the outer's
///   templates with the outer's `p0.*` variables replaced by the inner's
///   templates; [`graft_outcome::Absent::Unsupported`] when either side has
///   other than one clause, the outer other than one input, the inner other
///   than one output, or the generators disagree.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — single-clause linear chains expose the composed replay
///   and templates; zero or multiple clauses, wrong outer match count, wrong
///   inner emit count and mismatched middle generators each refuse. These
///   observations reject weakening any shape conjunct; the evidence does not
///   establish grafting for nonlinear programs.
/// - witness: `tests::vdc_dictionary::harness::tests::graft_refuses_each_unsupported_clause_shape`
/// - witness: `tests::vdc_dictionary::law2_cells::symbolic_graft_agrees_with_replay_composition`
/// - witness: `tests::vdc_dictionary::law2_cells::grafting_is_associative_up_to_replay`
#[spec(ensures: |ref result| {
    let eligible = outer_clauses.first().zip(inner_clauses.first()).filter(|pair|
        outer_clauses.len() == 1 && inner_clauses.len() == 1
            && pair.0.matches.len() == 1 && pair.1.emit.len() == 1
            && pair.0.matches.first() == pair.1.emit.first().map(|entry| &entry.0));
    match *result {
        | Maybe::Present(ref composite) => eligible.is_some_and(|(outer_clause, inner_clause)|
            composite.dom.eq(&inner.dom) && composite.cod.eq(&outer.cod)
                && composite.left_frame.eq(&inner.left_frame) && composite.right_frame.eq(&outer.right_frame)
                && match composite.kind.view() {
                    | CellView::Clauses(clauses) => clauses.len() == 1 && clauses.first().is_some_and(|clause|
                        clause.matches == inner_clause.matches
                            && clause.emit.iter().map(|entry| entry.0).eq(outer_clause.emit.iter().map(|entry| entry.0))
                            && clause.emit.iter().zip(&outer_clause.emit).all(|(emitted, template)| emitted.1.keys().eq(template.1.keys()))),
                    | _ => false,
                }),
        | Maybe::Absent(graft_outcome::Absent::Unsupported) => eligible.is_none(),
    }
})]
fn graft_linear_clause(
    outer: &Cell,
    outer_clauses: &[CellClause],
    inner: &Cell,
    inner_clauses: &[CellClause],
) -> Maybe<Cell, graft_outcome::Absent>
{
    let unsupported = Maybe::Absent(graft_outcome::Absent::Unsupported);
    let [ref outer_clause] = *outer_clauses
    else {
        return unsupported;
    };
    let [ref inner_clause] = *inner_clauses
    else {
        return unsupported;
    };
    let [outer_match] = *outer_clause.matches.as_slice()
    else {
        return unsupported;
    };
    let [(inner_emit, ref inner_templates)] = *inner_clause.emit.as_slice()
    else {
        return unsupported;
    };
    if outer_match != inner_emit {
        return unsupported;
    }
    let middle: Binding = inner_templates
        .iter()
        .map(|(variable, template)| (Name::from(format!("p0.{variable}")), template.clone()))
        .collect();
    let emit = outer_clause
        .emit
        .iter()
        .map(|&(generator, ref templates)| {
            let composed = templates
                .iter()
                .map(|(variable, template)| (variable.clone(), subst_term(template, &middle)))
                .collect();
            (generator, composed)
        })
        .collect();
    Maybe::Present(Cell {
        dom: inner.dom.clone(),
        cod: outer.cod.clone(),
        left_frame: inner.left_frame.clone(),
        right_frame: outer.right_frame.clone(),
        kind: CellKind::clauses(vec![CellClause {
            matches: inner_clause.matches.clone(),
            emit,
        }]),
    })
}

// ----------------------------------------------------------------------
// The saturation probe: instances closed under path action
// ----------------------------------------------------------------------

/// A saturated instance: a generating instance together with an absorbed
/// boundary path.
///
/// The shape the unit's universal property needs to be bijective: instances
/// closed under path action. Hand-built for one worked example, not a
/// general mechanism.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SaturatedInstance
{
    /// The generating instance whose left endpoint the path transports.
    pub generator: BaseInstance,
    /// The absorbed boundary path; empty is `refl`.
    pub absorbed: Vec<RewriteStep>,
    /// The start term of the absorbed path.
    pub path_start: FreeTerm,
}

/// Replays path induction on a saturated middle: the absorbed path
/// transports the left endpoint to meet the right, then the base fires.
///
/// On an empty path this is the `refl` case, so the value agrees with
/// [`replay`] of a path induction; on a non-empty path it is defined, which
/// shows the saturation invariant sufficient, not merely necessary.
///
/// # Specification
/// - ensures: the base's replay on the two outer inputs when the absorbed path
///   replays over `cells`; [`replay_outcome::Absent::Declined`] when it does
///   not.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — empty and valid nonempty absorbed paths expose the base
///   replay; an unknown rule or invalid position declines before even a total
///   terminal base can fire. These observations reject bypassing path
///   validation, while the worked saturation model does not prove a general
///   endpoint-alignment invariant.
/// - witness: `tests::vdc_dictionary::harness::tests::saturated_replay_requires_a_replayable_absorbed_path`
/// - witness: `tests::vdc_dictionary::law5_units::saturation_makes_the_non_refl_value_defined_and_beta_compatible`
#[spec(ensures: |ref result| match *result {
    | Maybe::Present(ref output) => saturated.absorbed.iter().all(|step| usize::from(step.cell) < cells.len())
        && (!matches!(base.kind.view(), CellView::Bang) || output.per_factor.is_empty()),
    | Maybe::Absent(replay_outcome::Absent::Declined) => true,
})]
pub fn replay_path_ind_saturated(
    base: &Cell,
    left_input: &LooseInstance,
    saturated: &SaturatedInstance,
    right_input: &LooseInstance,
    cells: &[RuleFace],
) -> Maybe<LooseInstance, replay_outcome::Absent>
{
    match apply_path(&saturated.path_start, &saturated.absorbed, cells) {
        | Maybe::Present(_) => replay(base, &[left_input.clone(), right_input.clone()]),
        | Maybe::Absent(_) => Maybe::Absent(replay_outcome::Absent::Declined),
    }
}

#[cfg(test)]
mod tests
{
    use gandr_theory_levitation::TermPositionIndex;

    use super::*;
    use crate::vdc_dictionary::fixtures;

    #[test]
    fn tight_products_observe_zero_and_multiple_factors()
    {
        let terminal = SigObj::terminal();
        assert_eq!(
            SigMorphism::diagonal(&terminal),
            SigMorphism::terminal(&terminal)
        );
        let a = fixtures::nat_obj(&fixtures::nat_names("a".into()));
        let b = fixtures::nat_obj(&fixtures::nat_names("b".into()));
        let product = SigObj::product(&a, &b);
        let diagonal = SigMorphism::diagonal(&product);
        assert_eq!(diagonal.tgt, SigObj {
            factors: [
                a.factors.clone(),
                b.factors.clone(),
                a.factors,
                b.factors.clone()
            ]
            .concat()
        });
        assert_eq!(
            diagonal
                .routes
                .iter()
                .map(|route| usize::from(route.src_factor))
                .collect::<Vec<_>>(),
            [0, 1, 0, 1]
        );
        assert!(check_morphism(&diagonal).is_empty());
        let projection = SigMorphism::projection(&product, DescriptorFactorIndex::from(1_usize));
        assert_eq!(projection.tgt, b);
        assert_eq!(
            projection
                .routes
                .iter()
                .map(|route| usize::from(route.src_factor))
                .collect::<Vec<_>>(),
            [1]
        );
        assert!(
            std::panic::catch_unwind(|| SigMorphism::projection(
                &product,
                DescriptorFactorIndex::from(2_usize)
            ))
            .is_err()
        );
    }

    #[test]
    fn morphism_checker_distinguishes_structural_failures()
    {
        let source = fixtures::nat_names("a".into());
        let target = fixtures::nat_names("b".into());
        let valid = fixtures::renaming(&source, &target);
        let mut wrong_count = valid.clone();
        wrong_count.routes.clear();
        assert_eq!(check_morphism(&wrong_count).len(), 1);
        let mut absent_factor = valid.clone();
        absent_factor
            .routes
            .first_mut()
            .expect("one route")
            .src_factor = DescriptorFactorIndex::from(1_usize);
        assert_eq!(check_morphism(&absent_factor).len(), 1);
        let mut unmapped = valid.clone();
        assert!(
            unmapped
                .routes
                .first_mut()
                .expect("one route")
                .map
                .remove(&target.zero)
                .is_some()
        );
        assert_eq!(check_morphism(&unmapped).len(), 1);
        for (target_name, image) in [
            (target.zero.clone(), source.plus.clone()),
            (target.plus.clone(), source.zero.clone()),
            (target.zero.clone(), source.succ.clone()),
            (target.plus.clone(), source.double.clone()),
            (Name::from("ghost"), source.zero.clone()),
        ] {
            let mut invalid = valid.clone();
            drop(
                invalid
                    .routes
                    .first_mut()
                    .expect("one route")
                    .map
                    .insert(target_name, image),
            );
            assert_eq!(check_morphism(&invalid).len(), 1);
        }
        let mut combined = valid;
        let map = &mut combined.routes.first_mut().expect("one route").map;
        drop(map.insert(target.zero, source.succ));
        drop(map.insert(target.plus, source.double));
        drop(map.insert("ghost".into(), source.zero));
        assert_eq!(check_morphism(&combined).len(), 3);
    }

    #[test]
    fn symbol_lookups_choose_the_first_declaration()
    {
        let names = fixtures::nat_names("a".into());
        let mut desc = fixtures::nat_from_names(&names, vec![]);
        assert_eq!(
            ctor_code(&desc, names.plus.as_name_ref()),
            Maybe::Absent(symbol::Absent::Undeclared)
        );
        assert_eq!(
            op_arity(&desc, names.zero.as_name_ref()),
            Maybe::Absent(symbol::Absent::Undeclared)
        );
        assert_eq!(
            ctor_code(&desc, "missing".into()),
            Maybe::Absent(symbol::Absent::Undeclared)
        );
        assert_eq!(
            op_arity(&desc, "missing".into()),
            Maybe::Absent(symbol::Absent::Undeclared)
        );
        desc.ctors.get_mut(1).expect("two constructors").name = names.zero.clone();
        desc.opers.get_mut(1).expect("two operations").name = names.plus.clone();
        assert_eq!(
            ctor_code(&desc, names.zero.as_name_ref()),
            Maybe::Present(&desc.ctors.first().expect("first constructor").code)
        );
        assert_eq!(
            op_arity(&desc, names.plus.as_name_ref()),
            Maybe::Present(&desc.opers.first().expect("first operation").arity)
        );
    }

    #[test]
    fn composition_and_term_action_keep_unmapped_heads()
    {
        let a = fixtures::nat_names("a".into());
        let b = fixtures::nat_names("b".into());
        let c = fixtures::nat_names("c".into());
        let mut first = fixtures::renaming(&a, &b);
        assert!(
            first
                .routes
                .first_mut()
                .expect("one route")
                .map
                .remove(&b.double)
                .is_some()
        );
        let second = fixtures::renaming(&b, &c);
        let composite = compose(&first, &second);
        assert_eq!(
            composite.routes.first().expect("one route").map,
            BTreeMap::from([
                (c.zero.clone(), a.zero.clone()),
                (c.succ.clone(), a.succ.clone()),
                (c.plus.clone(), a.plus.clone()),
                (c.double.clone(), b.double.clone()),
            ])
        );
        let term = FreeTerm::op(c.plus, [
            FreeTerm::ctor(c.zero, []),
            FreeTerm::op("external", [FreeTerm::var("x")]),
        ]);
        assert_eq!(
            apply_term(&composite, DescriptorFactorIndex::from(0_usize), &term),
            FreeTerm::op(a.plus, [
                FreeTerm::ctor(a.zero, []),
                FreeTerm::op("external", [FreeTerm::var("x")])
            ])
        );
        assert_eq!(
            apply_term(&composite, DescriptorFactorIndex::from(1_usize), &term),
            term
        );
        let unmapped = FreeTerm::op(b.double, [FreeTerm::var("y")]);
        assert_eq!(
            apply_term(&first, DescriptorFactorIndex::from(0_usize), &unmapped),
            unmapped
        );
        let mut invalid = second;
        invalid.routes.first_mut().expect("one route").src_factor =
            DescriptorFactorIndex::from(1_usize);
        assert!(std::panic::catch_unwind(|| compose(&first, &invalid)).is_err());
    }

    #[test]
    fn instance_equality_distinguishes_payloads_and_factor_order()
    {
        let gen_a = BaseInstance::Gen {
            generator: GeneratorIndex::from(0_usize),
            subst: Binding::from([(Name::from("x"), fixtures::zero())]),
        };
        let gen_b = BaseInstance::Gen {
            generator: GeneratorIndex::from(1_usize),
            subst: Binding::from([(Name::from("x"), fixtures::zero())]),
        };
        let gen_payload = BaseInstance::Gen {
            generator: GeneratorIndex::from(0_usize),
            subst: Binding::from([(Name::from("x"), fixtures::succ(fixtures::zero()))]),
        };
        let path_a = BaseInstance::Path {
            start: fixtures::zero(),
            steps: vec![],
        };
        let path_b = BaseInstance::Path {
            start: fixtures::succ(fixtures::zero()),
            steps: vec![],
        };
        let path_steps = BaseInstance::Path {
            start: fixtures::zero(),
            steps: vec![RewriteStep {
                cell: GeneratorIndex::from(0_usize),
                pos: vec![],
                subst: Binding::new(),
            }],
        };
        for (left, right, expected) in [
            (&gen_a, &gen_a, true),
            (&gen_a, &gen_b, false),
            (&gen_a, &gen_payload, false),
            (&gen_a, &path_a, false),
            (&path_a, &path_b, false),
            (&path_a, &path_steps, false),
            (&path_a, &path_a, true),
        ] {
            assert_eq!(bool::from(base_instance_eq(left, right)), expected);
        }
        let empty = LooseInstance { per_factor: vec![] };
        assert!(bool::from(loose_instance_eq(&empty, &empty)));
        let one = LooseInstance {
            per_factor: vec![gen_a.clone()],
        };
        let two = LooseInstance {
            per_factor: vec![gen_a.clone(), gen_b.clone()],
        };
        let reversed = LooseInstance {
            per_factor: vec![gen_b, gen_a],
        };
        assert!(!bool::from(loose_instance_eq(&one, &two)));
        assert!(!bool::from(loose_instance_eq(&two, &reversed)));
    }

    #[test]
    fn endpoint_reading_distinguishes_base_generator_and_path_failures()
    {
        let named = fixtures::loose_of(fixtures::unary_relation("R".into()));
        let factor = named.factors.first().expect("one factor");
        let value = fixtures::succ(fixtures::zero());
        let instance = BaseInstance::Gen {
            generator: GeneratorIndex::from(0_usize),
            subst: Binding::from([(Name::from("x"), value.clone())]),
        };
        assert_eq!(
            left_endpoint(factor, &instance),
            Maybe::Present(FreeTerm::op("plus", [value.clone(), fixtures::zero()]))
        );
        assert_eq!(
            right_endpoint(factor, &instance),
            Maybe::Present(value.clone())
        );
        let unknown = BaseInstance::Gen {
            generator: GeneratorIndex::from(1_usize),
            subst: Binding::new(),
        };
        assert_eq!(
            left_endpoint(factor, &unknown),
            Maybe::Absent(endpoint::Absent::UnknownGenerator)
        );
        assert_eq!(
            right_endpoint(factor, &unknown),
            Maybe::Absent(endpoint::Absent::UnknownGenerator)
        );
        let path_arrow = LooseArrow::path(&fixtures::nat_sig());
        let path_factor = path_arrow.factors.first().expect("one path factor");
        assert_eq!(
            left_endpoint(path_factor, &instance),
            Maybe::Absent(endpoint::Absent::BaseMismatch)
        );
        assert_eq!(
            right_endpoint(path_factor, &instance),
            Maybe::Absent(endpoint::Absent::BaseMismatch)
        );
        let start = FreeTerm::op("plus", [fixtures::zero(), value.clone()]);
        let step = RewriteStep {
            cell: GeneratorIndex::from(0_usize),
            pos: vec![],
            subst: Binding::from([(Name::from("n"), value.clone())]),
        };
        let path = BaseInstance::Path {
            start: start.clone(),
            steps: vec![step],
        };
        assert_eq!(
            left_endpoint(path_factor, &path),
            Maybe::Present(start.clone())
        );
        assert_eq!(right_endpoint(path_factor, &path), Maybe::Present(value));
        let refl = BaseInstance::Path {
            start: start.clone(),
            steps: vec![],
        };
        assert_eq!(
            right_endpoint(path_factor, &refl),
            Maybe::Present(start.clone())
        );
        assert_eq!(
            right_endpoint(factor, &path),
            Maybe::Absent(endpoint::Absent::BaseMismatch)
        );
        let terminal = SigObj::terminal();
        let terminal_path = FormalRestriction {
            left: SigMorphism::identity(&terminal),
            base: BaseLoose::Path {
                sig: terminal.clone(),
            },
            right: SigMorphism::identity(&terminal),
        };
        assert_eq!(
            right_endpoint(&terminal_path, &refl),
            Maybe::Absent(endpoint::Absent::BaseMismatch)
        );
        for (cell, pos) in [
            (3_usize, vec![]),
            (0, vec![TermPositionIndex::from(2_usize)]),
        ] {
            let invalid = BaseInstance::Path {
                start: start.clone(),
                steps: vec![RewriteStep {
                    cell: GeneratorIndex::from(cell),
                    pos,
                    subst: Binding::new(),
                }],
            };
            assert_eq!(
                right_endpoint(path_factor, &invalid),
                Maybe::Absent(endpoint::Absent::PathDeclined)
            );
        }
    }

    #[test]
    fn cell_program_parts_follow_nested_extents()
    {
        let relation = fixtures::unary_relation("R".into());
        let a = fixtures::relabel_cell(
            Arc::clone(&relation),
            Arc::clone(&relation),
            fixtures::zero(),
        );
        let b = fixtures::relabel_cell(
            Arc::clone(&relation),
            Arc::clone(&relation),
            fixtures::succ(fixtures::zero()),
        );
        let c = fixtures::relabel_cell(
            Arc::clone(&relation),
            relation,
            fixtures::succ(fixtures::succ(fixtures::zero())),
        );
        let ab = Cell {
            cod: LooseArrow::meet(&a.cod, &b.cod),
            kind: CellKind::pair(&a, &b),
            ..a.clone()
        };
        let bc = Cell {
            cod: LooseArrow::meet(&b.cod, &c.cod),
            kind: CellKind::pair(&b, &c),
            ..b.clone()
        };
        let left_nested = Cell {
            cod: LooseArrow::meet(&ab.cod, &c.cod),
            kind: CellKind::pair(&ab, &c),
            ..a.clone()
        };
        let right_nested = Cell {
            cod: LooseArrow::meet(&a.cod, &bc.cod),
            kind: CellKind::pair(&a, &bc),
            ..a
        };
        assert_eq!(
            left_nested.kind.two_parts(left_nested.kind.root()),
            (StepIndex::from(2_usize), StepIndex::from(3_usize))
        );
        assert_eq!(
            right_nested.kind.two_parts(right_nested.kind.root()),
            (StepIndex::from(0_usize), StepIndex::from(3_usize))
        );
        assert_eq!(
            right_nested.kind.two_parts(StepIndex::from(3_usize)),
            (StepIndex::from(1_usize), StepIndex::from(2_usize))
        );
        let expected = LooseInstance {
            per_factor: [
                fixtures::zero(),
                fixtures::succ(fixtures::zero()),
                fixtures::succ(fixtures::succ(fixtures::zero())),
            ]
            .into_iter()
            .map(|term| BaseInstance::Gen {
                generator: GeneratorIndex::from(0_usize),
                subst: Binding::from([(Name::from("x"), term)]),
            })
            .collect(),
        };
        let input = fixtures::gen_x(fixtures::zero());
        assert_eq!(
            replay(&left_nested, core::slice::from_ref(&input)),
            Maybe::Present(expected.clone())
        );
        assert_eq!(replay(&right_nested, &[input]), Maybe::Present(expected));
        let unary = CellKind::path_ind(&left_nested);
        assert_eq!(CellKind::one_part(unary.root()), StepIndex::from(4_usize));
        let leaf = CellKind::ident();
        assert!(
            std::panic::catch_unwind(|| {
                let _view = leaf.view_at(StepIndex::from(1_usize));
            })
            .is_err()
        );
        assert!(std::panic::catch_unwind(|| leaf.two_parts(StepIndex::from(0_usize))).is_err());
        assert!(std::panic::catch_unwind(|| CellKind::one_part(StepIndex::from(0_usize))).is_err());
    }

    #[test]
    fn replay_distinguishes_arity_projection_pairing_and_path_refusals()
    {
        let loose = fixtures::loose_of(fixtures::unary_relation("R".into()));
        let identity = fixtures::ident_cell(loose.clone());
        let first = fixtures::gen_x(fixtures::zero());
        let second = fixtures::gen_x(fixtures::succ(fixtures::zero()));
        let declined = Maybe::Absent(replay_outcome::Absent::Declined);
        assert_eq!(
            replay(&identity, core::slice::from_ref(&first)),
            Maybe::Present(first.clone())
        );
        assert_eq!(replay(&identity, &[]), declined);
        assert_eq!(
            replay(&identity, &[first.clone(), second.clone()]),
            declined
        );
        let projection = Cell {
            dom: vec![LooseArrow::meet(&loose, &loose)],
            kind: CellKind::proj(DescriptorFactorIndex::from(1_usize)),
            ..identity.clone()
        };
        let input = LooseInstance {
            per_factor: first
                .per_factor
                .iter()
                .chain(&second.per_factor)
                .cloned()
                .collect(),
        };
        assert_eq!(
            replay(&projection, core::slice::from_ref(&input)),
            Maybe::Present(second.clone())
        );
        assert_eq!(replay(&projection, &[]), declined);
        let missing = Cell {
            kind: CellKind::proj(DescriptorFactorIndex::from(2_usize)),
            ..projection
        };
        assert_eq!(replay(&missing, &[input]), declined);
        let bad = Cell {
            kind: CellKind::clauses(vec![]),
            ..identity.clone()
        };
        for (left, right) in [(&bad, &identity), (&identity, &bad)] {
            let pair = Cell {
                cod: LooseArrow::meet(&left.cod, &right.cod),
                kind: CellKind::pair(left, right),
                ..identity.clone()
            };
            assert_eq!(replay(&pair, core::slice::from_ref(&first)), declined);
        }
        let bang = Cell {
            cod: LooseArrow::top(&loose.src, &loose.tgt),
            kind: CellKind::bang(),
            ..identity
        };
        let empty = LooseInstance { per_factor: vec![] };
        assert_eq!(
            replay(&bang, core::slice::from_ref(&first)),
            Maybe::Present(empty.clone())
        );
        let base = Cell {
            dom: vec![loose.clone(), loose.clone()],
            ..bang
        };
        let induction = Cell {
            dom: vec![loose.clone(), LooseArrow::path(&fixtures::nat_sig()), loose],
            kind: CellKind::path_ind(&base),
            ..base.clone()
        };
        let refl = LooseInstance {
            per_factor: vec![BaseInstance::Path {
                start: fixtures::zero(),
                steps: vec![],
            }],
        };
        assert_eq!(
            replay(&induction, &[first.clone(), refl.clone(), second.clone()]),
            Maybe::Present(empty.clone())
        );
        assert_eq!(replay(&induction, &[first.clone(), refl]), declined);
        let nonempty = LooseInstance {
            per_factor: vec![BaseInstance::Path {
                start: FreeTerm::op("plus", [fixtures::zero(), fixtures::zero()]),
                steps: vec![RewriteStep {
                    cell: GeneratorIndex::from(0_usize),
                    pos: vec![],
                    subst: Binding::from([(Name::from("n"), fixtures::zero())]),
                }],
            }],
        };
        for middle in [empty, first.clone(), nonempty] {
            assert_eq!(
                replay(&induction, &[first.clone(), middle, second.clone()]),
                declined
            );
        }
    }

    #[test]
    fn clause_replay_uses_first_match_and_namespaced_bindings()
    {
        let zero = GeneratorIndex::from(0_usize);
        let one = GeneratorIndex::from(1_usize);
        let good = CellClause {
            matches: vec![zero, one],
            emit: vec![
                (
                    zero,
                    Binding::from([(
                        Name::from("both"),
                        FreeTerm::op("plus", [FreeTerm::var("p0.x"), FreeTerm::var("p1.x")]),
                    )]),
                ),
                (
                    one,
                    Binding::from([(Name::from("copy"), FreeTerm::var("p1.x"))]),
                ),
            ],
        };
        let skipped = CellClause {
            matches: vec![one, one],
            emit: vec![],
        };
        let shadowed = CellClause {
            matches: vec![zero, one],
            emit: vec![],
        };
        let clauses = [skipped, good, shadowed];
        let left = fixtures::gen_x(fixtures::zero());
        let right = LooseInstance {
            per_factor: vec![BaseInstance::Gen {
                generator: one,
                subst: Binding::from([(Name::from("x"), fixtures::succ(fixtures::zero()))]),
            }],
        };
        assert_eq!(
            replay_clauses(&clauses, &[left.clone(), right.clone()]),
            Maybe::Present(LooseInstance {
                per_factor: vec![
                    BaseInstance::Gen {
                        generator: zero,
                        subst: Binding::from([(
                            Name::from("both"),
                            FreeTerm::op("plus", [
                                fixtures::zero(),
                                fixtures::succ(fixtures::zero())
                            ])
                        )])
                    },
                    BaseInstance::Gen {
                        generator: one,
                        subst: Binding::from([(
                            Name::from("copy"),
                            fixtures::succ(fixtures::zero())
                        )])
                    },
                ]
            })
        );
        let declined = Maybe::Absent(replay_outcome::Absent::Declined);
        assert_eq!(
            replay_clauses(&clauses, core::slice::from_ref(&left)),
            declined
        );
        assert_eq!(replay_clauses(&[], &[left.clone(), right]), declined);
        for wrong in [
            LooseInstance { per_factor: vec![] },
            fixtures::gen_x(fixtures::zero()),
            LooseInstance {
                per_factor: vec![BaseInstance::Path {
                    start: fixtures::zero(),
                    steps: vec![],
                }],
            },
        ] {
            assert_eq!(replay_clauses(&clauses, &[left.clone(), wrong]), declined);
        }
        let nullary = CellClause {
            matches: vec![],
            emit: vec![(zero, Binding::from([(Name::from("x"), fixtures::zero())]))],
        };
        assert_eq!(
            replay_clauses(&[nullary], &[]),
            Maybe::Present(fixtures::gen_x(fixtures::zero()))
        );
    }

    #[test]
    fn replay_composition_propagates_inner_and_outer_refusal()
    {
        let relation = fixtures::unary_relation("R".into());
        let loose = fixtures::loose_of(Arc::clone(&relation));
        let identity = fixtures::ident_cell(loose.clone());
        let successor = fixtures::relabel_cell(
            Arc::clone(&relation),
            relation,
            fixtures::succ(FreeTerm::var("p0.x")),
        );
        let outer = Cell {
            dom: vec![loose.clone(), loose.clone()],
            kind: CellKind::clauses(vec![CellClause {
                matches: vec![GeneratorIndex::from(0_usize), GeneratorIndex::from(0_usize)],
                emit: vec![(
                    GeneratorIndex::from(0_usize),
                    Binding::from([(
                        Name::from("x"),
                        FreeTerm::op("plus", [FreeTerm::var("p0.x"), FreeTerm::var("p1.x")]),
                    )]),
                )],
            }]),
            ..identity.clone()
        };
        let input = fixtures::gen_x(fixtures::zero());
        assert_eq!(
            replay_compose(&outer, &[&identity, &successor], &[
                vec![input.clone()],
                vec![input.clone()]
            ]),
            Maybe::Present(fixtures::gen_x(FreeTerm::op("plus", [
                fixtures::zero(),
                fixtures::succ(fixtures::zero())
            ])))
        );
        let bang = Cell {
            cod: LooseArrow::top(&loose.src, &loose.tgt),
            kind: CellKind::bang(),
            ..identity.clone()
        };
        assert_eq!(
            replay_compose(&bang, &[&identity], &[vec![]]),
            Maybe::Absent(replay_outcome::Absent::Declined)
        );
        assert_eq!(
            replay_compose(&identity, &[&identity, &identity], &[
                vec![input.clone()],
                vec![input]
            ]),
            Maybe::Absent(replay_outcome::Absent::Declined)
        );
        let nullary = Cell {
            dom: vec![],
            ..bang
        };
        assert_eq!(
            replay_compose(&nullary, &[], &[]),
            Maybe::Present(LooseInstance { per_factor: vec![] })
        );
    }

    #[test]
    fn sample_equality_observes_disagreement_and_vacuity()
    {
        let relation = fixtures::unary_relation("R".into());
        let identity = fixtures::ident_cell(fixtures::loose_of(Arc::clone(&relation)));
        let successor = fixtures::relabel_cell(
            Arc::clone(&relation),
            relation,
            fixtures::succ(FreeTerm::var("p0.x")),
        );
        let corpus = vec![vec![], vec![fixtures::gen_x(fixtures::zero())]];
        assert!(bool::from(cells_equal(&identity, &successor, &[])));
        assert!(bool::from(cells_equal(&identity, &identity, &corpus)));
        assert!(!bool::from(cells_equal(&identity, &successor, &corpus)));
        let no_clause = Cell {
            kind: CellKind::clauses(vec![]),
            ..identity.clone()
        };
        let missing = Cell {
            kind: CellKind::proj(DescriptorFactorIndex::from(1_usize)),
            ..identity.clone()
        };
        assert!(bool::from(cells_equal(&no_clause, &missing, &corpus)));
        assert!(!bool::from(cells_equal(&no_clause, &identity, &corpus)));
    }

    #[test]
    fn graft_refuses_each_unsupported_clause_shape()
    {
        let relation = fixtures::unary_relation("R".into());
        let inner = fixtures::relabel_cell(
            Arc::clone(&relation),
            Arc::clone(&relation),
            fixtures::succ(FreeTerm::var("p0.x")),
        );
        let outer = fixtures::relabel_cell(
            Arc::clone(&relation),
            relation,
            FreeTerm::op("double", [FreeTerm::var("p0.x")]),
        );
        let Maybe::Present(composite) = graft(&outer, core::slice::from_ref(&inner))
        else {
            panic!("linear clauses compose");
        };
        let CellView::Clauses(composed) = composite.kind.view()
        else {
            panic!("composed clause");
        };
        assert_eq!(composed, [CellClause {
            matches: vec![GeneratorIndex::from(0_usize)],
            emit: vec![(
                GeneratorIndex::from(0_usize),
                Binding::from([(
                    Name::from("x"),
                    FreeTerm::op("double", [fixtures::succ(FreeTerm::var("p0.x"))])
                )])
            )]
        }]);
        let CellView::Clauses(outer_clauses) = outer.kind.view()
        else {
            panic!("outer clause");
        };
        let CellView::Clauses(inner_clauses) = inner.kind.view()
        else {
            panic!("inner clause");
        };
        let outer_clause = outer_clauses.first().expect("one clause").clone();
        let inner_clause = inner_clauses.first().expect("one clause").clone();
        let no_matches = CellClause {
            matches: vec![],
            ..outer_clause.clone()
        };
        let two_matches = CellClause {
            matches: vec![GeneratorIndex::from(0_usize), GeneratorIndex::from(0_usize)],
            ..outer_clause.clone()
        };
        let wrong_match = CellClause {
            matches: vec![GeneratorIndex::from(1_usize)],
            ..outer_clause.clone()
        };
        let no_emit = CellClause {
            emit: vec![],
            ..inner_clause.clone()
        };
        let two_emits = CellClause {
            emit: inner_clause
                .emit
                .iter()
                .chain(&inner_clause.emit)
                .cloned()
                .collect(),
            ..inner_clause.clone()
        };
        for (outer_program, inner_program) in [
            (vec![], vec![inner_clause.clone()]),
            (vec![outer_clause.clone(), outer_clause.clone()], vec![
                inner_clause.clone(),
            ]),
            (vec![outer_clause.clone()], vec![]),
            (vec![outer_clause.clone()], vec![
                inner_clause.clone(),
                inner_clause.clone(),
            ]),
            (vec![no_matches], vec![inner_clause.clone()]),
            (vec![two_matches], vec![inner_clause.clone()]),
            (vec![wrong_match], vec![inner_clause]),
            (vec![outer_clause.clone()], vec![no_emit]),
            (vec![outer_clause], vec![two_emits]),
        ] {
            let bad_outer = Cell {
                kind: CellKind::clauses(outer_program),
                ..outer.clone()
            };
            let bad_inner = Cell {
                kind: CellKind::clauses(inner_program),
                ..inner.clone()
            };
            assert_eq!(
                graft(&bad_outer, &[bad_inner]),
                Maybe::Absent(graft_outcome::Absent::Unsupported)
            );
        }
        assert_eq!(
            graft(&outer, &[]),
            Maybe::Absent(graft_outcome::Absent::Unsupported)
        );
        assert_eq!(
            graft(&outer, &[inner.clone(), inner]),
            Maybe::Absent(graft_outcome::Absent::Unsupported)
        );
    }

    #[test]
    fn saturated_replay_requires_a_replayable_absorbed_path()
    {
        let loose = fixtures::loose_of(fixtures::unary_relation("R".into()));
        let identity = fixtures::ident_cell(loose.clone());
        let base = Cell {
            dom: vec![loose.clone(), loose.clone()],
            cod: LooseArrow::top(&loose.src, &loose.tgt),
            kind: CellKind::bang(),
            ..identity.clone()
        };
        let input = fixtures::gen_x(fixtures::zero());
        let start = FreeTerm::op("plus", [fixtures::zero(), fixtures::succ(fixtures::zero())]);
        let valid = RewriteStep {
            cell: GeneratorIndex::from(0_usize),
            pos: vec![],
            subst: Binding::from([(Name::from("n"), fixtures::succ(fixtures::zero()))]),
        };
        let cells = fixtures::nat_desc().rules;
        let generator = input.per_factor.first().expect("one factor").clone();
        for absorbed in [vec![], vec![valid]] {
            let saturated = SaturatedInstance {
                generator: generator.clone(),
                absorbed,
                path_start: start.clone(),
            };
            assert_eq!(
                replay_path_ind_saturated(&base, &input, &saturated, &input, &cells),
                Maybe::Present(LooseInstance { per_factor: vec![] })
            );
            assert_eq!(
                replay_path_ind_saturated(&identity, &input, &saturated, &input, &cells),
                Maybe::Absent(replay_outcome::Absent::Declined)
            );
        }
        for (cell, pos) in [
            (3_usize, vec![]),
            (0, vec![TermPositionIndex::from(2_usize)]),
        ] {
            let saturated = SaturatedInstance {
                generator: generator.clone(),
                absorbed: vec![RewriteStep {
                    cell: GeneratorIndex::from(cell),
                    pos,
                    subst: Binding::new(),
                }],
                path_start: start.clone(),
            };
            assert_eq!(
                replay_path_ind_saturated(&base, &input, &saturated, &input, &cells),
                Maybe::Absent(replay_outcome::Absent::Declined)
            );
        }
    }
}
