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
    /// trivial.
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
/// trivial.
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
/// trivial.
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
/// - requires: `first.tgt` is `second.src`.
/// - ensures: one route per route of `second`, drawn from the source factor its
///   `first` route names, each symbol mapped through both renamings (a symbol
///   `first` leaves unmapped is kept).
/// - panics: when a route of `second` names a factor `first` does not route, a
///   test-author error.
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
/// trivial.
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
    /// trivial.
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
    /// trivial.
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
/// trivial.
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
/// - ensures: the same domain and kind, the codomain restricted by the two
///   frames, and identity frames on its endpoints; the kind is kept, so the
///   factorization is data-identical.
/// - panics: none.
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
/// trivial.
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
/// trivial.
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
    /// trivial.
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
/// - ensures: the outer cell's replay on the inner outputs in order;
///   [`replay_outcome::Absent::Declined`] when any replay declines.
/// - panics: none.
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
