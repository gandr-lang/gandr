//! Virtual double categories over replayable rewriting evidence.

use alloc::borrow::Cow;
use alloc::boxed::Box;
use alloc::vec::Vec;

use anodized::spec;
use gandr_theory_cell_complexes::CellId;
use gandr_theory_cell_complexes::CellStore;
use gandr_theory_coherent_resolutions::Tracelet;
use gandr_theory_coherent_resolutions::replay_equivalent;
use gandr_theory_decomposition_spaces::compose_invertible;
use gandr_theory_levitation::FreeTerm;
use gandr_theory_levitation::Name;
use gandr_theory_levitation::NameRef;
use gandr_theory_levitation::NominalId;
use gandr_theory_levitation::SignDesc;
use gandr_theory_levitation::tree::ArgumentCount;
use gandr_theory_levitation::tree::Head;
use gandr_theory_levitation::tree::Tree;
use gandr_theory_levitation::tree::TreeRef;
use quenchant_shape::shape::Maybe;

use crate::boundary::DerivationReplay;
use crate::boundary::DescTableEmptyStatus;
use crate::boundary::DescTableLength;
use crate::boundary::SigMorphismIdentity;
use crate::boundary::VdcCellEquality;
pub use crate::signature::SignatureRef;

/// A **term** in the free structure over a signature.
///
/// The reflection-face spelling of a [`gandr_theory_levitation::FreeTerm`].
///
/// A protype's faces (`Path { lhs, rhs }`, `Rel { lhs, rhs }`) are `TermRef`s;
/// the newtype gives the reflected layer its own vocabulary over the engine's
/// `D⋆(V)` term type.
#[repr(transparent)]
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct TermRef(FreeTerm);

impl TermRef
{
    /// A reflected term over a [`FreeTerm`].
    #[inline]
    #[must_use]
    /// # Specification
    /// trivial.
    pub fn new(term: FreeTerm) -> Self
    {
        Self(term)
    }

    /// The underlying free-structure term.
    #[inline]
    #[must_use]
    /// # Specification
    /// trivial.
    pub fn term(&self) -> &FreeTerm
    {
        &self.0
    }
}

/// A **signature morphism** — the VDC tight arrow.
///
/// A sort-respecting **generator renaming** with an explicit source and target
/// signature: `map` lists the generators that move (a name absent from `map`
/// maps to itself), so composition is function composition and the identity is
/// the empty renaming. The `map` is kept **canonical** — sorted by source name,
/// with identity entries dropped — so equal renamings are structurally equal
/// and the tight-category laws hold on the nose.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct SigMorphism
{
    /// The source signature.
    pub src: SignatureRef,
    /// The target signature.
    pub tgt: SignatureRef,
    /// The generators that move, `(from, to)`, canonical: sorted by `from`, no
    /// identity entries.
    pub map: Box<[(Name, Name)]>,
}

impl SigMorphism
{
    /// The identity morphism on `sig` — the empty renaming.
    ///
    /// # Specification
    /// - ensures: `src == tgt == sig` and an empty `map` (every generator maps
    ///   to itself).
    /// - panics: none.
    #[inline]
    #[must_use]
    /// # Adequacy
    /// - hypothesis: L3 — both unit compositions preserve the signatures and
    ///   generator images, including names absent from the finite map.
    /// - witness: `tests::laws::tests::tight_composition_is_associative_and_unital`
    #[spec(captures: expected = sig.clone(), ensures: |ret| ret.src == expected && ret.tgt == expected && ret.map.is_empty())]
    pub fn identity(sig: SignatureRef) -> Self
    {
        Self {
            src: sig.clone(),
            tgt: sig,
            map: Box::from([]),
        }
    }

    /// A morphism `src → tgt` renaming the listed generators; the renaming is
    /// canonicalized (identity pairs dropped, sorted by source name).
    ///
    /// # Specification
    /// - ensures: `self.src == src`, `self.tgt == tgt`, and `self.map` is the
    ///   canonical form of `pairs` — no `(x, x)` entries, sorted by the source
    ///   name — so two renamings denoting the same function are structurally
    ///   equal.
    /// - panics: none.
    #[inline]
    #[must_use]
    /// # Adequacy
    /// - hypothesis: L3 — structural equality of unit and associative
    ///   composites observes canonical names and boundaries, not the input
    ///   ordering of redundant pairs.
    /// - witness: `tests::laws::tests::tight_composition_is_associative_and_unital`
    #[spec(captures: boundaries = (src.clone(), tgt.clone()), ensures: |ret| ret.src == boundaries.0 && ret.tgt == boundaries.1 && ret.map.iter().all(|pair| pair.0 != pair.1) && ret.map.windows(2).all(|pair| matches!(pair, [first, second] if first.0 < second.0)))]
    pub fn renaming(
        src: SignatureRef,
        tgt: SignatureRef,
        pairs: Vec<(Name, Name)>,
    ) -> Self
    {
        Self {
            src,
            tgt,
            map: canonical_map(pairs),
        }
    }

    /// The image of a generator name under this renaming — the name itself when
    /// it is not moved.
    ///
    /// # Specification
    /// - ensures: the `to` of the `(from, to)` entry whose `from` equals
    ///   `name`, or `name` unchanged when no entry matches.
    /// - panics: none.
    #[inline]
    #[must_use]
    /// # Adequacy
    /// - hypothesis: L3 — composition compares the images of mapped generators
    ///   and the identity image of an unmapped name.
    /// - witness: `tests::laws::tests::tight_composition_is_associative_and_unital`
    #[spec(ensures: |ret| ret.as_ref() == self.map.iter().find(|pair| pair.0.as_ref() == name.as_ref()).map_or_else(|| name.as_ref(), |pair| pair.1.as_ref()))]
    pub fn apply_name(
        &self,
        name: NameRef<'_>,
    ) -> Name
    {
        for pair in &self.map {
            if pair.0.as_ref() == name.as_ref() {
                return pair.1.clone();
            }
        }
        Name::from(name)
    }

    /// Whether this is the identity renaming (an empty canonical map).
    #[inline]
    #[must_use]
    /// # Specification
    /// trivial.
    pub fn is_identity(&self) -> SigMorphismIdentity
    {
        SigMorphismIdentity::from(self.map.is_empty())
    }
}

/// Compose two renamings **`f` then `g`** (apply `f`, then `g`) as functions on
/// generator names.
///
/// # Specification
/// - requires: for a boundary-respecting composite, `f.tgt == g.src` (the
///   composite is `f.src → g.tgt`); the map composition itself is total and
///   ignores the boundary.
/// - ensures: a canonical renaming whose `apply_name(n) == g.apply_name(f
///   .apply_name(n))` for every name, with `src == f.src` and `tgt == g.tgt`;
///   composition is associative and has [`SigMorphism::identity`] as a
///   two-sided unit (both by function composition, preserved through
///   canonicalization).
/// - panics: none.
#[inline]
#[must_use]
/// # Adequacy
/// - hypothesis: L3 — left and right units and a three-arrow composite expose
///   reversed composition and lost boundary information.
/// - witness: `tests::laws::tests::tight_composition_is_associative_and_unital`
#[spec(ensures: |ret| ret.src == f.src && ret.tgt == g.tgt && f.map.iter().chain(g.map.iter()).all(|pair| ret.apply_name(NameRef::from(pair.0.as_ref())) == g.apply_name(NameRef::from(f.apply_name(NameRef::from(pair.0.as_ref())).as_ref()))))]
fn compose_renaming(
    f: &SigMorphism,
    g: &SigMorphism,
) -> SigMorphism
{
    let mut domain: Vec<Name> = Vec::new();
    for pair in f.map.iter().chain(g.map.iter()) {
        if !domain.contains(&pair.0) {
            domain.push(pair.0.clone());
        }
    }
    let mut pairs: Vec<(Name, Name)> = Vec::with_capacity(domain.len());
    for name in domain {
        let moved = f.apply_name(NameRef::from(name.as_ref()));
        let image = g.apply_name(NameRef::from(moved.as_ref()));
        pairs.push((name, image));
    }
    SigMorphism {
        src: f.src.clone(),
        tgt: g.tgt.clone(),
        map: canonical_map(pairs),
    }
}

/// Canonicalize a renaming: drop identity pairs, dedup on source name (first
/// non-identity pair wins), and sort by source name.
///
/// # Specification
/// - ensures: no `(x, x)` entries; at most one entry per source name (the first
///   non-identity occurrence's target); sorted by source name — the canonical
///   form on which [`SigMorphism`] equality is structural.
/// - panics: none.
#[inline]
/// # Adequacy
/// - hypothesis: L3 — the tight-arrow laws compare canonical renamings
///   structurally; explicit identity pairs cannot survive as a different
///   identity.
/// - witness: `tests::laws::tests::tight_composition_is_associative_and_unital`
#[spec(ensures: |ret| ret.iter().all(|pair| pair.0 != pair.1) && ret.windows(2).all(|pair| matches!(pair, [first, second] if first.0 < second.0)))]
fn canonical_map(pairs: Vec<(Name, Name)>) -> Box<[(Name, Name)]>
{
    let mut out: Vec<(Name, Name)> = Vec::with_capacity(pairs.len());
    for (from, to) in pairs {
        if from == to {
            continue;
        }
        let mut already_seen = false;
        for existing in &out {
            if existing.0 == from {
                already_seen = true;
                break;
            }
        }
        if already_seen {
            continue;
        }
        out.push((from, to));
    }
    out.sort_unstable();
    out.into_boxed_slice()
}

/// A **relation interface** — the VDC loose arrow `R : I ⇸ J`.
///
/// A named set of generating cells (by [`CellId`] into the shared store)
/// between two signatures, carrying two **restriction frames** — the
/// accumulated tight morphisms a [`Vdc::restrict`] precomposes on each side.
/// Restriction is **split/strict** because signature morphisms compose
/// associatively and the frames are content-addressed data : `R[id #
/// id] = R` and `R[s∘s′ # t∘t′] = R[s # t][s′ # t′]` hold definitionally on the
/// frames.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct RelationRef
{
    /// The relation's name.
    pub name: Name,
    /// The source signature `I` (after any restriction).
    pub src: SignatureRef,
    /// The target signature `J` (after any restriction).
    pub tgt: SignatureRef,
    /// The generating cells (by id into the [`CellStoreVdc`] store).
    pub generators: Box<[CellId]>,
    /// The accumulated left (source-side) restriction frame; identity for an
    /// unrestricted relation.
    pub left: SigMorphism,
    /// The accumulated right (target-side) restriction frame; identity for an
    /// unrestricted relation.
    pub right: SigMorphism,
}

impl RelationRef
{
    /// An unrestricted relation `src ⇸ tgt` named `name` over `generators`
    /// (both restriction frames identity).
    ///
    /// # Specification
    /// - ensures: `left` and `right` are the identity morphisms on `src` and
    ///   `tgt` respectively; the generating cells are carried verbatim.
    /// - panics: none.
    #[inline]
    #[must_use]
    /// # Adequacy
    /// - hypothesis: L3 — identity restriction compares the whole relation,
    ///   including both identity frames and its generating cells.
    /// - witness: `tests::laws::tests::restriction_by_identity_is_the_identity`
    #[spec(ensures: |ret| ret.left.src == ret.src && ret.left.tgt == ret.src && ret.left.map.is_empty() && ret.right.src == ret.tgt && ret.right.tgt == ret.tgt && ret.right.map.is_empty())]
    pub fn new(
        name: NameRef<'_>,
        src: SignatureRef,
        tgt: SignatureRef,
        generators: Box<[CellId]>,
    ) -> Self
    {
        Self {
            name: Name::from(name),
            left: SigMorphism::identity(src.clone()),
            right: SigMorphism::identity(tgt.clone()),
            src,
            tgt,
            generators,
        }
    }
}

/// The nonrecursive head of a reflected derivation.
#[derive(Clone, Debug, Eq, PartialEq)]
enum DerivationKind
{
    /// An identity cell.
    Id(RelationRef),
    /// A recorded engine certificate and its boundary.
    Cert
    {
        /// The recorded certificate.
        cert: Box<Tracelet>,
        /// The input relations.
        dom: Box<[RelationRef]>,
        /// The output relation.
        cod: RelationRef,
    },
    /// Grafting: outer cell first, then the input cells in order.
    Graft(ArgumentCount),
}
impl Head for DerivationKind
{
    /// The number of immediate subderivations.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn arity(&self) -> ArgumentCount
    {
        match *self {
            | Self::Id(_) | Self::Cert { .. } => 0_usize.into(),
            | Self::Graft(count) => count,
        }
    }
}
/// A reflected derivation held in one flat table.
#[repr(transparent)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Derivation(Tree<DerivationKind>);

/// The engine-level content a [`Derivation`] elaborates to.
///
/// `Trivial` is the identity transformation (no engine steps); `Cert` is a
/// single engine tracelet. Replay-equivalence of two elaborations
/// ([`elaborations_replay_equivalent`]) is the identity criterion.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Elaborated<'derivation>
{
    /// The identity transformation — no engine steps.
    Trivial,
    /// A single engine certificate.
    Cert(Cow<'derivation, Box<Tracelet>>),
    /// The elaboration failed — the derivation is not engine-realizable at this
    /// stage (a grafting shape outside the sequential-invertible case, or a
    /// broken seam).
    Stuck,
}

impl Derivation
{
    /// The identity cell on a relation.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn id(relation: RelationRef) -> Self
    {
        Self(Tree::leaf(DerivationKind::Id(relation)))
    }
    /// Embed a certificate with its input and output relations.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn cert(
        cert: Tracelet,
        dom: Box<[RelationRef]>,
        cod: RelationRef,
    ) -> Self
    {
        Self(Tree::leaf(DerivationKind::Cert {
            cert: Box::new(cert),
            dom,
            cod,
        }))
    }
    /// Graft input derivations into an outer cell.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn graft(
        outer: Self,
        inners: Vec<Self>,
    ) -> Self
    {
        let mut children = Vec::with_capacity(inners.len().saturating_add(1));
        children.push(outer.0);
        children.extend(inners.into_iter().map(|inner| inner.0));
        Self(Tree::node(
            DerivationKind::Graft(children.len().into()),
            children,
        ))
    }
    /// The input relation chain, in grafting order.
    ///
    /// # Specification
    /// - ensures: the concatenated leaf domains, excluding each graft's outer
    ///   cell.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — asymmetric grafts distinguish order, omission and
    ///   inclusion of the outer domain.
    /// - witness: `tests::laws::tests::cell_grafting_matches_engine_composition`
    #[inline]
    #[must_use]
    #[spec(ensures: |ret| match *self.0.to_ref().head() { DerivationKind::Id(ref relation) => ret.as_slice() == core::slice::from_ref(relation), DerivationKind::Cert { ref dom, .. } => ret.as_slice() == dom.as_ref(), DerivationKind::Graft(_) => true })]
    pub fn dom(&self) -> Vec<RelationRef>
    {
        self.domain().cloned().collect()
    }
    /// Borrow the input relation chain without cloning its interfaces.
    ///
    /// # Specification
    /// - ensures: yields leaf domains in grafting order, excluding outer cells.
    /// - panics: none.
    /// - executable: none — the backend cannot name the opaque iterator in its
    ///   generated closure signature; observing all results consumes it.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — asymmetric nested grafts expose reversed inputs,
    ///   omitted leaves and accidental inclusion of the outer cell's domain.
    /// - witness: `tests::laws::tests::cell_grafting_matches_engine_composition`
    #[inline]
    fn domain(&self) -> impl Iterator<Item = &RelationRef>
    {
        let mut pending = alloc::vec![self.0.to_ref()];
        let mut current: &[RelationRef] = &[];
        core::iter::from_fn(move || {
            loop {
                if let Some((head, tail)) = current.split_first() {
                    current = tail;
                    return Some(head);
                }
                let cell = pending.pop()?;
                match *cell.head() {
                    | DerivationKind::Id(ref relation) => return Some(relation),
                    | DerivationKind::Cert { ref dom, .. } => current = dom,
                    | DerivationKind::Graft(_) => {
                        let start = pending.len();
                        pending.extend(cell.children().skip(1));
                        if let Some(children) = pending.get_mut(start ..) {
                            children.reverse();
                        }
                    },
                }
            }
        })
    }
    /// The output relation of the outermost cell.
    ///
    /// # Specification
    /// - ensures: follows graft outer children to the recorded output relation.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns a malformed-derivation error if an outer child is absent.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — nested grafts retain the outermost output,
    ///   independently of inner outputs.
    /// - witness: `tests::laws::tests::cell_grafting_matches_engine_composition`
    #[inline]
    #[spec(ensures: |ret| match *self.0.to_ref().head() { DerivationKind::Id(ref relation) => ret == Ok(relation), DerivationKind::Cert { ref cod, .. } => ret == Ok(cod), DerivationKind::Graft(_) => true })]
    pub fn cod(&self) -> Result<&RelationRef, DerivationError>
    {
        let mut current = self.0.to_ref();
        loop {
            match *current.head() {
                | DerivationKind::Id(ref relation) => return Ok(relation),
                | DerivationKind::Cert { ref cod, .. } => return Ok(cod),
                | DerivationKind::Graft(_) => {
                    current = current
                        .children()
                        .next()
                        .ok_or(DerivationError::MissingOuter)?;
                },
            }
        }
    }
    /// Elaborate grafts through sequential invertible certificate composition.
    ///
    /// # Specification
    /// - ensures: identities are trivial; certificate leaves retain their
    ///   evidence; sequential grafts compose only at an equal seam. Unsupported
    ///   grafts and broken seams are stuck.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L1 — engine replay distinguishes omitted, reversed and
    ///   corrupted composition evidence.
    /// - witness: `tests::laws::tests::cell_grafting_matches_engine_composition`
    /// - witness: `tests::laws::tests::cell_grafting_is_unital_up_to_replay`
    #[inline]
    #[must_use]
    #[spec(ensures: |ref ret| match *self.0.to_ref().head() { DerivationKind::Id(_) => matches!(*ret, Elaborated::Trivial), DerivationKind::Cert { ref cert, .. } => matches!(*ret, Elaborated::Cert(ref actual) if actual.as_ref() == cert), DerivationKind::Graft(_) => true })]
    pub fn elaborate(&self) -> Elaborated<'_>
    {
        let mut frames = alloc::vec![ElaborateFrame::Enter(self.0.to_ref())];
        let mut values = Vec::new();
        while let Some(frame) = frames.pop() {
            match frame {
                | ElaborateFrame::Enter(cell) => match *cell.head() {
                    | DerivationKind::Id(_) => values.push(Elaborated::Trivial),
                    | DerivationKind::Cert { ref cert, .. } => {
                        values.push(Elaborated::Cert(Cow::Borrowed(cert)));
                    },
                    | DerivationKind::Graft(_) => {
                        let mut children = cell.children();
                        let Some(outer) = children.next()
                        else {
                            return Elaborated::Stuck;
                        };
                        if children
                            .clone()
                            .all(|inner| matches!(*inner.head(), DerivationKind::Id(_)))
                        {
                            frames.push(ElaborateFrame::Enter(outer));
                        }
                        else {
                            match (children.next(), children.next()) {
                                | (Some(inner), None) => {
                                    frames.push(ElaborateFrame::FinishSequential);
                                    frames.push(ElaborateFrame::Enter(outer));
                                    frames.push(ElaborateFrame::Enter(inner));
                                },
                                | _ => values.push(Elaborated::Stuck),
                            }
                        }
                    },
                },
                | ElaborateFrame::FinishSequential => {
                    let outer = values.pop().unwrap_or(Elaborated::Stuck);
                    let inner = values.pop().unwrap_or(Elaborated::Stuck);
                    values.push(graft_sequential(inner, outer));
                },
            }
        }
        values.pop().unwrap_or(Elaborated::Stuck)
    }
    /// Validate the elaborated certificate in the cell store.
    ///
    /// # Specification
    /// - ensures: trivial evidence passes, stuck evidence fails, and
    ///   certificate evidence has exactly its engine replay verdict.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L1 — accepted and corrupted certificates are compared
    ///   through engine replay.
    /// - witness: `tests::laws::tests::a_non_replaying_certificate_is_rejected`
    #[inline]
    #[must_use]
    #[spec(ensures: |ret| bool::from(ret) == match self.elaborate() { Elaborated::Trivial => true, Elaborated::Cert(cert) => bool::from(cert.replay(store)), Elaborated::Stuck => false })]
    pub fn replays(
        &self,
        store: &CellStore,
    ) -> DerivationReplay
    {
        DerivationReplay::from(match self.elaborate() {
            | Elaborated::Trivial => true,
            | Elaborated::Cert(cert) => bool::from(cert.replay(store)),
            | Elaborated::Stuck => false,
        })
    }
}
/// A malformed reflected derivation.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum DerivationError
{
    /// A graft has no outer cell.
    MissingOuter,
}
/// One step in the iterative elaboration machine.
enum ElaborateFrame<'derivation>
{
    /// Elaborate a borrowed subtree.
    Enter(TreeRef<'derivation, DerivationKind>),
    /// Compose the two completed children.
    FinishSequential,
}

/// Chain `inner` **then** `outer` at their shared seam.
///
/// # Specification
/// - ensures: [`Elaborated::Cert`] of
///   [`gandr_theory_decomposition_spaces::compose_invertible`] when both are
///   certificates sharing the seam (`inner.joins_at == outer.overlap.peak`);
///   the non-trivial side unchanged when the other is trivial;
///   [`Elaborated::Stuck`] on a mismatched seam or a stuck operand.
/// - panics: none.
#[inline]
/// # Adequacy
/// - hypothesis: L1 — graft elaboration is compared with engine composition and
///   replay, so a changed sequential seam or path changes the observation.
/// - witness: `tests::laws::tests::cell_grafting_matches_engine_composition`
#[spec(captures: refused = matches!((&inner, &outer), (Elaborated::Stuck, _) | (_, Elaborated::Stuck)) || matches!((&inner, &outer), (Elaborated::Cert(i), Elaborated::Cert(o)) if i.joins_at != o.overlap.peak), ensures: |ref ret| matches!(ret, Elaborated::Stuck) == refused)]
fn graft_sequential<'derivation>(
    inner: Elaborated<'derivation>,
    outer: Elaborated<'derivation>,
) -> Elaborated<'derivation>
{
    match (inner, outer) {
        | (Elaborated::Trivial, other) | (other, Elaborated::Trivial) => other,
        | (Elaborated::Cert(i), Elaborated::Cert(o)) => {
            if i.joins_at == o.overlap.peak {
                Elaborated::Cert(Cow::Owned(Box::new(compose_invertible(&i, &o))))
            }
            else {
                Elaborated::Stuck
            }
        },
        | (Elaborated::Stuck, _) | (_, Elaborated::Stuck) => Elaborated::Stuck,
    }
}

/// Whether two elaborations denote the **same transformation** up to replay.
///
/// # Specification
/// - ensures: two trivial elaborations agree; two certificates agree iff
///   [`gandr_theory_coherent_resolutions::replay_equivalent`] holds; a trivial
///   and a certificate agree iff the certificate is reflexive (`peak ==
///   joins_at`) and replays; a [`Elaborated::Stuck`] never agrees with anything
///   (an unrealized cell is not a transformation).
/// - panics: none.
#[inline]
#[must_use]
/// # Adequacy
/// - hypothesis: L1 — graft units are compared by engine replay; endpoint
///   agreement alone cannot establish equality.
/// - witness: `tests::laws::tests::cell_grafting_is_unital_up_to_replay`
#[spec(ensures: |ret| !bool::from(ret) || !matches!((a, b), (Elaborated::Stuck, _) | (_, Elaborated::Stuck)))]
fn elaborations_replay_equivalent(
    a: &Elaborated<'_>,
    b: &Elaborated<'_>,
    store: &CellStore,
) -> VdcCellEquality
{
    let equal = match (a, b) {
        | (&Elaborated::Trivial, &Elaborated::Trivial) => true,
        | (&Elaborated::Cert(ref ca), &Elaborated::Cert(ref cb)) => {
            bool::from(replay_equivalent(ca, cb, store))
        },
        | (&Elaborated::Trivial, &Elaborated::Cert(ref c))
        | (&Elaborated::Cert(ref c), &Elaborated::Trivial) => {
            c.overlap.peak == c.joins_at && bool::from(c.replay(store))
        },
        | (&Elaborated::Stuck, _) | (_, &Elaborated::Stuck) => false,
    };
    VdcCellEquality::from(equal)
}

/// A **description registry** — the signature namespace the reflection reads.
///
/// A thin owned map from [`NominalId`] to [`SignDesc`]:
/// `gandr-theory-levitation` mints descriptions but keeps no table, so the
/// reflection layer organizes them into the object namespace the [`Vdc`]
/// instance resolves signatures against.
#[repr(transparent)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct DescTable<G = ()>
{
    /// The descriptions, in insertion order.
    descs: Vec<SignDesc<G>>,
}

impl<G> Default for DescTable<G>
{
    /// An empty registry independent of the grade type.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn default() -> Self
    {
        Self { descs: Vec::new() }
    }
}

impl<G> DescTable<G>
{
    /// An empty registry.
    #[inline]
    #[must_use]
    /// # Specification
    /// trivial.
    pub fn new() -> Self
    {
        Self::default()
    }

    /// Register a description, returning its signature reference.
    ///
    /// # Specification
    /// - ensures: the description is appended and its [`SignatureRef::single`]
    ///   returned; lookup keeps the first description registered at an
    ///   identity.
    /// - panics: none.
    #[inline]
    /// # Adequacy
    /// - hypothesis: L3 — a real graded description remains retrievable,
    ///   duplicate identities retain the first entry, and a distinct serial
    ///   remains absent.
    /// - witness: `tests::constructor_menu::description_registry_retains_generic_grades_and_first_identity`
    #[spec(captures: expected = desc.id.clone(), ensures: |ret| ret == SignatureRef::single(expected.clone()))]
    pub fn insert(
        &mut self,
        desc: SignDesc<G>,
    ) -> SignatureRef
    {
        let id = desc.id.clone();
        self.descs.push(desc);
        SignatureRef::single(id)
    }

    /// The description with the given identity.
    ///
    /// # Specification
    /// - ensures: `Some` iff a description with a structurally-equal
    ///   [`NominalId`] was inserted.
    /// - panics: none.
    #[inline]
    /// # Adequacy
    /// - hypothesis: L3 — lookup distinguishes nominal identity from a shared
    ///   display name and retains the stored generic field grade.
    /// - witness: `tests::constructor_menu::description_registry_retains_generic_grades_and_first_identity`
    #[spec(ensures: |ref ret| match *ret { Maybe::Present(desc) => desc.id == *id, Maybe::Absent(_) => self.descs.iter().all(|desc| desc.id != *id) })]
    pub fn get(
        &self,
        id: &NominalId,
    ) -> Maybe<&SignDesc<G>, description_lookup::Absent>
    {
        match self.descs.iter().find(|desc| desc.id == *id) {
            | Some(desc) => Maybe::Present(desc),
            | None => Maybe::Absent(description_lookup::Absent::Unregistered),
        }
    }

    /// The number of registered descriptions.
    #[inline]
    #[must_use]
    /// # Specification
    /// trivial.
    pub fn len(&self) -> DescTableLength
    {
        DescTableLength::from(self.descs.len())
    }

    /// Whether the registry is empty.
    #[inline]
    #[must_use]
    /// # Specification
    /// trivial.
    pub fn is_empty(&self) -> DescTableEmptyStatus
    {
        DescTableEmptyStatus::from(self.descs.is_empty())
    }
}

/// The **virtual-double-category interface** the dictionary test checks and the
/// reflection face assumes.
///
/// Objects, tight arrows, loose arrows, and multi-ary cells, with total
/// restriction (split/fibrational by content-addressing), multicategorical cell
/// composition (grafting), and the replay-equivalence cell-equality of replay
/// semantics D1. "Virtual" is load-bearing: loose composites are **not** part
/// of the interface — they exist only as the overlap-indexed family the query
/// surface enumerates ([`crate::query`]).
pub trait Vdc
{
    /// The objects (described signatures).
    type Obj;
    /// The tight arrows (signature morphisms), strictly associative/unital.
    type Tight;
    /// The loose arrows (relation interfaces).
    type Loose;
    /// The multi-ary cells (replay-checked derived transformations).
    type Cell;

    /// The identity tight arrow on an object.
    ///
    /// # Specification
    /// - ensures: a tight arrow that is a two-sided unit for
    ///   [`Vdc::comp_tight`].
    /// - panics: none.
    /// - executable: none — this declaration has no implementing body; the
    ///   concrete interpretation carries the executable obligation.
    #[must_use]
    /// # Adequacy
    /// - hypothesis: L3 — the concrete cell-store law observes renaming images
    ///   and both boundaries under identity and composition. Other
    ///   implementations require their own interpretation witnesses.
    /// - witness: `tests::laws::tests::tight_composition_is_associative_and_unital`
    fn id_tight(
        &self,
        o: &Self::Obj,
    ) -> Self::Tight;

    /// Compose two tight arrows, `f` then `g`.
    ///
    /// # Specification
    /// - requires: `f`'s target is `g`'s source for a boundary-respecting
    ///   composite.
    /// - ensures: an associative composite with [`Vdc::id_tight`] as unit.
    /// - panics: none.
    /// - executable: none — this declaration has no implementing body; the
    ///   concrete interpretation carries the executable obligation.
    #[must_use]
    /// # Adequacy
    /// - hypothesis: L3 — the concrete cell-store law observes renaming images
    ///   and both boundaries under identity and composition. Other
    ///   implementations require their own interpretation witnesses.
    /// - witness: `tests::laws::tests::tight_composition_is_associative_and_unital`
    fn comp_tight(
        &self,
        f: &Self::Tight,
        g: &Self::Tight,
    ) -> Self::Tight;

    /// The source object of a loose arrow.
    ///
    /// # Specification
    /// - ensures: the loose arrow's source signature.
    /// - panics: none.
    /// - executable: none — this declaration has no implementing body; the
    ///   concrete interpretation carries the executable obligation.
    #[must_use]
    /// # Adequacy
    /// - hypothesis: L3 — the concrete cell-store law observes both restriction
    ///   frames and their boundaries in composition order. Other
    ///   implementations require their own interpretation witnesses.
    /// - witness: `tests::laws::tests::restriction_composes`
    fn src(
        &self,
        r: &Self::Loose,
    ) -> Self::Obj;

    /// The target object of a loose arrow.
    ///
    /// # Specification
    /// - ensures: the loose arrow's target signature.
    /// - panics: none.
    /// - executable: none — this declaration has no implementing body; the
    ///   concrete interpretation carries the executable obligation.
    #[must_use]
    /// # Adequacy
    /// - hypothesis: L3 — the concrete cell-store law observes both restriction
    ///   frames and their boundaries in composition order. Other
    ///   implementations require their own interpretation witnesses.
    /// - witness: `tests::laws::tests::restriction_composes`
    fn tgt(
        &self,
        r: &Self::Loose,
    ) -> Self::Obj;

    /// Restriction `R[s # t]` — total, split/fibrational by content-addressing.
    ///
    /// # Specification
    /// - requires: `s`'s target is `src(r)` and `t`'s target is `tgt(r)`.
    /// - ensures: the restricted loose arrow `s.src ⇸ t.src`; `restrict(r, id,
    ///   id) == r` and restriction composes (`R[s∘s′ # t∘t′] = R[s # t][s′ #
    ///   t′]`).
    /// - panics: none.
    /// - executable: none — this declaration has no implementing body; the
    ///   concrete interpretation carries the executable obligation.
    #[must_use]
    /// # Adequacy
    /// - hypothesis: L3 — the concrete cell-store law observes both restriction
    ///   frames and their boundaries in composition order. Other
    ///   implementations require their own interpretation witnesses.
    /// - witness: `tests::laws::tests::restriction_composes`
    fn restrict(
        &self,
        r: &Self::Loose,
        s: &Self::Tight,
        t: &Self::Tight,
    ) -> Self::Loose;

    /// The domain chain of a cell (`R₁; …; Rₙ`), globular after restriction.
    ///
    /// # Specification
    /// - ensures: the loose arrows the cell consumes, in order.
    /// - panics: none.
    /// - executable: none — this declaration has no implementing body; the
    ///   concrete interpretation carries the executable obligation.
    #[must_use]
    /// # Adequacy
    /// - hypothesis: L3 — the concrete cell-store law observes input order,
    ///   output boundaries and replayed grafts. Other implementations require
    ///   their own interpretation witnesses.
    /// - witness: `tests::laws::tests::cell_grafting_matches_engine_composition`
    fn cell_dom(
        &self,
        c: &Self::Cell,
    ) -> Vec<Self::Loose>;

    /// The codomain of a cell (`S`).
    ///
    /// # Specification
    /// - ensures: the loose arrow the cell produces.
    /// - panics: none.
    /// - executable: none — this declaration has no implementing body; the
    ///   concrete interpretation carries the executable obligation.
    /// # Errors
    /// Returns the derivation error when its outer cell is absent.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the concrete cell-store law observes input order,
    ///   output boundaries and replayed grafts. Other implementations require
    ///   their own interpretation witnesses.
    /// - witness: `tests::laws::tests::cell_grafting_matches_engine_composition`
    fn cell_cod(
        &self,
        c: &Self::Cell,
    ) -> Result<Self::Loose, DerivationError>;

    /// The identity cell on a loose arrow (the trivial derivation).
    ///
    /// # Specification
    /// - ensures: a cell `r ⇒ r` that is a unit for [`Vdc::compose_cells`] up
    ///   to [`Vdc::cells_equal`].
    /// - panics: none.
    /// - executable: none — this declaration has no implementing body; the
    ///   concrete interpretation carries the executable obligation.
    #[must_use]
    /// # Adequacy
    /// - hypothesis: L3 — the concrete cell-store law observes input order,
    ///   output boundaries and replayed grafts. Other implementations require
    ///   their own interpretation witnesses.
    /// - witness: `tests::laws::tests::cell_grafting_matches_engine_composition`
    fn id_cell(
        &self,
        r: &Self::Loose,
    ) -> Self::Cell;

    /// Multicategorical composition (grafting); the identity is
    /// replay-equivalence.
    ///
    /// # Specification
    /// - ensures: the cell obtained by grafting each `inners` cell into an
    ///   input slot of `outer`; associative and unital up to
    ///   [`Vdc::cells_equal`].
    /// - panics: none.
    /// - executable: none — this declaration has no implementing body; the
    ///   concrete interpretation carries the executable obligation.
    #[must_use]
    /// # Adequacy
    /// - hypothesis: L3 — the concrete cell-store law observes input order,
    ///   output boundaries and replayed grafts. Other implementations require
    ///   their own interpretation witnesses.
    /// - witness: `tests::laws::tests::cell_grafting_matches_engine_composition`
    fn compose_cells(
        &self,
        outer: &Self::Cell,
        inners: &[Self::Cell],
    ) -> Self::Cell;

    /// Whether two cells are the same transformation — replay both, compare.
    ///
    /// # Specification
    /// - ensures: `true` iff the cells share a loose-arrow boundary and their
    ///   engine elaborations are replay-equivalent.
    /// - panics: none.
    /// - executable: none — this declaration has no implementing body; the
    ///   concrete interpretation carries the executable obligation.
    #[must_use]
    /// # Adequacy
    /// - hypothesis: L3 — the concrete cell-store law observes input order,
    ///   output boundaries and replayed grafts. Other implementations require
    ///   their own interpretation witnesses.
    /// - witness: `tests::laws::tests::cell_grafting_matches_engine_composition`
    fn cells_equal(
        &self,
        a: &Self::Cell,
        b: &Self::Cell,
    ) -> VdcCellEquality;
}

/// The **cell-store instance** of [`Vdc`] — the dictionary reading of replay
/// semantics over the live rewrite layer.
///
/// Objects are [`SignatureRef`]s resolved against `descs`; tight arrows are
/// [`SigMorphism`]s; loose arrows are [`RelationRef`]s whose generating cells
/// live in `cells`; cells are [`Derivation`]s replayed against `cells`.
#[derive(Clone, Copy, Debug)]
pub struct CellStoreVdc<'store, G = ()>
{
    /// The signature namespace (`gandr-theory-levitation` descriptions).
    pub descs: &'store DescTable<G>,
    /// The content-addressed cell store (`gandr-theory-computads`).
    pub cells: &'store CellStore,
}

impl<'store, G> CellStoreVdc<'store, G>
{
    /// The instance over a description registry and a cell store.
    #[inline]
    #[must_use]
    /// # Specification
    /// trivial.
    pub fn new(
        descs: &'store DescTable<G>,
        cells: &'store CellStore,
    ) -> Self
    {
        Self { descs, cells }
    }
}

impl<G> Vdc for CellStoreVdc<'_, G>
{
    type Cell = Derivation;
    type Loose = RelationRef;
    type Obj = SignatureRef;
    type Tight = SigMorphism;

    #[inline]
    /// # Specification
    /// trivial.
    fn id_tight(
        &self,
        o: &SignatureRef,
    ) -> SigMorphism
    {
        SigMorphism::identity(o.clone())
    }

    #[inline]
    /// # Specification
    /// trivial.
    fn comp_tight(
        &self,
        f: &SigMorphism,
        g: &SigMorphism,
    ) -> SigMorphism
    {
        compose_renaming(f, g)
    }

    #[inline]
    /// # Specification
    /// trivial.
    fn src(
        &self,
        r: &RelationRef,
    ) -> SignatureRef
    {
        r.src.clone()
    }

    #[inline]
    /// # Specification
    /// trivial.
    fn tgt(
        &self,
        r: &RelationRef,
    ) -> SignatureRef
    {
        r.tgt.clone()
    }
    /// Restrict both faces while retaining the relation's generating cells.
    ///
    /// # Specification
    /// - ensures: frames compose in the split order and generators are
    ///   unchanged.
    /// - panics: none.
    #[inline]
    /// # Adequacy
    /// - hypothesis: L3 — nested and composite restriction compare both
    ///   composed frames, their boundaries and the unchanged relation
    ///   generators.
    /// - witness: `tests::laws::tests::restriction_composes`
    #[spec(ensures: |ret| ret.src == s.src && ret.tgt == t.tgt && ret.generators == r.generators && ret.name == r.name)]
    fn restrict(
        &self,
        r: &RelationRef,
        s: &SigMorphism,
        t: &SigMorphism,
    ) -> RelationRef
    {
        RelationRef {
            name: r.name.clone(),
            src: s.src.clone(),
            tgt: t.src.clone(),
            generators: r.generators.clone(),
            left: compose_renaming(s, &r.left),
            right: compose_renaming(t, &r.right),
        }
    }

    #[inline]
    /// # Specification
    /// trivial.
    fn cell_dom(
        &self,
        c: &Derivation,
    ) -> Vec<RelationRef>
    {
        c.dom()
    }

    #[inline]
    /// # Specification
    /// trivial.
    fn cell_cod(
        &self,
        c: &Derivation,
    ) -> Result<RelationRef, DerivationError>
    {
        c.cod().cloned()
    }

    #[inline]
    /// # Specification
    /// trivial.
    fn id_cell(
        &self,
        r: &RelationRef,
    ) -> Derivation
    {
        Derivation::id(r.clone())
    }

    #[inline]
    /// # Specification
    /// trivial.
    fn compose_cells(
        &self,
        outer: &Derivation,
        inners: &[Derivation],
    ) -> Derivation
    {
        Derivation::graft(outer.clone(), inners.to_vec())
    }
    /// Compare boundary chains and engine replay equivalence.
    ///
    /// # Specification
    /// - ensures: equality requires identical input and output relations and
    ///   replay-equivalent elaborations against the current store.
    /// - panics: none.
    #[inline]
    /// # Adequacy
    /// - hypothesis: L1 — graft equality compares ordered relation boundaries
    ///   and independently replayed engine evidence.
    /// - witness: `tests::laws::tests::cell_grafting_matches_engine_composition`
    #[spec(ensures: |ret| !bool::from(ret) || (a.domain().eq(b.domain()) && a.cod() == b.cod()))]
    fn cells_equal(
        &self,
        a: &Derivation,
        b: &Derivation,
    ) -> VdcCellEquality
    {
        let equal = a.domain().eq(b.domain())
            && a.cod() == b.cod()
            && bool::from(elaborations_replay_equivalent(
                &a.elaborate(),
                &b.elaborate(),
                self.cells,
            ));
        VdcCellEquality::from(equal)
    }
}

quenchant_shape::reason_enum! {
/// Why a description lookup has no result.
pub mod description_lookup {
    /// The reason the requested value is unavailable.
    #[derive(Clone, Copy, Debug, Eq, PartialEq)]
    pub enum Absent {
    /// No description with this nominal identity is registered.
    Unregistered,
}
}

}

impl core::fmt::Display for DerivationError
{
    /// Render the typed refusal and its boundary evidence.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result
    {
        f.write_str("graft has no outer derivation")
    }
}
impl core::error::Error for DerivationError
{
}
