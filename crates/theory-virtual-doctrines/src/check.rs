//! Bidirectional judgments over two-sided contexts.

use alloc::boxed::Box;
use alloc::vec::Vec;

use anodized::spec;
use gandr_theory_cell_complexes::CellId;
use gandr_theory_cell_complexes::CellStore;
use gandr_theory_levitation::Name;
use gandr_theory_levitation::NameRef;
use quenchant_shape::shape::Maybe;

use crate::boundary::CheckContextDeclaration;
use crate::boundary::DerivationIndex;
use crate::syntax::DerivationId;
use crate::syntax::ProVar;
use crate::syntax::Proterm;
use crate::syntax::ProtermKind;
use crate::syntax::ProtermNode;
use crate::syntax::Protype;
use crate::syntax::ProtypeKind;
use crate::syntax::ProtypeNode;
use crate::vdc::Derivation;
use crate::vdc::RelationRef;
use crate::vdc::SignatureRef;
use crate::vdc::TermRef;

/// The **two-sided object context** `Γ # Δ` — domain-side and codomain-side
/// object variables with their signatures.
///
/// A protype's framing terms range over the object variables declared here; the
/// two sides are the `FVDblTT` source/target contexts a protype is framed
/// between.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Context
{
    /// The domain-side (`Γ`) object variables.
    pub dom: Vec<(Name, SignatureRef)>,
    /// The codomain-side (`Δ`) object variables.
    pub cod: Vec<(Name, SignatureRef)>,
}

impl Context
{
    /// An empty two-sided context.
    #[inline]
    #[must_use]
    /// # Specification
    /// trivial.
    pub fn new() -> Self
    {
        Self::default()
    }

    /// Extend the domain side with an object variable.
    #[inline]
    #[must_use]
    /// # Specification
    /// trivial.
    pub fn with_dom(
        mut self,
        name: NameRef<'_>,
        sig: SignatureRef,
    ) -> Self
    {
        self.dom.push((Name::from(name), sig));
        self
    }

    /// Extend the codomain side with an object variable.
    #[inline]
    #[must_use]
    /// # Specification
    /// trivial.
    pub fn with_cod(
        mut self,
        name: NameRef<'_>,
        sig: SignatureRef,
    ) -> Self
    {
        self.cod.push((Name::from(name), sig));
        self
    }

    /// Whether `name` is declared on either side.
    ///
    /// # Specification
    /// - ensures: `true` iff `name` appears in `dom` or `cod`.
    /// - panics: none.
    #[inline]
    #[must_use]
    /// # Adequacy
    /// - hypothesis: L3 — names declared on either side are admitted; absent
    ///   names inside nested terms are rejected.
    /// - witness: `tests::constructor_menu::formation_observes_names_generators_and_both_seam_boundaries`
    #[spec(ensures: |ret| bool::from(ret) == self.dom.iter().chain(&self.cod).any(|entry| entry.0.as_ref() == name.as_ref()))]
    pub fn declares(
        &self,
        name: NameRef<'_>,
    ) -> CheckContextDeclaration
    {
        for declaration in self.dom.iter().chain(self.cod.iter()) {
            if declaration.0.as_ref() == name.as_ref() {
                return CheckContextDeclaration::from(true);
            }
        }
        CheckContextDeclaration::from(false)
    }
}

/// Why a protype or proterm failed to check.
///
/// Each variant is a distinct, testable rejection — the exact-variant oracle
/// the per-rule property tests assert against.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum CheckError
{
    /// A proterm variable is not bound in the hypothesis chain `Φ`.
    UnboundVar(ProVar),
    /// A [`ProtermKind::Cert`] references a derivation absent from the
    /// environment.
    UnboundDerivation(DerivationId),
    /// A term references an object variable not declared in the two-sided
    /// context.
    UndeclaredTermVar(Name),
    /// A relation protype (or tabulator) names a generating cell absent from
    /// the store — a dangling loose-arrow generator.
    UnknownRelationGenerator(CellId),
    /// `refl` was checked against a path whose endpoints differ, or whose
    /// signature disagrees with the `refl` term's.
    ReflOffDiagonal,
    /// A [`ProtermKind::Cert`] was checked against a protype that is not
    /// engine-backed (only [`ProtypeKind::Path`] / [`ProtypeKind::Rel`] are).
    NotEngineBacked,
    /// The embedded derivation of a [`ProtermKind::Cert`] does not replay.
    CertDoesNotReplay(DerivationId),
    /// A [`ProtypeKind::Compose`]'s seam signatures disagree (`tgt(l) != mid`
    /// or `src(r) != mid`).
    ComposeSeamMismatch,
    /// A synthesized or looked-up protype disagreed with the expected one.
    Mismatch
    {
        /// The protype the checker expected.
        expected: Box<Protype>,
        /// The protype it found.
        found: Box<Protype>,
    },
    /// A ⊙-introduction (`Pair`) was checked against a
    /// non-[`ProtypeKind::Compose`].
    ExpectedCompose,
    /// A ⊲/⊳-introduction (`Lam`) was checked against a non-extension protype.
    ExpectedExtension,
    /// A product introduction/projection met a non-[`ProtypeKind::Product`].
    ExpectedProduct,
    /// A path eliminator (`PathInd`) met a non-[`ProtypeKind::Path`] scrutinee.
    ExpectedPath,
    /// The unit proterm was checked against a non-[`ProtypeKind::Unit`]
    /// protype.
    ExpectedUnit,
    /// A seam eliminator (`SeamInd`) met a non-seam scrutinee.
    NotASeam,
    /// Type synthesis was requested for a proterm form that only checks.
    CannotSynthesize,
    /// A flat syntax node has fewer children than its constructor requires.
    MalformedSyntax,
}

/// The **checker** — an environment of embedded derivations and the cell store
/// they replay against.
#[derive(Clone, Copy, Debug)]
pub struct Checker<'env>
{
    /// The embedded engine derivations, indexed by [`DerivationId`].
    pub derivations: &'env [Derivation],
    /// The cell store the certificates replay against.
    pub cells: &'env CellStore,
}

/// A hypothesis chain `Φ` — a sequence of `(variable, protype)` bindings.
type Hyps = [(ProVar, Protype)];

/// A borrowed synthesized type, with a diagonal path represented without
/// allocation.
#[derive(Clone, Copy, Debug)]
enum Synthesized<'syntax>
{
    /// A type already held by the syntax or hypothesis environment.
    Type(ProtypeNode<'syntax>),
    /// The diagonal path synthesized from reflexivity.
    Refl
    {
        /// The reflected signature.
        sig: &'syntax SignatureRef,
        /// The repeated endpoint.
        term: &'syntax TermRef,
    },
}
impl Synthesized<'_>
{
    /// Own the inferred type at the public result boundary.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn to_owned(self) -> Protype
    {
        match self {
            | Self::Type(node) => node.to_owned(),
            | Self::Refl { sig, term } => Protype::path(sig.clone(), term.clone(), term.clone()),
        }
    }
}
/// The lexical scope of a judgment.
#[derive(Clone, Copy, Debug)]
enum Scope
{
    /// The caller's hypothesis chain.
    Root,
    /// A local extension stored in the binding table.
    Local(BindingIndex),
}
/// Index into the local binding table.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
struct BindingIndex(usize);
/// One immutable local binding, linked by index rather than ownership.
struct Binding<'syntax>
{
    /// The bound hypothesis.
    name: &'syntax ProVar,
    /// Its reflected type.
    ty: ProtypeNode<'syntax>,
    /// The outer lexical scope.
    parent: Scope,
}
/// One action in the iterative bidirectional judgment machine.
enum Judgment<'syntax>
{
    /// Check a term under a lexical scope.
    Check(Scope, ProtermNode<'syntax>, Synthesized<'syntax>),
    /// Infer a type under a lexical scope.
    Synth(Scope, ProtermNode<'syntax>),
    /// Compare the inferred result with an expected type.
    Expect(Synthesized<'syntax>),
    /// Require a path result.
    Path,
    /// Require a seam result.
    Seam,
    /// Project the first component.
    Left,
    /// Project the second component.
    Right,
    /// Check the argument after inferring the function.
    Apply(Scope, ProtermNode<'syntax>),
    /// Retain the inferred codomain after argument checking.
    Finish(ProtypeNode<'syntax>),
}
quenchant_shape::reason_enum! {
/// Why a successful judgment has no synthesized type.
mod synthesis_result {
    /// The reason the requested value is unavailable.
    #[derive(Clone, Copy, Debug, Eq, PartialEq)]
    pub enum Absent {
    /// The root judgment was in checking mode.
    Checking,
}
}
}
/// Which boundary of a protype a seam requires.
#[derive(Clone, Copy, Debug)]
enum Side
{
    /// The source boundary.
    Source,
    /// The target boundary.
    Target,
}

impl<'env> Checker<'env>
{
    /// Bind the derivation environment and replay store.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn new(
        derivations: &'env [Derivation],
        cells: &'env CellStore,
    ) -> Self
    {
        Self { derivations, cells }
    }

    /// Validate the framing variables, relation generators and seam boundaries
    /// of a type.
    ///
    /// # Specification
    /// - ensures: accepts exactly when all framing variables are declared, all
    ///   generators resolve and every composite's source and target meet its
    ///   middle signature.
    /// - fails: names the first unbound variable, absent generator or
    ///   disagreeing seam.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns the formation variant of [`CheckError`] for the failed
    /// obligation.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — nearest-invalid contexts, generators and asymmetric
    ///   seam signatures distinguish each formation guard.
    /// - witness: `tests::constructor_menu::formation_observes_names_generators_and_both_seam_boundaries`
    #[inline]
    #[spec(ensures: |ref result| !matches!(result, Err(CheckError::UnknownRelationGenerator(id)) if matches!(self.cells.get(*id), Maybe::Present(_))))]
    pub fn check_protype(
        &self,
        ctx: &Context,
        protype: &Protype,
    ) -> Result<(), CheckError>
    {
        let mut pending = alloc::vec![protype.to_node()];
        while let Some(node) = pending.pop() {
            match node.kind() {
                | &ProtypeKind::Path {
                    ref lhs, ref rhs, ..
                } => {
                    term_vars_declared(ctx, lhs)?;
                    term_vars_declared(ctx, rhs)?;
                },
                | &ProtypeKind::Rel {
                    ref rel,
                    ref lhs,
                    ref rhs,
                } => {
                    term_vars_declared(ctx, lhs)?;
                    term_vars_declared(ctx, rhs)?;
                    self.relation_generators_present(rel)?;
                },
                | &ProtypeKind::Tabulate { ref rel } => self.relation_generators_present(rel)?,
                | &ProtypeKind::Compose { ref mid } => {
                    let (left, right) = type_children(node)?;
                    if boundary(left, Side::Target)? != mid || boundary(right, Side::Source)? != mid
                    {
                        return Err(CheckError::ComposeSeamMismatch);
                    }
                },
                | &ProtypeKind::ExtendL
                | &ProtypeKind::ExtendR
                | &ProtypeKind::Product
                | &ProtypeKind::Unit => {},
            }
            let start = pending.len();
            pending.extend(node.children());
            if let Some(children) = pending.get_mut(start ..) {
                children.reverse();
            }
        }
        Ok(())
    }
    /// Check every generating-cell reference in a relation.
    ///
    /// # Specification
    /// - ensures: accepts exactly when all generators occur in the replay
    ///   store.
    /// - fails: returns the first absent generator.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns [`CheckError::UnknownRelationGenerator`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a relation with one absent generator is refused while
    ///   its resolvable neighbor is accepted.
    /// - witness: `tests::constructor_menu::formation_observes_names_generators_and_both_seam_boundaries`
    #[spec(ensures: |ref result| result.is_ok() == rel.generators.iter().all(|id| matches!(self.cells.get(*id), Maybe::Present(_))))]
    fn relation_generators_present(
        &self,
        rel: &RelationRef,
    ) -> Result<(), CheckError>
    {
        for &id in &rel.generators {
            if matches!(self.cells.get(id), Maybe::Absent(_)) {
                return Err(CheckError::UnknownRelationGenerator(id));
            }
        }
        Ok(())
    }
    /// Check a term against an expected type under the supplied hypotheses.
    ///
    /// # Specification
    /// - ensures: introduction and elimination rules preserve their constructor
    ///   shapes; reflexivity requires the diagonal; engine-backed certificate
    ///   terms pass exactly when their evidence replays.
    /// - fails: returns the precise shape, binding, equality or replay refusal.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns [`CheckError`] for the first refused judgment.
    ///
    /// # Adequacy
    /// - hypothesis: L1 replay and L3 constructor-menu near misses distinguish
    ///   each accepting and refusing rule through the public checker.
    /// - witness: `tests::constructor_menu::every_constructor_has_an_accepted_and_nearest_invalid_judgment`
    /// - witness: `tests::constructor_menu::certificate_judgments_follow_replay_under_field_corruption`
    #[inline]
    #[spec(ensures: |ref result| !matches!(result, Err(CheckError::UnboundDerivation(id)) if usize::from(id.index()) < self.derivations.len()))]
    pub fn check(
        &self,
        ctx: &Context,
        hyps: &Hyps,
        term: &Proterm,
        expected: &Protype,
    ) -> Result<(), CheckError>
    {
        self.run_judgment(
            ctx,
            hyps,
            Judgment::Check(
                Scope::Root,
                term.to_node(),
                Synthesized::Type(expected.to_node()),
            ),
        )
        .map(|_| ())
    }
    /// Infer the type of a variable, reflexivity term, projection or
    /// application.
    ///
    /// # Specification
    /// - ensures: returns the selected hypothesis, diagonal path, product
    ///   factor or extension codomain.
    /// - fails: checking-only forms yield `CannotSynthesize`; ill-shaped
    ///   eliminations retain their precise refusal.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns [`CheckError`] for a failed synthesis obligation.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — both product projections, both extensions, shadowed
    ///   hypotheses and check-only forms distinguish synthesis from checking.
    /// - witness: `tests::constructor_menu::every_constructor_has_an_accepted_and_nearest_invalid_judgment`
    #[inline]
    #[spec(ensures: |ref result| !matches!(result, Err(CheckError::UnboundDerivation(_))))]
    pub fn synth(
        &self,
        ctx: &Context,
        hyps: &Hyps,
        term: &Proterm,
    ) -> Result<Protype, CheckError>
    {
        match self.run_judgment(ctx, hyps, Judgment::Synth(Scope::Root, term.to_node()))? {
            | Maybe::Present(ty) => Ok(ty.to_owned()),
            | Maybe::Absent(synthesis_result::Absent::Checking) => {
                Err(CheckError::CannotSynthesize)
            },
        }
    }
    /// Execute a judgment with borrowed types and index-linked lexical scopes.
    ///
    /// # Specification
    /// - ensures: checking has no result type; synthesis retains its inferred
    ///   type; local extensions affect only their descendants.
    /// - fails: returns the first failed constructor obligation.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns [`CheckError`] from the selected judgment rule.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — sibling scopes and nested eliminations expose leaked
    ///   hypotheses, result-stack reversal and skipped premises.
    /// - witness: `tests::constructor_menu::every_constructor_has_an_accepted_and_nearest_invalid_judgment`
    #[spec(ensures: |ref result| !matches!(result, Err(CheckError::UnboundDerivation(id)) if usize::from(id.index()) < self.derivations.len()))]
    fn run_judgment<'syntax>(
        &self,
        _ctx: &Context,
        hyps: &'syntax Hyps,
        initial: Judgment<'syntax>,
    ) -> Result<Maybe<Synthesized<'syntax>, synthesis_result::Absent>, CheckError>
    {
        let mut pending = alloc::vec![initial];
        let mut results = Vec::new();
        let mut bindings = Vec::new();
        while let Some(judgment) = pending.pop() {
            match judgment {
                | Judgment::Check(scope, term, expected) => match term.kind() {
                    | &ProtermKind::Var { ref var } => expect_equal(
                        expected,
                        Synthesized::Type(lookup_hyp(hyps, &bindings, scope, var)?),
                    )?,
                    | &ProtermKind::Refl { ref sig, ref term } => {
                        if expected != (Synthesized::Refl { sig, term }) {
                            return Err(CheckError::ReflOffDiagonal);
                        }
                    },
                    | &ProtermKind::Cert { ref id } => self.check_cert(*id, expected)?,
                    | &ProtermKind::PathInd { ref motive } => {
                        expect_equal(expected, Synthesized::Type(motive.to_node()))?;
                        let (base, scrut) = term_children(term)?;
                        pending.push(Judgment::Check(
                            scope,
                            base,
                            Synthesized::Type(motive.to_node()),
                        ));
                        pending.push(Judgment::Path);
                        pending.push(Judgment::Synth(scope, scrut));
                    },
                    | &ProtermKind::Pair { .. } | &ProtermKind::ProdIntro => {
                        let Synthesized::Type(ty) = expected
                        else {
                            return Err(if matches!(term.kind(), &ProtermKind::Pair { .. }) {
                                CheckError::ExpectedCompose
                            }
                            else {
                                CheckError::ExpectedProduct
                            });
                        };
                        match (term.kind(), ty.kind()) {
                            | (&ProtermKind::Pair { .. }, &ProtypeKind::Compose { .. })
                            | (&ProtermKind::ProdIntro, &ProtypeKind::Product) => {},
                            | (&ProtermKind::Pair { .. }, _) => {
                                return Err(CheckError::ExpectedCompose);
                            },
                            | _ => return Err(CheckError::ExpectedProduct),
                        }
                        let (l, r) = term_children(term)?;
                        let (pl, pr) = type_children(ty)?;
                        pending.push(Judgment::Check(scope, r, Synthesized::Type(pr)));
                        pending.push(Judgment::Check(scope, l, Synthesized::Type(pl)));
                    },
                    | &ProtermKind::SeamInd => {
                        let (scrut, arm) = term_children(term)?;
                        pending.push(Judgment::Check(scope, arm, expected));
                        pending.push(Judgment::Seam);
                        pending.push(Judgment::Synth(scope, scrut));
                    },
                    | &ProtermKind::Lam { ref hyp } => {
                        let ty = extension(expected)?;
                        let (dom, cod) = type_children(ty)?;
                        let child_scope = Scope::Local(BindingIndex(bindings.len()));
                        bindings.push(Binding {
                            name: hyp,
                            ty: dom,
                            parent: scope,
                        });
                        let body = term.children().next().ok_or(CheckError::MalformedSyntax)?;
                        pending.push(Judgment::Check(child_scope, body, Synthesized::Type(cod)));
                    },
                    | &ProtermKind::App | &ProtermKind::ProjL | &ProtermKind::ProjR => {
                        pending.push(Judgment::Expect(expected));
                        pending.push(Judgment::Synth(scope, term));
                    },
                    | &ProtermKind::UnitTerm => {
                        if !matches!(expected, Synthesized::Type(ty) if matches!(ty.kind(), &ProtypeKind::Unit))
                        {
                            return Err(CheckError::ExpectedUnit);
                        }
                    },
                },
                | Judgment::Synth(scope, term) => match term.kind() {
                    | &ProtermKind::Var { ref var } => {
                        results.push(Synthesized::Type(lookup_hyp(hyps, &bindings, scope, var)?));
                    },
                    | &ProtermKind::Refl { ref sig, ref term } => {
                        results.push(Synthesized::Refl { sig, term });
                    },
                    | &ProtermKind::ProjL | &ProtermKind::ProjR => {
                        pending.push(if matches!(term.kind(), &ProtermKind::ProjL) {
                            Judgment::Left
                        }
                        else {
                            Judgment::Right
                        });
                        pending.push(Judgment::Synth(
                            scope,
                            term.children().next().ok_or(CheckError::MalformedSyntax)?,
                        ));
                    },
                    | &ProtermKind::App => {
                        let (f, arg) = term_children(term)?;
                        pending.push(Judgment::Apply(scope, arg));
                        pending.push(Judgment::Synth(scope, f));
                    },
                    | _ => return Err(CheckError::CannotSynthesize),
                },
                | Judgment::Expect(expected) => {
                    expect_equal(expected, results.pop().ok_or(CheckError::CannotSynthesize)?)?;
                },
                | Judgment::Path => match results.pop().ok_or(CheckError::CannotSynthesize)? {
                    | Synthesized::Refl { .. } => {},
                    | Synthesized::Type(ty) if matches!(ty.kind(), &ProtypeKind::Path { .. }) => {},
                    | _ => return Err(CheckError::ExpectedPath),
                },
                | Judgment::Seam => {
                    if !matches!(results.pop(), Some(Synthesized::Type(ty)) if matches!(ty.kind(), &ProtypeKind::Compose { .. }))
                    {
                        return Err(CheckError::NotASeam);
                    }
                },
                | Judgment::Left | Judgment::Right => {
                    let Some(Synthesized::Type(ty)) = results.pop()
                    else {
                        return Err(CheckError::ExpectedProduct);
                    };
                    if !matches!(ty.kind(), &ProtypeKind::Product) {
                        return Err(CheckError::ExpectedProduct);
                    }
                    let (left, right) = type_children(ty)?;
                    results.push(Synthesized::Type(if matches!(judgment, Judgment::Left) {
                        left
                    }
                    else {
                        right
                    }));
                },
                | Judgment::Apply(scope, arg) => {
                    let ty = extension(results.pop().ok_or(CheckError::CannotSynthesize)?)?;
                    let (dom, cod) = type_children(ty)?;
                    pending.push(Judgment::Finish(cod));
                    pending.push(Judgment::Check(scope, arg, Synthesized::Type(dom)));
                },
                | Judgment::Finish(cod) => results.push(Synthesized::Type(cod)),
            }
        }
        Ok(match results.pop() {
            | Some(ty) => Maybe::Present(ty),
            | None => Maybe::Absent(synthesis_result::Absent::Checking),
        })
    }
    /// Validate an embedded derivation for an engine-backed expected type.
    ///
    /// # Specification
    /// - ensures: only path and relation types accept certificates, and only on
    ///   successful replay.
    /// - fails: distinguishes an absent derivation, a non-engine type and
    ///   failed replay.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns `UnboundDerivation`, `NotEngineBacked` or `CertDoesNotReplay`.
    ///
    /// # Adequacy
    /// - hypothesis: L1 — corrupting one certificate field separates validation
    ///   from mere environment membership.
    /// - witness: `tests::constructor_menu::certificate_judgments_follow_replay_under_field_corruption`
    #[spec(ensures: |ref result| !matches!(result, Err(CheckError::UnboundDerivation(_))) || usize::from(id.index()) >= self.derivations.len())]
    fn check_cert(
        &self,
        id: DerivationId,
        expected: Synthesized<'_>,
    ) -> Result<(), CheckError>
    {
        let derivation = self
            .derivations
            .get(usize::from(DerivationIndex::from(id)))
            .ok_or(CheckError::UnboundDerivation(id))?;
        if !matches!(expected, Synthesized::Refl { .. })
            && !matches!(expected, Synthesized::Type(ty) if matches!(ty.kind(), &ProtypeKind::Path { .. } | &ProtypeKind::Rel { .. }))
        {
            return Err(CheckError::NotEngineBacked);
        }
        if bool::from(derivation.replays(self.cells)) {
            Ok(())
        }
        else {
            Err(CheckError::CertDoesNotReplay(id))
        }
    }
}

impl PartialEq for Synthesized<'_>
{
    /// Compare inferred types, including a diagonal path represented by
    /// reflexivity.
    ///
    /// # Specification
    /// - ensures: equality observes the same signature and endpoints as an
    ///   owned path type.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — diagonal, off-diagonal and wrong-signature paths
    ///   distinguish the borrowed and reflexive representations.
    /// - witness: `tests::constructor_menu::every_constructor_has_an_accepted_and_nearest_invalid_judgment`
    #[inline]
    #[spec(ensures: |result| result == ((*self).to_owned() == (*other).to_owned()))]
    fn eq(
        &self,
        other: &Self,
    ) -> bool
    {
        match (*self, *other) {
            | (Self::Type(left), Self::Type(right)) => left == right,
            | (
                Self::Refl {
                    sig: left_sig,
                    term: left,
                },
                Self::Refl {
                    sig: right_sig,
                    term: right,
                },
            ) => left_sig == right_sig && left == right,
            | (Self::Type(node), Self::Refl { sig, term })
            | (Self::Refl { sig, term }, Self::Type(node)) => {
                matches!(*node.kind(), ProtypeKind::Path { sig: ref expected, ref lhs, ref rhs } if sig == expected && term == lhs && term == rhs)
            },
        }
    }
}
/// Retrieve two type children from a binary form.
///
/// # Specification
/// - ensures: returns the first and second children in declaration order.
/// - fails: `MalformedSyntax` when either child is absent.
/// - panics: none.
///
/// # Errors
/// Returns `MalformedSyntax` for a non-binary form.
///
/// # Adequacy
/// - hypothesis: L3 — asymmetric product and extension types distinguish
///   swapped children.
/// - witness: `tests::constructor_menu::every_constructor_has_an_accepted_and_nearest_invalid_judgment`
#[spec(ensures: |ref result| result.is_ok() == (node.children().count() >= 2))]
fn type_children(node: ProtypeNode<'_>) -> Result<(ProtypeNode<'_>, ProtypeNode<'_>), CheckError>
{
    let mut children = node.children();
    let left = children.next().ok_or(CheckError::MalformedSyntax)?;
    let right = children.next().ok_or(CheckError::MalformedSyntax)?;
    Ok((left, right))
}
/// Retrieve two term children from a binary form.
///
/// # Specification
/// - ensures: returns the first and second children in declaration order.
/// - fails: `MalformedSyntax` when either child is absent.
/// - panics: none.
///
/// # Errors
/// Returns `MalformedSyntax` for a non-binary form.
///
/// # Adequacy
/// - hypothesis: L3 — asymmetric applications and eliminations distinguish
///   reversed children.
/// - witness: `tests::constructor_menu::every_constructor_has_an_accepted_and_nearest_invalid_judgment`
#[spec(ensures: |ref result| result.is_ok() == (node.children().count() >= 2))]
fn term_children(node: ProtermNode<'_>) -> Result<(ProtermNode<'_>, ProtermNode<'_>), CheckError>
{
    let mut children = node.children();
    let left = children.next().ok_or(CheckError::MalformedSyntax)?;
    let right = children.next().ok_or(CheckError::MalformedSyntax)?;
    Ok((left, right))
}
/// Select an extension type from a synthesized result.
///
/// # Specification
/// - ensures: returns precisely left and right extension forms.
/// - fails: `ExpectedExtension` for every other type.
/// - panics: none.
///
/// # Errors
/// Returns `ExpectedExtension` outside the extension fragment.
///
/// # Adequacy
/// - hypothesis: L3 — both extension forms and the nearest product form
///   distinguish the shape guard.
/// - witness: `tests::constructor_menu::every_constructor_has_an_accepted_and_nearest_invalid_judgment`
#[spec(ensures: |ref result| result.is_ok() == matches!(ty, Synthesized::Type(node) if matches!(node.kind(), &ProtypeKind::ExtendL | &ProtypeKind::ExtendR)))]
fn extension(ty: Synthesized<'_>) -> Result<ProtypeNode<'_>, CheckError>
{
    match ty {
        | Synthesized::Type(node)
            if matches!(node.kind(), &ProtypeKind::ExtendL | &ProtypeKind::ExtendR) =>
        {
            Ok(node)
        },
        | _ => Err(CheckError::ExpectedExtension),
    }
}
/// Find the innermost hypothesis without copying the environment.
///
/// # Specification
/// - ensures: local scopes shadow outer scopes, which shadow the caller's chain
///   in reverse binding order.
/// - fails: `UnboundVar` when no visible binding matches.
/// - panics: none.
///
/// # Errors
/// Returns `UnboundVar` for an absent hypothesis or `MalformedSyntax` for an
/// invalid scope index.
///
/// # Adequacy
/// - hypothesis: L3 — nested lambdas and sibling checks distinguish lexical
///   scope from global accumulation.
/// - witness: `tests::constructor_menu::every_constructor_has_an_accepted_and_nearest_invalid_judgment`
#[spec(ensures: |ref result| !matches!(result, Err(CheckError::UnboundVar(found)) if found != var))]
fn lookup_hyp<'syntax>(
    hyps: &'syntax Hyps,
    bindings: &[Binding<'syntax>],
    mut scope: Scope,
    var: &ProVar,
) -> Result<ProtypeNode<'syntax>, CheckError>
{
    while let Scope::Local(index) = scope {
        let binding = bindings.get(index.0).ok_or(CheckError::MalformedSyntax)?;
        if binding.name == var {
            return Ok(binding.ty);
        }
        scope = binding.parent;
    }
    for entry in hyps.iter().rev() {
        if &entry.0 == var {
            return Ok(entry.1.to_node());
        }
    }
    Err(CheckError::UnboundVar(var.clone()))
}
/// Compare an expected and inferred type, preserving mismatches as owned
/// evidence.
///
/// # Specification
/// - ensures: accepts exactly equal reflected types.
/// - fails: Mismatch retains both types, in expected/found order.
/// - panics: none.
///
/// # Errors
/// Returns Mismatch on unequal types.
///
/// # Adequacy
/// - hypothesis: L3 — asymmetric type pairs distinguish an omitted comparison
///   or reversed diagnostic payload.
/// - witness: `tests::constructor_menu::every_constructor_has_an_accepted_and_nearest_invalid_judgment`
#[spec(ensures: |ref result| result.is_ok() == (expected == found))]
fn expect_equal(
    expected: Synthesized<'_>,
    found: Synthesized<'_>,
) -> Result<(), CheckError>
{
    if expected == found {
        Ok(())
    }
    else {
        Err(CheckError::Mismatch {
            expected: Box::new(expected.to_owned()),
            found: Box::new(found.to_owned()),
        })
    }
}
/// Check free-variable declaration without collecting a copied variable list.
///
/// # Specification
/// - ensures: accepts exactly when every free variable is declared on either
///   side.
/// - fails: `UndeclaredTermVar` retains the first absent variable.
/// - panics: none.
///
/// # Errors
/// Returns `UndeclaredTermVar` for an absent object variable.
///
/// # Adequacy
/// - hypothesis: L3 — one declared and one undeclared variable under a
///   constructor distinguish traversal from head-only checking.
/// - witness: `tests::constructor_menu::formation_observes_names_generators_and_both_seam_boundaries`
#[spec(ensures: |ref result| result.is_ok() == term.term().to_node().vars().all(|var| bool::from(ctx.declares(NameRef::from(var.as_ref())))))]
fn term_vars_declared(
    ctx: &Context,
    term: &TermRef,
) -> Result<(), CheckError>
{
    for var in term.term().to_node().vars() {
        if !bool::from(ctx.declares(NameRef::from(var.as_ref()))) {
            return Err(CheckError::UndeclaredTermVar(var.clone()));
        }
    }
    Ok(())
}
/// Follow the selected edge of composites to its framing signature.
///
/// # Specification
/// - ensures: returns the path signature or selected relation boundary under
///   nested composition.
/// - fails: `ComposeSeamMismatch` for forms without one framing signature.
/// - panics: none.
///
/// # Errors
/// Returns `ComposeSeamMismatch` or `MalformedSyntax` for an absent child.
///
/// # Adequacy
/// - hypothesis: L3 — distinct source, middle and target signatures distinguish
///   either boundary direction.
/// - witness: `tests::constructor_menu::formation_observes_names_generators_and_both_seam_boundaries`
#[spec(ensures: |ref result| !matches!(result, Err(CheckError::UnboundVar(_))))]
fn boundary(
    mut node: ProtypeNode<'_>,
    side: Side,
) -> Result<&SignatureRef, CheckError>
{
    loop {
        match node.kind() {
            | &ProtypeKind::Path { ref sig, .. } => return Ok(sig),
            | &ProtypeKind::Rel { ref rel, .. } => {
                return Ok(match side {
                    | Side::Source => &rel.src,
                    | Side::Target => &rel.tgt,
                });
            },
            | &ProtypeKind::Compose { .. } => {
                let (left, right) = type_children(node)?;
                node = match side {
                    | Side::Source => left,
                    | Side::Target => right,
                };
            },
            | _ => return Err(CheckError::ComposeSeamMismatch),
        }
    }
}

impl core::fmt::Display for CheckError
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
        f.write_str(match *self {
            | Self::UnboundVar(_) => "unbound proterm variable",
            | Self::UnboundDerivation(_) => "unbound derivation",
            | Self::UndeclaredTermVar(_) => "undeclared object variable",
            | Self::UnknownRelationGenerator(_) => "unissued relation generator",
            | Self::ReflOffDiagonal => "reflexivity does not match the path diagonal",
            | Self::NotEngineBacked => "certificate judgment requires a path or relation",
            | Self::CertDoesNotReplay(_) => "certificate does not replay",
            | Self::ComposeSeamMismatch => "composition signatures do not agree at the seam",
            | Self::Mismatch { .. } => "synthesized and expected protypes disagree",
            | Self::ExpectedCompose => "expected a seam composite",
            | Self::ExpectedExtension => "expected an extension",
            | Self::ExpectedProduct => "expected a product",
            | Self::ExpectedPath => "expected a path",
            | Self::ExpectedUnit => "expected the unit protype",
            | Self::NotASeam => "scrutinee is not a seam",
            | Self::CannotSynthesize => "this proterm requires an expected protype",
            | Self::MalformedSyntax => "syntax is missing a constructor child",
        })
    }
}
impl core::error::Error for CheckError
{
}
