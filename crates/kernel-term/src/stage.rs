//! Experimental structural staging vocabulary, separate from the persisted
//! core.
//!
//! `In M` is an ordinary hypothesis. Object classifiers carry `Inner(M)`;
//! lifting, quotation and splicing never transform a context. This arena has
//! no wire encoding and confers no typing or conversion authority.

mod lookup;

use alloc::collections::BTreeMap;
use alloc::vec::Vec;
use core::fmt;

use anodized::spec;
use lookup::Lookup;
use lookup::Probe;
use lookup::hash_of;
use quenchant_shape::shape::Maybe;

/// Declare an arena-local nominal coordinate.
macro_rules! coordinate {
    ($name:ident, $doc:literal) => {
        #[doc = $doc]
        #[repr(transparent)]
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub struct $name(pub usize);
    };
}

coordinate!(Model, "An object-language model index, not a context lock.");
coordinate!(TypeId, "An arena-local classifier coordinate.");
coordinate!(TermId, "An arena-local term coordinate.");
coordinate!(
    Index,
    "A de Bruijn distance in the ordinary hypothesis telescope."
);
coordinate!(
    Natural,
    "A finite natural numeral used by the staging experiment."
);
coordinate!(Budget, "Remaining work units for a staging walk.");

/// The outer framework and one indexed inner universe.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Stage
{
    /// The meta level.
    Outer,
    /// The object level entered by an `In` hypothesis.
    Inner(Model),
}

/// Classifiers of the structural natural-number staging fragment.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Type
{
    /// Permission to use an object-language model.
    In(Model),
    /// Codes for types of the indexed object language.
    Universe(Model),
    /// Naturals at one stage.
    Nat(Stage),
    /// A non-dependent structural function, with both ends at one stage.
    Arrow(TypeId, TypeId),
    /// Meta programs producing terms of an inner type: `⇑ A`.
    Lift(TypeId),
}

/// Terms; all recursive positions are arena coordinates.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Term
{
    /// An ordinary hypothesis, counted from the telescope's end.
    Variable(Index),
    /// A natural numeral at its stated stage.
    Natural(Stage, Natural),
    /// A code in the inner universe.
    Code(TypeId),
    /// Structural abstraction with an explicit domain.
    Lambda(TypeId, TermId),
    /// Structural application.
    Apply(TermId, TermId),
    /// Object multiplication, deliberately residual rather than evaluated.
    Multiply(TermId, TermId),
    /// Quote an object term as a meta program.
    Quote(TermId),
    /// Splice a meta program into the object language.
    Splice(TermId),
    /// Natural iteration: count, initial value, endomorphism.
    Iterate(TermId, TermId, TermId),
    /// A proposed elimination with a result classifier; formation checks the
    /// universe boundary before deciding the supported identity case.
    Eliminate(TermId, TypeId),
}

/// One elementary conversion rule in an untrusted certificate.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Rule
{
    /// Equal constructors over already certified child pairs.
    Congruence,
    /// Structural lambda application.
    Beta,
    /// `~<t> = t`.
    SpliceQuote,
    /// `<~u> = u`.
    QuoteSplice,
    /// Natural iteration at zero.
    IterateZero,
    /// Natural iteration at a successor.
    IterateSuccessor,
    /// Identity elimination within a universe.
    Eliminate,
}

/// A proposed equation, carrying no authority until kernel replay.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Step
{
    /// Left side of the proposed equation.
    pub source: TermId,
    /// Right side of the proposed equation.
    pub target: TermId,
    /// Rule the producer asks the kernel to check.
    pub rule: Rule,
}

/// A normalization proposal; replay must relate its endpoints through steps.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Certificate
{
    /// Original program.
    pub source: TermId,
    /// Proposed normal form.
    pub target: TermId,
    /// Ordered elementary equations.
    pub steps: Vec<Step>,
}

/// Typed refusals shared by syntax, formation, normalization and replay.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum StageError
{
    /// A referenced term does not belong to the available arena prefix.
    UnknownTerm(TermId),
    /// A referenced classifier does not belong to the available prefix.
    UnknownType(TypeId),
    /// A variable is outside the ordinary telescope.
    Unbound(Index),
    /// The indexed universe has no `j : In M` hypothesis.
    MissingHypothesis(Model),
    /// A term or classifier violates a formation rule.
    TypeMismatch,
    /// An elimination attempts to leave the inner universe for the outer.
    InnerToOuter,
    /// Nested staging is outside this one-depth fragment.
    StageMismatch,
    /// A numeral, index, or residual arithmetic result overflowed.
    Overflow,
    /// A bounded walk exhausted its work allowance.
    Exhausted,
    /// A certificate equation or endpoint connection is invalid.
    InvalidCertificate,
    /// An internal worklist did not have its required result.
    Unbalanced,
    /// A proposed residual is not a closed first-order natural function.
    NotResidual,
}

impl fmt::Display for StageError
{
    /// Render a typed refusal without discarding its payload.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        match *self {
            | Self::UnknownTerm(id) => write!(f, "unknown stage term {}", id.0),
            | Self::UnknownType(id) => write!(f, "unknown stage type {}", id.0),
            | Self::Unbound(index) => write!(f, "unbound stage variable {}", index.0),
            | Self::MissingHypothesis(model) => {
                write!(f, "missing In hypothesis for model {}", model.0)
            },
            | Self::TypeMismatch => f.write_str("stage type mismatch"),
            | Self::InnerToOuter => f.write_str("inner-to-outer elimination refused"),
            | Self::StageMismatch => f.write_str("stage universe mismatch"),
            | Self::Overflow => f.write_str("stage arithmetic overflow"),
            | Self::Exhausted => f.write_str("stage work budget exhausted"),
            | Self::InvalidCertificate => f.write_str("invalid stage certificate"),
            | Self::Unbalanced => f.write_str("unbalanced stage worklist"),
            | Self::NotResidual => f.write_str("not a closed first-order residual"),
        }
    }
}
impl core::error::Error for StageError
{
}

/// Append-only staging syntax with canonical classifier identities.
///
/// # Specification
/// - ensures: allocated children precede parents; equal classifier descriptors
///   share an identity. Term allocation preserves supplied graph sharing.
/// - panics: none.
/// - executable: none — this data declaration has no callable boundary;
///   allocation and lookup carry the executable prefix and interning laws.
///
/// # Adequacy
/// - hypothesis: L3 — valid and forward references, repeated classifiers and
///   shared children distinguish cyclic allocation and lost canonical identity.
/// - witness: `stage::tests::syntax_boundaries`
#[derive(Clone, Debug, Default)]
pub struct Arena
{
    /// Canonical classifier descriptors in dependency order.
    types: Vec<Type>,
    /// Descriptor lookup; equality here concerns syntax, not conversion.
    type_ids: Lookup,
    /// Terms in dependency order.
    terms: Vec<Term>,
    /// Exact constructor, payload and child lookup within this arena.
    term_ids: Lookup,
}

quenchant_shape::reason_enum! {
    /// Why an exact lookup names no coordinate.
    pub mod interned {
        /// The reason no coordinate is returned.
        #[derive(Clone, Copy, Debug, Eq, PartialEq)]
        pub enum Absent {
            /// No term with this constructor, payload and children is interned.
            Uninterned,
        }
    }
}

impl Budget
{
    /// Charge one bounded operation.
    ///
    /// # Specification
    /// - ensures: decrements a positive allowance exactly once.
    /// - fails: `Exhausted` at zero, leaving it unchanged.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns `Exhausted` at zero.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the zero boundary distinguishes exhaustion.
    /// - witness: `stage::tests::syntax_boundaries`
    #[inline]
    #[spec(captures: remaining = self.0, ensures: |ret| match remaining.checked_sub(1) {
        Some(next) => ret.is_ok() && self.0 == next,
        None => ret == Err(StageError::Exhausted) && self.0 == remaining,
    })]
    pub fn spend(&mut self) -> Result<(), StageError>
    {
        self.0 = self.0.checked_sub(1).ok_or(StageError::Exhausted)?;
        Ok(())
    }
}

impl Arena
{
    /// Resolve a classifier.
    ///
    /// # Specification
    /// - ensures: returns the descriptor at the supplied coordinate.
    /// - fails: `UnknownType` outside the arena.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns `UnknownType` for an absent coordinate.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — live and absent coordinates distinguish lookup.
    /// - witness: `stage::tests::syntax_boundaries`
    #[inline]
    #[spec(ensures: |ret| ret == self.types.get(id.0).copied().ok_or(StageError::UnknownType(id)))]
    pub fn ty(
        &self,
        id: TypeId,
    ) -> Result<Type, StageError>
    {
        self.types
            .get(id.0)
            .copied()
            .ok_or(StageError::UnknownType(id))
    }

    /// Resolve a term.
    ///
    /// # Specification
    /// - ensures: returns the term at the supplied coordinate.
    /// - fails: `UnknownTerm` outside the arena.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns `UnknownTerm` for an absent coordinate.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — live and absent coordinates distinguish lookup.
    /// - witness: `stage::tests::syntax_boundaries`
    #[inline]
    #[spec(ensures: |ret| ret == self.terms.get(id.0).copied().ok_or(StageError::UnknownTerm(id)))]
    pub fn term(
        &self,
        id: TermId,
    ) -> Result<Term, StageError>
    {
        self.terms
            .get(id.0)
            .copied()
            .ok_or(StageError::UnknownTerm(id))
    }

    /// Look up an exact term without interning it.
    ///
    /// # Specification
    /// - ensures: `Present(id)` exactly when `alloc(term)` would return the
    ///   existing `id`; the arena is unchanged and nothing is allocated.
    /// - provides: `interned::Absent::Uninterned` when no equal term is live.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — interned, uninterned and payload-distinct terms
    ///   distinguish exact lookup from coincidence.
    /// - witness: `stage::tests::term_interning_preserves_exact_content`
    #[inline]
    #[spec(ensures: |ret| match ret {
        Maybe::Present(id) => self.terms.get(id.0) == Some(term)
            && self.terms.iter().position(|stored| stored == term) == Some(id.0),
        Maybe::Absent(_) => !self.terms.contains(term),
    })]
    pub fn find(
        &self,
        term: &Term,
    ) -> Maybe<TermId, interned::Absent>
    {
        match self.term_ids.probe(hash_of(term), &self.terms, term) {
            | Probe::Found(position) => Maybe::Present(TermId(position)),
            | Probe::Vacant(_) => Maybe::Absent(interned::Absent::Uninterned),
        }
    }

    /// Intern a classifier over existing children, without forming it.
    ///
    /// # Specification
    /// - ensures: equal descriptors receive the same coordinate; children
    ///   precede their parent, so classifier cycles cannot be minted.
    /// - fails: `UnknownType` for an absent child; `Overflow` when the arena
    ///   already holds `u32::MAX` classifiers.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns `UnknownType` for an absent child, `Overflow` at the
    /// coordinate bound.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — equal classifiers and forward edges distinguish
    ///   canonicalization and the acyclic-prefix guard.
    /// - witness: `stage::tests::syntax_boundaries`
    /// - witness: `stage::tests::interning_survives_lookup_growth`
    #[inline]
    #[spec(ensures: |ret| ret.as_ref().ok().is_none_or(|id|
        self.types.get(id.0) == Some(&ty)
        && self.types.iter().position(|stored| *stored == ty) == Some(id.0)
        && match ty {
            Type::Arrow(a, b) => a.0 < id.0 && b.0 < id.0,
            Type::Lift(inner) => inner.0 < id.0,
            _ => true,
        }))]
    pub fn alloc_type(
        &mut self,
        ty: Type,
    ) -> Result<TypeId, StageError>
    {
        match ty {
            | Type::Arrow(domain, codomain) => {
                self.ty(domain)?;
                self.ty(codomain)?;
            },
            | Type::Lift(inner) => {
                self.ty(inner)?;
            },
            | Type::In(_) | Type::Universe(_) | Type::Nat(_) => {},
        }
        let hash = hash_of(&ty);
        match self.type_ids.probe(hash, &self.types, &ty) {
            | Probe::Found(position) => Ok(TypeId(position)),
            | Probe::Vacant(slot) => {
                let id = TypeId(self.types.len());
                self.type_ids
                    .insert(slot, hash, &self.types)
                    .map_err(|_full| StageError::Overflow)?;
                self.types.push(ty);
                Ok(id)
            },
        }
    }

    /// Intern a term over existing children, without checking its typing.
    ///
    /// # Specification
    /// - ensures: equal descriptors receive the same coordinate; all edges
    ///   point backward, preventing cycles. Identity is arena-local syntax.
    /// - fails: `UnknownTerm` or `UnknownType` for an absent child; `Overflow`
    ///   when the arena already holds `u32::MAX` terms.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns the absent child's typed lookup error, or `Overflow` at the
    /// coordinate bound.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — equal and unequal descriptors distinguish exact
    ///   interning; live and forward edges distinguish prefix checking.
    /// - witness: `stage::tests::syntax_boundaries`
    /// - witness: `stage::tests::term_interning_preserves_exact_content`
    /// - witness: `stage::tests::interning_survives_lookup_growth`
    #[inline]
    #[spec(ensures: |ret| ret.as_ref().ok().is_none_or(|id|
        self.terms.get(id.0) == Some(&term)
        && term.children().into_iter().flatten().all(|child| child.0 < id.0)))]
    pub fn alloc(
        &mut self,
        term: Term,
    ) -> Result<TermId, StageError>
    {
        for child in term.children().into_iter().flatten() {
            self.term(child)?;
        }
        match term {
            | Term::Code(ty) | Term::Lambda(ty, _) | Term::Eliminate(_, ty) => {
                self.ty(ty)?;
            },
            | _ => {},
        }
        let hash = hash_of(&term);
        match self.term_ids.probe(hash, &self.terms, &term) {
            | Probe::Found(position) => Ok(TermId(position)),
            | Probe::Vacant(slot) => {
                let id = TermId(self.terms.len());
                self.term_ids
                    .insert(slot, hash, &self.terms)
                    .map_err(|_full| StageError::Overflow)?;
                self.terms.push(term);
                Ok(id)
            },
        }
    }
}

/// A constructor child slot, vacant exactly when that position is unused.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Child
{
    /// This constructor has no child at the slot.
    Vacant,
    /// The child at this slot.
    Present(TermId),
}

impl IntoIterator for Child
{
    type Item = TermId;
    type IntoIter = core::option::IntoIter<TermId>;
    /// Iterate the occupied slot at the standard iterator boundary.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn into_iter(self) -> Self::IntoIter
    {
        match self {
            | Self::Vacant => None,
            | Self::Present(id) => Some(id),
        }
        .into_iter()
    }
}

impl<'slot> IntoIterator for &'slot mut Child
{
    type Item = &'slot mut TermId;
    type IntoIter = core::option::IntoIter<&'slot mut TermId>;
    /// Borrow the occupied slot through the standard iterator boundary.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn into_iter(self) -> Self::IntoIter
    {
        self.iter_mut()
    }
}

impl Child
{
    /// Mutably iterate the occupied child slot.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn iter_mut(&mut self) -> core::option::IntoIter<&mut TermId>
    {
        match *self {
            | Self::Vacant => None,
            | Self::Present(ref mut id) => Some(id),
        }
        .into_iter()
    }
}

impl Term
{
    /// The fixed-capacity child slots, in constructor order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn children(self) -> [Child; 3]
    {
        match self {
            | Self::Variable(_) | Self::Natural(..) | Self::Code(_) => [Child::Vacant; 3],
            | Self::Lambda(_, body)
            | Self::Quote(body)
            | Self::Splice(body)
            | Self::Eliminate(body, _) => [Child::Present(body), Child::Vacant, Child::Vacant],
            | Self::Apply(first, second) | Self::Multiply(first, second) => {
                [Child::Present(first), Child::Present(second), Child::Vacant]
            },
            | Self::Iterate(count, zero, step) => [
                Child::Present(count),
                Child::Present(zero),
                Child::Present(step),
            ],
        }
    }

    /// Replace occupied child slots, preserving the head and its payload.
    ///
    /// # Specification
    /// - ensures: preserves non-child fields and requires the same arity.
    /// - fails: `Unbalanced` for missing or excess child slots.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns `Unbalanced` for a mismatched child shape.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — binder substitution observes child order and an
    ///   absent child distinguishes malformed rebuilding.
    /// - witness: `stage::tests::substitution_avoids_capture`
    /// - witness: `stage::tests::syntax_boundaries`
    /// - witness: `stage::tests::rebuild_preserves_heads_and_slots`
    #[inline]
    #[spec(ensures: |ret| ret.map_or_else(
        |_| self.children().into_iter().zip(children).any(|(old, new)|
            matches!(old, Child::Vacant) != matches!(new, Child::Vacant)),
        |rebuilt| rebuilt.children() == children
            && core::mem::discriminant(&rebuilt) == core::mem::discriminant(&self)
            && match (self, rebuilt) {
                (Self::Lambda(a, _), Self::Lambda(b, _))
                | (Self::Eliminate(_, a), Self::Eliminate(_, b)) => a == b,
                (Self::Variable(_) | Self::Natural(..) | Self::Code(_), _) => self == rebuilt,
                _ => true,
            },
    ))]
    pub fn rebuild(
        self,
        children: [Child; 3],
    ) -> Result<Self, StageError>
    {
        let [first, second, third] = children;
        Ok(match (self, first, second, third) {
            | (Self::Lambda(ty, _), Child::Present(body), Child::Vacant, Child::Vacant) => {
                Self::Lambda(ty, body)
            },
            | (Self::Quote(_), Child::Present(body), Child::Vacant, Child::Vacant) => {
                Self::Quote(body)
            },
            | (Self::Splice(_), Child::Present(body), Child::Vacant, Child::Vacant) => {
                Self::Splice(body)
            },
            | (Self::Eliminate(_, ty), Child::Present(body), Child::Vacant, Child::Vacant) => {
                Self::Eliminate(body, ty)
            },
            | (Self::Apply(..), Child::Present(a), Child::Present(b), Child::Vacant) => {
                Self::Apply(a, b)
            },
            | (Self::Multiply(..), Child::Present(a), Child::Present(b), Child::Vacant) => {
                Self::Multiply(a, b)
            },
            | (Self::Iterate(..), Child::Present(a), Child::Present(b), Child::Present(c)) => {
                Self::Iterate(a, b, c)
            },
            | (
                leaf @ (Self::Variable(_) | Self::Natural(..) | Self::Code(_)),
                Child::Vacant,
                Child::Vacant,
                Child::Vacant,
            ) => leaf,
            | _ => return Err(StageError::Unbalanced),
        })
    }
}

/// A binder-aware syntax rewrite; no typing or equality judgement.
#[derive(Clone, Copy, Debug)]
enum Rewrite
{
    /// Raise free indices by this amount.
    Shift(Index),
    /// Replace the removed outer binder by a term.
    Substitute(TermId),
}

/// Instantiate the outermost free variable of a body, avoiding capture.
///
/// # Specification
/// - ensures: substitutes index zero, lowers greater free indices, and raises
///   the replacement beneath every intervening lambda.
/// - fails: lookup, index overflow, or work exhaustion errors.
/// - panics: none.
///
/// # Errors
/// Returns a syntax lookup error, `Overflow`, `Exhausted`, or `Unbalanced`.
///
/// # Adequacy
/// - hypothesis: L3 — a free argument beneath binders distinguishes capture,
///   failure to lower, and accidental substitution of bound slots.
/// - witness: `stage::tests::substitution_avoids_capture`
/// - witness: `stage::tests::substitution_boundaries`
#[spec(ensures: |ret| ret.as_ref().ok().is_none_or(|result|
    match arena.term(body) {
        Ok(Term::Variable(Index(0))) => *result == argument,
        Ok(Term::Variable(index)) => arena.term(*result) == Ok(Term::Variable(Index(index.0.saturating_sub(1)))),
        Ok(Term::Natural(..) | Term::Code(_)) => *result == body,
        _ => arena.term(*result).is_ok(),
    }))]
#[inline]
pub fn instantiate(
    arena: &mut Arena,
    body: TermId,
    argument: TermId,
    budget: &mut Budget,
) -> Result<TermId, StageError>
{
    arena.term(argument)?;
    rewrite(arena, body, Rewrite::Substitute(argument), budget)
}

/// Rewrite syntax in postorder, memoizing each node at each binder depth.
///
/// # Specification
/// - ensures: implements the selected free-variable rewrite without changing
///   any constructor or classifier.
/// - fails: lookup, index overflow, or work exhaustion errors.
/// - panics: none.
///
/// # Errors
/// Returns a syntax lookup error, `Overflow`, `Exhausted`, or `Unbalanced`.
///
/// # Adequacy
/// - hypothesis: L3 — nested binders and shared occurrences observe capture
///   avoidance and preservation of bound variables.
/// - witness: `stage::tests::substitution_avoids_capture`
/// - witness: `stage::tests::substitution_boundaries`
#[spec(ensures: |ret| ret.as_ref().ok().is_none_or(|result|
    match (arena.term(root), operation) {
        (Ok(Term::Variable(index)), Rewrite::Shift(amount)) =>
            index.0.checked_add(amount.0).is_some_and(|raised| arena.term(*result) == Ok(Term::Variable(Index(raised)))),
        (Ok(Term::Variable(Index(0))), Rewrite::Substitute(argument)) => *result == argument,
        (Ok(Term::Variable(index)), Rewrite::Substitute(_)) =>
            arena.term(*result) == Ok(Term::Variable(Index(index.0.saturating_sub(1)))),
        (Ok(Term::Natural(..) | Term::Code(_)), _) => *result == root,
        _ => arena.term(*result).is_ok(),
    }))]
fn rewrite(
    arena: &mut Arena,
    root: TermId,
    operation: Rewrite,
    budget: &mut Budget,
) -> Result<TermId, StageError>
{
    // Shift jobs precede the substitution job. This avoids recursive calls
    // even when a replacement must be carried under deeply nested binders.
    let mut shifted = BTreeMap::new();
    if let Rewrite::Substitute(argument) = operation {
        let mut pending = Vec::from([(root, Index(0))]);
        let mut seen = alloc::collections::BTreeSet::new();
        while let Some((id, depth)) = pending.pop() {
            budget.spend()?;
            if !seen.insert((id, depth)) {
                continue;
            }
            let term = arena.term(id)?;
            if term == Term::Variable(depth) {
                shifted.insert(depth, argument);
            }
            let below = if matches!(term, Term::Lambda(..)) {
                Index(depth.0.checked_add(1).ok_or(StageError::Overflow)?)
            }
            else {
                depth
            };
            pending.extend(
                term.children()
                    .into_iter()
                    .flatten()
                    .map(|child| (child, below)),
            );
        }
    }
    let mut jobs: Vec<_> = shifted
        .keys()
        .copied()
        .filter(|depth| depth.0 != 0)
        .map(|depth| {
            let Rewrite::Substitute(argument) = operation
            else {
                return (root, Rewrite::Shift(depth), depth);
            };
            (argument, Rewrite::Shift(depth), depth)
        })
        .collect();
    jobs.push((root, operation, Index(0)));
    let mut answer = root;
    for (job_root, job, depth_key) in jobs {
        let mut results = BTreeMap::new();
        let mut pending = Vec::from([(job_root, Index(0), false)]);
        while let Some((id, depth, ready)) = pending.pop() {
            budget.spend()?;
            if results.contains_key(&(id, depth)) {
                continue;
            }
            let term = arena.term(id)?;
            let below = if matches!(term, Term::Lambda(..)) {
                Index(depth.0.checked_add(1).ok_or(StageError::Overflow)?)
            }
            else {
                depth
            };
            if !ready {
                pending.push((id, depth, true));
                pending.extend(
                    term.children()
                        .into_iter()
                        .flatten()
                        .rev()
                        .map(|child| (child, below, false)),
                );
                continue;
            }
            let result = if let Term::Variable(index) = term {
                if index.0 < depth.0 {
                    id
                }
                else {
                    match job {
                        | Rewrite::Shift(amount) => {
                            let raised =
                                index.0.checked_add(amount.0).ok_or(StageError::Overflow)?;
                            arena.alloc(Term::Variable(Index(raised)))?
                        },
                        | Rewrite::Substitute(_) if index == depth => {
                            *shifted.get(&depth).ok_or(StageError::Unbalanced)?
                        },
                        | Rewrite::Substitute(_) => arena.alloc(Term::Variable(Index(
                            index.0.checked_sub(1).ok_or(StageError::Overflow)?,
                        )))?,
                    }
                }
            }
            else {
                let mut children = term.children();
                for child in children.iter_mut().flatten() {
                    *child = *results
                        .get(&(*child, below))
                        .ok_or(StageError::Unbalanced)?;
                }
                let rebuilt = term.rebuild(children)?;
                if rebuilt == term {
                    id
                }
                else {
                    arena.alloc(rebuilt)?
                }
            };
            results.insert((id, depth), result);
        }
        answer = *results
            .get(&(job_root, Index(0)))
            .ok_or(StageError::Unbalanced)?;
        if matches!(job, Rewrite::Shift(_)) {
            shifted.insert(depth_key, answer);
        }
    }
    Ok(answer)
}

#[cfg(test)]
mod tests
{
    use super::*;

    #[test]
    fn syntax_boundaries()
    {
        let mut arena = Arena::default();
        assert_eq!(arena.ty(TypeId(0)), Err(StageError::UnknownType(TypeId(0))));
        assert_eq!(
            arena.alloc(Term::Quote(TermId(0))),
            Err(StageError::UnknownTerm(TermId(0)))
        );
        assert_eq!(
            arena.alloc_type(Type::Lift(TypeId(0))),
            Err(StageError::UnknownType(TypeId(0)))
        );
        let nat = arena.alloc_type(Type::Nat(Stage::Outer)).unwrap();
        assert_eq!(arena.alloc_type(Type::Nat(Stage::Outer)), Ok(nat));
        assert_eq!(
            Term::Quote(TermId(0)).rebuild([Child::Vacant; 3]),
            Err(StageError::Unbalanced)
        );
        let mut budget = Budget(1);
        assert_eq!(budget.spend(), Ok(()));
        assert_eq!(budget.0, 0);
        assert_eq!(budget.spend(), Err(StageError::Exhausted));
        assert_eq!(budget.0, 0);
        assert_eq!(arena.ty(nat), Ok(Type::Nat(Stage::Outer)));
        let zero = arena
            .alloc(Term::Natural(Stage::Outer, Natural(0)))
            .unwrap();
        let pair = arena.alloc(Term::Multiply(zero, zero)).unwrap();
        assert_eq!(arena.term(pair), Ok(Term::Multiply(zero, zero)));
        let absent = TypeId(usize::MAX);
        for ty in [
            Type::Arrow(absent, nat),
            Type::Arrow(nat, absent),
            Type::Lift(absent),
        ] {
            assert_eq!(arena.alloc_type(ty), Err(StageError::UnknownType(absent)));
        }
        for term in [
            Term::Code(absent),
            Term::Lambda(absent, zero),
            Term::Eliminate(zero, absent),
        ] {
            assert_eq!(arena.alloc(term), Err(StageError::UnknownType(absent)));
        }
    }

    #[test]
    fn term_interning_preserves_exact_content()
    {
        let mut arena = Arena::default();
        let outer = arena.alloc_type(Type::Nat(Stage::Outer)).unwrap();
        let inner = arena.alloc_type(Type::Nat(Stage::Inner(Model(0)))).unwrap();
        let a = arena
            .alloc(Term::Natural(Stage::Outer, Natural(2)))
            .unwrap();
        let b = arena
            .alloc(Term::Natural(Stage::Outer, Natural(3)))
            .unwrap();
        let terms = [
            Term::Variable(Index(0)),
            Term::Variable(Index(1)),
            Term::Natural(Stage::Outer, Natural(2)),
            Term::Natural(Stage::Outer, Natural(3)),
            Term::Natural(Stage::Inner(Model(0)), Natural(2)),
            Term::Natural(Stage::Inner(Model(1)), Natural(2)),
            Term::Code(outer),
            Term::Code(inner),
            Term::Lambda(outer, a),
            Term::Lambda(inner, a),
            Term::Lambda(outer, b),
            Term::Apply(a, b),
            Term::Apply(b, a),
            Term::Multiply(a, b),
            Term::Multiply(b, a),
            Term::Quote(a),
            Term::Quote(b),
            Term::Splice(a),
            Term::Splice(b),
            Term::Iterate(a, b, a),
            Term::Iterate(a, a, b),
            Term::Eliminate(a, outer),
            Term::Eliminate(a, inner),
            Term::Eliminate(b, outer),
        ];
        let before = terms.map(|term| arena.find(&term));
        let ids: Vec<_> = terms
            .iter()
            .map(|term| arena.alloc(*term).unwrap())
            .collect();
        let mut cloned = arena.clone();
        for ((term, id), found) in terms.iter().zip(&ids).zip(before) {
            let preexisting = *id == a || *id == b;
            assert_eq!(
                found,
                if preexisting {
                    Maybe::Present(*id)
                }
                else {
                    Maybe::Absent(interned::Absent::Uninterned)
                }
            );
            assert_eq!(arena.find(term), Maybe::Present(*id));
            assert_eq!(cloned.find(term), Maybe::Present(*id));
            assert_eq!(arena.alloc(*term), Ok(*id));
            assert_eq!(cloned.alloc(*term), Ok(*id));
            for (other, other_id) in terms.iter().zip(&ids) {
                assert_eq!(term == other, id == other_id);
            }
        }
        let fresh = Term::Natural(Stage::Outer, Natural(4));
        assert_eq!(
            arena.find(&fresh),
            Maybe::Absent(interned::Absent::Uninterned)
        );
        assert_eq!(arena.alloc(fresh), Ok(TermId(ids.len())));
        assert_eq!(
            arena.alloc(Term::Quote(TermId(usize::MAX))),
            Err(StageError::UnknownTerm(TermId(usize::MAX)))
        );
        assert_eq!(
            arena.alloc(Term::Code(TypeId(usize::MAX))),
            Err(StageError::UnknownType(TypeId(usize::MAX)))
        );
    }

    #[test]
    fn interning_survives_lookup_growth()
    {
        let mut arena = Arena::default();
        let mut types = Vec::from([arena.alloc_type(Type::Nat(Stage::Outer)).unwrap()]);
        for model in 0 .. 200 {
            let previous = *types.last().unwrap();
            let universe = arena.alloc_type(Type::Universe(Model(model))).unwrap();
            types.push(arena.alloc_type(Type::Arrow(universe, previous)).unwrap());
        }
        let mut terms = Vec::new();
        let mut ids = Vec::new();
        for value in 0 .. 3_000_usize {
            let term = match (value.checked_rem(3), ids.as_slice()) {
                | (Some(1 | 2), &[.., older, newer]) => Term::Apply(newer, older),
                | _ => Term::Natural(Stage::Outer, Natural(value)),
            };
            terms.push(term);
            ids.push(arena.alloc(term).unwrap());
        }
        assert_eq!(ids, (0 .. 3_000).map(TermId).collect::<Vec<_>>());
        let cloned = arena.clone();
        for (term, id) in terms.iter().zip(&ids) {
            assert_eq!(arena.find(term), Maybe::Present(*id));
            assert_eq!(cloned.find(term), Maybe::Present(*id));
        }
        for (term, id) in terms.iter().zip(&ids) {
            assert_eq!(arena.alloc(*term), Ok(*id));
        }
        assert_eq!(arena.terms.len(), 3_000);
        for id in &types {
            let ty = arena.ty(*id).unwrap();
            assert_eq!(arena.alloc_type(ty), Ok(*id));
        }
        assert_eq!(arena.types.len(), 401);
    }

    #[test]
    fn substitution_avoids_capture()
    {
        let mut arena = Arena::default();
        let nat = arena.alloc_type(Type::Nat(Stage::Outer)).unwrap();
        let bound = arena.alloc(Term::Variable(Index(0))).unwrap();
        let free = arena.alloc(Term::Variable(Index(1))).unwrap();
        let outer = arena.alloc(Term::Variable(Index(2))).unwrap();
        let body = arena.alloc(Term::Iterate(bound, free, outer)).unwrap();
        let body = arena.alloc(Term::Lambda(nat, body)).unwrap();
        let result = instantiate(&mut arena, body, bound, &mut Budget(100)).unwrap();
        let Term::Lambda(_, body) = arena.term(result).unwrap()
        else {
            panic!("lambda");
        };
        let Term::Iterate(a, b, c) = arena.term(body).unwrap()
        else {
            panic!("iterate");
        };
        assert_eq!(arena.term(a), Ok(Term::Variable(Index(0))));
        assert_eq!(arena.term(b), Ok(Term::Variable(Index(1))));
        assert_eq!(arena.term(c), Ok(Term::Variable(Index(1))));
        assert_eq!(
            instantiate(&mut arena, body, bound, &mut Budget(0)),
            Err(StageError::Exhausted)
        );
    }

    #[test]
    fn substitution_boundaries()
    {
        let mut arena = Arena::default();
        let nat = arena.alloc_type(Type::Nat(Stage::Outer)).unwrap();
        let zero = arena.alloc(Term::Variable(Index(0))).unwrap();
        let free = arena.alloc(Term::Variable(Index(3))).unwrap();
        let literal = arena
            .alloc(Term::Natural(Stage::Outer, Natural(7)))
            .unwrap();
        let code = arena.alloc(Term::Code(nat)).unwrap();
        assert_eq!(
            instantiate(&mut arena, zero, literal, &mut Budget(100)),
            Ok(literal)
        );
        for leaf in [literal, code] {
            assert_eq!(
                instantiate(&mut arena, leaf, zero, &mut Budget(100)),
                Ok(leaf)
            );
        }
        let lowered = instantiate(&mut arena, free, literal, &mut Budget(100)).unwrap();
        assert_eq!(arena.term(lowered), Ok(Term::Variable(Index(2))));
        let huge = arena.alloc(Term::Variable(Index(usize::MAX))).unwrap();
        let under = arena.alloc(Term::Variable(Index(1))).unwrap();
        let lambda = arena.alloc(Term::Lambda(nat, under)).unwrap();
        assert_eq!(
            instantiate(&mut arena, lambda, huge, &mut Budget(100)),
            Err(StageError::Overflow)
        );
        let absent = TermId(usize::MAX);
        for (body, argument) in [(absent, zero), (zero, absent)] {
            assert_eq!(
                instantiate(&mut arena, body, argument, &mut Budget(100)),
                Err(StageError::UnknownTerm(absent))
            );
        }
    }

    #[test]
    fn rebuild_preserves_heads_and_slots()
    {
        let a = TermId(10);
        let b = TermId(20);
        let c = TermId(30);
        let ty = TypeId(7);
        for (source, expected) in [
            (Term::Variable(Index(4)), Term::Variable(Index(4))),
            (
                Term::Natural(Stage::Inner(Model(3)), Natural(9)),
                Term::Natural(Stage::Inner(Model(3)), Natural(9)),
            ),
            (Term::Code(ty), Term::Code(ty)),
            (Term::Lambda(ty, c), Term::Lambda(ty, a)),
            (Term::Apply(c, a), Term::Apply(a, b)),
            (Term::Multiply(c, a), Term::Multiply(a, b)),
            (Term::Quote(c), Term::Quote(a)),
            (Term::Splice(c), Term::Splice(a)),
            (Term::Eliminate(c, ty), Term::Eliminate(a, ty)),
            (Term::Iterate(c, a, b), Term::Iterate(a, b, c)),
        ] {
            for mask in 0_u8 .. 8 {
                let children = core::array::from_fn(|slot| {
                    if mask & (1 << slot) == 0 {
                        Child::Vacant
                    }
                    else {
                        Child::Present([a, b, c].get(slot).copied().unwrap())
                    }
                });
                if children == expected.children() {
                    assert_eq!(source.rebuild(children), Ok(expected));
                }
                else {
                    assert_eq!(source.rebuild(children), Err(StageError::Unbalanced));
                }
            }
        }
    }
}
