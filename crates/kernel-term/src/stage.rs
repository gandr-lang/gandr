//! Experimental structural staging vocabulary, separate from the persisted
//! core.
//!
//! `In M` is an ordinary hypothesis. Object classifiers carry `Inner(M)`;
//! lifting, quotation and splicing never transform a context. This arena has
//! no wire encoding and confers no typing or conversion authority.

use alloc::collections::BTreeMap;
use alloc::vec::Vec;
use core::fmt;

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
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum Stage
{
    /// The meta level.
    Outer,
    /// The object level entered by an `In` hypothesis.
    Inner(Model),
}

/// Classifiers of the structural natural-number staging fragment.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
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
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
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

/// Append-only staging syntax with exact classifier and term identities.
#[derive(Clone, Debug, Default)]
pub struct Arena
{
    /// Canonical classifier descriptors in dependency order.
    types: Vec<Type>,
    /// Descriptor lookup; equality here concerns syntax, not conversion.
    type_ids: BTreeMap<Type, TypeId>,
    /// Terms in dependency order.
    terms: Vec<Term>,
    /// Exact constructor, payload and child lookup within this arena.
    term_ids: BTreeMap<Term, TermId>,
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

    /// Look up an exact term without allocating (research scratch).
    ///
    /// # Specification
    /// - ensures: returns the coordinate `alloc` would return for `term` when
    ///   it is already interned, and nothing otherwise.
    /// - panics: none.
    #[inline]
    #[must_use]
    pub fn find(
        &self,
        term: &Term,
    ) -> Option<TermId>
    {
        self.term_ids.get(term).copied()
    }

    /// Intern a classifier over existing children, without forming it.
    ///
    /// # Specification
    /// - ensures: equal descriptors receive the same coordinate; children
    ///   precede their parent, so classifier cycles cannot be minted.
    /// - fails: `UnknownType` for an absent child.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns `UnknownType` for an absent child.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — equal classifiers and forward edges distinguish
    ///   canonicalization and the acyclic-prefix guard.
    /// - witness: `stage::tests::syntax_boundaries`
    #[inline]
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
        if let Some(id) = self.type_ids.get(&ty) {
            return Ok(*id);
        }
        let id = TypeId(self.types.len());
        self.types.push(ty);
        self.type_ids.insert(ty, id);
        Ok(id)
    }

    /// Intern a term over existing children, without checking its typing.
    ///
    /// # Specification
    /// - ensures: equal descriptors receive the same coordinate; all edges
    ///   point backward, preventing cycles. Identity is arena-local syntax.
    /// - fails: `UnknownTerm` or `UnknownType` for an absent child.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns the absent child's typed lookup error.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — equal and unequal descriptors distinguish exact
    ///   interning; live and forward edges distinguish prefix checking.
    /// - witness: `stage::tests::syntax_boundaries`
    /// - witness: `stage::tests::term_interning_preserves_exact_content`
    #[inline]
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
        if let Some(id) = self.term_ids.get(&term) {
            return Ok(*id);
        }
        let id = TermId(self.terms.len());
        self.terms.push(term);
        self.term_ids.insert(term, id);
        Ok(id)
    }

    /// Research scratch: the term and type counts.
    #[must_use]
    pub fn extent(&self) -> (usize, usize)
    {
        (self.terms.len(), self.types.len())
    }

    /// Research scratch: drop every term and type at or above `extent`, and
    /// their lookup entries, so a worker reuses one snapshot across sources.
    pub fn truncate_to(
        &mut self,
        extent: (usize, usize),
    )
    {
        for term in self.terms.drain(extent.0.min(self.terms.len()) ..) {
            let _gone = self.term_ids.remove(&term);
        }
        for ty in self.types.drain(extent.1.min(self.types.len()) ..) {
            let _gone = self.type_ids.remove(&ty);
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
    #[inline]
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
/// - hypothesis: L3 — a free argument beneath two binders distinguishes
///   capture, failure to lower, and accidental substitution of bound slots.
/// - witness: `stage::tests::substitution_avoids_capture`
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
        assert_eq!(budget.spend(), Err(StageError::Exhausted));
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
        let ids: Vec<_> = terms
            .iter()
            .map(|term| arena.alloc(*term).unwrap())
            .collect();
        let mut cloned = arena.clone();
        for (term, id) in terms.iter().zip(&ids) {
            assert_eq!(arena.alloc(*term), Ok(*id));
            assert_eq!(cloned.alloc(*term), Ok(*id));
            for (other, other_id) in terms.iter().zip(&ids) {
                assert_eq!(term == other, id == other_id);
            }
        }
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
}
