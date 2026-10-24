//! Signature-derived, simply-sorted syntax with restricted binding, and its
//! two views.
//!
//! A signature is simply sorted when no sort is indexed: every argument and
//! every binder domain is a bare sort, so a context is a list of sort names
//! and a variable is a de Bruijn index into it. [`SimplySorted`] admits such
//! a signature once and then serves both views from its declarations alone,
//! with no case on any sort or operation name:
//!
//! - the first-order view: [`SimplySorted::to_first_order`] and
//!   [`SimplySorted::from_first_order`] identify a binding judgement with its
//!   canonical term in the generated single-substitution model (`$q` under one
//!   `$p` per newer context entry), both composites the identity on well-sorted
//!   judgements;
//! - the internal view: [`SimplySorted::evaluate`] (`Y`) builds a value under a
//!   reflected environment and [`Evaluation::readback`] (`Λ`) quotes it back,
//!   `Λ ∘ Y` the identity; [`SimplySorted::evaluate_in`] evaluates under
//!   explicit images, which is capture-avoiding parallel substitution.
//!
//! Judgements retain their context and result sort, so two terms that agree
//! as bare trees but differ in typing stay distinct. Flat trees supply
//! canonical structural equality independently of allocation or arena
//! identity.
//!
//! A sort indexed by terms of another sort is refused at admission
//! ([`AdmissionError::TermDependentSort`]): its evaluation needs dependent
//! pairs in the value domain, which the fragment's model in source waits on.

#[path = "binding_first_order.rs"]
mod first_order;
#[path = "semantics.rs"]
mod semantics;

use alloc::collections::BTreeMap;
use alloc::vec::Vec;
use core::fmt;

use anodized::spec;

pub use self::first_order::FirstOrderJudgement;
pub use self::semantics::Evaluation;
use crate::boundary::VariableIndex;
use crate::code::Name;
use crate::desc::OperDesc;
use crate::desc::Representability;
use crate::desc::SortDesc;
use crate::desc::TheoryDesc;
use crate::first_order::TranslationError;
use crate::tree::ArgumentCount;
use crate::tree::Head;
use crate::tree::Tree;
use crate::tree::TreeRef;

/// A node of the signature-derived binding carrier.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
enum BindingHead
{
    /// A de Bruijn variable.
    Variable(VariableIndex),
    /// A signature operation and its number of arguments.
    Operation(Name, ArgumentCount),
}

impl Head for BindingHead
{
    /// Return the number of immediate subterms.
    ///
    /// # Specification
    /// trivial.
    fn arity(&self) -> ArgumentCount
    {
        match *self {
            Self::Variable(_) => ArgumentCount::from(0),
            Self::Operation(_, count) => count,
        }
    }
}

/// A finite term whose argument binders are determined by its signature.
///
/// # Specification
/// - provides: allocation-independent structural equality over a flat tree;
///   scope and typing are checked by `SimplySorted::check`.
#[repr(transparent)]
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct BindingTerm(Tree<BindingHead>);

impl BindingTerm
{
    /// Construct a variable, counting from the newest context entry.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn variable(index: VariableIndex) -> Self
    {
        Self(Tree::leaf(BindingHead::Variable(index)))
    }

    /// Construct an operation with arguments in declaration order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn operation<A>(
        name: Name,
        arguments: A,
    ) -> Self
    where
        A: IntoIterator<Item = Self>,
    {
        let arguments: Vec<_> = arguments.into_iter().map(|term| term.0).collect();
        let count = ArgumentCount::from(arguments.len());
        Self(Tree::node(BindingHead::Operation(name, count), arguments))
    }
}

/// A typed observation of binding syntax, including its ambient context.
///
/// # Specification
/// - provides: structural equality including context order, result sort and
///   every term node. Public fields are input data, validated at each boundary.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct BindingJudgement
{
    /// Ambient representable sorts, oldest first.
    pub context: Vec<Name>,
    /// The result sort, including ordinary sorts.
    pub sort: Name,
    /// The term under the ambient context.
    pub term: BindingTerm,
}

/// Why a signature cannot generate simply-sorted binding semantics.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum AdmissionError
{
    /// Failure shared with the first-order signature translation.
    Signature(TranslationError),
    /// A declared sort has a term-index telescope.
    TermDependentSort(Name),
    /// An unindexed sort occurrence nevertheless supplies index arguments.
    IndexedOccurrence(Name),
    /// A result port binds variables, outside the operation-signature grammar.
    BindingResult(Name),
}

impl fmt::Display for AdmissionError
{
    /// Describe the named rejected component.
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
            Self::Signature(ref error) => error.fmt(f),
            Self::TermDependentSort(ref name) => write!(f, "term-dependent sort: {name}"),
            Self::IndexedOccurrence(ref name) => {
                write!(f, "indexed occurrence of simple sort: {name}")
            },
            Self::BindingResult(ref name) => write!(f, "binding result of operation: {name}"),
        }
    }
}

impl core::error::Error for AdmissionError
{
}

/// A typing, scoping or canonical-presentation refusal.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum BindingError
{
    /// The sort is not declared.
    UnknownSort(Name),
    /// An ordinary sort cannot extend a context.
    NonRepresentable(Name),
    /// The operation is not declared.
    UnknownOperation(Name),
    /// A variable lies outside its context.
    UnboundVariable(VariableIndex),
    /// A node's actual sort differs from its expected sort.
    SortMismatch
    {
        /// Expected sort.
        expected: Name,
        /// Actual sort.
        actual: Name,
    },
    /// The operation has the wrong number of arguments.
    Arity(Name),
    /// An environment has the wrong number of entries.
    EnvironmentArity,
    /// The input is not a canonical q/p representative.
    NonCanonical,
    /// An internal arena reference or machine stack is inconsistent.
    InvalidState,
}

impl fmt::Display for BindingError
{
    /// Render a typed semantic refusal.
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
            Self::UnknownSort(ref name) => write!(f, "unknown sort: {name}"),
            Self::NonRepresentable(ref name) => write!(f, "nonrepresentable sort: {name}"),
            Self::UnknownOperation(ref name) => write!(f, "unknown operation: {name}"),
            Self::UnboundVariable(index) => write!(f, "unbound variable: {index}"),
            Self::SortMismatch {
                ref expected,
                ref actual,
            } => write!(f, "expected {expected}, found {actual}"),
            Self::Arity(ref name) => write!(f, "wrong argument count: {name}"),
            Self::EnvironmentArity => f.write_str("wrong environment length"),
            Self::NonCanonical => f.write_str("noncanonical first-order term"),
            Self::InvalidState => f.write_str("inconsistent semantic state"),
        }
    }
}

impl core::error::Error for BindingError
{
}

/// An admitted simply-sorted signature, borrowing its declaration table.
///
/// # Specification
/// - provides: the free finite binding syntax of any closed, single-output
///   operation signature with unindexed sorts and representable binder domains.
///   Source equations are retained by the description, not oriented or reduced.
#[repr(transparent)]
#[derive(Debug)]
pub struct SimplySorted<'signature, G>
{
    /// The validated signature; no per-signature interpreter is stored.
    source: &'signature TheoryDesc<G>,
}

impl<'signature, G> SimplySorted<'signature, G>
{
    /// Admit a signature beside `check_desc`, adding the simple-sort boundary.
    ///
    /// # Specification
    /// - ensures: all sorts are unindexed, every binder domain is a declared
    ///   representable sort, and every operation has one result that binds
    ///   nothing.
    /// - fails: names the first term-dependent sort; then the first translation
    ///   refusal (a malformed or non-product signature); then the first indexed
    ///   occurrence or binding result, in operation order.
    /// - panics: none.
    ///
    /// # Errors
    /// - `AdmissionError::TermDependentSort`: a declared sort has an index
    ///   telescope.
    /// - `AdmissionError::Signature`: the signature itself is outside
    ///   [`first_order`]'s domain, with its [`TranslationError`]; an equation
    ///   the translation would not read is not this check's.
    /// - `AdmissionError::IndexedOccurrence`: a port or binder applies an
    ///   unindexed sort to index arguments.
    /// - `AdmissionError::BindingResult`: an operation's result port binds.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the three admitted signatures and the empty one are
    ///   accepted; the indexed identity-return signature, an indexed
    ///   occurrence, a binding result and an ordinary binder domain are each
    ///   refused by their exact variant and payload, so a skipped check, a
    ///   swapped order or a lost name changes an observed refusal.
    /// - witness: `tests::glf::model::admission`
    ///
    /// [`first_order`]: crate::first_order::first_order
    #[inline]
    #[spec(ensures: |ref result| match *result {
        Ok(_) => source.sorts.iter().all(|sort| sort.indices.is_empty())
            && source.opers.iter().all(|operation| operation.arity.outputs.len() == 1
                && operation.arity.outputs.iter().all(|port| port.bindings.is_empty())),
        Err(AdmissionError::TermDependentSort(ref name)) =>
            source.sorts.iter().any(|sort| sort.name == *name && !sort.indices.is_empty()),
        Err(AdmissionError::BindingResult(ref name)) => source.opers.iter().any(|operation|
            operation.name == *name && operation.arity.outputs.iter().any(|port| !port.bindings.is_empty())),
        Err(AdmissionError::Signature(_) | AdmissionError::IndexedOccurrence(_)) => true,
    })]
    pub fn new(source: &'signature TheoryDesc<G>) -> Result<Self, AdmissionError>
    {
        if let Some(sort) = source.sorts.iter().find(|sort| !sort.indices.is_empty()) {
            return Err(AdmissionError::TermDependentSort(sort.name.clone()));
        }
        crate::first_order::validate(source).map_err(AdmissionError::Signature)?;
        for operation in &source.opers {
            for port in operation
                .arity
                .inputs
                .iter()
                .chain(&operation.arity.outputs)
            {
                if !port.arguments.is_empty() {
                    return Err(AdmissionError::IndexedOccurrence(port.sort.clone()));
                }
                for binder in &port.bindings {
                    if !binder.arguments.is_empty() {
                        return Err(AdmissionError::IndexedOccurrence(binder.sort.clone()));
                    }
                }
            }
            if operation
                .arity
                .outputs
                .iter()
                .any(|port| !port.bindings.is_empty())
            {
                return Err(AdmissionError::BindingResult(operation.name.clone()));
            }
        }
        Ok(Self { source })
    }

    /// Check a complete, context-annotated binding judgement.
    ///
    /// # Specification
    /// - ensures: every context entry is a declared representable sort, every
    ///   variable has its contextual sort, and every operation has its declared
    ///   result, arity and argument-local binder telescope.
    /// - fails: undeclared or ordinary context sorts, unbound variables,
    ///   unknown operations, arity errors and sort mismatches are
    ///   distinguished.
    /// - panics: none.
    /// - executable: none — the check is its own decision procedure; a
    ///   predicate would run it a second time.
    ///
    /// # Errors
    /// Returns the refusal of [`Self::check_context`] or
    /// [`Self::check_term`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — mixed sorts, sibling-local binders and one invalid
    ///   position per refusal separate incorrect scope, arity and sort
    ///   acceptance; every generated well-scoped judgement is accepted.
    /// - witness: `tests::glf::model::typing_boundaries`
    /// - witness: `tests::glf::model::identification`
    #[inline]
    pub fn check(
        &self,
        judgement: &BindingJudgement,
    ) -> Result<(), BindingError>
    {
        self.check_context(&judgement.context)?;
        self.check_term(&judgement.context, &judgement.sort, &judgement.term)
    }

    /// Check the representable context alphabet.
    ///
    /// # Specification
    /// - ensures: all context entries name representable declared sorts.
    /// - fails: the first undeclared or nonrepresentable entry is named.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns `UnknownSort` or `NonRepresentable`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — ordinary and absent sorts distinguish both refusals.
    /// - witness: `tests::glf::model::typing_boundaries`
    #[spec(ensures: |ref result| match *result {
        Ok(()) => true,
        Err(BindingError::UnknownSort(ref name) | BindingError::NonRepresentable(ref name)) =>
            context.contains(name),
        Err(
            BindingError::UnknownOperation(_)
            | BindingError::UnboundVariable(_)
            | BindingError::SortMismatch { .. }
            | BindingError::Arity(_)
            | BindingError::EnvironmentArity
            | BindingError::NonCanonical
            | BindingError::InvalidState,
        ) => false,
    })]
    pub(crate) fn check_context(
        &self,
        context: &[Name],
    ) -> Result<(), BindingError>
    {
        let sorts: BTreeMap<&Name, &SortDesc> = self
            .source
            .sorts
            .iter()
            .map(|sort| (&sort.name, sort))
            .collect();
        for name in context {
            let sort = sorts
                .get(name)
                .ok_or_else(|| BindingError::UnknownSort(name.clone()))?;
            if sort.representability != Representability::Representable {
                return Err(BindingError::NonRepresentable(name.clone()));
            }
        }
        Ok(())
    }

    /// Check one tree using an explicit scope-restoration stack.
    ///
    /// # Specification
    /// - requires: ambient context entries are admitted representable sorts.
    /// - ensures: acceptance exactly for well-sorted variables and operations.
    /// - fails: unknown result sorts, operations, arities or variable sorts.
    /// - panics: none.
    /// - executable: none — the check is its own decision procedure; a
    ///   predicate would run it a second time.
    ///
    /// # Errors
    /// Returns the corresponding `BindingError`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — sibling-local mixed binders and out-of-scope
    ///   variables expose failure to restore scopes and wrong de Bruijn
    ///   direction.
    /// - witness: `tests::glf::model::typing_boundaries`
    pub(crate) fn check_term(
        &self,
        context: &[Name],
        sort: &Name,
        term: &BindingTerm,
    ) -> Result<(), BindingError>
    {
        if !self
            .source
            .sorts
            .iter()
            .any(|declared| declared.name == *sort)
        {
            return Err(BindingError::UnknownSort(sort.clone()));
        }
        let mut scope = context.to_vec();
        let mut work = alloc::vec![Check::Term(term.0.to_ref(), sort)];
        while let Some(step) = work.pop() {
            match step {
                Check::Restore(length) => scope.truncate(length),
                Check::Argument(node, port) => {
                    work.push(Check::Restore(scope.len()));
                    scope.extend(port.bindings.iter().map(|binder| binder.sort.clone()));
                    work.push(Check::Term(node, &port.sort));
                },
                Check::Term(node, expected) => match *node.head() {
                    BindingHead::Variable(index) => {
                        let actual = scope
                            .iter()
                            .rev()
                            .nth(usize::from(index))
                            .ok_or(BindingError::UnboundVariable(index))?;
                        same_sort(expected, actual)?;
                    },
                    BindingHead::Operation(ref name, count) => {
                        let operation = self.operation(name)?;
                        let result = operation
                            .arity
                            .outputs
                            .first()
                            .ok_or(BindingError::InvalidState)?;
                        same_sort(expected, &result.sort)?;
                        if usize::from(count) != operation.arity.inputs.len() {
                            return Err(BindingError::Arity(name.clone()));
                        }
                        // The stack reverses traversal, not argument/port pairing.
                        work.extend(
                            node.children()
                                .zip(&operation.arity.inputs)
                                .map(|(child, port)| Check::Argument(child, port)),
                        );
                    },
                },
            }
        }
        Ok(())
    }

    /// Resolve a source operation by its declared name.
    ///
    /// # Specification
    /// - ensures: the first declaration with the requested name.
    /// - fails: an undeclared name is retained in the error.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns `UnknownOperation`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — unknown and non-first operation names distinguish a
    ///   missing lookup or accidental first-declaration fallback.
    /// - witness: `tests::glf::model::typing_boundaries`
    #[spec(ensures: |ref result| match *result {
        Ok(operation) => operation.name == *name,
        Err(ref error) => *error == BindingError::UnknownOperation(name.clone()),
    })]
    pub(crate) fn operation(
        &self,
        name: &Name,
    ) -> Result<&'signature OperDesc, BindingError>
    {
        self.source
            .opers
            .iter()
            .find(|operation| operation.name == *name)
            .ok_or_else(|| BindingError::UnknownOperation(name.clone()))
    }
}

/// Work for a nonrecursive sort checker.
enum Check<'term, 'signature>
{
    /// Visit one term at an expected sort.
    Term(TreeRef<'term, BindingHead>, &'signature Name),
    /// Enter the binders local to one operation argument.
    Argument(
        TreeRef<'term, BindingHead>,
        &'signature crate::arity::SortRef,
    ),
    /// Restore the ambient prefix after a child.
    Restore(usize),
}

/// Compare two known sorts without erasing the mismatch payload.
///
/// # Specification
/// - ensures: success exactly when names agree.
/// - fails: a mismatch retains both names.
/// - panics: none.
///
/// # Errors
/// Returns `SortMismatch`.
///
/// # Adequacy
/// - hypothesis: L3 — distinct declared sorts expose a collapsed comparison.
/// - witness: `tests::glf::model::typing_boundaries`
#[spec(ensures: |ref result| match *result {
    Ok(()) => expected == actual,
    Err(ref error) => *error == BindingError::SortMismatch { expected: expected.clone(), actual: actual.clone() },
})]
fn same_sort(
    expected: &Name,
    actual: &Name,
) -> Result<(), BindingError>
{
    if expected == actual {
        Ok(())
    }
    else {
        Err(BindingError::SortMismatch {
            expected: expected.clone(),
            actual: actual.clone(),
        })
    }
}
