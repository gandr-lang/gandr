//! Evaluation (`Y`) and readback (`Λ`) for every simply-sorted signature,
//! computed from the signature's declarations alone.
//!
//! A value is a neutral level or an operation whose arguments are
//! defunctionalized Kripke closures: a source body and the environment it
//! captured, opened under the binder telescope its operation declares for that
//! argument. No operation, sort or signature name selects a case: the
//! interpreter reads each argument's telescope from its [`OperDesc`].
//!
//! # Equality
//!
//! Semantic equality is observed by readback into a typed judgement at a fixed
//! context, which compares by structure. Arena handles are allocation order,
//! never identity: two evaluations of one term allocate distinct handles and
//! read back equal. An environment is data under one chosen isomorphism, the
//! empty environment or a prefix paired with its newest image; extension is the
//! one point where an evaluation allocates rather than copies, and readback
//! dereferences it. This is the ratified equality boundary of the first
//! experiment: canonical structural equality after dereferencing arena nodes.
//!
//! # Termination and space
//!
//! Evaluation stops at an operation: its arguments stay closures until
//! readback opens them, so evaluation is linear in the spine it reads.
//! Readback is an explicit continuation stack, so a term four thousand binders
//! deep reads back without host recursion, and it caches nothing: every call
//! opens every closure again, and the nodes it allocates are released when it
//! returns.

use alloc::boxed::Box;
use alloc::vec::Vec;

use anodized::spec;

use crate::binding::BindingError;
use crate::binding::BindingHead;
use crate::binding::BindingJudgement;
use crate::binding::BindingTerm;
use crate::binding::SimplySorted;
use crate::boundary::VariableIndex;
use crate::boundary::count_wrapper;
use crate::code::Name;
use crate::desc::OperDesc;
use crate::tree::TreeRef;

count_wrapper! {
    /// A semantic value's address in one evaluation's arena: allocation order,
    /// never structural identity.
    struct ValueId(usize);
}

count_wrapper! {
    /// An environment entry's address in one evaluation's arena.
    struct EntryId(usize);
}

count_wrapper! {
    /// A neutral's position counted from the oldest context entry, which
    /// extending the context leaves unchanged.
    struct Level(usize);
}

/// A persistent environment prefix, held in a flat entry arena.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Environment
{
    /// The empty environment.
    Empty,
    /// The newest entry's address.
    Extended(EntryId),
}

/// One context-extension pair, held without recursive ownership.
#[derive(Debug)]
struct Entry
{
    /// The captured prefix.
    prefix: Environment,
    /// The newest variable's image.
    value: ValueId,
}

/// The body/environment representation of a signature argument's binder action.
#[derive(Clone, Copy, Debug)]
struct Closure<'term>
{
    /// The source subtree; no quotation cache is retained.
    body: TreeRef<'term, BindingHead>,
    /// The source context's images in the target context.
    environment: Environment,
}

/// A generic semantic node; binding behavior comes only from its declaration.
#[derive(Debug)]
enum SemanticValue<'term, 'signature>
{
    /// A variable of the target context, at its stable level.
    Neutral(Level),
    /// A source operation with delayed arguments in declaration order.
    Operation(&'signature OperDesc, Box<[Closure<'term>]>),
}

/// A semantic judgement together with its flat values and environments.
///
/// # Specification
/// - provides: a value of the signature-derived free binding model, at a target
///   context and result sort. Environments are data under the chosen
///   empty/extension isomorphism; arena handles are private. Semantic equality
///   is observed by [`Evaluation::readback`] at the fixed typed context.
#[derive(Debug)]
pub struct Evaluation<'term, 'signature>
{
    /// The admitted operation table, fixed for this interpretation.
    operations: &'signature [OperDesc],
    /// The target context, oldest first.
    context: &'term [Name],
    /// The judgement's result sort.
    sort: &'term Name,
    /// The interpreted root.
    root: ValueId,
    /// Values owned by this interpretation.
    values: Vec<SemanticValue<'term, 'signature>>,
    /// Persistent captured environments.
    entries: Vec<Entry>,
}

impl<'signature, G> SimplySorted<'signature, G>
{
    /// Evaluate a judgement against the identity environment of its own
    /// context (`Y`).
    ///
    /// # Specification
    /// - ensures: variables reflect at their contextual levels; each operation
    ///   keeps exactly its declared argument bodies and the environment it
    ///   captured. The value's context and sort are the judgement's.
    /// - fails: ill-sorted or out-of-scope syntax is refused before evaluation.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns the typing refusal of [`Self::check`].
    ///
    /// # Adequacy
    /// - hypothesis: L2 — readback after evaluation is the identity on 256
    ///   generated judgements of each of three signatures, and on independent
    ///   goldens, so a lost operation, a wrong variable, a dropped or excess
    ///   binder and a reordered argument each change an observed judgement;
    ///   evaluation commutes with every operation at the root, observed through
    ///   readback.
    /// - witness: `tests::glf::model::both_views`
    /// - witness: `tests::glf::model::three_signatures`
    #[inline]
    #[spec(ensures: |ref result| result.as_ref().map_or(true, |value|
        value.context == judgement.context && value.sort == &judgement.sort))]
    pub fn evaluate<'term>(
        &self,
        judgement: &'term BindingJudgement,
    ) -> Result<Evaluation<'term, 'signature>, BindingError>
    {
        self.check(judgement)?;
        let (mut evaluation, environment) =
            Evaluation::reflect(&self.source.opers, &judgement.context, &judgement.sort);
        evaluation.root = evaluation.eval(judgement.term.0.to_ref(), environment)?;
        Ok(evaluation)
    }

    /// Evaluate under a sorted environment of images into an arbitrary target
    /// context: the action of a substitution.
    ///
    /// # Specification
    /// - ensures: `images` holds the image of each entry of the judgement's
    ///   context, oldest first, and each source variable reads its image;
    ///   entering a binder keeps the captured images, which their levels make
    ///   stable under extension, and adds the fresh variable of the binder's
    ///   sort. The value's context is `target` and its sort the judgement's.
    /// - fails: the judgement, the target context, the environment's length and
    ///   each image's sort are checked before evaluation.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns `EnvironmentArity` when the images and the context differ in
    /// length, otherwise the exact typing refusal of the judgement, the target
    /// context or the first ill-sorted image.
    ///
    /// # Adequacy
    /// - hypothesis: L2/L3 — single substitution, weakening, mixed-sort lifting
    ///   and operation naturality separate capture, reversed images and a
    ///   missing binder extension; an environment extended by one fresh
    ///   variable agrees with evaluation in the extended context; empty and
    ///   wrong-length environments pin the boundaries.
    /// - witness: `tests::glf::model::substitution_laws`
    /// - witness: `tests::glf::model::both_views`
    /// - witness: `tests::glf::model::typing_boundaries`
    #[inline]
    #[spec(ensures: |ref result| match *result {
        Ok(ref value) => value.context == target && value.sort == &judgement.sort,
        Err(BindingError::EnvironmentArity) => images.len() != judgement.context.len(),
        Err(_) => true,
    })]
    pub fn evaluate_in<'term>(
        &self,
        judgement: &'term BindingJudgement,
        target: &'term [Name],
        images: &'term [BindingTerm],
    ) -> Result<Evaluation<'term, 'signature>, BindingError>
    {
        self.check(judgement)?;
        self.check_context(target)?;
        if images.len() != judgement.context.len() {
            return Err(BindingError::EnvironmentArity);
        }
        for (image, sort) in images.iter().zip(&judgement.context) {
            self.check_term(target, sort, image)?;
        }
        let (mut evaluation, reflected) =
            Evaluation::reflect(&self.source.opers, target, &judgement.sort);
        let mut environment = Environment::Empty;
        for image in images {
            let value = evaluation.eval(image.0.to_ref(), reflected)?;
            environment = evaluation.extend(environment, value);
        }
        evaluation.root = evaluation.eval(judgement.term.0.to_ref(), environment)?;
        Ok(evaluation)
    }
}

impl<'term, 'signature> Evaluation<'term, 'signature>
{
    /// Reflect an open target context to its neutral levels.
    ///
    /// # Specification
    /// - ensures: one neutral and one entry per context entry, the environment
    ///   mapping each entry to its own level, oldest first.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — generated open contexts of every length up to eight,
    ///   with every position selected, expose a reversed or shifted initial
    ///   level through readback.
    /// - witness: `tests::glf::model::both_views`
    #[spec(ensures: |ref reflected| reflected.0.values.len() == context.len()
        && reflected.0.entries.len() == context.len()
        && (context.is_empty() == (reflected.1 == Environment::Empty)))]
    fn reflect(
        operations: &'signature [OperDesc],
        context: &'term [Name],
        sort: &'term Name,
    ) -> (Self, Environment)
    {
        let mut evaluation = Self {
            operations,
            context,
            sort,
            root: ValueId::from(0),
            values: Vec::with_capacity(context.len()),
            entries: Vec::with_capacity(context.len()),
        };
        let mut environment = Environment::Empty;
        for level in 0 .. context.len() {
            let value = evaluation.allocate(SemanticValue::Neutral(Level::from(level)));
            environment = evaluation.extend(environment, value);
        }
        (evaluation, environment)
    }

    /// Allocate one nonrecursive semantic node.
    ///
    /// # Specification
    /// trivial.
    fn allocate(
        &mut self,
        value: SemanticValue<'term, 'signature>,
    ) -> ValueId
    {
        let id = ValueId::from(self.values.len());
        self.values.push(value);
        id
    }

    /// Extend an environment by its newest image: one side of the
    /// prefix/newest-value isomorphism.
    ///
    /// # Specification
    /// - ensures: one entry is appended, pairing `prefix` with `value`, and the
    ///   result addresses it; lookup at zero then yields `value` and later
    ///   positions read `prefix`.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — different images for adjacent variables distinguish
    ///   extension from overwrite and prefix reversal.
    /// - witness: `tests::glf::model::substitution_laws`
    #[spec(
        captures: before = self.entries.len(),
        ensures: |environment| environment == Environment::Extended(EntryId::from(before))
            && self.entries.len() == before.saturating_add(1)
            && self.entries.last().is_some_and(|entry| entry.prefix == prefix && entry.value == value),
    )]
    fn extend(
        &mut self,
        prefix: Environment,
        value: ValueId,
    ) -> Environment
    {
        let id = EntryId::from(self.entries.len());
        self.entries.push(Entry { prefix, value });
        Environment::Extended(id)
    }

    /// Interpret a node without traversing beneath operation binders.
    ///
    /// # Specification
    /// - requires: the node is checked in the source context of `environment`.
    /// - ensures: a variable's image, allocating nothing, or one new operation
    ///   value whose arguments are closures over `environment`.
    /// - fails: an environment shorter than the variable's index or an
    ///   undeclared operation.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns `InvalidState` or `UnknownOperation`.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — nonidentity substitutions under several binders
    ///   distinguish closures from syntax copies or identity-only evaluation.
    /// - witness: `tests::glf::model::substitution_laws`
    #[spec(
        captures: before = self.values.len(),
        ensures: |ref result| match *result {
            Ok(id) => match *term.head() {
                BindingHead::Variable(_) => self.values.len() == before,
                BindingHead::Operation(..) => self.values.len() == before.saturating_add(1)
                    && usize::from(id) == before,
            },
            Err(_) => self.values.len() == before,
        },
    )]
    fn eval(
        &mut self,
        term: TreeRef<'term, BindingHead>,
        environment: Environment,
    ) -> Result<ValueId, BindingError>
    {
        match *term.head() {
            BindingHead::Variable(index) => {
                // economy: a lookup follows `index` links; an index-addressed
                // environment would make it constant if a measurement asks.
                let mut environment = environment;
                for offset in 0 ..= usize::from(index) {
                    let Environment::Extended(id) = environment
                    else {
                        return Err(BindingError::InvalidState);
                    };
                    let entry = self
                        .entries
                        .get(usize::from(id))
                        .ok_or(BindingError::InvalidState)?;
                    if offset == usize::from(index) {
                        return Ok(entry.value);
                    }
                    environment = entry.prefix;
                }
                Err(BindingError::InvalidState)
            },
            BindingHead::Operation(ref name, _) => {
                // economy: the operation is found by a scan of the declarations;
                // an index by name pays off only for large signatures.
                let operation = self
                    .operations
                    .iter()
                    .find(|operation| operation.name == *name)
                    .ok_or_else(|| BindingError::UnknownOperation(name.clone()))?;
                let arguments = term
                    .children()
                    .map(|body| Closure { body, environment })
                    .collect();
                Ok(self.allocate(SemanticValue::Operation(operation, arguments)))
            },
        }
    }

    /// Read the value back as a typed judgement (`Λ`), opening every closure
    /// again on each call.
    ///
    /// # Specification
    /// - ensures: the canonical typed binding judgement, with fresh levels
    ///   under each argument's exact binder telescope; its context and sort are
    ///   the evaluation's. Repeated calls read back the same judgement,
    ///   whatever handles they allocate, and every node a call allocates is
    ///   released before it returns.
    /// - fails: inconsistent internal values, environments or quotation stacks.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns `InvalidState` for inconsistent internal data.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — both identification composites and readback twice on
    ///   256 generated judgements of each of three signatures expose a lost
    ///   head, argument reversal and capture; L3 — nonidentity substitutions
    ///   distinguish readback from source reuse, and a term four thousand
    ///   binders deep distinguishes an iterative readback from a recursive one.
    /// - witness: `tests::glf::model::both_views`
    /// - witness: `tests::glf::model::substitution_laws`
    /// - witness: `tests::glf::model::deep_uncached_binders`
    #[inline]
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            spec_clause_traversal,
            reason = "parity: the body copies the context into the judgement once; the check compares it once"
        )
    )]
    #[spec(
        captures: before = (self.values.len(), self.entries.len()),
        ensures: |ref result| (self.values.len(), self.entries.len()) == before
            && match *result {
                Ok(ref judgement) => judgement.context == self.context && &judgement.sort == self.sort,
                Err(_) => true,
            },
    )]
    pub fn readback(&mut self) -> Result<BindingJudgement, BindingError>
    {
        let values = self.values.len();
        let entries = self.entries.len();
        let result = self.quote();
        self.values.truncate(values);
        self.entries.truncate(entries);
        result
    }

    /// Rebuild the typed tree, keeping temporary arena nodes until it is
    /// complete.
    ///
    /// # Specification
    /// - ensures: the canonical readback of the root at its target context.
    /// - fails: inconsistent arena links or continuation stacks.
    /// - panics: none.
    /// - executable: none — the readback is observed by evaluating and reading
    ///   it back again, which [`Self::readback`]'s witnesses do; a predicate
    ///   here would repeat the quotation.
    ///
    /// # Errors
    /// Returns `InvalidState` for inconsistent internal data.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — asymmetric typed goldens expose capture and reversal.
    /// - witness: `tests::glf::model::both_views`
    /// - witness: `tests::glf::model::substitution_laws`
    fn quote(&mut self) -> Result<BindingJudgement, BindingError>
    {
        let mut work = alloc::vec![Quote::Value(self.root, Level::from(self.context.len()))];
        let mut terms = Vec::new();
        while let Some(step) = work.pop() {
            match step {
                Quote::Value(id, depth) => {
                    let value = self
                        .values
                        .get(usize::from(id))
                        .ok_or(BindingError::InvalidState)?;
                    match *value {
                        SemanticValue::Neutral(level) => {
                            let index = usize::from(depth)
                                .checked_sub(usize::from(level))
                                .and_then(|distance| distance.checked_sub(1))
                                .ok_or(BindingError::InvalidState)?;
                            terms.push(BindingTerm::variable(VariableIndex::from(index)));
                        },
                        SemanticValue::Operation(operation, ref arguments) => {
                            work.push(Quote::Close(&operation.name, arguments.len()));
                            work.extend(
                                arguments
                                    .iter()
                                    .zip(&operation.arity.inputs)
                                    .rev()
                                    .map(|(closure, port)| Quote::Open(*closure, port, depth)),
                            );
                        },
                    }
                },
                Quote::Open(closure, port, depth) => {
                    let mut environment = closure.environment;
                    let mut depth = usize::from(depth);
                    for _ in &port.bindings {
                        let fresh = self.allocate(SemanticValue::Neutral(Level::from(depth)));
                        environment = self.extend(environment, fresh);
                        depth = depth.saturating_add(1);
                    }
                    let value = self.eval(closure.body, environment)?;
                    work.push(Quote::Value(value, Level::from(depth)));
                },
                Quote::Close(name, count) => {
                    let start = terms
                        .len()
                        .checked_sub(count)
                        .ok_or(BindingError::InvalidState)?;
                    let arguments = terms.split_off(start);
                    terms.push(BindingTerm::operation(name.clone(), arguments));
                },
            }
        }
        let term = terms.pop().ok_or(BindingError::InvalidState)?;
        Ok(BindingJudgement {
            context: self.context.to_vec(),
            sort: self.sort.clone(),
            term,
        })
    }
}

/// Explicit continuation frames for uncached quotation.
enum Quote<'term, 'signature>
{
    /// Observe a value in a context of the given length.
    Value(ValueId, Level),
    /// Open a closure under the port's telescope, in a context of the given
    /// length.
    Open(Closure<'term>, &'signature crate::arity::SortRef, Level),
    /// Rebuild an operation from its quoted arguments.
    Close(&'signature Name, usize),
}
