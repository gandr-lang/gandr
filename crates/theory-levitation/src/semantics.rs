//! One environment interpretation and uncached readback for binding signatures.
//!
//! Operation arguments are defunctionalized Kripke closures: a body and
//! captured environment, opened under their signature's representable binder
//! telescope.

use alloc::boxed::Box;
use alloc::vec::Vec;

use crate::binding::BindingError;
use crate::binding::BindingHead;
use crate::binding::BindingJudgement;
use crate::binding::BindingTerm;
use crate::binding::SimplySorted;
use crate::binding::VariableIndex;
use crate::code::Name;
use crate::desc::OperDesc;
use crate::tree::TreeRef;

/// A local semantic arena address, never structural identity.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
struct ValueId(usize);

/// A persistent environment prefix, represented by a flat entry arena.
#[derive(Clone, Copy, Debug)]
enum Environment
{
    /// The empty environment.
    Empty,
    /// The newest entry's address.
    Extended(usize),
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
    /// A stable oldest-first level, invariant under target-context extension.
    Neutral(usize),
    /// A source operation with delayed arguments in declaration order.
    Operation(&'signature OperDesc, Box<[Closure<'term>]>),
}

/// A semantic judgement together with its flat values and environments.
///
/// # Specification
/// - provides: a signature-derived free binding model. Environments are data
///   under the chosen empty/extension isomorphism; arena handles are private.
///   Semantic equality is observed by uncached readback at a fixed typed
///   context.
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
    /// Evaluate a judgement against its reflected identity environment (`Y`).
    ///
    /// # Specification
    /// - ensures: variables reflect at their contextual levels; each operation
    ///   retains exactly its declared argument bodies and captured environment.
    /// - fails: ill-sorted or out-of-scope syntax is refused before evaluation.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns the typing refusal from `check`, or `InvalidState` for an
    /// inconsistent internal environment.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — independently constructed q/p and binding terms on
    ///   three signatures separate lost operations, wrong variables and
    ///   binders.
    /// - witness: `tests::glf::model::three_signatures`
    #[inline]
    #[anodized::spec(ensures: |ref result| match *result {
        | Ok(ref value) => value.context == judgement.context && value.sort == &judgement.sort,
        | Err(_) => true,
    })]
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

    /// Evaluate using a sorted substitution into an arbitrary target context.
    ///
    /// # Specification
    /// - ensures: source variables select images oldest-first; entering a
    ///   binder weakens captured images and extends with the fresh variable of
    ///   its sort.
    /// - fails: environment length, target context and image typing are
    ///   checked.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns `EnvironmentArity` or the exact context/image/term typing
    /// refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L2/L3 — single substitution, weakening, mixed-sort lifting
    ///   and operation naturality separate capture, reversed images and missing
    ///   binder extension. Empty and wrong-length environments pin boundaries.
    /// - witness: `tests::glf::model::substitution_laws`
    /// - witness: `tests::glf::model::typing_boundaries`
    #[inline]
    #[anodized::spec(ensures: |ref result| match *result {
        | Ok(ref value) => value.context == target && value.sort == &judgement.sort,
        | Err(_) => true,
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
    /// Reflect an open target context to stable neutral levels.
    ///
    /// # Specification
    /// - ensures: the environment maps each context entry to its own level.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — mixed open contexts and every selected position
    ///   expose reversal or an incorrect initial level.
    /// - witness: `tests::glf::model::three_signatures`
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
            root: ValueId(0),
            values: Vec::with_capacity(context.len()),
            entries: Vec::with_capacity(context.len()),
        };
        let mut environment = Environment::Empty;
        for level in 0 .. context.len() {
            let value = evaluation.allocate(SemanticValue::Neutral(level));
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
        let id = ValueId(self.values.len());
        self.values.push(value);
        id
    }

    /// Implement the prefix/newest-value environment isomorphism.
    ///
    /// # Specification
    /// - ensures: lookup at zero yields `value`, later positions read `prefix`.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — different images for adjacent variables distinguish
    ///   extension from overwrite and prefix reversal.
    /// - witness: `tests::glf::model::substitution_laws`
    fn extend(
        &mut self,
        prefix: Environment,
        value: ValueId,
    ) -> Environment
    {
        let id = self.entries.len();
        self.entries.push(Entry { prefix, value });
        Environment::Extended(id)
    }

    /// Interpret a node without traversing beneath operation binders.
    ///
    /// # Specification
    /// - requires: the node is checked in the source context of `environment`.
    /// - ensures: a variable's image or an operation with captured arguments.
    /// - fails: inconsistent environment links or an undeclared operation.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns `InvalidState` or `UnknownOperation`.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — nonidentity substitutions under multiple binders
    ///   distinguish closures from syntax copies or identity-only evaluation.
    /// - witness: `tests::glf::model::substitution_laws`
    fn eval(
        &mut self,
        term: TreeRef<'term, BindingHead>,
        environment: Environment,
    ) -> Result<ValueId, BindingError>
    {
        match *term.head() {
            | BindingHead::Variable(index) => {
                let mut environment = environment;
                for offset in 0 ..= index.0 {
                    let Environment::Extended(id) = environment
                    else {
                        return Err(BindingError::InvalidState);
                    };
                    let entry = self.entries.get(id).ok_or(BindingError::InvalidState)?;
                    if offset == index.0 {
                        return Ok(entry.value);
                    }
                    environment = entry.prefix;
                }
                Err(BindingError::InvalidState)
            },
            | BindingHead::Operation(ref name, _) => {
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

    /// Quote the semantic judgement, opening every binder without a source
    /// cache.
    ///
    /// # Specification
    /// - ensures: the canonical typed binding judgement (`Λ`), using fresh
    ///   levels under each argument's exact binder telescope. Repeated calls
    ///   observe the same structure regardless of fresh arena allocations.
    /// - fails: inconsistent internal values, environments or quotation stacks.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns `InvalidState` for inconsistent internal data.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — both identification composites and uncached quotation
    ///   on three signatures expose lost heads, argument reversal and capture;
    ///   L3 — nonidentity substitutions distinguish readback from source reuse.
    /// - witness: `tests::glf::model::three_signatures`
    /// - witness: `tests::glf::model::substitution_laws`
    #[inline]
    #[anodized::spec(ensures: |ref result| match *result {
        | Ok(ref judgement) => judgement.context == self.context && &judgement.sort == self.sort,
        | Err(_) => true,
    })]
    pub fn readback(&mut self) -> Result<BindingJudgement, BindingError>
    {
        let values = self.values.len();
        let entries = self.entries.len();
        let result = self.quote();
        self.values.truncate(values);
        self.entries.truncate(entries);
        result
    }

    /// Rebuild the typed tree, retaining temporary arena nodes until
    /// completion.
    ///
    /// # Specification
    /// - ensures: the canonical readback of the root at its target context.
    /// - fails: inconsistent arena links or continuation stacks.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns `InvalidState` for inconsistent internal data.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — asymmetric typed goldens expose capture and reversal.
    /// - witness: `tests::glf::model::three_signatures`
    /// - witness: `tests::glf::model::substitution_laws`
    fn quote(&mut self) -> Result<BindingJudgement, BindingError>
    {
        let mut work = alloc::vec![Quote::Value(self.root, self.context.len())];
        let mut terms = Vec::new();
        while let Some(step) = work.pop() {
            match step {
                | Quote::Value(id, depth) => {
                    let value = self.values.get(id.0).ok_or(BindingError::InvalidState)?;
                    match *value {
                        | SemanticValue::Neutral(level) => {
                            let index = depth
                                .checked_sub(level)
                                .and_then(|distance| distance.checked_sub(1))
                                .ok_or(BindingError::InvalidState)?;
                            terms.push(BindingTerm::variable(VariableIndex(index)));
                        },
                        | SemanticValue::Operation(operation, ref arguments) => {
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
                | Quote::Open(closure, port, depth) => {
                    let mut environment = closure.environment;
                    let mut depth = depth;
                    for _ in &port.bindings {
                        let fresh = self.allocate(SemanticValue::Neutral(depth));
                        environment = self.extend(environment, fresh);
                        depth = depth.saturating_add(1);
                    }
                    let value = self.eval(closure.body, environment)?;
                    work.push(Quote::Value(value, depth));
                },
                | Quote::Close(name, count) => {
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
    /// Observe a value at an ambient context length.
    Value(ValueId, usize),
    /// Open a closure at the port's telescope.
    Open(Closure<'term>, &'signature crate::arity::SortRef, usize),
    /// Rebuild an operation from its quoted arguments.
    Close(&'signature Name, usize),
}
