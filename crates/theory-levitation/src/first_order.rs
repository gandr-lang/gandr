//! The first-order model a signature generates: Kaposi and Xie's
//! single-substitution translation, written as one fold over the signature's
//! declarations.
//!
//! The translation follows Ambrus Kaposi and Szumi Xie, _Second-Order
//! Generalised Algebraic Theories: Signatures and First-Order Semantics_, FSCD
//! 2024, `doi:10.4230/LIPIcs.FSCD.2024.10`: Definitions 3–4 give the
//! signatures and their first-order models, §6 the translation, and §7 its
//! single-substitution variant. The generated presentation has a sort of
//! contexts `$Con`, a sort of substitutions `$Sub(D, G)` and, for every source
//! sort, a family indexed by a context and the sort's own indices, with its
//! substitution action `$sub`. Each representable sort adds context extension
//! `$extend`, weakening `$p`, the newest variable `$q`, single substitution
//! `$single` and lifting `$lift`, with the eight single-substitution laws
//! specialized to it (four of them vacuous for an unindexed sort). Each
//! operation is translated once, its π⁺ binders extending the context of the
//! argument they bind, and gains its naturality equation: substitution
//! commutes with it, lifted once under each binder.
//!
//! # Decisions
//!
//! **One fold, no per-signature case.** Sorts, operations and equations are
//! visited in declaration order by one fold whose step reads only the
//! declaration; no sort, operation or signature name selects a case, and a
//! signature renamed throughout translates to the renamed presentation.
//!
//! **Single substitution.** Contexts and substitutions form a pointed graph,
//! not a category: no identity substitution, no composition and no empty
//! substitution are generated (`$empty` is the empty context). These are the
//! operations the kernel's de Bruijn machinery already implements — shifting,
//! substitution of the innermost binder — so the generated model is the one
//! the kernel can check against.
//!
//! - **Alternatives.** The parallel-substitution translation of the paper's §6
//!   adds a category of substitutions and its laws, which nothing in the kernel
//!   implements; a translation written per signature duplicates the structural
//!   laws for each one.
//! - **Reversal.** A consumer that needs composite substitutions as terms,
//!   rather than as iterated single ones, takes the parallel translation; the
//!   paper conjectures the two equivalent (§8).
//!
//! **Equations are carried, not oriented.** A source equation is copied into
//! the model with its context parameters implicit, as the paper's equation
//! notation writes them; the fold neither orients nor completes it, and the
//! generated laws are equations, not rewrite rules. Deciding equality in a
//! generated model owes a normalizer, which this module does not provide.
//!
//! **The input must already be well typed.** Index expressions are taken as
//! written: [`check_desc`] checks names, binder domains and arities, not
//! dependent typing, so the fold's output is well typed exactly when its input
//! was.

use alloc::boxed::Box;
use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use alloc::format;
use alloc::vec;
use alloc::vec::Vec;
use core::fmt;

use anodized::spec;

use crate::arity::BridgeArity;
use crate::arity::SortRef;
use crate::boundary::NameRef;
use crate::code::Attrs;
use crate::code::Name;
use crate::desc::DeclPolarity;
use crate::desc::NominalId;
use crate::desc::OperDesc;
use crate::desc::Representability;
use crate::desc::SortDesc;
use crate::desc::SortIndex;
use crate::desc::SurfaceSpan;
use crate::desc::TheoryDesc;
use crate::rule::FreeTerm;
use crate::rule::RuleFace;
use crate::wellformed::WfDiagnostic;
use crate::wellformed::check_desc;
use crate::wellformed::derive_cell_var_meta;

/// A description outside the translation's syntactic domain.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum TranslationError
{
    /// The source fails the description checker.
    Malformed(Vec<WfDiagnostic>),
    /// Constructor payloads or circuit fillers are not SOGAT operation
    /// declarations.
    NonSignatureMembers,
    /// A generated infrastructure name collides with a source name.
    ReservedName(Name),
    /// A sort index names an undeclared sort.
    UnknownIndexSort(Name),
    /// An operation is not a single-output product of its input telescope.
    NonProductOperation(Name),
    /// An operation abstracts an atom over a port, which the
    /// single-substitution model has no context extension for.
    AtomAbstraction(Name),
}

impl fmt::Display for TranslationError
{
    /// Render the rejected source component.
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
            Self::Malformed(_) => f.write_str("malformed signature"),
            Self::NonSignatureMembers => f.write_str(
                "constructor, circuit or external parameter outside the SOGAT signature",
            ),
            Self::ReservedName(ref name) => write!(f, "reserved generated name: {name}"),
            Self::UnknownIndexSort(ref name) => write!(f, "undeclared index sort: {name}"),
            Self::NonProductOperation(ref name) => write!(f, "non-product operation: {name}"),
            Self::AtomAbstraction(ref name) => {
                write!(f, "operation abstracting an atom: {name}")
            },
        }
    }
}

impl core::error::Error for TranslationError
{
}

/// A declaration visited by the translation fold.
enum Declaration<'source>
{
    /// One sort family.
    Sort(&'source SortDesc),
    /// One operation telescope.
    Operation(&'source OperDesc),
    /// An equation over operation applications.
    Equation(&'source RuleFace),
}

/// Mutable vectors owned by the declaration fold, frozen once at its boundary.
struct Model
{
    /// Context-indexed sort families.
    sorts: Vec<SortDesc>,
    /// Structural and signature operations.
    opers: Vec<OperDesc>,
    /// Single-substitution and naturality equations.
    rules: Vec<RuleFace>,
}

/// Translate one closed finitary operation signature to its first-order model,
/// the single-substitution presentation.
///
/// # Specification
/// - requires: index arguments are well-typed in their declared telescopes;
///   equation variables keep their source typing context.
/// - ensures: the model declares `$Con`, `$Sub` and one context-indexed family
///   per source sort; the operation `$empty`, one action `$sub` per sort, five
///   structural operations per representable sort and one operation per source
///   operation; the source equations, then for each representable sort its four
///   term laws and four laws per sort indexing it, and one naturality equation
///   per source operation. No model sort is representable and no model port
///   binds: the model is first-order. No composition, identity or empty
///   substitution is generated.
/// - fails: malformed descriptions, constructor/circuit members, generated-name
///   collisions, undeclared index sorts and non-product operations are refused.
/// - panics: none.
///
/// # Errors
/// Returns the corresponding variant of [`TranslationError`].
///
/// # Adequacy
/// - hypothesis: L2 — the λ-calculus presentation derived independently from
///   the paper (three sorts, nine operations, six equations) and the eight
///   printed laws of the dependent `Ty/Tm` fixture separate a missing
///   structural operation, a swapped substitution leg and missing or excess
///   lifting. L3 — an indexed family and a renamed signature separate a
///   hard-coded case; each refusal is observed by its exact variant.
/// - witness: `tests::glf::generation`
/// - witness: `tests::glf::indexed_signature_translates_without_name_cases`
/// - witness: `tests::glf::translation_refuses_non_signatures`
#[spec(ensures: |ref result| result.as_ref().map_or(true, |model|
    model.sorts.len() == source.sorts.len().saturating_add(2)
        && model.opers.len() == source.sorts.len()
            .saturating_add(1)
            .saturating_add(source.sorts.iter()
                .filter(|sort| sort.representability == Representability::Representable)
                .count()
                .saturating_mul(5))
            .saturating_add(source.opers.len())
        && model.rules.len() == source.rules.len()
            .saturating_add(source.opers.len())
            .saturating_add(source.sorts.iter()
                .filter(|sort| sort.representability == Representability::Representable)
                .map(|sort| source.sorts.iter()
                    .filter(|family| sort.indices.iter().any(|index| index.sort == family.name))
                    .count()
                    .saturating_add(1)
                    .saturating_mul(4))
                .fold(0_usize, usize::saturating_add))
        && model.sorts.iter().all(|sort| sort.representability == Representability::Ordinary)
        && model.opers.iter().all(|op| op.arity.inputs.iter().all(|port| port.bindings.is_empty()))))]
#[inline]
pub fn first_order<G>(source: &TheoryDesc<G>) -> Result<TheoryDesc<G>, TranslationError>
{
    validate(source)?;
    let initial = Model {
        sorts: vec![
            SortDesc::new("$Con", DeclPolarity::Data),
            SortDesc::family("$Sub", DeclPolarity::Data, [
                SortIndex::new("D", "$Con"),
                SortIndex::new("G", "$Con"),
            ]),
        ],
        opers: vec![operation("$empty", [], port("", "$Con", []))],
        rules: Vec::new(),
    };
    let declarations = source
        .sorts
        .iter()
        .map(Declaration::Sort)
        .chain(source.opers.iter().map(Declaration::Operation))
        .chain(source.rules.iter().map(Declaration::Equation));
    let model = declarations.fold(initial, |mut model, declaration| {
        match declaration {
            Declaration::Sort(sort) => translate_sort(&mut model, source, sort),
            Declaration::Operation(op) => translate_operation(&mut model, source, op),
            Declaration::Equation(rule) => model.rules.push(rule.clone()),
        }
        model
    });
    Ok(TheoryDesc::new(
        NominalId::new(source.id.serial, format!("{}$ssc", source.id.name)),
        [],
        [],
        model.opers,
        model.rules,
        DeclPolarity::Data,
        Attrs::empty(),
    )
    .with_sorts(model.sorts))
}

/// Validate the structural domain before producing any model declarations.
///
/// # Specification
/// - ensures: success exactly for well-formed operation signatures with
///   declared index sorts, reserved-name-free names, single-output product
///   telescopes and no atom abstraction.
/// - fails: malformed descriptions, non-signature members or the first
///   offending name or operation are refused.
/// - panics: none.
///
/// # Errors
/// Returns [`TranslationError::Malformed`],
/// [`TranslationError::NonSignatureMembers`],
/// [`TranslationError::ReservedName`], [`TranslationError::UnknownIndexSort`],
/// [`TranslationError::NonProductOperation`] or
/// [`TranslationError::AtomAbstraction`].
///
/// # Adequacy
/// - hypothesis: L3 — name, unknown-sort and non-product boundaries distinguish
///   the refusals from valid telescopes; each member kind and each product
///   condition (one output, one monomial, the inputs in order) is refused
///   alone, and so is a port abstracting an atom.
/// - witness: `tests::glf::translation_refuses_non_signatures`
/// - witness: `tests::glf::model::admission`
#[spec(ensures: |ref result| result.is_err() || source.sorts.iter().all(|sort| !sort.name.as_ref().starts_with('$')))]
pub fn validate<G>(source: &TheoryDesc<G>) -> Result<(), TranslationError>
{
    let diagnostics = check_desc(source);
    if !diagnostics.is_empty() {
        return Err(TranslationError::Malformed(diagnostics));
    }
    if !source.ctors.is_empty() || !source.circuits.is_empty() || !source.params.is_empty() {
        return Err(TranslationError::NonSignatureMembers);
    }
    for name in source
        .sorts
        .iter()
        .map(|sort| &sort.name)
        .chain(source.opers.iter().map(|op| &op.name))
    {
        if name.as_ref().starts_with('$') {
            return Err(TranslationError::ReservedName(name.clone()));
        }
    }
    let declared: BTreeSet<&Name> = source.sorts.iter().map(|sort| &sort.name).collect();
    for index in source.sorts.iter().flat_map(|sort| &sort.indices) {
        if !declared.contains(&index.sort) {
            return Err(TranslationError::UnknownIndexSort(index.sort.clone()));
        }
    }
    // A product: one output and one monomial reading every input once, in
    // order. Well-formedness then fixes the monomial's destination to output
    // 0, so `dest` needs no comparison of its own.
    for op in &source.opers {
        if op.arity.outputs.len() != 1
            || op.arity.factors.as_ref()
                != [u32::try_from(op.arity.inputs.len()).unwrap_or(u32::MAX)]
            || !op
                .arity
                .source
                .iter()
                .copied()
                .eq(0 .. u32::try_from(op.arity.inputs.len()).unwrap_or(u32::MAX))
        {
            return Err(TranslationError::NonProductOperation(op.name.clone()));
        }
        if op
            .arity
            .inputs
            .iter()
            .chain(&op.arity.outputs)
            .any(|port| !port.abstractions.is_empty())
        {
            return Err(TranslationError::AtomAbstraction(op.name.clone()));
        }
    }
    Ok(())
}

/// Build a named port of an indexed sort.
///
/// # Specification
/// trivial.
fn port<const N: usize>(
    name: impl Into<Name>,
    sort: impl Into<Name>,
    arguments: [FreeTerm; N],
) -> SortRef
{
    SortRef::new(name, sort).applied(arguments)
}

/// Build a single-output operation over an ordinary telescope.
///
/// # Specification
/// trivial.
fn operation<I>(
    name: impl Into<Name>,
    inputs: I,
    output: SortRef,
) -> OperDesc
where
    I: Into<Box<[SortRef]>>,
{
    OperDesc::new(
        name,
        BridgeArity::single_output(inputs, output),
        Attrs::empty(),
    )
}

/// A signature variable in a generated equation.
///
/// # Specification
/// trivial.
fn variable(name: impl Into<Name>) -> FreeTerm
{
    FreeTerm::var(name)
}

/// An infrastructure operation specialized to a sort name.
///
/// # Specification
/// trivial.
fn named(
    kind: NameRef<'_>,
    sort: &Name,
) -> Name
{
    Name::from(format!("${}_{sort}", kind.as_ref()))
}

/// An application with context parameters left explicit.
///
/// # Specification
/// trivial.
fn application(
    name: impl Into<Name>,
    arguments: impl IntoIterator<Item = FreeTerm>,
) -> FreeTerm
{
    FreeTerm::op(name, arguments)
}

/// Append an operation to a description under construction.
///
/// # Specification
/// trivial.
fn push_operation(
    model: &mut Model,
    op: OperDesc,
)
{
    model.opers.push(op);
}

/// Append an equation, deriving its variable metadata from its actual sides.
///
/// # Specification
/// trivial.
fn push_equation(
    model: &mut Model,
    lhs: FreeTerm,
    rhs: FreeTerm,
)
{
    let vars = derive_cell_var_meta(&lhs);
    model
        .rules
        .push(RuleFace::new(lhs, rhs, vars, SurfaceSpan::default()));
}

/// The source index telescope's variables.
///
/// # Specification
/// trivial.
fn indices(sort: &SortDesc) -> Vec<FreeTerm>
{
    sort.indices
        .iter()
        .map(|index| FreeTerm::var(index.name.clone()))
        .collect()
}

/// Substitute a term of the given sort with all context and index parameters.
///
/// # Specification
/// trivial.
fn action(
    sort: &Name,
    from: FreeTerm,
    to: FreeTerm,
    indices: &[FreeTerm],
    term: FreeTerm,
    substitution: FreeTerm,
) -> FreeTerm
{
    application(
        named("sub".into(), sort),
        [from, to]
            .into_iter()
            .chain(indices.iter().cloned())
            .chain([term, substitution]),
    )
}

/// Translate a sort telescope to one context and its dependent indices.
///
/// # Specification
/// - ensures: the context precedes the source indices; every index sort is
///   applied to that context followed by its own index arguments.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L2 — indexed identity-return signatures distinguish erasure
///   and reversal of context and sort arguments.
/// - witness: `tests::glf::indexed_signature_translates_without_name_cases`
#[spec(ensures: |ref ports| ports.len() == sort.indices.len().saturating_add(1))]
fn telescope(
    sort: &SortDesc,
    context: NameRef<'_>,
) -> Vec<SortRef>
{
    let mut ports = vec![port(context.as_ref(), "$Con", [])];
    for index in &sort.indices {
        ports.push(
            SortRef::new(index.name.clone(), index.sort.clone()).applied(
                core::iter::once(variable(context.as_ref()))
                    .chain(index.arguments.iter().cloned())
                    .collect::<Vec<_>>(),
            ),
        );
    }
    ports
}

/// Translate one sort and the structural operations its representability owns.
///
/// # Specification
/// - ensures: one context-indexed family and its action are appended; only a
///   representable family receives variable and substitution constructors.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L2 — the λ-calculus table distinguishes omitted
///   infrastructure; L3 — mixed representability distinguishes adding variables
///   to every sort.
/// - witness: `tests::glf::generation`
/// - witness: `tests::glf::indexed_signature_translates_without_name_cases`
#[spec(
    captures: before = model.sorts.len(),
    ensures: model.sorts.len() == before.saturating_add(1)
        && model.sorts.last().is_some_and(|generated| generated.name == sort.name
            && generated.indices.len() == sort.indices.len().saturating_add(1)),
)]
fn translate_sort<G>(
    model: &mut Model,
    source: &TheoryDesc<G>,
    sort: &SortDesc,
)
{
    let index_telescope = telescope(sort, "G".into())
        .into_iter()
        .map(|index| SortIndex::new(index.name, index.sort).applied(index.arguments))
        .collect::<Vec<_>>();
    model.sorts.push(SortDesc::family(
        sort.name.clone(),
        DeclPolarity::Data,
        index_telescope,
    ));
    let args = indices(sort);
    let mut inputs = telescope(sort, "G".into());
    inputs.insert(1, port("D", "$Con", []));
    inputs.push(
        SortRef::new("t", sort.name.clone()).applied(
            core::iter::once(variable("G"))
                .chain(args.iter().cloned())
                .collect::<Vec<_>>(),
        ),
    );
    inputs.push(port("s", "$Sub", [variable("D"), variable("G")]));
    let shifted = sort.indices.iter().zip(&args).map(|(index, arg)| {
        action(
            &index.sort,
            variable("G"),
            variable("D"),
            &index.arguments,
            arg.clone(),
            variable("s"),
        )
    });
    let output = SortRef::new("", sort.name.clone()).applied(
        core::iter::once(variable("D"))
            .chain(shifted)
            .collect::<Vec<_>>(),
    );
    push_operation(
        model,
        operation(named("sub".into(), &sort.name), inputs, output),
    );
    if sort.representability == Representability::Representable {
        representable(model, source, sort);
    }
}

/// Generate context extension, weakening, newest variable, single substitution
/// and lifting for one representable family.
///
/// # Specification
/// - ensures: exactly those five structural operations are appended, lifting
///   last, with the lifted source context extending by the substituted family
///   and q typed by weakened indices.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L2 — λ-calculus and indexed-family tables observe all five
///   operations and their endpoint order; the q and weakening equations expose
///   a swapped leg.
/// - witness: `tests::glf::generation`
/// - witness: `tests::glf::indexed_signature_translates_without_name_cases`
#[spec(
    captures: before = model.opers.len(),
    ensures: model.opers.len() == before.saturating_add(5)
        && model.opers.last().is_some_and(|op| op.name == named("lift".into(), &sort.name)),
)]
fn representable<G>(
    model: &mut Model,
    source: &TheoryDesc<G>,
    sort: &SortDesc,
)
{
    let args = indices(sort);
    let base = telescope(sort, "G".into());
    let extension = application(
        named("extend".into(), &sort.name),
        core::iter::once(variable("G")).chain(args.iter().cloned()),
    );
    let weakening = application(
        named("p".into(), &sort.name),
        core::iter::once(variable("G")).chain(args.iter().cloned()),
    );
    push_operation(
        model,
        operation(
            named("extend".into(), &sort.name),
            base.clone(),
            port("", "$Con", []),
        ),
    );
    push_operation(
        model,
        operation(
            named("p".into(), &sort.name),
            base.clone(),
            port("", "$Sub", [extension.clone(), variable("G")]),
        ),
    );
    let weakened = sort.indices.iter().zip(&args).map(|(index, arg)| {
        action(
            &index.sort,
            variable("G"),
            extension.clone(),
            &index.arguments,
            arg.clone(),
            weakening.clone(),
        )
    });
    push_operation(
        model,
        operation(
            named("q".into(), &sort.name),
            base.clone(),
            SortRef::new("", sort.name.clone()).applied(
                core::iter::once(extension.clone())
                    .chain(weakened)
                    .collect::<Vec<_>>(),
            ),
        ),
    );
    let mut single = base.clone();
    single.push(
        SortRef::new("a", sort.name.clone()).applied(
            core::iter::once(variable("G"))
                .chain(args.iter().cloned())
                .collect::<Vec<_>>(),
        ),
    );
    push_operation(
        model,
        operation(
            named("single".into(), &sort.name),
            single,
            port("", "$Sub", [variable("G"), extension.clone()]),
        ),
    );
    let mut lift = base;
    lift.insert(1, port("D", "$Con", []));
    lift.push(port("s", "$Sub", [variable("D"), variable("G")]));
    let shifted = sort.indices.iter().zip(&args).map(|(index, arg)| {
        action(
            &index.sort,
            variable("G"),
            variable("D"),
            &index.arguments,
            arg.clone(),
            variable("s"),
        )
    });
    let extended_source = application(
        named("extend".into(), &sort.name),
        core::iter::once(variable("D")).chain(shifted),
    );
    push_operation(
        model,
        operation(
            named("lift".into(), &sort.name),
            lift,
            port("", "$Sub", [extended_source, extension]),
        ),
    );
    structural_equations(model, source, sort);
}

/// Generate the eight SSC law schemas specialized to the representable family.
///
/// # Specification
/// - ensures: two q laws and two term laws, then four index laws for each
///   source sort that indexes the family. For an unindexed representable sort
///   the index laws are vacuous and only the four term equations are appended.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L2 — source-derived λ-calculus equations and the dependent
///   `Ty/Tm` equations distinguish single substitution, lifting and
///   cancellation.
/// - witness: `tests::glf::generation`
#[spec(
    captures: before = model.rules.len(),
    ensures: model.rules.len() == before.saturating_add(source.sorts.iter()
        .filter(|family| sort.indices.iter().any(|index| index.sort == family.name))
        .count()
        .saturating_add(1)
        .saturating_mul(4)),
)]
fn structural_equations<G>(
    model: &mut Model,
    source: &TheoryDesc<G>,
    sort: &SortDesc,
)
{
    // Context and index parameters are implicit in equation notation, as in
    // the paper; operation declarations above carry their full telescopes.
    let p = application(named("p".into(), &sort.name), []);
    let q = application(named("q".into(), &sort.name), []);
    let single = |term| application(named("single".into(), &sort.name), [term]);
    let lift = |substitution| application(named("lift".into(), &sort.name), [substitution]);
    let sub = |family: &Name, term, substitution| {
        application(named("sub".into(), family), [term, substitution])
    };
    push_equation(
        model,
        sub(&sort.name, q.clone(), single(variable("b"))),
        variable("b"),
    );
    push_equation(
        model,
        sub(&sort.name, q.clone(), lift(variable("s"))),
        q.clone(),
    );
    push_equation(
        model,
        sub(
            &sort.name,
            sub(&sort.name, variable("b"), p.clone()),
            lift(variable("s")),
        ),
        sub(
            &sort.name,
            sub(&sort.name, variable("b"), variable("s")),
            p.clone(),
        ),
    );
    push_equation(
        model,
        sub(
            &sort.name,
            sub(&sort.name, variable("b"), p.clone()),
            single(variable("a")),
        ),
        variable("b"),
    );
    let indexed: BTreeSet<&Name> = sort.indices.iter().map(|index| &index.sort).collect();
    for family in source
        .sorts
        .iter()
        .filter(|family| indexed.contains(&family.name))
    {
        push_equation(
            model,
            sub(
                &family.name,
                sub(&family.name, variable("A"), p.clone()),
                lift(variable("s")),
            ),
            sub(
                &family.name,
                sub(&family.name, variable("A"), variable("s")),
                p.clone(),
            ),
        );
        push_equation(
            model,
            sub(
                &family.name,
                sub(&family.name, variable("A"), p.clone()),
                single(variable("b")),
            ),
            variable("A"),
        );
        push_equation(
            model,
            sub(
                &family.name,
                sub(&family.name, variable("A"), single(variable("b"))),
                variable("s"),
            ),
            sub(
                &family.name,
                sub(&family.name, variable("A"), lift(variable("s"))),
                single(sub(&sort.name, variable("b"), variable("s"))),
            ),
        );
        push_equation(
            model,
            sub(
                &family.name,
                sub(&family.name, variable("A"), lift(p.clone())),
                single(q.clone()),
            ),
            variable("A"),
        );
    }
}

/// Translate one operation telescope and its substitution naturality equation.
///
/// # Specification
/// - requires: the operation has one output, as [`validate`] admits.
/// - ensures: one model operation and one naturality equation are appended per
///   output; each π⁺ domain extends the context of its body, and naturality
///   applies a lifted substitution once per binder; ordinary arguments keep the
///   ambient context. The output stays in the ambient context.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L2 — λ-calculus naturality distinguishes missing or excess
///   lifting; indexed identity-return operations distinguish context placement.
/// - witness: `tests::glf::generation`
/// - witness: `tests::glf::indexed_signature_translates_without_name_cases`
#[spec(
    captures: before = (model.opers.len(), model.rules.len()),
    ensures: model.opers.len() == before.0.saturating_add(op.arity.outputs.len())
        && model.rules.len() == before.1.saturating_add(op.arity.outputs.len())
        && model.opers.last().is_some_and(|generated| generated.name == op.name
            && generated.arity.inputs.len() == op.arity.inputs.len().saturating_add(1)),
)]
fn translate_operation<G>(
    model: &mut Model,
    source: &TheoryDesc<G>,
    op: &OperDesc,
)
{
    let families: BTreeMap<&Name, &SortDesc> =
        source.sorts.iter().map(|sort| (&sort.name, sort)).collect();
    let mut inputs = vec![port("G", "$Con", [])];
    let mut natural_arguments = Vec::new();
    for input in &op.arity.inputs {
        let family = families.get(&input.sort);
        let mut context = variable("G");
        let mut substitution = variable("s");
        let mut arguments = input.arguments.to_vec();
        for binding in &input.bindings {
            let weakening = application(
                named("p".into(), &binding.sort),
                core::iter::once(context.clone()).chain(binding.arguments.iter().cloned()),
            );
            let extended = application(
                named("extend".into(), &binding.sort),
                core::iter::once(context.clone()).chain(binding.arguments.iter().cloned()),
            );
            if let Some(family) = family {
                for (argument, index) in arguments.iter_mut().zip(&family.indices) {
                    *argument = action(
                        &index.sort,
                        context.clone(),
                        extended.clone(),
                        &index.arguments,
                        argument.clone(),
                        weakening.clone(),
                    );
                }
            }
            context = extended;
            substitution = application(named("lift".into(), &binding.sort), [substitution]);
        }
        inputs.push(
            SortRef::new(input.name.clone(), input.sort.clone()).applied(
                core::iter::once(context)
                    .chain(arguments)
                    .collect::<Vec<_>>(),
            ),
        );
        natural_arguments.push(application(named("sub".into(), &input.sort), [
            FreeTerm::var(input.name.clone()),
            substitution,
        ]));
    }
    for output in &op.arity.outputs {
        let family = &output.sort;
        let output = SortRef::new(output.name.clone(), output.sort.clone()).applied(
            core::iter::once(variable("G"))
                .chain(output.arguments.iter().cloned())
                .collect::<Vec<_>>(),
        );
        push_operation(model, operation(op.name.clone(), inputs.clone(), output));
        let subject = application(
            op.name.clone(),
            op.arity
                .inputs
                .iter()
                .map(|input| FreeTerm::var(input.name.clone())),
        );
        let lhs = application(named("sub".into(), family), [subject, variable("s")]);
        push_equation(
            model,
            lhs,
            application(op.name.clone(), natural_arguments.clone()),
        );
    }
}
