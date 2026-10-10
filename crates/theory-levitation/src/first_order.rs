//! The finitary single-substitution translation of signature declarations.
//!
//! Kaposi and Xie, *Second-Order Generalised Algebraic Theories: Signatures
//! and First-Order Semantics*, doi:10.4230/LIPIcs.FSCD.2024.10, §§6–7.
//! Contexts and substitutions form a pointed graph, not a category. Each
//! representable family contributes extension, weakening, a newest variable,
//! single substitution and lifting. Operations become natural transformations.

use alloc::boxed::Box;
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
use crate::desc::SignDesc;
use crate::desc::SortDesc;
use crate::desc::SortIndex;
use crate::desc::SurfaceSpan;
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
            | Self::Malformed(_) => f.write_str("malformed signature"),
            | Self::NonSignatureMembers => f.write_str(
                "constructor, circuit or external parameter outside the SOGAT signature",
            ),
            | Self::ReservedName(ref name) => write!(f, "reserved generated name: {name}"),
            | Self::UnknownIndexSort(ref name) => write!(f, "undeclared index sort: {name}"),
            | Self::NonProductOperation(ref name) => write!(f, "non-product operation: {name}"),
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

/// Translate one closed finitary operation signature to its SSC presentation.
///
/// # Specification
/// - requires: index arguments are well-typed in their declared telescopes;
///   equation variables retain their source typing context.
/// - ensures: each sort is indexed by a context and has substitution action;
///   representable sorts supply extension, weakening, newest variable, single
///   substitution and lifting; each operation preserves substitution, lifting
///   under every restricted binder. No composition or identity is generated.
/// - fails: malformed descriptions, constructor/circuit members, generated-name
///   collisions, undeclared index sorts and non-product operations are refused.
/// - panics: none.
///
/// # Errors
/// Returns the corresponding variant of [`TranslationError`].
///
/// # Adequacy
/// - hypothesis: L2 — an independently derived LC presentation separates
///   missing structural operations, swapped substitutions and missing lifting.
///   L3 — indexed families and renamed signatures separate hard-coded LC cases;
///   malformed boundaries separate acceptance from refusal.
/// - witness: `tests::glf::generation_matches_derived_lc`
/// - witness: `tests::glf::indexed_signature_translates_without_name_cases`
/// - witness: `tests::glf::translation_refuses_non_signatures`
#[spec(ensures: |ref result| match *result {
    | Ok(ref model) => model.sorts.iter().all(|sort| sort.representability == Representability::Ordinary)
        && model.opers.iter().all(|op| op.arity.inputs.iter().all(|port| port.bindings.is_empty())),
    | Err(_) => true,
})]
#[inline]
pub fn first_order<G>(source: &SignDesc<G>) -> Result<SignDesc<G>, TranslationError>
{
    let diagnostics = check_desc(source);
    if !diagnostics.is_empty() {
        return Err(TranslationError::Malformed(diagnostics));
    }
    if !source.ctors.is_empty() || !source.circuits.is_empty() || !source.params.is_empty() {
        return Err(TranslationError::NonSignatureMembers);
    }
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
            | Declaration::Sort(sort) => translate_sort(&mut model, source, sort),
            | Declaration::Operation(op) => translate_operation(&mut model, source, op),
            | Declaration::Equation(rule) => model.rules.push(rule.clone()),
        }
        model
    });
    Ok(SignDesc::new(
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
/// - ensures: success exactly for declared index sorts, reserved-name-free
///   source names and single-output product operation telescopes.
/// - fails: the first offending name or operation, in declaration order.
/// - panics: none.
///
/// # Errors
/// Returns [`TranslationError::ReservedName`],
/// [`TranslationError::UnknownIndexSort`] or
/// [`TranslationError::NonProductOperation`].
///
/// # Adequacy
/// - hypothesis: L3 — name, unknown-sort and non-product boundaries distinguish
///   the three refusals from valid telescopes.
/// - witness: `tests::glf::translation_refuses_non_signatures`
#[spec(ensures: |ref result| result.is_err() || source.sorts.iter().all(|sort| !sort.name.as_ref().starts_with('$')))]
fn validate<G>(source: &SignDesc<G>) -> Result<(), TranslationError>
{
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
    for index in source.sorts.iter().flat_map(|sort| &sort.indices) {
        if !source.sorts.iter().any(|sort| sort.name == index.sort) {
            return Err(TranslationError::UnknownIndexSort(index.sort.clone()));
        }
    }
    for op in &source.opers {
        if op.arity.outputs.len() != 1
            || op.arity.dest.as_ref() != [0]
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
/// - ensures: a context-indexed family and its action are emitted; only a
///   representable family receives variable and substitution constructors.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L2 — the LC table distinguishes omitted infrastructure; L3 —
///   mixed representability distinguishes adding variables to every sort.
/// - witness: `tests::glf::generation_matches_derived_lc`
/// - witness: `tests::glf::indexed_signature_translates_without_name_cases`
#[spec(ensures: model.sorts.iter().any(|generated| generated.name == sort.name))]
fn translate_sort<G>(
    model: &mut Model,
    source: &SignDesc<G>,
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
/// - ensures: exactly those five structural operations, with the lifted source
///   context extending by the substituted family and q typed by weakened
///   indices.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L2 — LC and indexed-family tables observe all five operations
///   and their endpoint order; the q and weakening equations expose a swapped
///   leg.
/// - witness: `tests::glf::generation_matches_derived_lc`
/// - witness: `tests::glf::indexed_signature_translates_without_name_cases`
#[spec(ensures: model.opers.iter().any(|op| op.name == named("lift".into(), &sort.name)))]
fn representable<G>(
    model: &mut Model,
    source: &SignDesc<G>,
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
/// - ensures: four type/index laws for each index family, two q laws and two
///   term laws. For an unindexed representable sort the four index laws are
///   vacuous and only the four term equations remain.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L2 — source-derived LC equations and the dependent Ty/Tm
///   equations distinguish single substitution, lifting and cancellation.
/// - witness: `tests::glf::generation_matches_derived_lc`
/// - witness: `tests::glf::eight_dependent_single_substitution_laws`
#[spec(ensures: model.rules.len() >= 4)]
fn structural_equations<G>(
    model: &mut Model,
    source: &SignDesc<G>,
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
    for family in source
        .sorts
        .iter()
        .filter(|family| sort.indices.iter().any(|index| index.sort == family.name))
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
/// - ensures: each π⁺ domain extends the context of its body, and naturality
///   applies a lifted substitution once per binder; ordinary arguments keep the
///   ambient context. The output remains in the ambient context.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L2 — LC naturality distinguishes missing or excess lifting;
///   indexed identity-return operations distinguish context placement.
/// - witness: `tests::glf::generation_matches_derived_lc`
/// - witness: `tests::glf::indexed_signature_translates_without_name_cases`
#[spec(ensures: model.opers.iter().any(|generated| generated.name == op.name))]
fn translate_operation<G>(
    model: &mut Model,
    source: &SignDesc<G>,
    op: &OperDesc,
)
{
    let mut inputs = vec![port("G", "$Con", [])];
    let mut natural_arguments = Vec::new();
    for input in &op.arity.inputs {
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
            if let Some(family) = source.sorts.iter().find(|sort| sort.name == input.sort) {
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
        let family = output.sort.clone();
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
        let lhs = application(named("sub".into(), &family), [subject, variable("s")]);
        push_equation(
            model,
            lhs,
            application(op.name.clone(), natural_arguments.clone()),
        );
    }
}
