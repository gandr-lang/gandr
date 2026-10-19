//! The meaning a rewrite keeps: two parses of one source, each lowered into
//! one arena, compared declaration by declaration.
//!
//! A layout keeps every token, so the content digest is its check. A rewrite
//! changes tokens on purpose — `#{A, B}` for `A * B` — and the digest with
//! them, so its check is the lowering: the rewritten text lowers to what the
//! source lowers to. The two lowerings share an arena and admit their
//! declarations at the same positions, so a reference to a declaration is one
//! index in both, and the core's syntactic equality, which never reads an
//! allocation's position, compares what each declaration lowered to.

use alloc::format;
use alloc::string::String;
use alloc::vec::Vec;
use core::mem::discriminant;

use anodized::spec;
use gandr_core_term::CertificateEquality;
use gandr_core_term::CoreArena;
use gandr_core_term::ValueTypeId;
use gandr_core_term::equal_certificate_syntax;
use gandr_core_term::equal_type_syntax;
use gandr_surface_grammar::Pbg;
use gandr_surface_lowering::DeclarationOutcome;
use gandr_surface_lowering::LoweredDeclaration;
use gandr_surface_lowering::LoweredModule;
use gandr_surface_lowering::LoweringBudget;
use gandr_surface_lowering::Unit;
use gandr_surface_lowering::lower_unit;
use gandr_surface_lowering::namespace::Recognition;
use gandr_surface_syntax::ByteOffset;
use gandr_surface_syntax::ByteSpan;
use gandr_surface_syntax::NodeKey;
use gandr_surface_syntax::SyntaxTree;
use quenchant_shape::shape::Maybe;

use crate::Withdrawal;
use crate::Withdrawn;

/// Whether two lowerings mean one thing.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Agreement
{
    /// Every declaration lowered to the same core.
    Same,
    /// These declarations of the first lowered otherwise in the second, in
    /// order.
    Declarations(Vec<Differing>),
    /// The two do not declare the same names in the same order.
    Unpaired,
}

/// `tree`, the text `unit` lays out, lowered into `arena`, or nothing when
/// the lowering refuses it whole.
///
/// # Specification
/// trivial.
pub fn lowered<'source>(
    grammar: &Pbg,
    tree: &SyntaxTree<'source>,
    unit: &Unit,
    arena: &mut CoreArena,
) -> Option<LoweredModule<'source>>
{
    lower_unit(
        grammar,
        tree,
        unit,
        arena,
        LoweringBudget::DEFAULT,
        Recognition::default(),
    )
    .ok()
}

/// The declarations `module` refused at or after `base`, where no rewrite's
/// meaning can be checked: the keys of the forms holding each — its
/// signature, definition and duplicate — and its withdrawal, the refusal its
/// reason.
///
/// # Specification
/// trivial.
pub fn refused(
    module: &LoweredModule<'_>,
    base: ByteOffset,
) -> Vec<Differing>
{
    module
        .declarations()
        .iter()
        .filter(|declaration| declaration.span().start() >= base)
        .filter_map(|declaration| match declaration.outcome() {
            DeclarationOutcome::Refused(refusal) => Some(Differing {
                keys: halves(declaration).collect(),
                withdrawal: Withdrawal {
                    declaration: format!("{}", declaration.name()),
                    span: own(declaration.span(), base),
                    reason: Withdrawn::Unchecked(format!("{refusal}")),
                },
            }),
            DeclarationOutcome::Completed { .. }
            | DeclarationOutcome::Uncompleted { .. }
            | DeclarationOutcome::Bodied { .. }
            | DeclarationOutcome::Data(_)
            | DeclarationOutcome::Abstract(_)
            | DeclarationOutcome::World => None,
        })
        .collect()
}

/// The withdrawal, for `reason`, of the first declaration `module` lowered at
/// or after `base` whose forms' keys `held` accepts.
///
/// # Specification
/// trivial.
pub fn holding<Held>(
    module: &LoweredModule<'_>,
    base: ByteOffset,
    reason: &Withdrawn,
    held: Held,
) -> Option<Withdrawal>
where
    Held: Fn(&[NodeKey]) -> bool,
{
    module
        .declarations()
        .iter()
        .filter(|declaration| declaration.span().start() >= base)
        .find(|declaration| held(&halves(declaration).collect::<Vec<_>>()))
        .map(|declaration| Withdrawal {
            declaration: format!("{}", declaration.name()),
            span: own(declaration.span(), base),
            reason: reason.clone(),
        })
}

/// The withdrawal of each declaration `module` lowered at or after `base`
/// whose forms' keys `held` accepts and whose name `reader` maps to the
/// declaration that reads it: the declarations a reader's meaning depends on
/// through their spelling.
///
/// # Specification
/// trivial.
pub fn read<Held, Reader>(
    module: &LoweredModule<'_>,
    base: ByteOffset,
    held: Held,
    reader: Reader,
) -> Vec<Differing>
where
    Held: Fn(&[NodeKey]) -> bool,
    Reader: Fn(&str) -> Option<String>,
{
    module
        .declarations()
        .iter()
        .filter(|declaration| declaration.span().start() >= base)
        .filter_map(|declaration| {
            let keys: Vec<NodeKey> = halves(declaration).collect();
            if !held(&keys) {
                return None;
            }
            let name = format!("{}", declaration.name());
            let by = reader(&name)?;
            Some(Differing {
                keys,
                withdrawal: Withdrawal {
                    declaration: name,
                    span: own(declaration.span(), base),
                    reason: Withdrawn::Read(by),
                },
            })
        })
        .collect()
}

/// The keys of the forms holding `declaration`: its signature, its
/// definition and a duplicate, those it has.
///
/// # Specification
/// trivial.
fn halves(declaration: &LoweredDeclaration<'_>) -> impl Iterator<Item = NodeKey>
{
    [
        declaration.signature(),
        declaration.definition(),
        declaration.duplicate(),
    ]
    .into_iter()
    .filter_map(|half| match half {
        Maybe::Present(key) => Some(key.form()),
        Maybe::Absent(_) => None,
    })
}

/// Whether `before` and `after`, lowered into `arena`, declare the same names
/// in the same order, each to the same core, and which of `before`'s
/// declarations lowered otherwise.
///
/// # Specification
/// - requires: both modules were lowered into `arena`.
/// - ensures: [`Agreement::Unpaired`] unless the two hold as many declarations;
///   else [`Agreement::Same`] exactly when each pair, in order, has one name,
///   role and container and outcomes of one kind whose types, bodies and data
///   signatures are syntactically equal — evidence erased, no reduction — whose
///   seals agree but for their types' positions, and whose refusals are of one
///   kind; else [`Agreement::Declarations`] with each of `before`'s
///   declarations whose pair is not so, in order: the keys of the forms holding
///   it, its name, its span in the source starting at `base`, and why — the
///   refusal the rewritten declaration met, or that it lowered otherwise.
/// - provides: the check a rewrite's output passes.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — every rewrite of the table, at each direction, is checked
///   over the corpus by the rewrites' sweep, and a rewrite whose output swaps
///   two operands is withdrawn from its declaration.
/// - witness: `rewrite::tests::a_rewrite_that_changes_what_a_source_means_is_withdrawn`
/// - witness: `tests::rewrite::sweeps::every_source_formats_into_either_form_and_keeps_its_meaning`
#[spec(ensures: |ret| !matches!(ret, Agreement::Declarations(ref keys) if keys.is_empty()))]
pub fn agree(
    arena: &CoreArena,
    (before, after): (&LoweredModule<'_>, &LoweredModule<'_>),
    base: ByteOffset,
) -> Agreement
{
    let types = |left: ValueTypeId, right: ValueTypeId| {
        equal_type_syntax(arena, left, right) == CertificateEquality::Equal
    };
    let all_types = |left: &[ValueTypeId], right: &[ValueTypeId]| {
        left.len() == right.len()
            && left
                .iter()
                .zip(right)
                .all(|(&left, &right)| types(left, right))
    };
    let values =
        |left, right| equal_certificate_syntax(arena, left, right) == CertificateEquality::Equal;
    let declared = before.declarations();
    let written = after.declarations();
    if declared.len() != written.len() {
        return Agreement::Unpaired;
    }
    let differing: Vec<Differing> = declared
        .iter()
        .zip(written)
        .filter(|&(left, right)| {
            left.name() != right.name()
                || left.role() != right.role()
                || left.container() != right.container()
                || !match (left.outcome(), right.outcome()) {
                    (
                        DeclarationOutcome::Completed {
                            declared_type: left_type,
                            body: left_body,
                        },
                        DeclarationOutcome::Completed {
                            declared_type: right_type,
                            body: right_body,
                        },
                    ) => types(left_type, right_type) && values(left_body, right_body),
                    (
                        DeclarationOutcome::Uncompleted {
                            declared_type: left_type,
                        },
                        DeclarationOutcome::Uncompleted {
                            declared_type: right_type,
                        },
                    ) => types(left_type, right_type),
                    (
                        DeclarationOutcome::Bodied { body: left_body },
                        DeclarationOutcome::Bodied { body: right_body },
                    ) => values(left_body, right_body),
                    (
                        DeclarationOutcome::Data(left_index),
                        DeclarationOutcome::Data(right_index),
                    ) => match (before.data(left_index), after.data(right_index)) {
                        (
                            quenchant_shape::shape::Maybe::Present(left_data),
                            quenchant_shape::shape::Maybe::Present(right_data),
                        ) => {
                            let named =
                                before.constructors(left_index) == after.constructors(right_index);
                            all_types(left_data.parameters(), right_data.parameters())
                                && types(left_data.kind(), right_data.kind())
                                && left_data.constructors().len() == right_data.constructors().len()
                                && left_data
                                    .constructors()
                                    .iter()
                                    .zip(right_data.constructors())
                                    .all(|(left, right)| all_types(left, right))
                                && left_data.presentation() == right_data.presentation()
                                && named
                        },
                        _ => false,
                    },
                    (
                        DeclarationOutcome::Abstract(left_seal),
                        DeclarationOutcome::Abstract(right_seal),
                    ) => {
                        types(left_seal.kind, right_seal.kind)
                            && types(left_seal.representation, right_seal.representation)
                            && left_seal.extent == right_seal.extent
                            && left_seal.sealing == right_seal.sealing
                            && left_seal.component == right_seal.component
                            && left_seal.mark == right_seal.mark
                    },
                    (DeclarationOutcome::World, DeclarationOutcome::World) => true,
                    (DeclarationOutcome::Refused(left), DeclarationOutcome::Refused(right)) => {
                        discriminant(&left) == discriminant(&right)
                    },
                    _ => false,
                }
        })
        .map(|(left, right)| Differing {
            keys: halves(left).collect(),
            withdrawal: Withdrawal {
                declaration: format!("{}", left.name()),
                span: own(left.span(), base),
                reason: reason(right.outcome()),
            },
        })
        .collect();
    if differing.is_empty() {
        Agreement::Same
    }
    else {
        Agreement::Declarations(differing)
    }
}

/// `span`, a span of a unit's text, in the text of the source starting at
/// `base`.
///
/// # Specification
/// trivial.
fn own(
    span: ByteSpan,
    base: ByteOffset,
) -> ByteSpan
{
    let shift = |offset: ByteOffset| {
        ByteOffset::from(usize::from(offset).saturating_sub(usize::from(base)))
    };
    ByteSpan::new(shift(span.start()), shift(span.end())).unwrap_or(span)
}

/// Why a declaration whose rewritten text lowered to `outcome` keeps its
/// spelling.
///
/// # Specification
/// trivial.
fn reason(outcome: DeclarationOutcome<'_>) -> Withdrawn
{
    match outcome {
        DeclarationOutcome::Refused(refusal) => Withdrawn::Refused(format!("{refusal}")),
        DeclarationOutcome::Completed { .. }
        | DeclarationOutcome::Uncompleted { .. }
        | DeclarationOutcome::Bodied { .. }
        | DeclarationOutcome::Data(_)
        | DeclarationOutcome::Abstract(_)
        | DeclarationOutcome::World => Withdrawn::Lowered,
    }
}

/// A declaration that lowered otherwise once rewritten.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Differing
{
    /// The keys of the forms holding it in the source.
    pub keys: Vec<NodeKey>,
    /// What the caller reports.
    pub withdrawal: Withdrawal,
}
