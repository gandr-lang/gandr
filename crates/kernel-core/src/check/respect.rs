//! A case over a presented type respects the type's rules, re-derived.
//!
//! Each rule `l ==> r` of the scrutinee's type obliges the case to compute
//! one result from both sides: `F(l) ≡ F(r)`, `l` and `r` built over one
//! fresh variable per pattern variable. At the root of a structural fixpoint,
//! `fix f. λy. case y { … }`, `F` is the fixpoint, so a recursive call at a
//! constructor field unfolds and one at a variable meets its twin stuck; any
//! other case is `F` itself, its scrutinee replaced by each side. The
//! conversion is the kernel's own, [`crate::replay::convert`]: the forced
//! rules, no constant unfolding, a presented type's terms read by their normal
//! forms. The checker decides the same obligation δ-free and the kernel
//! re-derives it with no trace, so no dialogue carries it and the wire is
//! unchanged.

use alloc::vec::Vec;

use anodized::spec;
use gandr_kernel_check_memo::NullMemo;
use gandr_kernel_term::CompType;
use gandr_kernel_term::CompTypeId;
use gandr_kernel_term::Computation;
use gandr_kernel_term::ComputationId;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::FieldCount;
use gandr_kernel_term::PresentedRule;
use gandr_kernel_term::RuleIndex;
use gandr_kernel_term::RuleNode;
use gandr_kernel_term::TermArena;
use gandr_kernel_term::Value;
use gandr_kernel_term::ValueType;
use gandr_kernel_term::ValueTypeId;
use gandr_kernel_term::build_side;
use quenchant_shape::shape::Maybe;

use crate::encoding::ContentTable;
use crate::env::AdmittedDeclaration;
use crate::error::KernelError;
use crate::presented::Presentations;
use crate::replay::KernelVerdict;
use crate::replay::ReplayBudget;
use crate::replay::ReplaySides;
use crate::rewrite::BinderDepth;
use crate::rewrite::shift_computation;
use crate::rewrite::shift_value_type;

quenchant_shape::reason_enum! {
    /// Why a case carries no obligation against its type's rules.
    pub(super) mod obligation {
        /// The reason no rule binds the case.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub(in crate::check) enum Absent {
            /// The scrutinee's type is free: it has no rules.
            Free,
            /// The scrutinee's type names no admitted data declaration, which
            /// the case's own formation has refused already.
            NotData,
        }
    }
}

quenchant_shape::reason_enum! {
    /// Why no case is marked as a structural fixpoint's root.
    pub(super) mod root {
        /// The reason no case is marked.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub(in crate::check) enum Absent {
            /// No structural fixpoint has been checked since the last case
            /// was met.
            Unmarked,
            /// The fixpoint's type has no domain, or its body is not a lambda
            /// over a case on the lambda's argument.
            NotOverCase,
        }
    }
}

/// How a case's computation from its scrutinee is read.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum Reading
{
    /// The case is the root of a structural fixpoint: the fixpoint itself,
    /// out of `domain`, both standing where the fixpoint stands.
    Fold
    {
        /// The fixpoint.
        fixpoint: ComputationId,
        /// The data application it recurses over.
        domain: ValueTypeId,
    },
    /// Any other case: the case itself, its scrutinee of `datatype`, both
    /// standing where the case stands.
    Case
    {
        /// The scrutinee's data application.
        datatype: ValueTypeId,
    },
}

/// The case a structural fixpoint opens with, read as the fixpoint against
/// its type's rules.
///
/// # Specification
/// - requires: `body` is the body of the fixpoint `fixpoint`, whose
///   structural-descent claim replayed at `expected`.
/// - ensures: the case under the body's lambda beside [`Reading::Fold`] naming
///   the fixpoint and the domain of `expected`, when that case's scrutinee is
///   the lambda's argument; [`root::Absent::NotOverCase`] otherwise.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — as [`respected`]: the fold reading admits a fixpoint over
///   the circle that a bare reading of its case would refuse.
/// - witness: `native_formers::native_formers::a_case_respects_its_type_s_rules_or_is_refused_by_the_rule`
#[spec(ensures: |ret| match ret { Maybe::Present((_, reading)) => matches!(reading, Reading::Fold { fixpoint: marked, .. } if marked == fixpoint), Maybe::Absent(reason) => reason == root::Absent::NotOverCase })]
pub(super) fn fold_root(
    arena: &TermArena,
    fixpoint: ComputationId,
    expected: CompTypeId,
    body: ComputationId,
) -> Maybe<(ComputationId, Reading), root::Absent>
{
    let not_over_case = Maybe::Absent(root::Absent::NotOverCase);
    let Some(&(CompType::Arrow { domain, .. } | CompType::Pi { domain, .. })) =
        arena.comp_type(expected)
    else {
        return not_over_case;
    };
    let Some(&Computation::Lambda(case)) = arena.computation(body)
    else {
        return not_over_case;
    };
    let Some(&Computation::DataCase { scrutinee, .. }) = arena.computation(case)
    else {
        return not_over_case;
    };
    if arena.value(scrutinee) != Some(&Value::Variable(DeBruijnIndex::from(0_u32))) {
        return not_over_case;
    }
    Maybe::Present((case, Reading::Fold { fixpoint, domain }))
}

/// The obligation a case over `datatype` owes its type's rules, read as
/// `reading` says.
///
/// # Specification
/// - requires: `datatype` is the case's scrutinee type, its formation checked.
/// - ensures: `reading` when the declaration `datatype` names carries rules;
///   [`obligation::Absent::Free`] when it carries none;
///   [`obligation::Absent::NotData`] when `datatype` names no admitted data
///   declaration.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the same case over a free circle is admitted with no
///   obligation, and over the presented circle is decided against its rules.
/// - witness: `native_formers::native_formers::a_case_respects_its_type_s_rules_or_is_refused_by_the_rule`
#[spec(ensures: |ret| match ret { Maybe::Present(owed) => owed == reading, Maybe::Absent(_) => true })]
pub(super) fn obliged(
    arena: &TermArena,
    entries: &[AdmittedDeclaration],
    datatype: ValueTypeId,
    reading: Reading,
) -> Maybe<Reading, obligation::Absent>
{
    let Some(&ValueType::Data { declaration, .. }) = arena.value_type(datatype)
    else {
        return Maybe::Absent(obligation::Absent::NotData);
    };
    match entries.get(usize::from(declaration)) {
        | Some(entry) if !entry.declaration().presentation().rules().is_empty() => {
            Maybe::Present(reading)
        },
        | Some(_) => Maybe::Absent(obligation::Absent::Free),
        | None => Maybe::Absent(obligation::Absent::NotData),
    }
}

/// Decide that the case `case` respects every rule of its scrutinee's type,
/// read as `reading` says.
///
/// # Specification
/// - requires: `reading`'s data application names an admitted data declaration,
///   and the case's branches have checked.
/// - ensures: `Ok(())` exactly when, for every rule `l ==> r` in written order,
///   `F(l)` converts with `F(r)` under [`crate::replay::convert`] within
///   [`ReplayBudget::DEFAULT`], `l` and `r` built over one fresh variable per
///   pattern variable; `arena` holds what it held on entry either way.
/// - fails: [`KernelError::RuleNotRespected`] naming the first rule whose sides
///   do not convert; [`KernelError::NotADataType`] or
///   [`KernelError::ArenaFault`] for a reading whose type or case the arena and
///   the entries do not hold, or a rule side that does not build.
/// - panics: none.
///
/// # Errors
/// As `- fails:`.
///
/// # Termination
/// - reason: the `for` loop over the declaration's finite rules, not recursion;
///   each conversion runs under its budget.
/// - measure: the rules left.
///
/// # Adequacy
/// - hypothesis: L3 — over the circle, a fixpoint recursing through both
///   inverse letters is admitted, and a case reading the letter as written is
///   refused at the first rule, as the checker refuses and admits them.
/// - witness: `native_formers::native_formers::a_case_respects_its_type_s_rules_or_is_refused_by_the_rule`
#[spec(
    captures: before = arena.watermark(),
    ensures: |ret| arena.watermark() == before
        && (ret.is_ok() || matches!(ret, Err(KernelError::RuleNotRespected(_) | KernelError::NotADataType { .. } | KernelError::ArenaFault))),
)]
pub(super) fn respected(
    arena: &mut TermArena,
    entries: &[AdmittedDeclaration],
    presentations: &Presentations,
    case: ComputationId,
    reading: Reading,
) -> Result<(), KernelError>
{
    let (head, datatype) = match reading {
        | Reading::Fold { fixpoint, domain } => (fixpoint, domain),
        | Reading::Case { datatype } => (case, datatype),
    };
    let Some(&ValueType::Data { declaration, .. }) = arena.value_type(datatype)
    else {
        return Err(KernelError::ArenaFault);
    };
    let arities: Vec<FieldCount> = super::former::signature(entries, declaration)?
        .constructors
        .iter()
        .map(|fields| FieldCount::from(fields.len()))
        .collect();
    let presentation = entries
        .get(usize::from(declaration))
        .ok_or(KernelError::NotADataType { index: declaration })?
        .declaration()
        .presentation();
    for (index, rule) in presentation.rules().iter().enumerate() {
        let watermark = arena.watermark();
        let respects = obligation(arena, (head, datatype), reading, rule, &arities).map(|sides| {
            crate::replay::convert(arena, presentations, sides, ReplayBudget::DEFAULT)
                == KernelVerdict::Convertible
        });
        arena.truncate_to(watermark);
        if !respects? {
            return Err(KernelError::RuleNotRespected(RuleIndex::from(index)));
        }
    }
    Ok(())
}

/// The two sides of one rule's obligation, minted in `arena`.
///
/// # Specification
/// - requires: `head` is the fixpoint or the case `reading` names, and
///   `datatype` its data application.
/// - ensures: `F(l)` and `F(r)` beneath one fresh binder per pattern variable,
///   `head` and `datatype` shifted past them: the shifted fixpoint applied to
///   each side, or the shifted case with each side in its scrutinee's place.
/// - fails: [`KernelError::ArenaFault`] for a rule side that does not build or
///   a case node the arena does not hold.
/// - panics: none.
///
/// # Errors
/// As `- fails:`.
///
/// # Adequacy
/// - hypothesis: L3 — as [`respected`].
/// - witness: `native_formers::native_formers::a_case_respects_its_type_s_rules_or_is_refused_by_the_rule`
#[spec(ensures: |ret| ret.is_ok() || matches!(ret, Err(KernelError::ArenaFault)))]
fn obligation(
    arena: &mut TermArena,
    (head, datatype): (ComputationId, ValueTypeId),
    reading: Reading,
    rule: &PresentedRule,
    arities: &[FieldCount],
) -> Result<ReplaySides, KernelError>
{
    let bound = u32::from(rule.variables());
    let amount = BinderDepth::from(bound);
    let mut table = ContentTable::default();
    let datatype = shift_value_type(
        arena,
        &mut table,
        &mut NullMemo,
        datatype,
        BinderDepth::NONE,
        amount,
    );
    let head = shift_computation(
        arena,
        &mut table,
        &mut NullMemo,
        head,
        BinderDepth::NONE,
        amount,
    );
    let mut side = |nodes: &[RuleNode]| {
        build_side(nodes, arities, |node, fields| match node {
            | RuleNode::Variable(variable) => {
                // Pattern variable `v` of `bound` is the binder `bound - 1 - v`
                // out: the first variable outermost.
                let index = bound
                    .checked_sub(u32::from(variable))
                    .and_then(|past| past.checked_sub(1_u32))
                    .unwrap_or_default();
                arena.value_variable(DeBruijnIndex::from(index))
            },
            | RuleNode::Constructor(tag) => arena.value_constructor(datatype, tag, fields),
        })
        .map_err(|_fault| KernelError::ArenaFault)
    };
    let left = side(rule.left())?;
    let right = side(rule.right())?;
    Ok(match reading {
        | Reading::Fold { .. } => ReplaySides::Computations(
            arena.computation_application(head, left),
            arena.computation_application(head, right),
        ),
        | Reading::Case { .. } => {
            let Some(&Computation::DataCase {
                motive,
                ref branches,
                ..
            }) = arena.computation(head)
            else {
                return Err(KernelError::ArenaFault);
            };
            let branches = branches.clone();
            ReplaySides::Computations(
                arena.computation_data_case(left, motive, branches.clone()),
                arena.computation_data_case(right, motive, branches),
            )
        },
    })
}
