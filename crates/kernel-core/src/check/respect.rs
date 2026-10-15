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
//! forms, and a cong chain whose functions compose to the identity read as its
//! path, the chain's functions read through the admitted definitions by the
//! kernel's own evaluator. The checker decides the same obligation δ-free and
//! the kernel re-derives it with no trace, so no dialogue carries it.
//!
//! A dependent fold into a path type meets a rule's two sides as cong chains:
//! `sect(Loop(Unloop(x)))` binds `sect(x)` into `cong(unlooped, _)` and that
//! into `cong(looped, _)`, and the chain's composite `looped ∘ unlooped`
//! reads as the identity once the circle's rules apply, so the obligation
//! against `sect(x)` converts by the commuting conversions of `F` and the
//! chain's reading, with no law named.
//!
//! A fold into a model meets a rule only up to the model's law: the winding
//! number computes `turn(unturn(wind(x)))` against `wind(x)`. Such a fold's
//! definition names one law per rule ([`gandr_kernel_term::KIND_DEF_LAWFUL`]),
//! and where conversion leaves a rule's sides apart the kernel instantiates
//! the rule's law at the fold of its variables and relates the instance's
//! endpoints to the two sides. The instance is fixed by the rule, so nothing
//! is searched, and the definition rests on the laws it names: where the model
//! owes them, its audit names them as axioms.

use alloc::vec::Vec;

use anodized::spec;
use gandr_kernel_check_memo::NullMemo;
use gandr_kernel_term::CompType;
use gandr_kernel_term::CompTypeId;
use gandr_kernel_term::Computation;
use gandr_kernel_term::ComputationId;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::FieldCount;
use gandr_kernel_term::PresentedRule;
use gandr_kernel_term::RuleIndex;
use gandr_kernel_term::RuleNode;
use gandr_kernel_term::RuleSlot;
use gandr_kernel_term::RuleVariable;
use gandr_kernel_term::TermArena;
use gandr_kernel_term::Value;
use gandr_kernel_term::ValueId;
use gandr_kernel_term::ValueType;
use gandr_kernel_term::ValueTypeId;
use gandr_kernel_term::VariableCount;
use gandr_kernel_term::build_side;
use quenchant_shape::shape::Maybe;

use crate::encoding::ContentTable;
use crate::env::AdmittedDeclaration;
use crate::error::KernelError;
use crate::presented::Presentations;
use crate::replay::KernelVerdict;
use crate::replay::ReplayBudget;
use crate::replay::ReplaySides;
use crate::replay::Unfoldings;
use crate::rewrite::BinderDepth;
use crate::rewrite::shift_computation;
use crate::rewrite::shift_value;
use crate::rewrite::shift_value_type;
use crate::rewrite::substitute_comp_type;
use crate::rewrite::substitute_value_type;

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
        /// The fixpoint's type, whose codomain a law's endpoints stand at.
        arrow: CompTypeId,
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
/// - requires: `body` is the body of the fixpoint `fixpoint`, whose structural
///   evidence stages its first parameter at `expected`.
/// - ensures: the case under the body's lambda beside [`Reading::Fold`] naming
///   the fixpoint and the domain of `expected`, read as its words where it is a
///   path at a looped point ([`Presentations::identified`]), when that case's
///   scrutinee is the lambda's argument; [`root::Absent::NotOverCase`]
///   otherwise.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — as [`respected`]: the fold reading admits a fixpoint over
///   the circle that a bare reading of its case would refuse, and a fold over a
///   path at a looped point respects its words' cancellations.
/// - witness: `native_formers::native_formers::a_case_respects_its_type_s_rules_or_is_refused_by_the_rule`
/// - witness: `presented::tests::a_path_at_a_looped_point_reads_as_its_words`
#[spec(ensures: |ret| match ret { Maybe::Present((_, reading)) => matches!(reading, Reading::Fold { fixpoint: marked, .. } if marked == fixpoint), Maybe::Absent(reason) => reason == root::Absent::NotOverCase })]
pub(super) fn fold_root(
    arena: &mut TermArena,
    presentations: &Presentations,
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
    Maybe::Present((case, Reading::Fold {
        fixpoint,
        domain: presentations.identified(arena, domain),
        arrow: expected,
    }))
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
        Some(entry) if !entry.declaration().presentation().rules().is_empty() => {
            Maybe::Present(reading)
        },
        Some(_) => Maybe::Absent(obligation::Absent::Free),
        None => Maybe::Absent(obligation::Absent::NotData),
    }
}

/// Decide that the case `case` respects every rule of its scrutinee's type,
/// read as `reading` says, a fold resting on `laws` where it computes a rule's
/// sides apart.
///
/// # Specification
/// - requires: `reading`'s data application names an admitted data declaration,
///   and the case's branches have checked.
/// - ensures: `Ok(())` exactly when, for every rule `l ==> r` in written order,
///   `F(l)` converts with `F(r)` under [`crate::replay::convert`] within
///   [`ReplayBudget::DEFAULT`], `l` and `r` built over one fresh variable per
///   pattern variable, or the reading is a fold and the law at the rule's
///   position relates the two sides as [`lawful`] decides; `arena` holds what
///   it held on entry either way.
/// - fails: [`KernelError::RuleNotRespected`] naming the first rule respected
///   neither way; [`KernelError::NotADataType`] or [`KernelError::ArenaFault`]
///   for a reading whose type or case the arena and the entries do not hold, or
///   a rule side that does not build.
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
///   refused at the first rule, as the checker refuses and admits them; a fold
///   into the integers is admitted on its two laws and refused at the rule
///   whose law states the other cancellation.
/// - witness: `native_formers::native_formers::a_case_respects_its_type_s_rules_or_is_refused_by_the_rule`
/// - witness: `native_formers::native_formers::a_fold_rests_on_the_law_of_each_rule_it_computes_apart`
#[spec(
    captures: before = arena.watermark(),
    ensures: |ret| arena.watermark() == before
        && (ret.is_ok() || matches!(ret, Err(KernelError::RuleNotRespected(_) | KernelError::NotADataType { .. } | KernelError::ArenaFault))),
)]
pub(super) fn respected(
    arena: &mut TermArena,
    (entries, unfoldings): (&[AdmittedDeclaration], &Unfoldings),
    case: ComputationId,
    reading: Reading,
    laws: &[ConstantIndex],
) -> Result<(), KernelError>
{
    let (head, datatype) = match reading {
        Reading::Fold {
            fixpoint, domain, ..
        } => (fixpoint, domain),
        Reading::Case { datatype } => (case, datatype),
    };
    let Some(&ValueType::Data { declaration, .. }) = arena.value_type(datatype)
    else {
        return Err(KernelError::ArenaFault);
    };
    let signature = super::former::signature(entries, declaration)?;
    let arities: Vec<FieldCount> = signature
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
        let refusal = KernelError::RuleNotRespected(RuleIndex::from(index));
        let watermark = arena.watermark();
        let decided =
            obligation(arena, (head, datatype), reading, rule, &arities).and_then(|obliged| {
                let sides = ReplaySides::Computations(obliged.left, obliged.right);
                if crate::replay::convert(arena, unfoldings, sides, ReplayBudget::DEFAULT)
                    == KernelVerdict::Convertible
                {
                    return Ok(());
                }
                match (reading, laws.get(index)) {
                    (Reading::Fold { arrow, .. }, Some(&law)) => {
                        let related = lawful(
                            arena,
                            (entries, unfoldings),
                            (obliged, arrow),
                            (rule, signature, declaration),
                            law,
                        )?;
                        match related {
                            Related::Related => Ok(()),
                            Related::Apart => Err(refusal),
                        }
                    },
                    (Reading::Fold { .. } | Reading::Case { .. }, _) => Err(refusal),
                }
            });
        arena.truncate_to(watermark);
        decided?;
    }
    Ok(())
}

/// One rule's obligation, minted in `arena` beneath one fresh binder per
/// pattern variable.
#[derive(Clone, Copy, Debug)]
struct Obliged
{
    /// `F(l)`.
    left: ComputationId,
    /// `F(r)`.
    right: ComputationId,
    /// The fixpoint or the case, shifted past the pattern's binders.
    head: ComputationId,
    /// The scrutinee's data application, shifted past the pattern's binders.
    datatype: ValueTypeId,
}

/// Whether a law relates a fold's two sides of its rule.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Related
{
    /// The law's instance relates them.
    Related,
    /// The law does not state the rule at this fold.
    Apart,
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
) -> Result<Obliged, KernelError>
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
            RuleNode::Variable(variable) => {
                arena.value_variable(pattern_binder(rule.variables(), variable))
            },
            RuleNode::Constructor(tag) => arena.value_constructor(datatype, tag, fields),
        })
        .map_err(|_fault| KernelError::ArenaFault)
    };
    let left = side(rule.left())?;
    let right = side(rule.right())?;
    let (left, right) = match reading {
        Reading::Fold { .. } => (
            arena.computation_application(head, left),
            arena.computation_application(head, right),
        ),
        Reading::Case { .. } => {
            let Some(&Computation::DataCase {
                motive,
                ref branches,
                ..
            }) = arena.computation(head)
            else {
                return Err(KernelError::ArenaFault);
            };
            let branches = branches.clone();
            (
                arena.computation_data_case(left, motive, branches.clone()),
                arena.computation_data_case(right, motive, branches),
            )
        },
    };
    Ok(Obliged {
        left,
        right,
        head,
        datatype,
    })
}

/// The binder pattern variable `variable` of `bound` stands at: the first
/// variable outermost.
///
/// # Specification
/// - requires: `variable < bound`.
/// - ensures: the index `bound - 1 - variable`; `0` when `variable` is not
///   below `bound`.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — as [`respected`]: the circle's one variable is the
///   innermost binder.
/// - witness: `native_formers::native_formers::a_case_respects_its_type_s_rules_or_is_refused_by_the_rule`
#[spec(ensures: |ret| u32::from(ret) == u32::from(bound).checked_sub(u32::from(variable)).and_then(|past| past.checked_sub(1_u32)).unwrap_or_default())]
fn pattern_binder(
    bound: VariableCount,
    variable: RuleVariable,
) -> DeBruijnIndex
{
    DeBruijnIndex::from(
        u32::from(bound)
            .checked_sub(u32::from(variable))
            .and_then(|past| past.checked_sub(1_u32))
            .unwrap_or_default(),
    )
}

/// Decide that `law` relates the two sides a fold computes for `rule`.
///
/// The law is instantiated at the rule's variables as a model reads them: a
/// variable standing at the folded type as the fold of it, any other as
/// itself. Each parameter's classifier must be the fold's codomain or the
/// field's classifier, the instance's carrier the fold's codomain, and its two
/// endpoints must convert with `F(l)` and `F(r)`. An endpoint is a value, a
/// call among it written as the value its run returns, and a fold's arms reach
/// the kernel with their runs in place or elaborated into binds; so an
/// endpoint is read as its own run with the runs in its arguments in place,
/// and else [`sequenced`], those runs bound ahead as elaboration binds them —
/// the two readings the checker tries. Nothing is searched: the instance is
/// the rule's own, so the kernel re-derives the claim from the rule, the fold
/// and the law's declared type alone.
///
/// # Specification
/// - requires: `obliged` is `rule`'s obligation at the fold whose type is
///   `arrow`, over the data declaration `declaration` whose signature is
///   `signature`.
/// - ensures: [`Related::Related`] exactly when `arrow` is a non-dependent
///   arrow into a returner, `law` names an admitted declaration whose type is a
///   path type behind one parameter per pattern variable, each parameter's
///   classifier converts with its instance's, the path's carrier with the
///   codomain, and each endpoint, read in place or sequenced, with its side
///   under [`crate::replay::convert`]; [`Related::Apart`] otherwise.
/// - fails: [`KernelError::ArenaFault`] for a rule side that does not read
///   against the constructor table.
/// - panics: none.
///
/// # Errors
/// As `- fails:`.
///
/// # Termination
/// - reason: `for` loops over the rule's finite variables and the data's finite
///   parameters, not recursion; each conversion runs under its budget.
/// - measure: the variables left, then the parameters left.
///
/// # Adequacy
/// - hypothesis: L3 — the winding number is admitted on the circle's two
///   cancellation laws and refused when the laws are crossed.
/// - witness: `native_formers::native_formers::a_fold_rests_on_the_law_of_each_rule_it_computes_apart`
#[spec(ensures: |ret| ret.is_ok() || matches!(ret, Err(KernelError::ArenaFault | KernelError::DataArgumentArity)))]
fn lawful(
    arena: &mut TermArena,
    (entries, unfoldings): (&[AdmittedDeclaration], &Unfoldings),
    (obliged, arrow): (Obliged, CompTypeId),
    (rule, signature, declaration): (&PresentedRule, super::former::Signature<'_>, ConstantIndex),
    law: ConstantIndex,
) -> Result<Related, KernelError>
{
    let Some(&CompType::Arrow { codomain, .. }) = arena.comp_type(arrow)
    else {
        return Ok(Related::Apart);
    };
    let Some(&CompType::Returner(codomain)) = arena.comp_type(codomain)
    else {
        return Ok(Related::Apart);
    };
    let Some(entry) = entries.get(usize::from(law))
    else {
        return Ok(Related::Apart);
    };
    let bound = u32::from(rule.variables());
    let mut table = ContentTable::default();
    let codomain = shift_value_type(
        arena,
        &mut table,
        &mut NullMemo,
        codomain,
        BinderDepth::NONE,
        BinderDepth::from(bound),
    );
    let slots = rule
        .slots(&crate::presented::slot_table(
            arena,
            declaration,
            signature.constructors,
        ))
        .map_err(|_fault| KernelError::ArenaFault)?;
    // A law over no variable may state its path bare; any other states it
    // behind one parameter per variable.
    let declared = entry.declaration().declared_id();
    let statement = match arena.value_type(declared) {
        Some(&ValueType::Path { .. }) if bound == 0 => declared,
        Some(&ValueType::Thunk(parameters)) => {
            let mut at = parameters;
            for (variable, slot) in (0_u32 ..).map(RuleVariable::from).zip(slots) {
                let bound_at = arena.value_variable(pattern_binder(rule.variables(), variable));
                let (instance, classifier) = match slot {
                    RuleSlot::Own => {
                        let folded = arena.computation_application(obliged.head, bound_at);
                        (arena.value_returned(folded), codomain)
                    },
                    RuleSlot::Other(field) => (
                        bound_at,
                        instantiate_field(arena, &mut table, field, obliged.datatype, signature)?,
                    ),
                };
                let (domain, rest) = match arena.comp_type(at) {
                    Some(&CompType::Arrow { domain, codomain }) => (domain, codomain),
                    Some(&CompType::Pi { domain, codomain }) => (
                        domain,
                        substitute_comp_type(arena, &mut table, &mut NullMemo, codomain, instance),
                    ),
                    _ => return Ok(Related::Apart),
                };
                if crate::conv::convert_value_type(arena, classifier, domain).is_err() {
                    return Ok(Related::Apart);
                }
                at = rest;
            }
            let Some(&CompType::Returner(stated)) = arena.comp_type(at)
            else {
                return Ok(Related::Apart);
            };
            stated
        },
        _ => return Ok(Related::Apart),
    };
    let Some(&ValueType::Path {
        domain: carrier,
        left,
        right,
    }) = arena.value_type(statement)
    else {
        return Ok(Related::Apart);
    };
    if crate::conv::convert_value_type(arena, codomain, carrier).is_err() {
        return Ok(Related::Apart);
    }
    for (side, endpoint) in [(obliged.left, left), (obliged.right, right)] {
        let in_place = match arena.value(endpoint) {
            Some(&Value::Returned(run)) => run,
            _ => arena.computation_return(endpoint),
        };
        let sides = ReplaySides::Computations(side, in_place);
        if crate::replay::convert(arena, unfoldings, sides, ReplayBudget::DEFAULT)
            == KernelVerdict::Convertible
        {
            continue;
        }
        let mut table = ContentTable::default();
        let stated = sequenced(arena, &mut table, endpoint);
        let sides = ReplaySides::Computations(side, stated);
        if crate::replay::convert(arena, unfoldings, sides, ReplayBudget::DEFAULT)
            != KernelVerdict::Convertible
        {
            return Ok(Related::Apart);
        }
    }
    Ok(Related::Related)
}

/// One application spine of a law's endpoint, read argument by argument.
#[derive(Debug)]
struct Spine
{
    /// The computation the arguments are applied to.
    head: ComputationId,
    /// The arguments, the first applied first.
    arguments: Vec<ValueId>,
    /// What each argument read so far stands as, in the same order.
    read: Vec<Argument>,
}

/// What one argument of a spine stands as once read.
#[derive(Clone, Copy, Debug)]
enum Argument
{
    /// A value the spine keeps, scoped where the endpoint stands.
    Kept(ValueId),
    /// A run bound ahead of the spine, by its position among the binds.
    Bound(usize),
}

/// The spine of `computation`: its head and its arguments, none read yet.
///
/// # Specification
/// - requires: `computation` is live in `arena`.
/// - ensures: `computation` is the head applied to the arguments in order, and
///   the head is no application.
/// - fails: never.
/// - panics: none.
///
/// # Termination
/// - reason: a `while` loop down the application's head, which is finite.
/// - measure: the applications left above the head.
///
/// # Adequacy
/// - hypothesis: L3 — as [`sequenced`].
/// - witness: `native_formers::native_formers::a_fold_rests_on_the_law_of_each_rule_it_computes_apart`
#[spec(ensures: |ref ret| ret.read.is_empty()
    && !matches!(arena.computation(ret.head), Some(&Computation::Application(..))))]
fn spine_of(
    arena: &TermArena,
    computation: ComputationId,
) -> Spine
{
    let mut head = computation;
    let mut arguments = Vec::new();
    while let Some(&Computation::Application(function, argument)) = arena.computation(head) {
        arguments.push(argument);
        head = function;
    }
    arguments.reverse();
    Spine {
        head,
        arguments,
        read: Vec::new(),
    }
}

/// The computation that returns what `endpoint` denotes, its runs sequenced.
///
/// A law states its endpoints as values, a call among them as the value its
/// computation returns, `Returned(M)`; the fold's arms reach the kernel with
/// their runs elaborated into binds. `Returned(M a₁ … aₙ)` is read as
/// `M a₁ … aₙ` with each argument that is itself `Returned(N …)` run first and
/// bound, innermost first, and every kept argument carried under the binds
/// before it; any other endpoint is returned as written. The checker reads the
/// law the same way, so the kernel re-derives its verdict without a trace.
///
/// # Specification
/// - requires: `endpoint` is live in `arena`.
/// - ensures: `return endpoint` when `endpoint` is no `Returned`; otherwise one
///   bind per run among its spine's arguments, the first bound outermost, over
///   the endpoint's own spine applied to its arguments read.
/// - fails: never.
/// - panics: none.
///
/// # Termination
/// - reason: a worklist over the endpoint's finite spines, each pushed once for
///   the argument that holds it and built once its arguments are read; not
///   recursion.
/// - measure: the spines unbuilt, then their arguments unread.
///
/// # Adequacy
/// - hypothesis: L3 — the winding number's cancellation law, whose endpoint
///   calls `turn` on the run of `unturn` on the fold's run, meets the fold's
///   side, and a crossed law does not.
/// - witness: `native_formers::native_formers::a_fold_rests_on_the_law_of_each_rule_it_computes_apart`
#[spec(ensures: |ret| arena.computation(ret).is_some())]
fn sequenced(
    arena: &mut TermArena,
    table: &mut ContentTable,
    endpoint: ValueId,
) -> ComputationId
{
    let Some(&Value::Returned(top)) = arena.value(endpoint)
    else {
        return arena.computation_return(endpoint);
    };
    let mut bound: Vec<ComputationId> = Vec::new();
    let mut spines = Vec::from([spine_of(arena, top)]);
    let mut body = top;
    while let Some(mut spine) = spines.pop() {
        if let Some(&argument) = spine.arguments.get(spine.read.len()) {
            if let Some(&Value::Returned(run)) = arena.value(argument) {
                let inner = spine_of(arena, run);
                spines.push(spine);
                spines.push(inner);
            }
            else {
                spine.read.push(Argument::Kept(argument));
                spines.push(spine);
            }
            continue;
        }
        let depth = bound.len();
        let amount = BinderDepth::from(u32::try_from(depth).unwrap_or(u32::MAX));
        let mut built = shift_computation(
            arena,
            table,
            &mut NullMemo,
            spine.head,
            BinderDepth::NONE,
            amount,
        );
        for &argument in &spine.read {
            let value = match argument {
                Argument::Kept(kept) => {
                    shift_value(arena, table, &mut NullMemo, kept, BinderDepth::NONE, amount)
                },
                Argument::Bound(position) => {
                    let past = depth.saturating_sub(position).saturating_sub(1);
                    arena.value_variable(DeBruijnIndex::from(
                        u32::try_from(past).unwrap_or(u32::MAX),
                    ))
                },
            };
            built = arena.computation_application(built, value);
        }
        match spines.last_mut() {
            Some(holder) => {
                holder.read.push(Argument::Bound(depth));
                bound.push(built);
            },
            None => body = built,
        }
    }
    bound
        .iter()
        .rev()
        .fold(body, |body, &run| arena.computation_bind(run, body))
}

/// A field's classifier at the data application `datatype`: the field type,
/// scoped under the declaration's parameters, instantiated at its arguments.
///
/// # Specification
/// - requires: `field` is one of `signature`'s field types and `datatype` an
///   application of its declaration.
/// - ensures: the field type with each parameter replaced by the matching
///   argument of `datatype`, the field type itself for a declaration of no
///   parameters.
/// - fails: [`KernelError::DataArgumentArity`] when `datatype` supplies fewer
///   arguments than the declaration has parameters or a parameter index does
///   not fit a binder depth; [`KernelError::ArenaFault`] when `datatype` is not
///   a data application.
/// - panics: none.
///
/// # Errors
/// As `- fails:`.
///
/// # Termination
/// - reason: one `for` loop over the declaration's finite parameters.
/// - measure: the parameters left.
///
/// # Adequacy
/// - hypothesis: L3 — as [`lawful`]: the circle has no parameters, and a
///   variable at another type is read at its classifier.
/// - witness: `native_formers::native_formers::a_fold_rests_on_the_law_of_each_rule_it_computes_apart`
#[spec(ensures: |ret| !signature.parameters.is_empty() || ret.as_ref() == Ok(&field))]
fn instantiate_field(
    arena: &mut TermArena,
    table: &mut ContentTable,
    field: ValueTypeId,
    datatype: ValueTypeId,
    signature: super::former::Signature<'_>,
) -> Result<ValueTypeId, KernelError>
{
    let mut result = field;
    for index in (0 .. signature.parameters.len()).rev() {
        let argument = match arena.value_type(datatype) {
            Some(&ValueType::Data { ref arguments, .. }) => arguments
                .get(index)
                .copied()
                .ok_or(KernelError::DataArgumentArity)?,
            _ => return Err(KernelError::ArenaFault),
        };
        let depth = BinderDepth::from(
            u32::try_from(index).map_err(|_cause| KernelError::DataArgumentArity)?,
        );
        let argument = shift_value(
            arena,
            table,
            &mut NullMemo,
            argument,
            BinderDepth::NONE,
            depth,
        );
        result = substitute_value_type(arena, table, &mut NullMemo, result, argument);
    }
    Ok(result)
}
