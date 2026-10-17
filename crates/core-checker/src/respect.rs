//! A case over a presented type respects the type's rules.
//!
//! A case reads its scrutinee's constructor as written, and a presented
//! type's rules identify terms written apart: over the circle `Loop(Unloop(x))`
//! and `x` are one term. A case whose arms tell such a pair apart would let
//! `cong` carry the path between them to a path between distinct results, so
//! each rule `l ==> r` of the scrutinee's type is an obligation on the case:
//! `F(l) ≡ F(r)`, where `F` is what the case computes from its scrutinee and
//! `l` and `r` are built over fresh variables, one per pattern variable.
//!
//! `F` is read two ways. A case at the root of a structural fixpoint, `fix f.
//! λy. case y { … }`, is read as the fixpoint itself: the obligation is the
//! fixpoint applied to each side, so a recursive call at a field of `l`
//! unfolds again where the field is a constructor, and stops at a variable,
//! where both sides meet the same stuck call. Any other case is read as
//! itself at each side: its scrutinee replaced by `l` and by `r`. The
//! conversion is δ-free, [`crate::code::CodeDefinitions::convert_rigidly`],
//! every constant compared by name and a presented type's terms by their
//! normal forms, which is what the kernel re-derives on readmission with no
//! trace to replay.
//!
//! A body holding a computation written where a value is read is judged
//! twice (`nested`), and the obligation is judged on the second run only,
//! over the elaborated body: there `S(S(dbl(x)))` is the bind its explicit
//! spelling `run d <- dbl(x); S(S(d))` writes, so the fixpoint unfolds the
//! call as it unfolds the written bind, and one fold checks to one term
//! whichever way it is spelled. Read in place, on the first run, the call is
//! a value no conversion unfolds, and a fold that respects its rules would
//! be refused. **Alternative.** The lowering writing the bind itself, which
//! runs every call at a thunk-typed parameter. **Reversal.** A checker that
//! mints each bind as it judges, which `nested` names, judges it in one run.
//!
//! A dependent fold into a path type meets a rule as a cong chain: at
//! `Loop(Unloop(x))` the section of the circle binds its call at `x` into
//! `cong(unaround, _)` and that into `cong(around, _)`. Conversion reads such
//! a chain whose functions compose to the identity as the path it starts
//! from, the functions read through their definitions even in a δ-free run,
//! and the kernel reads the same chain by its own evaluator; the two sides
//! then meet as the one stuck call, with no law named.
//!
//! A dependent fold into the paths of a set meets a rule however its arms
//! compose those paths: `plusComm` over the integers binds its call at `x`
//! into a `then` through a lemma, which nothing reduces. A set has no cells,
//! so two parallel paths in one are one path. Where conversion leaves the
//! sides apart and the fold's codomain at both sides is a path type in a set
//! ([`sethood`]: a parameterless data type with no cells and no loop at it,
//! its fields such types), the obligation holds once the two instances'
//! endpoints convert ([`parallel_in_a_set`]); the kernel re-derives the same
//! reading. **Alternatives.** Owing the obligation by name under `respects`,
//! a law per rule restating what the set already gives; comparing paths at a
//! set by their endpoints inside conversion itself, which needs a
//! type-directed conversion neither engine has. **Reversal.** A conversion
//! that compares values at their types decides paths in a set there, and
//! this reading retires into it.
//!
//! A fold into a model meets a rule only up to the model's law: the winding
//! number computes `turn(unturn(wind(x)))` against `wind(x)`. Such a fold
//! names one law per rule, in rule order ([`crate::Declaration::laws`],
//! written `respects`), and where the δ-free test leaves rule `i`'s sides
//! apart, law `i` is instantiated at the fold of the rule's variables and its
//! endpoints must convert with the two sides ([`lawful`]). The instance is
//! fixed by the rule, so nothing is searched, and the fold rests on the laws
//! it names: the kernel's audit names each owed one as an axiom.
//!
//! A case that respects every rule, by conversion or by its law, is admitted;
//! one that does not is refused `RuleNotRespected`, naming the case, the
//! rule's position and its two sides as built. Witnesses:
//! `native_formers::native_formers::a_case_respects_its_type_s_rules_or_is_refused_by_the_rule_357`
//! and
//! `native_formers::native_formers::a_fold_rests_on_the_laws_of_the_rules_it_computes_apart`.
//!
//! **Choice.** The fold form, `F(l) ≡ F(r)` under the arms, is the
//! obligation the rule's quotient puts on any map out of the type, and over a
//! free type it is empty; where it holds only up to a path, the path is a law
//! the definition names, a declaration of its own that the ledger counts.
//! **Alternatives.** Refusing every case over a presented type, which leaves
//! the type without an eliminator; an eliminator per rule taking a path for
//! each, which moves the obligation to every caller; a goal minted per rule
//! beside the fold, which repeats the model's laws for every fold out of it.
//! **Reversal.** Arms generated from a model's signature carry the laws with
//! the model, and the attribute retires.

use alloc::collections::BTreeSet;
use alloc::vec::Vec;

use anodized::spec;
use gandr_core_term::Binders;
use gandr_core_term::CompType;
use gandr_core_term::CompTypeId;
use gandr_core_term::Computation;
use gandr_core_term::ComputationId;
use gandr_core_term::CoreArena;
use gandr_core_term::DataSignature;
use gandr_core_term::Value;
use gandr_core_term::ValueId;
use gandr_core_term::ValueType;
use gandr_core_term::ValueTypeId;
use gandr_core_term::Zone;
use gandr_core_term::instantiate_comp_type;
use gandr_core_term::shift_comp_type;
use gandr_core_term::shift_computation_under_traced;
use gandr_core_term::shift_value;
use gandr_core_term::shift_value_type;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::FieldCount;
use gandr_kernel_term::PresentedRule;
use gandr_kernel_term::RuleIndex;
use gandr_kernel_term::RuleNode;
use gandr_kernel_term::RuleSlot;
use gandr_kernel_term::RuleVariable;
use gandr_kernel_term::VariableCount;
use gandr_kernel_term::build_side;
use quenchant_shape::shape::Maybe;

use crate::CheckRefusal;
use crate::CheckingContext;
use crate::conversion::Agreement;

quenchant_shape::reason_enum! {
    /// Why a case carries no obligation against its type's rules.
    pub mod obligation {
        /// The reason no rule binds the case.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The scrutinee's type is free: it has no rules.
            Free,
            /// The case has no branch: its scrutinee is a path between two
            /// apart terms, and no arm reads a rule's sides.
            Absurd,
        }
    }
}

quenchant_shape::reason_enum! {
    /// Why no case is marked as a structural fixpoint's root.
    pub mod root {
        /// The reason no case is marked.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
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
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Reading
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

/// Decide that the case `at` respects every rule of `signature`, read as
/// `reading` says, resting a fold on the laws its declaration names where
/// conversion does not decide.
///
/// # Specification
/// - requires: `signature` presents the scrutinee's type at `reading`'s data
///   application, and the case's branches have checked.
/// - ensures: `Ok(())` exactly when, for every rule `l ==> r` in written order,
///   `F(l)` converts with `F(r)` under
///   [`crate::code::CodeDefinitions::convert_rigidly`], `l` and `r` built over
///   one fresh variable per pattern variable and `F` read as `reading` says;
///   or, at a fold, the law at the rule's position among the laws the
///   declaration under judgement names relates them, as [`lawful`] decides.
/// - fails: [`CheckRefusal::RuleNotRespected`] at `at` naming the first rule
///   whose sides neither convert nor are related by a law, with the two sides
///   as built; [`CheckRefusal::MachineInvariant`] for a rule side that does not
///   build or a case node the arena does not hold.
/// - panics: none.
///
/// # Errors
/// As `- fails:`.
///
/// # Termination
/// - reason: the `for` loop over the signature's finite rules, not recursion;
///   each conversion runs under the machine's fuel.
/// - measure: the rules left.
///
/// # Adequacy
/// - hypothesis: L3 — over the circle, a fixpoint recursing through both
///   inverse letters is admitted, a case reading the letter as written is
///   refused at the first rule, and the same refusal names the rule's two
///   sides; a fold computing the integers is admitted on its two cancellation
///   laws and refused without them or with a law stating another path; the
///   kernel re-derives every verdict.
/// - witness: `native_formers::native_formers::a_case_respects_its_type_s_rules_or_is_refused_by_the_rule_357`
/// - witness: `native_formers::native_formers::a_fold_rests_on_the_laws_of_the_rules_it_computes_apart`
#[spec(ensures: |ret| ret.is_ok() || matches!(ret, Err(CheckRefusal::RuleNotRespected { at: refused, .. }) if refused == at) || matches!(ret, Err(CheckRefusal::MachineInvariant)))]
pub fn respected(
    context: &mut CheckingContext<'_>,
    at: ComputationId,
    signature: &DataSignature,
    reading: Reading,
) -> Result<(), CheckRefusal>
{
    let arities: Vec<FieldCount> = signature
        .constructors()
        .iter()
        .map(|fields| FieldCount::from(fields.len()))
        .collect();
    let (head, datatype) = match reading {
        Reading::Fold {
            fixpoint, domain, ..
        } => (fixpoint, domain),
        Reading::Case { datatype } => (at, datatype),
    };
    for (index, rule) in signature.presentation().rules().iter().enumerate() {
        let bound = u32::from(rule.variables());
        let amount = Binders::from(bound);
        let arena = context.arena_mut();
        let datatype = shift_value_type(arena, datatype, amount);
        let head =
            shift_computation_under_traced(arena, head, Binders::NONE, amount, &mut Vec::new());
        let mut side = |nodes: &[RuleNode]| {
            build_side(nodes, &arities, |node, fields| match node {
                RuleNode::Variable(variable) => arena.value_variable(
                    Zone::Intuitionistic,
                    pattern_binder(rule.variables(), variable),
                ),
                RuleNode::Constructor(tag) => arena.value_constructor(datatype, tag, fields),
            })
            .map_err(|_fault| CheckRefusal::MachineInvariant)
        };
        let left = side(rule.left())?;
        let right = side(rule.right())?;
        let obligation = match reading {
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
                    return Err(CheckRefusal::MachineInvariant);
                };
                let branches = branches.clone();
                (
                    arena.computation_data_case(left, motive, branches.clone()),
                    arena.computation_data_case(right, motive, branches),
                )
            },
        };
        if context
            .definitions()
            .convert_rigidly(context.arena(), obligation)
            == Maybe::Present(())
        {
            continue;
        }
        if let Reading::Fold { arrow, .. } = reading
            && parallel_in_a_set(context, (arrow, amount), (left, right)) == Related::Related
        {
            continue;
        }
        let law = context.admitted_laws().get(index).copied();
        let related = match (reading, law) {
            (Reading::Fold { arrow, .. }, Some(law)) => {
                let obliged = Obliged {
                    sides: obligation,
                    head,
                    datatype,
                };
                lawful(context, (obliged, arrow), (rule, signature), law)?
            },
            (Reading::Fold { .. } | Reading::Case { .. }, _) => Related::Apart,
        };
        if related == Related::Apart {
            return Err(CheckRefusal::RuleNotRespected {
                at,
                rule: RuleIndex::from(index),
                left,
                right,
            });
        }
    }
    Ok(())
}

/// Whether a fold's two sides of a rule are paths in a set with the same
/// endpoints: `arrow`'s codomain at each rule side, `amount` binders past the
/// fold's type, is `F Path(C, a, b)` for one set `C`, and the two instances'
/// endpoints convert.
///
/// A set has no cells: two parallel paths in one are one path, so a fold
/// into its paths meets each rule however its arms compose them, a cong of
/// the recursive call or a chain of `then` through a lemma that nothing
/// reduces. Its endpoints at the two sides are the rule's identification
/// carried through the codomain, which conversion decides, so nothing about
/// the paths themselves is compared. An endpoint is a value, a call among it
/// written as the value its run returns; each is compared as its run, as
/// [`lawful`] reads a law's endpoint, since a held run is compared only
/// structurally and never meets a presented term's normal form.
///
/// # Specification
/// - requires: `arrow` is the type of the fold whose two sides of a rule are
///   built over `left` and `right`, beneath `amount` binders.
/// - ensures: [`Related::Related`] exactly when `arrow` is `A → F P` or `Π (y :
///   A). F P`, `P` at `left` and at `right` is `Path(C, a, b)` and `Path(C',
///   a', b')` with `C` equivalent to `C'`, `C` a set as [`sethood`] decides,
///   and `a` converting with `a'` and `b` with `b'`, each a returned run read
///   as that run, under [`crate::code::CodeDefinitions::convert_rigidly`];
///   [`Related::Apart`] otherwise.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a fold over the integers into a path between two sums,
///   whose arms compose the recursive call with a lemma, is admitted; a fold
///   into the circle's paths is refused at the rule its words tell apart.
/// - witness: `native_formers::native_formers::a_fold_into_the_paths_of_a_set_respects_its_rules`
#[spec(
    captures: arrowed = matches!(context.arena().comp_type(arrow), Some(&(CompType::Arrow { .. } | CompType::Pi { .. }))),
    ensures: |ret| ret == Related::Apart || arrowed,
)]
fn parallel_in_a_set(
    context: &mut CheckingContext<'_>,
    (arrow, amount): (CompTypeId, Binders),
    (left, right): (ValueId, ValueId),
) -> Related
{
    let arena = context.arena_mut();
    let arrow = shift_comp_type(arena, arrow, amount);
    let (from, to) = if let Some(&CompType::Pi { codomain, .. }) = arena.comp_type(arrow) {
        (
            instantiate_comp_type(arena, codomain, left),
            instantiate_comp_type(arena, codomain, right),
        )
    }
    else if let Some(&CompType::Arrow { codomain, .. }) = arena.comp_type(arrow) {
        (codomain, codomain)
    }
    else {
        return Related::Apart;
    };
    let path = |at: CompTypeId| {
        let Some(&CompType::Returner { result, .. }) = arena.comp_type(at)
        else {
            return None;
        };
        let Some(&ValueType::Path {
            carrier,
            left,
            right,
        }) = arena.value_type(result)
        else {
            return None;
        };
        Some((carrier, left, right))
    };
    let (Some((carrier, from_left, from_right)), Some((other, to_left, to_right))) =
        (path(from), path(to))
    else {
        return Related::Apart;
    };
    if sethood(context, carrier) == Sethood::Unread
        || !matches!(
            crate::conversion::equivalent(context, carrier, other),
            Ok(Agreement::Convertible)
        )
    {
        return Related::Apart;
    }
    for (from, to) in [(from_left, to_left), (from_right, to_right)] {
        let arena = context.arena_mut();
        let mut in_place = |endpoint: ValueId| {
            if let Some(&Value::Returned(run)) = arena.value(endpoint) {
                run
            }
            else {
                arena.computation_return(endpoint)
            }
        };
        let sides = (in_place(from), in_place(to));
        if let Maybe::Absent(_) = context
            .definitions()
            .convert_rigidly(context.arena(), sides)
        {
            return Related::Apart;
        }
    }
    Related::Related
}

/// Whether a type is read as a set.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Sethood
{
    /// A parameterless data type with no cells and no loop at it, whose
    /// fields are such types.
    Set,
    /// Any other type: one with cells or a loop at it, or one nothing here
    /// reads as a set.
    Unread,
}

/// Whether `carrier` is a set: a parameterless data type with no cells of
/// its own and no loop at it, whose every constructor's fields are such types.
///
/// # Specification
/// - requires: `carrier` is formed.
/// - ensures: [`Sethood::Set`] exactly when every data type reached from
///   `carrier` through constructor fields is applied to no argument, declares
///   no parameter, carries no cells and has no loop at it as
///   [`crate::loops::loops`] finds them; [`Sethood::Unread`] otherwise. Each
///   data type read is logged as consulted.
/// - fails: never.
/// - panics: none.
///
/// # Termination
/// - reason: a worklist over the field types of data declarations, each
///   declaration expanded once; not recursion.
/// - measure: the declarations not yet expanded, then the field types pending.
///
/// # Adequacy
/// - hypothesis: L3 — the integers are a set and the circle is not, so a fold
///   into the integers' paths is admitted and one into the circle's refused.
/// - witness: `native_formers::native_formers::a_fold_into_the_paths_of_a_set_respects_its_rules`
#[spec(ensures: |ret| ret == Sethood::Unread || matches!(context.arena().value_type(carrier), Some(&ValueType::Data { ref arguments, .. }) if arguments.is_empty()))]
fn sethood(
    context: &mut CheckingContext<'_>,
    carrier: ValueTypeId,
) -> Sethood
{
    let mut expanded = BTreeSet::new();
    let mut pending = Vec::from([carrier]);
    while let Some(next) = pending.pop() {
        let Some(&ValueType::Data {
            declaration,
            ref arguments,
        }) = context.arena().value_type(next)
        else {
            return Sethood::Unread;
        };
        if !arguments.is_empty() {
            return Sethood::Unread;
        }
        if !expanded.insert(declaration) {
            continue;
        }
        if !crate::loops::loops(context, next).is_empty() {
            return Sethood::Unread;
        }
        let Some(signature) = context.consult_data(declaration)
        else {
            return Sethood::Unread;
        };
        if signature.presentation().cells().is_some() || !signature.parameters().is_empty() {
            return Sethood::Unread;
        }
        pending.extend(signature.constructors().iter().flatten().copied());
    }
    Sethood::Set
}

/// One rule's obligation at a fold, built beneath one fresh binder per
/// pattern variable.
#[derive(Clone, Copy, Debug)]
struct Obliged
{
    /// `F(l)` and `F(r)`.
    sides: (ComputationId, ComputationId),
    /// The fixpoint, shifted past the pattern's binders.
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
    /// It does not: its statement is of another shape, or its endpoints are
    /// not the two sides.
    Apart,
}

/// The binder pattern variable `variable` of `bound` stands at: the first
/// variable outermost.
///
/// # Specification
/// - requires: `variable < bound`.
/// - ensures: `bound - variable - 1`; zero when the requirement fails.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — as [`respected`]: a rule over one variable reads it at
///   the innermost binder.
/// - witness: `native_formers::native_formers::a_case_respects_its_type_s_rules_or_is_refused_by_the_rule_357`
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
/// The fold's sides `F(l)` and `F(r)` stand under one binder per pattern
/// variable. The law states, for every assignment of its parameters, a path
/// in the fold's carrier; it is instantiated at the fold's reading of each
/// variable — `F(x)` returned where the variable stands at the folded type
/// itself, the variable where it stands at another field — and its two
/// endpoints must then convert with the two sides, δ-free as the kernel
/// re-derives them.
///
/// An endpoint is a value, a call among it written as the value its run
/// returns, `Returned(M)`. The fold's sides hold their calls as its arms do:
/// in place where an arm writes `Returned`, and bound ahead of the arm where
/// the arm's nested runs were elaborated into binds, which happens before the
/// obligation is judged. An endpoint is read to match: its own run with the
/// runs in its arguments in place, and else [`sequenced`], the runs bound
/// ahead as elaboration binds them.
///
/// # Specification
/// - requires: `obliged` is `rule`'s obligation at a fold whose type is
///   `arrow`, built beneath `rule`'s pattern binders over a data application of
///   `signature`.
/// - ensures: [`Related::Related`] exactly when `arrow` is `A → F C`, the law's
///   declared type is `Path(C', a, b)` for a rule over no variable or `U (Π (x₁
///   : A₁) … (xₙ : Aₙ). F Path(C', a, b))` with one parameter per variable,
///   each `Aᵢ` equivalent to the classifier of the `i`th variable's reading,
///   `C'` equivalent to `C`, and at the instance `a` converts with `F(l)` and
///   `b` with `F(r)`, each endpoint read in place or sequenced;
///   [`Related::Apart`] otherwise, a conversion that faults included.
/// - fails: [`CheckRefusal::MachineInvariant`] when the rule does not read
///   against the signature's constructor table.
/// - panics: none.
///
/// # Errors
/// As `- fails:`.
///
/// # Termination
/// - reason: the `for` loop over the rule's finite variables and the two
///   endpoints, not recursion; each conversion runs under the machine's fuel.
/// - measure: the variables, then the endpoints, left.
///
/// # Adequacy
/// - hypothesis: L3 — the circle's fold into the integers is related by the two
///   cancellation laws and refused when a law states another path.
/// - witness: `native_formers::native_formers::a_fold_rests_on_the_laws_of_the_rules_it_computes_apart`
/// - witness: `native_formers::native_formers::a_law_is_stated_bare_only_over_no_variable`
#[spec(ensures: |ret| ret.is_ok() || matches!(ret, Err(CheckRefusal::MachineInvariant)))]
fn lawful(
    context: &mut CheckingContext<'_>,
    (obliged, arrow): (Obliged, CompTypeId),
    (rule, signature): (&PresentedRule, &DataSignature),
    law: ConstantIndex,
) -> Result<Related, CheckRefusal>
{
    let arena = context.arena();
    let Some(&CompType::Arrow { codomain, .. }) = arena.comp_type(arrow)
    else {
        return Ok(Related::Apart);
    };
    let Some(&CompType::Returner {
        result: carrier, ..
    }) = arena.comp_type(codomain)
    else {
        return Ok(Related::Apart);
    };
    let Some(&ValueType::Data { declaration, .. }) = arena.value_type(obliged.datatype)
    else {
        return Err(CheckRefusal::MachineInvariant);
    };
    let Maybe::Present(declared) = context.signature(law)
    else {
        return Ok(Related::Apart);
    };
    let declared = declared.id();
    let slots = rule
        .slots(&crate::former::slot_table(arena, declaration, signature))
        .map_err(|_fault| CheckRefusal::MachineInvariant)?;
    let bound = u32::from(rule.variables());
    let carrier = shift_value_type(context.arena_mut(), carrier, Binders::from(bound));
    let parameters = gandr_core_term::BinderDepth::from(signature.parameters().len());
    // A law over no variable may state its path bare; any other states it
    // behind one parameter per variable.
    let statement = match context.arena().value_type(declared) {
        Some(&ValueType::Path { .. }) if bound == 0 => declared,
        Some(&ValueType::Thunk(stated)) => {
            let mut at = stated;
            for (variable, slot) in (0_u32 ..).map(RuleVariable::from).zip(slots) {
                let arena = context.arena_mut();
                let reached = arena.value_variable(
                    Zone::Intuitionistic,
                    pattern_binder(rule.variables(), variable),
                );
                let (instance, classifier) = match slot {
                    RuleSlot::Own => {
                        let folded = arena.computation_application(obliged.head, reached);
                        (arena.value_returned(folded), carrier)
                    },
                    RuleSlot::Other(field) => (
                        reached,
                        crate::former::instantiate(context, obliged.datatype, field, parameters)?,
                    ),
                    // A validated rule binds no variable at a dependent field.
                    RuleSlot::Dependent => return Err(CheckRefusal::MachineInvariant),
                };
                let arena = context.arena_mut();
                let (domain, rest) = match arena.comp_type(at) {
                    Some(&CompType::Arrow { domain, codomain }) => (domain, codomain),
                    Some(&CompType::Pi { domain, codomain }) => {
                        (domain, instantiate_comp_type(arena, codomain, instance))
                    },
                    _ => return Ok(Related::Apart),
                };
                if !matches!(
                    crate::conversion::equivalent(context, classifier, domain),
                    Ok(Agreement::Convertible)
                ) {
                    return Ok(Related::Apart);
                }
                at = rest;
            }
            let Some(&CompType::Returner { result, .. }) = context.arena().comp_type(at)
            else {
                return Ok(Related::Apart);
            };
            result
        },
        _ => return Ok(Related::Apart),
    };
    let Some(&ValueType::Path {
        carrier: stated,
        left,
        right,
    }) = context.arena().value_type(statement)
    else {
        return Ok(Related::Apart);
    };
    if !matches!(
        crate::conversion::equivalent(context, carrier, stated),
        Ok(Agreement::Convertible)
    ) {
        return Ok(Related::Apart);
    }
    let (from, to) = obliged.sides;
    for (side, endpoint) in [(from, left), (to, right)] {
        let in_place = match context.arena().value(endpoint) {
            Some(&Value::Returned(run)) => run,
            _ => context.arena_mut().computation_return(endpoint),
        };
        if context
            .definitions()
            .convert_rigidly(context.arena(), (side, in_place))
            == Maybe::Present(())
        {
            continue;
        }
        let stated = sequenced(context.arena_mut(), endpoint);
        if let Maybe::Absent(_) = context
            .definitions()
            .convert_rigidly(context.arena(), (side, stated))
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
/// - witness: `native_formers::native_formers::a_fold_rests_on_the_laws_of_the_rules_it_computes_apart`
#[spec(ensures: |ref ret| ret.read.is_empty()
    && !matches!(arena.computation(ret.head), Some(&Computation::Application(..))))]
fn spine_of(
    arena: &CoreArena,
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
/// A law states its endpoints as values, and a call written where a value is
/// read is the value its computation returns, `Returned(M)`. The sides a fold
/// computes are computations whose runs elaboration already sequenced into
/// binds, the innermost first; the endpoint is read the same way, so the two
/// meet under δ-free conversion. `Returned(M a₁ … aₙ)` is `M a₁ … aₙ` with each
/// argument that is itself `Returned(N …)` run first and bound, innermost
/// first, and every kept argument carried under the binds before it; any
/// other endpoint is returned as written. No conversion rule is added: the
/// law's statement is read as the fold's arms were elaborated.
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
/// - hypothesis: L3 — the circle's cancellation law, whose endpoint calls
///   `turn` on the run of `unturn` on the fold's run, meets the fold's side,
///   and a crossed law does not.
/// - witness: `native_formers::native_formers::a_fold_rests_on_the_laws_of_the_rules_it_computes_apart`
#[spec(ensures: |ret| arena.computation(ret).is_some())]
fn sequenced(
    arena: &mut CoreArena,
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
        let amount = Binders::from(u32::try_from(depth).unwrap_or(u32::MAX));
        let mut built = shift_computation_under_traced(
            arena,
            spine.head,
            Binders::NONE,
            amount,
            &mut Vec::new(),
        );
        for &argument in &spine.read {
            let value = match argument {
                Argument::Kept(kept) => shift_value(arena, kept, amount),
                Argument::Bound(position) => {
                    let past = depth.saturating_sub(position).saturating_sub(1);
                    arena.value_variable(
                        Zone::Intuitionistic,
                        DeBruijnIndex::from(u32::try_from(past).unwrap_or(u32::MAX)),
                    )
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
