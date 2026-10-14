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
//! A case that respects every rule is admitted; one that does not is refused
//! `RuleNotRespected`, naming the case, the rule's position and its two sides
//! as built. Witness:
//! `native_formers::native_formers::a_case_respects_its_type_s_rules_or_is_refused_by_the_rule`.
//!
//! **Choice.** The fold form, `F(l) ≡ F(r)` under the arms, is the
//! obligation the rule's quotient puts on any map out of the type, and over a
//! free type it is empty. **Alternatives.** Refusing every case over a
//! presented type, which leaves the type without an eliminator; an
//! eliminator per rule taking a path for each, which moves the obligation to
//! every caller. **Reversal.** A respect that holds only up to a path, as
//! `(n - 1) + 1` and `n` over the integers, takes that path as an owed
//! obligation instead of a conversion.

use alloc::vec::Vec;

use anodized::spec;
use gandr_core_term::Binders;
use gandr_core_term::Computation;
use gandr_core_term::ComputationId;
use gandr_core_term::DataSignature;
use gandr_core_term::ValueTypeId;
use gandr_core_term::Zone;
use gandr_core_term::shift_computation_under_traced;
use gandr_core_term::shift_value_type;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::FieldCount;
use gandr_kernel_term::RuleIndex;
use gandr_kernel_term::RuleNode;
use gandr_kernel_term::build_side;
use quenchant_shape::shape::Maybe;

use crate::CheckRefusal;
use crate::CheckingContext;

quenchant_shape::reason_enum! {
    /// Why a case carries no obligation against its type's rules.
    pub mod obligation {
        /// The reason no rule binds the case.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The scrutinee's type is free: it has no rules.
            Free,
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
/// `reading` says.
///
/// # Specification
/// - requires: `signature` presents the scrutinee's type at `reading`'s data
///   application, and the case's branches have checked.
/// - ensures: `Ok(())` exactly when, for every rule `l ==> r` in written order,
///   `F(l)` converts with `F(r)` under
///   [`crate::code::CodeDefinitions::convert_rigidly`], `l` and `r` built over
///   one fresh variable per pattern variable and `F` read as `reading` says.
/// - fails: [`CheckRefusal::RuleNotRespected`] at `at` naming the first rule
///   whose sides do not convert, with the two sides as built;
///   [`CheckRefusal::MachineInvariant`] for a rule side that does not build or
///   a case node the arena does not hold.
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
///   sides; the kernel re-derives both verdicts.
/// - witness: `native_formers::native_formers::a_case_respects_its_type_s_rules_or_is_refused_by_the_rule`
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
        | Reading::Fold { fixpoint, domain } => (fixpoint, domain),
        | Reading::Case { datatype } => (at, datatype),
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
                | RuleNode::Variable(variable) => {
                    let index = bound
                        .checked_sub(u32::from(variable))
                        .and_then(|past| past.checked_sub(1_u32))
                        .unwrap_or_default();
                    arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(index))
                },
                | RuleNode::Constructor(tag) => arena.value_constructor(datatype, tag, fields),
            })
            .map_err(|_fault| CheckRefusal::MachineInvariant)
        };
        let left = side(rule.left())?;
        let right = side(rule.right())?;
        let obligation = match reading {
            | Reading::Fold { .. } => (
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
                    return Err(CheckRefusal::MachineInvariant);
                };
                let branches = branches.clone();
                (
                    arena.computation_data_case(left, motive, branches.clone()),
                    arena.computation_data_case(right, motive, branches),
                )
            },
        };
        if let Maybe::Absent(_) = context
            .definitions()
            .convert_rigidly(context.arena(), obligation)
        {
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
