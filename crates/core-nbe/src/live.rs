//! Live evaluation: a program with holes runs, a fill resumes it, and a match
//! over a value holding a hole answers in three values.
//!
//! # A hole evaluates to a neutral carrying its closure
//!
//! Evaluation meets a hole and does not stop: the hole becomes the head of a
//! neutral, [`NeutralHead::Hole`], closed over the environment it was met in,
//! and every elimination that could not fire because of it stacks on that
//! neutral's spine as any stuck elimination does. The result is indeterminate
//! rather than an error, so an unfinished program still has a value to show
//! (Omar et al., *Live Functional Programming with Typed Holes*, POPL 2019,
//! doi:10.1145/3290327). A mark is suspended the same way: its body was not
//! well typed, so it is never run.
//!
//! # Filling resumes rather than restarts
//!
//! [`fill_and_resume`] writes a hole of a result. Every hole closure of the
//! name reads back as the filling, its free variables replaced by the
//! read-back entries of the environment the hole was met in; a hole kept
//! inside a retained source face, which was evaluated in no environment, is
//! filled where it stands. The written term is then evaluated, so an
//! elimination that was stuck on the hole fires and everything already
//! reduced is not reduced again. Filling the result agrees with evaluating the
//! filled program: the commutation the paper proves, and the witnesses check.
//!
//! # A match over a hole answers per arm
//!
//! [`match_pattern`] classifies one arm against a scrutinee: satisfied with
//! its bindings, refuted, or possibly — when a pattern hole or a scrutinee
//! stuck on a hole decides. [`select_arm`] takes the first arm not refuted,
//! and is indeterminate when that arm only possibly matches, because a later
//! arm the fill might still reach is not the one the finished program takes
//! (Yuan et al., *Live Pattern Matching with Typed Holes*, OOPSLA 2023,
//! doi:10.1145/3586048).
//!
//! # References
//!
//! - Cyrus Omar, Ian Voysey, Ravi Chugh and Matthew A. Hammer. "Live Functional
//!   Programming with Typed Holes." _Proceedings of the ACM on Programming Languages_
//!   3 (POPL), 2019. <https://doi.org/10.1145/3290327> — evaluation around
//!   holes to indeterminate results, and fill-and-resume commuting with filling
//!   the program.
//! - Yongwei Yuan et al. "Live Pattern Matching with Typed Holes." _Proceedings
//!   of the ACM on Programming Languages_ 7 (OOPSLA1), 2023. <https://doi.org/10.1145/3586048>
//!   — matching a scrutinee that may hold a hole, against patterns that may
//!   hold one, in three values.
//!
//! # A hole evaluates to a neutral
//!
//! Evaluation meets a hole and does not stop: a hole evaluates to a neutral
//! headed by `NeutralHead::Hole`, closed over the environment it was met in as
//! a `Suspended` closure, and every elimination that could not fire because of
//! it stacks on the neutral's spine. The result is indeterminate rather than an
//! error, so an unfinished program still has a value to show; a mark is
//! suspended the same way under `NeutralHead::Mark`, its body never run because
//! it was not well typed (Omar et al., POPL 2019). Readback writes a suspended
//! hole back as the hole, and a suspended mark as the mark over its body with
//! the body's free variables replaced by the read-back entries of its
//! environment.
//!
//! # A comparison over a hole declines
//!
//! A comparison that meets a hole or a mark on either side answers
//! `Deferral::Indeterminate` from the search-free steps and
//! `DeclineReason::Indeterminate` from the machine: a fill may still make the
//! sides agree or differ, so no verdict is the comparison's to give, and no
//! refutation rests on a hole. A neutral headed by a hole or a mark carries a
//! closure, so its cached word is flexible and the guard decides nothing about
//! it either.
//!
//! # Filling resumes rather than restarts
//!
//! `fill_and_resume` writes every hole of one name in a result: each hole
//! closure reads back as the fill, its free variables replaced by the read-back
//! entries of its environment, a hole kept inside a retained source face is
//! filled where it stands, and the written term is evaluated, so an elimination
//! stuck on the hole fires and what was already reduced stays reduced. Filling
//! the result agrees with evaluating the filled program, the commutation the
//! paper proves and the witnesses check. The alternative was re-evaluating the
//! filled program from the start, which repeats every reduction the hole did
//! not block; it remains the reference the fill is compared against.
//!
//! # A match over a hole answers per arm
//!
//! `match_pattern` classifies one arm against a scrutinee as satisfied with its
//! bindings, refuted, or possibly when a pattern hole or a scrutinee stuck on a
//! hole decides. `select_arm` stops at the first arm not refuted, and is
//! indeterminate when that arm only possibly matches, because a later arm the
//! fill might still reach is not the one the finished program takes (Yuan et
//! al., OOPSLA 2023). A `Matched` projects to
//! `gandr_core_term::pattern::BranchStatus`, the vocabulary static coverage in
//! `gandr-core-checker` answers in too.
//!
//! # Witnesses
//!
//! `live::tests::a_hole_evaluates_to_a_neutral_carrying_its_environment`,
//! `live::tests::a_computation_hole_keeps_the_eliminations_that_could_not_fire`,
//! `live::tests::a_mark_reads_back_through_its_environment`,
//! `live::tests::a_comparison_that_meets_a_hole_declines`,
//! `live::tests::filling_resumes_where_the_hole_stood`,
//! `live::tests::a_fill_leaves_other_holes_standing`,
//! `live::tests::a_match_over_a_hole_answers_per_arm`,
//! `live::tests::a_determinate_match_binds_left_to_right`.

use alloc::vec::Vec;

use anodized::spec;
use gandr_core_term::CoreArena;
use gandr_core_term::Summand;
use gandr_core_term::Value;
use gandr_core_term::fill_hole;
use gandr_core_term::hole::HoleId;
use gandr_core_term::hole::TermId;
use gandr_core_term::pattern::BranchStatus;
use gandr_core_term::pattern::Pattern;
use gandr_core_term::pattern::PatternId;
use gandr_core_term::pattern::Patterns;

use crate::arena::DomainArena;
use crate::arena::DomainFault;
use crate::arena::DomainValueId;
use crate::closure::Environment;
use crate::domain::DomainValue;
use crate::domain::Glued;
#[cfg(doc)]
use crate::domain::NeutralHead;
use crate::eval::Definitions;
use crate::eval::EvalFault;
use crate::eval::Fuel;
use crate::eval::eval_closed_value;
use crate::eval::eval_comp_within;
use crate::readback::ReadbackFault;
use crate::readback::read_written;

/// Why filling a result stopped.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum LiveFault
{
    /// Reading the result back with the hole written refused.
    Readback(ReadbackFault),
    /// Evaluating the written term refused.
    Eval(EvalFault),
}

/// Fill every hole of one name in a closed result, and run what the fill
/// unblocked.
///
/// # Specification
/// - requires: `result` resolves in `domain`, was evaluated from a closed term
///   and stands under no binder; `filling` is live in `core` and written in the
///   context the holes of the name stand in.
/// - ensures: on success the result the program would have had with every hole
///   of the name, in the filling's family, written as `filling` — its hole
///   closures written through their environments, the holes inside retained
///   source faces filled where they stand, and the written term evaluated to
///   weak head — paired with the fuel left over, in the result's family.
/// - provides: fill-and-resume: the eliminations stuck on the hole fire, and
///   the work already done stays done.
/// - fails: [`LiveFault::Readback`] when reading the result back refuses, and
///   [`LiveFault::Eval`] when evaluating the written term refuses.
/// - panics: none.
///
/// # Errors
/// As above.
///
/// # Adequacy
/// - hypothesis: L2 against the filled program — a stuck force under a binder
///   whose filling reads the bound thunk fires once filled, agreeing with the
///   program filled before it ran; a second hole stands while the first is
///   written; a computation hole is filled in computation position.
/// - witness: `live::tests::filling_resumes_where_the_hole_stood`
/// - witness: `live::tests::a_fill_leaves_other_holes_standing`
/// - witness: `live::tests::a_computation_hole_keeps_the_eliminations_that_could_not_fire`
#[spec(ensures: |ret| ret.as_ref().map_or(true, |&(filled, remaining)| u32::from(remaining) <= u32::from(fuel) && match (filled, result) {
    (Glued::Value(id), Glued::Value(_)) => domain.value(id).is_some(),
    (Glued::Computation(id), Glued::Computation(_)) => domain.computation(id).is_some(),
    (Glued::Value(_), Glued::Computation(_)) | (Glued::Computation(_), Glued::Value(_)) => false,
}))]
#[inline]
pub fn fill_and_resume(
    core: &mut CoreArena,
    domain: &mut DomainArena,
    definitions: Definitions<'_>,
    fuel: Fuel,
    result: Glued,
    hole: HoleId,
    filling: TermId,
) -> Result<(Glued, Fuel), LiveFault>
{
    let (read, remaining) = read_written(core, domain, definitions, fuel, result, hole, filling)
        .map_err(LiveFault::Readback)?;
    match fill_hole(core, read, hole, filling) {
        | TermId::Value(value) => {
            let (filled, left) = eval_closed_value(core, domain, definitions, remaining, value)
                .map_err(LiveFault::Eval)?;
            Ok((Glued::Value(filled), left))
        },
        | TermId::Computation(comp) => {
            let (filled, left) = eval_comp_within(
                core,
                domain,
                definitions,
                remaining,
                comp,
                Environment::new(),
            )
            .map_err(LiveFault::Eval)?;
            Ok((Glued::Computation(filled), left))
        },
    }
}

/// Why classifying an arm stopped.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum MatchFault
{
    /// A scrutinee node, or a field span, does not resolve.
    Domain(DomainFault),
    /// A pattern id names nothing in the table.
    DanglingPattern,
    /// A domain literal names a core node that is not a literal.
    LiteralPayload,
    /// A pattern's former cannot classify the value it met: the arm and the
    /// scrutinee disagree on their type.
    Mismatched,
}

/// What one arm's pattern answers against a scrutinee.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Matched
{
    /// The pattern matches whatever any hole is filled with; the values its
    /// binders bind, left to right.
    Satisfied(Vec<DomainValueId>),
    /// A hole decides whether the pattern matches.
    Possibly,
    /// The pattern cannot match, whatever any hole is filled with.
    Refuted,
}

impl Matched
{
    /// The branch status this answer reports.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn status(&self) -> BranchStatus
    {
        match *self {
            | Self::Satisfied(_) => BranchStatus::Satisfied,
            | Self::Possibly => BranchStatus::Possibly,
            | Self::Refuted => BranchStatus::Refuted,
        }
    }
}

/// The position of an arm among a match's arms.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ArmIndex(usize);

impl From<usize> for ArmIndex
{
    /// Read a `usize` as an arm position.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(index: usize) -> Self
    {
        Self(index)
    }
}

impl From<ArmIndex> for usize
{
    /// The position an arm index names.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(arm: ArmIndex) -> Self
    {
        arm.0
    }
}

/// The arm a match takes, or why it takes none.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Selection
{
    /// The first arm not refuted matches whatever the holes are filled with.
    Taken
    {
        /// The arm.
        arm: ArmIndex,
        /// The values its binders bind, left to right.
        bindings: Vec<DomainValueId>,
    },
    /// The first arm not refuted only possibly matches: the match is
    /// indeterminate until a fill decides it.
    Indeterminate
    {
        /// The arm a hole decides.
        arm: ArmIndex,
    },
    /// Every arm is refuted.
    Exhausted,
}

/// Classify one arm's pattern against a scrutinee.
///
/// # Specification
/// - requires: `scrutinee` resolves in `domain`, and every pattern part
///   resolves in `patterns`.
/// - ensures: [`Matched::Refuted`] when some part's former disagrees with the
///   value it meets — another constructor, side or literal — whatever else
///   holds a hole; otherwise [`Matched::Possibly`] when some part is a pattern
///   hole or meets a neutral value, which a hole or a stuck elimination stands
///   behind; otherwise [`Matched::Satisfied`] with the binders' values in
///   left-to-right order. A wildcard and a binder match anything, a neutral
///   included; a lift is matched through.
/// - provides: live pattern matching's three-valued judgement, one arm at a
///   time, as a heap worklist over the pattern's parts.
/// - fails: [`MatchFault::Domain`] for a dangling node or field span,
///   [`MatchFault::DanglingPattern`] for a dangling part,
///   [`MatchFault::LiteralPayload`] for a literal naming no core literal, and
///   [`MatchFault::Mismatched`] when a former meets a value of another type or
///   a constructor pattern's arity differs from its value's.
/// - panics: none.
///
/// # Errors
/// As above.
///
/// # Adequacy
/// - hypothesis: L3 — an injection holding a hole against a wildcard, a
///   literal, the other side and a pattern hole separates satisfaction, doubt
///   from the scrutinee, refutation through doubt and doubt from the pattern; a
///   determinate pair of literals binds in order; a pair pattern against an
///   injection is a mismatch.
/// - witness: `live::tests::a_match_over_a_hole_answers_per_arm`
/// - witness: `live::tests::a_determinate_match_binds_left_to_right`
#[spec(ensures: |ret| match ret {
    Ok(Matched::Satisfied(_)) => patterns.pattern(pattern).is_some() && domain.value(scrutinee).is_some(),
    Ok(Matched::Possibly | Matched::Refuted) => domain.value(scrutinee).is_some(),
    Err(_) => true,
})]
#[inline]
pub fn match_pattern(
    core: &CoreArena,
    domain: &DomainArena,
    patterns: &Patterns,
    pattern: PatternId,
    scrutinee: DomainValueId,
) -> Result<Matched, MatchFault>
{
    let mut status = BranchStatus::Satisfied;
    let mut bindings = Vec::new();
    let mut pending = Vec::from([(pattern, scrutinee)]);
    while let Some((part, value)) = pending.pop() {
        let shape = patterns.pattern(part).ok_or(MatchFault::DanglingPattern)?;
        let node = *domain
            .value(value)
            .ok_or(MatchFault::Domain(DomainFault::Dangling))?;
        let local = match (shape, node) {
            | (&Pattern::Wildcard, _) => BranchStatus::Satisfied,
            | (&Pattern::Unit, DomainValue::Tuple { fields, .. }) => {
                if domain
                    .fields(fields)
                    .map_err(MatchFault::Domain)?
                    .is_empty()
                {
                    BranchStatus::Satisfied
                }
                else {
                    return Err(MatchFault::Mismatched);
                }
            },
            | (&Pattern::Binder, _) => {
                bindings.push(value);
                BranchStatus::Satisfied
            },
            | (&Pattern::Hole(_), _)
            | (
                &(Pattern::Unit
                | Pattern::Literal(_)
                | Pattern::Pair(..)
                | Pattern::Injection(..)
                | Pattern::Constructor { .. }),
                DomainValue::Neutral { .. },
            ) => BranchStatus::Possibly,
            | (
                &(Pattern::Unit
                | Pattern::Literal(_)
                | Pattern::Pair(..)
                | Pattern::Injection(..)
                | Pattern::Constructor { .. }),
                DomainValue::Lift { body, .. },
            ) => {
                pending.push((part, body));
                BranchStatus::Satisfied
            },
            | (&Pattern::Literal(ref expected), DomainValue::Literal { literal, .. }) => match core
                .value(literal)
            {
                | Some(&Value::Literal(ref found)) if found == expected => BranchStatus::Satisfied,
                | Some(&Value::Literal(_)) => BranchStatus::Refuted,
                | Some(_) | None => return Err(MatchFault::LiteralPayload),
            },
            | (&Pattern::Pair(first, second), DomainValue::Tuple { fields, .. }) => {
                let &[left, right] = domain.fields(fields).map_err(MatchFault::Domain)?
                else {
                    return Err(MatchFault::Mismatched);
                };
                pending.push((second, right));
                pending.push((first, left));
                BranchStatus::Satisfied
            },
            | (
                &Pattern::Injection(side, body),
                DomainValue::Injection {
                    summand: found,
                    body: inner,
                    ..
                },
            ) => {
                if Summand::from(side) == found {
                    pending.push((body, inner));
                    BranchStatus::Satisfied
                }
                else {
                    BranchStatus::Refuted
                }
            },
            | (
                &Pattern::Constructor { tag, ref fields },
                DomainValue::Constructor {
                    tag: found,
                    fields: span,
                    ..
                },
            ) => {
                if tag == found {
                    let values = domain.fields(span).map_err(MatchFault::Domain)?;
                    if values.len() != fields.len() {
                        return Err(MatchFault::Mismatched);
                    }
                    pending.extend(fields.iter().copied().zip(values.iter().copied()).rev());
                    BranchStatus::Satisfied
                }
                else {
                    BranchStatus::Refuted
                }
            },
            | (
                &(Pattern::Unit
                | Pattern::Literal(_)
                | Pattern::Pair(..)
                | Pattern::Injection(..)
                | Pattern::Constructor { .. }),
                DomainValue::Constructor { .. }
                | DomainValue::Record { .. }
                | DomainValue::PathCertificate { .. }
                | DomainValue::PathProduct { .. }
                | DomainValue::Here { .. }
                | DomainValue::Tuple { .. }
                | DomainValue::Literal { .. }
                | DomainValue::Injection { .. }
                | DomainValue::Thunk { .. }
                | DomainValue::Code { .. }
                | DomainValue::StaticLambda { .. }
                | DomainValue::ListNil { .. }
                | DomainValue::ListCons { .. },
            ) => return Err(MatchFault::Mismatched),
        };
        status = status.and(local);
        if status == BranchStatus::Refuted {
            return Ok(Matched::Refuted);
        }
    }
    Ok(match status {
        | BranchStatus::Satisfied => Matched::Satisfied(bindings),
        | BranchStatus::Possibly => Matched::Possibly,
        | BranchStatus::Refuted => Matched::Refuted,
    })
}

/// Choose the arm a match over `scrutinee` takes.
///
/// # Specification
/// - requires: as [`match_pattern`], for every arm.
/// - ensures: the first arm [`match_pattern`] does not refute — taken with its
///   bindings when it is satisfied, indeterminate when it is only possible — or
///   [`Selection::Exhausted`] when every arm is refuted. Arms after the first
///   not refuted are not classified.
/// - provides: live match evaluation: a match on a hole is indeterminate rather
///   than taking an arm the fill may yet rule out.
/// - fails: whatever [`match_pattern`] refuses for an arm it reaches.
/// - panics: none.
///
/// # Errors
/// As above.
///
/// # Adequacy
/// - hypothesis: L3 — a refuted first arm skipped, a possible second arm
///   stopping the match before a satisfied third, a determinate scrutinee
///   taking its arm with bindings, and a scrutinee every arm refutes.
/// - witness: `live::tests::a_match_over_a_hole_answers_per_arm`
/// - witness: `live::tests::a_determinate_match_binds_left_to_right`
#[spec(ensures: |ret| match ret {
    Ok(Selection::Taken { arm, .. } | Selection::Indeterminate { arm }) => arm.0 < arms.len(),
    Ok(Selection::Exhausted) | Err(_) => true,
})]
#[inline]
pub fn select_arm(
    core: &CoreArena,
    domain: &DomainArena,
    patterns: &Patterns,
    arms: &[PatternId],
    scrutinee: DomainValueId,
) -> Result<Selection, MatchFault>
{
    for (index, &arm) in arms.iter().enumerate() {
        match match_pattern(core, domain, patterns, arm, scrutinee)? {
            | Matched::Satisfied(bindings) => {
                return Ok(Selection::Taken {
                    arm: ArmIndex(index),
                    bindings,
                });
            },
            | Matched::Possibly => {
                return Ok(Selection::Indeterminate {
                    arm: ArmIndex(index),
                });
            },
            | Matched::Refuted => {},
        }
    }
    Ok(Selection::Exhausted)
}

#[cfg(test)]
mod tests
{
    use alloc::string::String;
    use alloc::vec;

    use gandr_core_term::CertificateEquality;
    use gandr_core_term::Computation;
    use gandr_core_term::CoreArena;
    use gandr_core_term::DefinitionalEnvironment;
    use gandr_core_term::ValueId;
    use gandr_core_term::Zone;
    use gandr_core_term::equal_certificate_syntax;
    use gandr_core_term::fill_hole;
    use gandr_core_term::hole::HoleId;
    use gandr_core_term::hole::MarkIndex;
    use gandr_core_term::hole::TermId;
    use gandr_core_term::pattern::BranchStatus;
    use gandr_core_term::pattern::Pattern;
    use gandr_core_term::pattern::Patterns;
    use gandr_kernel_check_memo::NullMemo;
    use gandr_kernel_conversion_trace::NullSink;
    use gandr_kernel_term::DeBruijnIndex;
    use gandr_kernel_term::Literal;
    use gandr_kernel_term::Side;
    use gandr_kernel_term::StringLiteral;

    use super::ArmIndex;
    use super::Matched;
    use super::Selection;
    use super::fill_and_resume;
    use super::match_pattern;
    use super::select_arm;
    use crate::arena::DomainArena;
    use crate::closure::ValueBody;
    use crate::conv::Deferral;
    use crate::conv::Settlement;
    use crate::conv::convert_values;
    use crate::domain::DomainComp;
    use crate::domain::DomainValue;
    use crate::domain::Glued;
    use crate::domain::NeutralHead;
    use crate::domain::Suspended;
    use crate::eval::Definitions;
    use crate::eval::Fuel;
    use crate::eval::LoweredChain;
    use crate::eval::eval_computation;
    use crate::eval::eval_value;
    use crate::machine::DeclineReason;
    use crate::machine::MachineSettings;
    use crate::machine::MachineVerdict;
    use crate::machine::Problem;
    use crate::machine::decide;
    use crate::readback::ReadbackMode;
    use crate::readback::readback_computation;
    use crate::readback::readback_value;

    /// A budget far above the step count any fixture below needs.
    ///
    /// # Specification
    /// trivial.
    fn ample() -> Fuel
    {
        Fuel::from(100_000_u32)
    }

    /// The text literal `five`.
    ///
    /// # Specification
    /// trivial.
    fn literal_five(core: &mut CoreArena) -> ValueId
    {
        core.value_literal(Literal::Text(StringLiteral::new(String::from("five"))))
    }

    /// The text literal `six`.
    ///
    /// # Specification
    /// trivial.
    fn literal_six(core: &mut CoreArena) -> ValueId
    {
        core.value_literal(Literal::Text(StringLiteral::new(String::from("six"))))
    }

    /// The variable at the innermost binder.
    ///
    /// # Specification
    /// trivial.
    fn innermost(core: &mut CoreArena) -> ValueId
    {
        core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32))
    }

    #[test]
    fn a_hole_evaluates_to_a_neutral_carrying_its_environment()
    {
        let mut core = CoreArena::new();
        let five = literal_five(&mut core);
        let hole = HoleId::from(0_u32);
        let standing = core.value_hole(hole);
        let returned = core.computation_return(standing);
        let lambda = core.computation_lambda(returned);
        let applied = core.computation_application(lambda, five);
        let chain = LoweredChain::new();
        let environment = DefinitionalEnvironment::new();
        let definitions = Definitions::new(&chain, &environment, environment.root());
        let mut domain = DomainArena::new();

        let evaluated = eval_computation(&core, &mut domain, definitions, ample(), applied)
            .expect("a hole does not stop evaluation");
        let Some(&DomainComp::Return { value, .. }) = domain.computation(evaluated)
        else {
            panic!("the redex fires around the hole and returns");
        };
        let Some(&DomainValue::Neutral { neutral, .. }) = domain.value(value)
        else {
            panic!("the hole stands as a neutral");
        };
        let held = domain.neutral(neutral).expect("the neutral resolves");
        let NeutralHead::Hole {
            hole: named,
            closure: Suspended::Value(closure),
        } = held.head()
        else {
            panic!("the hole is the neutral's head, in value position");
        };
        assert_eq!(named, hole);
        assert!(held.spine().is_empty(), "nothing eliminated the hole");
        let closure = domain.value_closure(closure).expect("the closure resolves");
        assert_eq!(
            closure.body(),
            ValueBody::Source(standing),
            "the closure suspends the hole itself"
        );
        let bound = closure
            .environment()
            .lookup(Zone::Intuitionistic, DeBruijnIndex::from(0_u32))
            .expect("the argument the hole was met under is in its environment");
        assert!(
            matches!(domain.value(bound), Some(&DomainValue::Literal { literal, .. }) if literal == five),
            "the environment binds the argument"
        );

        let read = readback_computation(
            &mut core,
            &mut domain,
            definitions,
            ReadbackMode::Unfolding,
            ample(),
            evaluated,
        )
        .expect("an indeterminate result reads back");
        assert!(
            matches!(core.computation(read), Some(&Computation::Return(read_hole)) if read_hole == standing),
            "a hole reads back as itself"
        );
    }

    #[test]
    fn a_computation_hole_keeps_the_eliminations_that_could_not_fire()
    {
        let mut core = CoreArena::new();
        let five = literal_five(&mut core);
        let hole = HoleId::from(1_u32);
        let head = core.computation_hole(hole);
        let applied = core.computation_application(head, five);
        let chain = LoweredChain::new();
        let environment = DefinitionalEnvironment::new();
        let definitions = Definitions::new(&chain, &environment, environment.root());
        let mut domain = DomainArena::new();

        let evaluated = eval_computation(&core, &mut domain, definitions, ample(), applied)
            .expect("an applied hole evaluates");
        let Some(&DomainComp::Neutral { neutral, .. }) = domain.computation(evaluated)
        else {
            panic!("an applied hole is stuck");
        };
        let held = domain.neutral(neutral).expect("the neutral resolves");
        assert!(
            matches!(
                held.head(),
                NeutralHead::Hole { hole: named, closure: Suspended::Computation(_) } if named == hole
            ),
            "the hole is the head, in computation position"
        );
        assert_eq!(held.spine().len(), 1, "the application waits on the hole");

        let read = readback_computation(
            &mut core,
            &mut domain,
            definitions,
            ReadbackMode::Unfolding,
            ample(),
            evaluated,
        )
        .expect("a stuck application reads back");
        let Some(&Computation::Application(read_head, argument)) = core.computation(read)
        else {
            panic!("the elimination folds back over the hole");
        };
        assert_eq!(core.computation(read_head), Some(&Computation::Hole(hole)));
        assert_eq!(
            equal_certificate_syntax(&core, argument, five),
            CertificateEquality::Equal
        );

        let body = returned_innermost(&mut core);
        let filling = core.computation_lambda(body);
        let (filled, _) = fill_and_resume(
            &mut core,
            &mut domain,
            definitions,
            ample(),
            Glued::Computation(evaluated),
            hole,
            TermId::Computation(filling),
        )
        .expect("a computation hole fills");
        let Glued::Computation(filled) = filled
        else {
            panic!("a computation result stays a computation");
        };
        let Some(&DomainComp::Return { value, .. }) = domain.computation(filled)
        else {
            panic!("the application fires once its head is a lambda");
        };
        assert!(
            matches!(domain.value(value), Some(&DomainValue::Literal { .. })),
            "and returns its argument"
        );
    }

    /// A return of the variable at the innermost binder.
    ///
    /// # Specification
    /// trivial.
    fn returned_innermost(core: &mut CoreArena) -> gandr_core_term::ComputationId
    {
        let occurrence = innermost(core);
        core.computation_return(occurrence)
    }

    #[test]
    fn a_mark_reads_back_through_its_environment()
    {
        let mut core = CoreArena::new();
        let five = literal_five(&mut core);
        let occurrence = innermost(&mut core);
        let mark = MarkIndex::from(0_u32);
        let marked = core.value_mark(mark, occurrence);
        let returned = core.computation_return(marked);
        let lambda = core.computation_lambda(returned);
        let applied = core.computation_application(lambda, five);
        let closed = core.value_mark(mark, five);
        let chain = LoweredChain::new();
        let environment = DefinitionalEnvironment::new();
        let definitions = Definitions::new(&chain, &environment, environment.root());
        let mut domain = DomainArena::new();

        let evaluated = eval_computation(&core, &mut domain, definitions, ample(), applied)
            .expect("a mark does not stop evaluation");
        let read = readback_computation(
            &mut core,
            &mut domain,
            definitions,
            ReadbackMode::Unfolding,
            ample(),
            evaluated,
        )
        .expect("a marked result reads back");
        let Some(&Computation::Return(read_mark)) = core.computation(read)
        else {
            panic!("the redex fires around the mark");
        };
        assert_eq!(
            equal_certificate_syntax(&core, read_mark, closed),
            CertificateEquality::Equal,
            "the mark's body reads the argument its environment binds"
        );
        assert_ne!(read_mark, marked, "a substituted mark is a new term");

        let alone = eval_value(&core, &mut domain, definitions, ample(), closed)
            .expect("a closed mark evaluates");
        let read_alone = readback_value(
            &mut core,
            &mut domain,
            definitions,
            ReadbackMode::Unfolding,
            ample(),
            alone,
        )
        .expect("a closed mark reads back");
        assert_eq!(read_alone, closed, "a mark met in no environment is itself");
    }

    #[test]
    fn a_comparison_that_meets_a_hole_declines()
    {
        let mut core = CoreArena::new();
        let five = literal_five(&mut core);
        let six = literal_six(&mut core);
        let hole = core.value_hole(HoleId::from(0_u32));
        let other = core.value_hole(HoleId::from(0_u32));
        let left_pair = core.value_tuple(&[hole, five]);
        let right_pair = core.value_tuple(&[other, six]);
        let chain = LoweredChain::new();
        let environment = DefinitionalEnvironment::new();
        let definitions = Definitions::new(&chain, &environment, environment.root());
        let mut domain = DomainArena::new();
        let mut eval = |term| {
            eval_value(&core, &mut domain, definitions, ample(), term).expect("closed values")
        };
        let (hole, other, five, left_pair, right_pair) = (
            eval(hole),
            eval(other),
            eval(five),
            eval(left_pair),
            eval(right_pair),
        );

        assert_eq!(
            convert_values(&core, &domain, hole, five),
            Ok(Settlement::Deferred(Deferral::Indeterminate)),
            "a hole against a literal is not apart: a fill may write the literal"
        );
        assert_eq!(
            convert_values(&core, &domain, hole, other),
            Ok(Settlement::Deferred(Deferral::Indeterminate)),
            "two occurrences of one hole may still be filled apart"
        );
        let mut decided = |left, right| {
            decide::<NullSink, NullMemo>(
                &core,
                &mut domain,
                definitions,
                MachineSettings::default(),
                Problem::values(left, right),
                &mut NullSink,
            )
            .expect("the machine answers")
            .verdict()
        };
        assert_eq!(
            decided(hole, five),
            MachineVerdict::Declined(DeclineReason::Indeterminate),
            "the machine declines rather than refuting"
        );
        assert_eq!(
            decided(hole, other),
            MachineVerdict::Declined(DeclineReason::Indeterminate)
        );
        assert_eq!(
            decided(left_pair, right_pair),
            MachineVerdict::NotConvertible,
            "a difference beside the hole refutes whatever the fill"
        );
        assert_eq!(
            decided(hole, hole),
            MachineVerdict::Convertible,
            "one node is itself"
        );
    }

    #[test]
    fn filling_resumes_where_the_hole_stood()
    {
        let mut core = CoreArena::new();
        let five = literal_five(&mut core);
        let hole = HoleId::from(0_u32);
        let standing = core.value_hole(hole);
        let forced = core.computation_force(standing);
        let lambda = core.computation_lambda(forced);
        let returned = core.computation_return(five);
        let thunk = core.value_thunk(returned);
        let program = core.computation_application(lambda, thunk);
        let filling = innermost(&mut core);
        let chain = LoweredChain::new();
        let environment = DefinitionalEnvironment::new();
        let definitions = Definitions::new(&chain, &environment, environment.root());
        let mut domain = DomainArena::new();

        let evaluated = eval_computation(&core, &mut domain, definitions, ample(), program)
            .expect("the program runs to the hole");
        assert!(
            matches!(
                domain.computation(evaluated),
                Some(DomainComp::Neutral { .. })
            ),
            "the force is stuck on the hole"
        );
        let (filled, _) = fill_and_resume(
            &mut core,
            &mut domain,
            definitions,
            ample(),
            Glued::Computation(evaluated),
            hole,
            TermId::Value(filling),
        )
        .expect("the fill resumes");
        let Glued::Computation(filled) = filled
        else {
            panic!("a computation result stays a computation");
        };
        let resumed = readback_computation(
            &mut core,
            &mut domain,
            definitions,
            ReadbackMode::Unfolding,
            ample(),
            filled,
        )
        .expect("the resumed result reads back");

        let TermId::Computation(written) = fill_hole(
            &mut core,
            TermId::Computation(program),
            hole,
            TermId::Value(filling),
        )
        else {
            panic!("filling a computation leaves a computation");
        };
        let direct = eval_computation(&core, &mut domain, definitions, ample(), written)
            .expect("the filled program runs");
        let expected = readback_computation(
            &mut core,
            &mut domain,
            definitions,
            ReadbackMode::Unfolding,
            ample(),
            direct,
        )
        .expect("the filled program's result reads back");
        let (Some(&Computation::Return(resumed)), Some(&Computation::Return(expected))) =
            (core.computation(resumed), core.computation(expected))
        else {
            panic!("both force the bound thunk and return");
        };
        assert_eq!(
            equal_certificate_syntax(&core, resumed, expected),
            CertificateEquality::Equal,
            "filling the result agrees with running the filled program"
        );
        assert_eq!(
            equal_certificate_syntax(&core, resumed, five),
            CertificateEquality::Equal,
            "and both return what the thunk the filling reads returns"
        );
    }

    #[test]
    fn a_fill_leaves_other_holes_standing()
    {
        let mut core = CoreArena::new();
        let five = literal_five(&mut core);
        let first = HoleId::from(0_u32);
        let second = HoleId::from(1_u32);
        let written = core.value_hole(first);
        let standing = core.value_hole(second);
        let pair = core.value_tuple(&[written, standing]);
        let returned = core.computation_return(pair);
        let lambda = core.computation_lambda(returned);
        let program = core.computation_application(lambda, five);
        let filling = innermost(&mut core);
        let chain = LoweredChain::new();
        let environment = DefinitionalEnvironment::new();
        let definitions = Definitions::new(&chain, &environment, environment.root());
        let mut domain = DomainArena::new();

        let evaluated = eval_computation(&core, &mut domain, definitions, ample(), program)
            .expect("the program runs");
        let (filled, _) = fill_and_resume(
            &mut core,
            &mut domain,
            definitions,
            ample(),
            Glued::Computation(evaluated),
            first,
            TermId::Value(filling),
        )
        .expect("the fill resumes");
        let Glued::Computation(filled) = filled
        else {
            panic!("a computation result stays a computation");
        };
        let read = readback_computation(
            &mut core,
            &mut domain,
            definitions,
            ReadbackMode::Unfolding,
            ample(),
            filled,
        )
        .expect("the filled result reads back");
        let expected_pair = core.value_tuple(&[five, standing]);
        let Some(&Computation::Return(read_pair)) = core.computation(read)
        else {
            panic!("the result still returns");
        };
        assert_eq!(
            equal_certificate_syntax(&core, read_pair, expected_pair),
            CertificateEquality::Equal,
            "the written hole reads the bound argument and the other stands"
        );
    }

    #[test]
    fn a_match_over_a_hole_answers_per_arm()
    {
        let mut core = CoreArena::new();
        let three = Literal::Text(StringLiteral::new(String::from("three")));
        let hole = core.value_hole(HoleId::from(0_u32));
        let injected = core.value_injection(Side::Left.into(), hole);
        let chain = LoweredChain::new();
        let environment = DefinitionalEnvironment::new();
        let definitions = Definitions::new(&chain, &environment, environment.root());
        let mut domain = DomainArena::new();
        let scrutinee = eval_value(&core, &mut domain, definitions, ample(), injected)
            .expect("an injected hole evaluates");

        let mut patterns = Patterns::new();
        let wildcard = patterns.mint(Pattern::Wildcard);
        let literal = patterns.mint(Pattern::Literal(three));
        let pattern_hole = patterns.mint(Pattern::Hole(HoleId::from(7_u32)));
        let right = patterns.mint(Pattern::Injection(Side::Right, wildcard));
        let left_literal = patterns.mint(Pattern::Injection(Side::Left, literal));
        let left_any = patterns.mint(Pattern::Injection(Side::Left, wildcard));
        let pair = patterns.mint(Pattern::Pair(wildcard, wildcard));

        let status = |arm| {
            match_pattern(&core, &domain, &patterns, arm, scrutinee)
                .expect("the arm classifies")
                .status()
        };
        assert_eq!(status(right), BranchStatus::Refuted, "the side is known");
        assert_eq!(
            status(left_literal),
            BranchStatus::Possibly,
            "the hole inside decides the literal"
        );
        assert_eq!(
            status(left_any),
            BranchStatus::Satisfied,
            "a wildcard decides nothing"
        );
        assert_eq!(
            status(pattern_hole),
            BranchStatus::Possibly,
            "a pattern hole decides itself"
        );
        assert_eq!(
            match_pattern(&core, &domain, &patterns, pair, scrutinee),
            Err(super::MatchFault::Mismatched),
            "a pair pattern cannot classify an injection"
        );
        assert_eq!(
            select_arm(
                &core,
                &domain,
                &patterns,
                &[right, left_literal, left_any],
                scrutinee
            ),
            Ok(Selection::Indeterminate {
                arm: ArmIndex::from(1_usize)
            }),
            "the match stops at the first arm a hole decides"
        );
        assert_eq!(
            select_arm(&core, &domain, &patterns, &[right], scrutinee),
            Ok(Selection::Exhausted)
        );
    }

    #[test]
    fn a_determinate_match_binds_left_to_right()
    {
        let mut core = CoreArena::new();
        let five = literal_five(&mut core);
        let six = literal_six(&mut core);
        let pair = core.value_tuple(&[five, six]);
        let chain = LoweredChain::new();
        let environment = DefinitionalEnvironment::new();
        let definitions = Definitions::new(&chain, &environment, environment.root());
        let mut domain = DomainArena::new();
        let scrutinee =
            eval_value(&core, &mut domain, definitions, ample(), pair).expect("a pair evaluates");
        let Some(&[first, second]) = domain
            .value(scrutinee)
            .and_then(|held| domain.components(held))
        else {
            panic!("a pair evaluates to a pair");
        };

        let mut patterns = Patterns::new();
        let binder = patterns.mint(Pattern::Binder);
        let six_pattern = patterns.mint(Pattern::Literal(Literal::Text(StringLiteral::new(
            String::from("six"),
        ))));
        let five_pattern = patterns.mint(Pattern::Literal(Literal::Text(StringLiteral::new(
            String::from("five"),
        ))));
        let both = patterns.mint(Pattern::Pair(binder, binder));
        let wrong = patterns.mint(Pattern::Pair(binder, five_pattern));
        let right = patterns.mint(Pattern::Pair(binder, six_pattern));

        assert_eq!(
            match_pattern(&core, &domain, &patterns, both, scrutinee),
            Ok(Matched::Satisfied(vec![first, second])),
            "binders bind left to right"
        );
        assert_eq!(
            select_arm(&core, &domain, &patterns, &[wrong, right], scrutinee),
            Ok(Selection::Taken {
                arm: ArmIndex::from(1_usize),
                bindings: vec![first]
            }),
            "a determinate scrutinee takes the first arm that matches"
        );
    }
}
