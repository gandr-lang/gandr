//! Superinstructions: two adjacent stencils run as one, each fusion a
//! decision that a search-free replay re-derives.
//!
//! A bind is a seq. `⟨p |+ μ̃x. s⟩` runs `p`, delivers its value to `x` and
//! runs `s`, handing the value over in the value register. Where the lowering
//! emits `const a` and then `bind s`, and no label enters the `bind`, the two
//! run as one instruction, `const_bind a s`, which leaves the window and the
//! registers as the pair does. That is [`Rule::ConstBind`]: a rewrite over the
//! instruction alphabet by seq associativity, the handoff a linear edge. Every
//! other instruction is kept.
//!
//! [`fuse`] scans for each rule's left side and records every match as a
//! [`Fused`] decision. [`replay`] re-derives the fused function from the
//! unfused one and the decisions alone, in order. It refuses a decision whose
//! position does not hold the rule's left side, one a label enters between,
//! and one that does not follow the decision before it. The function [`fuse`]
//! answers is the replay's.
//!
//! # Cost
//!
//! The stencil table charges every stencil one dispatch ([`dispatches`]). A
//! decision runs two instructions as one, so a fused function holds exactly
//! one dispatch fewer per decision, and every run through a fused pair takes
//! one dispatch fewer than the same run unfused.

use alloc::vec::Vec;

use gandr_runtime_stencils::StencilId;

use crate::function::Alt;
use crate::function::Function;
use crate::function::Instruction;
use crate::function::Operand;
use crate::function::Position;

/// A rewrite of the instruction alphabet: two stencils in sequence, the
/// first's value handed to the second in the value register, run as one.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Rule
{
    /// `const a · bind s ⇒ const_bind a s`: a constant loaded and bound.
    ConstBind,
}

impl Rule
{
    /// Every rule, in the order [`fuse`] tries them.
    pub const ALL: [Self; 1] = [Self::ConstBind];

    /// The rule's left side: the two stencils it fuses, in order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn left(self) -> [StencilId; 2]
    {
        match self {
            Self::ConstBind => [StencilId::Const, StencilId::Bind],
        }
    }

    /// The rule's right side: the stencil that runs the two.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn right(self) -> StencilId
    {
        match self {
            Self::ConstBind => StencilId::ConstBind,
        }
    }

    /// The one instruction running `first` then `second`, when they are the
    /// rule's left side.
    ///
    /// # Specification
    /// - ensures: present exactly when `first` and `second` run the left side's
    ///   stencils, neither has a second continuation, and each leaves operand B
    ///   unread; then the right side's stencil, `first`'s operand A as its A
    ///   and `second`'s operand A as its B.
    /// - panics: none.
    /// - executable: none — the clause is the match itself.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a constant and a bind fuse; a constant before any
    ///   other stencil does not.
    /// - witness: `fuse::tests::a_constant_bound_runs_as_one_dispatch`
    /// - witness: `fuse::tests::a_forged_decision_is_refused_by_name`
    fn fused(
        self,
        first: Instruction,
        second: Instruction,
    ) -> Option<Instruction>
    {
        let [head, tail] = self.left();
        let alone = |instruction: Instruction| {
            instruction.alt == Alt::None && instruction.b == Operand::Unused
        };
        (first.stencil == head && second.stencil == tail && alone(first) && alone(second)).then(
            || Instruction {
                stencil: self.right(),
                a: first.a,
                b: second.a,
                alt: Alt::None,
            },
        )
    }
}

/// One fusion: the position, in the unfused function, of the pair's first
/// instruction, and the rule that fused it.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct Fused
{
    /// The pair's first instruction.
    pub at: Position,
    /// The rule.
    pub rule: Rule,
}

/// Why a replay refused a decision.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum FusionRefusal
{
    /// The decision's position does not hold the rule's left side.
    Unmatched(Fused),
    /// A label enters the pair's second instruction, so the two do not run in
    /// sequence on every path.
    Entered(Fused),
    /// The decision does not follow the one before it: its pair overlaps the
    /// last one or comes before it.
    Unordered(Fused),
}

/// How many dispatches a function's instructions cost, one per stencil.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Dispatches(pub usize);

/// The dispatches `function` costs: one per instruction, the stencil table's
/// charge for every stencil.
///
/// # Specification
/// trivial.
#[inline]
#[must_use]
pub fn dispatches(function: &Function) -> Dispatches
{
    Dispatches(function.instructions().len())
}

/// Fuse every pair of `function` some rule's left side matches and no label
/// enters between: the fused function and its trace of decisions.
///
/// # Specification
/// - ensures: the trace names each such pair once, ascending, the leftmost
///   match taken first; the function is [`replay`] of the trace over
///   `function`, which costs one dispatch fewer per decision.
/// - panics: none.
/// - executable: none — the clause would replay the trace, which the body
///   already does to build the result.
///
/// # Adequacy
/// - hypothesis: L2 — every named, generated and corpus program runs fused and
///   unfused with equal outcomes, and the run asserts that fusions occur; L3 —
///   a constant bound, a pair a label enters and a label past a fused pair.
/// - witness: `fuse::tests::a_constant_bound_runs_as_one_dispatch`
/// - witness: `fuse::tests::a_pair_a_label_enters_is_kept_apart`
/// - witness: `fuse::tests::a_label_past_a_fused_pair_names_its_instruction`
#[inline]
#[must_use]
pub fn fuse(function: &Function) -> (Function, Vec<Fused>)
{
    let instructions = function.instructions();
    let entries = function.entries();
    let mut trace = Vec::new();
    let mut index = 0_usize;
    while let (Some(&first), Some(&second)) = (
        instructions.get(index),
        instructions.get(index.saturating_add(1)),
    ) {
        let next = Position(index.saturating_add(1));
        let rule = Rule::ALL
            .into_iter()
            .find(|rule| rule.fused(first, second).is_some());
        match rule {
            Some(rule) if entries.binary_search(&next).is_err() => {
                trace.push(Fused {
                    at: Position(index),
                    rule,
                });
                index = index.saturating_add(2);
            },
            Some(_) | None => index = index.saturating_add(1),
        }
    }
    // The scan proposes only pairs the replay accepts; were it to propose
    // another, the function runs unfused.
    replay(function, &trace).map_or_else(|_| (function.clone(), Vec::new()), |fused| (fused, trace))
}

/// Re-derive the function `trace` fuses from `function`, in order, searching
/// for nothing.
///
/// # Specification
/// - ensures: on success one instruction fewer per decision, each decision's
///   pair run as its rule's right side and every label naming the instruction
///   it named.
/// - fails: [`FusionRefusal::Unordered`] for a decision at or before the
///   previous pair's second instruction, [`FusionRefusal::Unmatched`] for one
///   whose position does not hold its rule's left side, and
///   [`FusionRefusal::Entered`] for one whose second instruction a label
///   enters; the first such decision is named.
/// - panics: none.
/// - executable: none — the clause would re-run the checks the body makes.
///
/// # Errors
/// As above.
///
/// # Adequacy
/// - hypothesis: L3 — a trace [`fuse`] made replays to its function, and a
///   forged, an entered and an overlapping decision are each refused by name.
/// - witness: `fuse::tests::a_forged_decision_is_refused_by_name`
/// - witness: `fuse::tests::a_constant_bound_runs_as_one_dispatch`
#[inline]
pub fn replay(
    function: &Function,
    trace: &[Fused],
) -> Result<Function, FusionRefusal>
{
    let instructions = function.instructions();
    let entries = function.entries();
    let mut merges = Vec::with_capacity(trace.len());
    let mut free = 0_usize;
    for &decision in trace {
        let Position(at) = decision.at;
        if at < free {
            return Err(FusionRefusal::Unordered(decision));
        }
        let second = at.saturating_add(1);
        let fused = match (instructions.get(at), instructions.get(second)) {
            (Some(&first), Some(&next)) => decision.rule.fused(first, next),
            (Some(_) | None, _) => None,
        };
        let Some(fused) = fused
        else {
            return Err(FusionRefusal::Unmatched(decision));
        };
        if entries.binary_search(&Position(second)).is_ok() {
            return Err(FusionRefusal::Entered(decision));
        }
        merges.push((decision.at, fused));
        free = second.saturating_add(1);
    }
    Ok(function.merged(&merges))
}

#[cfg(test)]
mod tests
{
    use super::*;
    use crate::function::Constant;
    use crate::function::Immediate;

    /// `const` at constant `at`.
    ///
    /// # Specification
    /// trivial.
    fn constant(at: Constant) -> Instruction
    {
        Instruction {
            stencil: StencilId::Const,
            a: Operand::Data(at),
            b: Operand::Unused,
            alt: Alt::None,
        }
    }

    /// `stencil` reading slot `slot` as operand A.
    ///
    /// # Specification
    /// trivial.
    fn slotted(
        stencil: StencilId,
        slot: Immediate,
    ) -> Instruction
    {
        Instruction {
            stencil,
            a: Operand::Immediate(slot),
            b: Operand::Unused,
            alt: Alt::None,
        }
    }

    /// `ret`.
    ///
    /// # Specification
    /// trivial.
    fn ret() -> Instruction
    {
        Instruction {
            stencil: StencilId::Ret,
            a: Operand::Unused,
            b: Operand::Unused,
            alt: Alt::None,
        }
    }

    #[test]
    fn a_constant_bound_runs_as_one_dispatch()
    {
        let mut function = Function::default();
        let at = function.constant(&[gandr_runtime_stencils::Word::ZERO]);
        let _bound = function.push(constant(at));
        let _bind = function.push(slotted(StencilId::Bind, Immediate::from(0_u32)));
        let _read = function.push(slotted(StencilId::Var, Immediate::from(0_u32)));
        let _ret = function.push(ret());
        let (fused, trace) = fuse(&function);
        assert_eq!(trace, [Fused {
            at: Position(0),
            rule: Rule::ConstBind,
        }]);
        assert_eq!(fused.instructions(), [
            Instruction {
                stencil: StencilId::ConstBind,
                a: Operand::Data(at),
                b: Operand::Immediate(Immediate::from(0_u32)),
                alt: Alt::None,
            },
            slotted(StencilId::Var, Immediate::from(0_u32)),
            ret(),
        ]);
        assert_eq!(dispatches(&fused), Dispatches(3));
        assert_eq!(dispatches(&function), Dispatches(4));
        assert_eq!(replay(&function, &trace), Ok(fused));
    }

    #[test]
    fn a_pair_a_label_enters_is_kept_apart()
    {
        let mut function = Function::default();
        let at = function.constant(&[gandr_runtime_stencils::Word::ZERO]);
        let entered = function.label();
        let _bound = function.push(constant(at));
        function.bind(entered);
        let _bind = function.push(slotted(StencilId::Bind, Immediate::from(0_u32)));
        let _ret = function.push(ret());
        let (fused, trace) = fuse(&function);
        assert_eq!(trace, []);
        assert_eq!(fused, function);
        assert_eq!(
            replay(&function, &[Fused {
                at: Position(0),
                rule: Rule::ConstBind,
            }]),
            Err(FusionRefusal::Entered(Fused {
                at: Position(0),
                rule: Rule::ConstBind,
            }))
        );
    }

    #[test]
    fn a_label_past_a_fused_pair_names_its_instruction()
    {
        let mut function = Function::default();
        let at = function.constant(&[gandr_runtime_stencils::Word::ZERO]);
        let head = function.label();
        let tail = function.label();
        function.bind(head);
        let _bound = function.push(constant(at));
        let _bind = function.push(slotted(StencilId::Bind, Immediate::from(1_u32)));
        function.bind(tail);
        let _read = function.push(slotted(StencilId::Var, Immediate::from(1_u32)));
        let _ret = function.push(ret());
        let (fused, _trace) = fuse(&function);
        assert_eq!(fused.target(head), Ok(Position(0)));
        assert_eq!(fused.target(tail), Ok(Position(1)));
        assert_eq!(
            fused
                .instructions()
                .get(1)
                .map(|instruction| instruction.stencil),
            Some(StencilId::Var)
        );
    }

    #[test]
    fn a_forged_decision_is_refused_by_name()
    {
        let mut function = Function::default();
        let at = function.constant(&[gandr_runtime_stencils::Word::ZERO]);
        let _bound = function.push(constant(at));
        let _push = function.push(slotted(StencilId::Push, Immediate::from(0_u32)));
        let _again = function.push(constant(at));
        let _bind = function.push(slotted(StencilId::Bind, Immediate::from(0_u32)));
        let _ret = function.push(ret());
        let forged = Fused {
            at: Position(0),
            rule: Rule::ConstBind,
        };
        assert_eq!(
            replay(&function, &[forged]),
            Err(FusionRefusal::Unmatched(forged))
        );
        let made = Fused {
            at: Position(2),
            rule: Rule::ConstBind,
        };
        assert_eq!(fuse(&function).1, [made]);
        assert_eq!(
            replay(&function, &[made, made]),
            Err(FusionRefusal::Unordered(made))
        );
    }
}
