//! The body a ruled definition carries is its rules' decision tree.
//!
//! An operation lowers to `thunk(fix f. λx₁…λxₙ. t)`, `t` a tree of cases on
//! the inputs and the fields earlier cases bound, each branch one lambda per
//! field of its constructor. Each leaf of the tree must be the right side of
//! a rule whose left side matches what the cases above the leaf learned,
//! minted as the lowering mints one: every call below the root bound in
//! post-order, the root returned, delivered as one tuple or called last. A
//! call of the operation itself is a call of the fixpoint's binder. The leaf
//! and the minted side are compared by the kernel's own conversion.
//!
//! Together with the rules' convergence this makes the body compute what the
//! rules compute: a closed call walks the tree to one leaf, which is one step
//! of a rule, and the recursive calls it makes are calls of the same rules.

use alloc::vec::Vec;

use anodized::spec;
use gandr_kernel_term::CompType;
use gandr_kernel_term::Computation;
use gandr_kernel_term::ComputationId;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::ConstructorTag;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::DeclarationContent;
use gandr_kernel_term::FieldCount;
use gandr_kernel_term::OperationNode;
use gandr_kernel_term::OperationRule;
use gandr_kernel_term::OperationRules;
use gandr_kernel_term::RuleIndex;
use gandr_kernel_term::TermArena;
use gandr_kernel_term::Value;
use gandr_kernel_term::ValueId;
use gandr_kernel_term::ValueType;
use gandr_kernel_term::ValueTypeId;

use crate::env::AdmittedDeclaration;
use crate::replay::KernelVerdict;
use crate::replay::ReplayBudget;
use crate::replay::ReplaySides;
use crate::replay::Unfoldings;

/// Why a ruled definition's body is not its rules' decision tree.
///
/// # Specification
/// - provides: the first fault the walk of the body meets.
/// - panics: none.
/// - executable: none — data declaration.
///
/// # Adequacy
/// - hypothesis: L3 — a body whose leaf returns another constructor than its
///   rule is refused naming that rule, and one that is no fixpoint is refused
///   for its shape.
/// - witness: `ruled::tests::a_body_is_admitted_only_as_its_rules_decision_tree`
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum OperationBodyFault
{
    /// The body is not a thunked fixpoint over one lambda per input, or a
    /// case of its tree is not over a data declaration's whole constructor
    /// table with one lambda per field.
    Shape,
    /// No rule's left side matches what the cases above a leaf learned.
    Unmatched,
    /// A leaf is the right side of no rule whose left side matches it; the
    /// first rule that matches.
    Apart(RuleIndex),
}

/// A binder of the body by its depth from the root: the fixpoint's own binder
/// is level zero, the inputs follow it, and each case's fields follow those.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct Level(usize);

/// How many binders enclose a point of the body.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct Depth(usize);

impl Depth
{
    /// `count` binders further in.
    ///
    /// # Specification
    /// trivial.
    fn plus(
        self,
        binders: Self,
    ) -> Option<Self>
    {
        self.0.checked_add(binders.0).map(Self)
    }
}

/// A fact's position in the walk's fact list.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct FactAt(usize);

/// A position in the slot list a leaf's fields, arguments and components
/// are read from.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Slot(usize);

/// The positions of a run of slots.
#[repr(transparent)]
#[derive(Clone, Debug, Eq, PartialEq)]
struct SlotRange(core::ops::Range<usize>);

/// What one branch of a case learned: the value at `scrutinee` is the
/// constructor `tag` of `family`, its fields bound at the levels from
/// `fields` on.
#[derive(Clone, Copy, Debug)]
struct Fact
{
    /// The scrutinised value's level.
    scrutinee: Level,
    /// The scrutinised data declaration.
    family: ConstantIndex,
    /// The branch's constructor.
    tag: ConstructorTag,
    /// The level of the constructor's first field.
    fields: Level,
    /// How many fields it binds.
    count: FieldCount,
    /// The fact the enclosing branch learned, if any.
    parent: Option<FactAt>,
}

/// A value a leaf builds, by position among the built values.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct BuiltAt(usize);

/// One value a leaf builds.
#[derive(Clone, Copy, Debug)]
enum Built
{
    /// The value at a level.
    Bound(Level),
    /// A constructor over the built values in the slots from `first`.
    Constructed
    {
        /// The constructed family.
        family: ConstantIndex,
        /// The constructor.
        tag: ConstructorTag,
        /// Its first field's slot.
        first: Slot,
        /// How many fields.
        count: FieldCount,
    },
}

/// A call a leaf makes: its callee and its arguments' slots.
#[derive(Clone, Copy, Debug)]
struct Call
{
    /// The called definition.
    callee: ConstantIndex,
    /// The first argument's slot.
    first: Slot,
    /// How many arguments.
    count: FieldCount,
}

/// How a leaf ends.
#[derive(Clone, Copy, Debug)]
enum Ending
{
    /// Return the built value at a position.
    Return(BuiltAt),
    /// Return the values in the slots from `first` as one tuple.
    Deliver
    {
        /// The first component's slot.
        first: Slot,
        /// How many components.
        count: FieldCount,
    },
    /// Call last.
    Tail(Call),
}

/// The walk of one body: the declarations it reads, its rules and every
/// buffer a leaf reuses.
///
/// # Specification
/// trivial.
struct Linker<'walk>
{
    /// The declarations admitted before the definition.
    entries: &'walk [AdmittedDeclaration],
    /// The definition's position.
    position: ConstantIndex,
    /// Each input's data declaration, where its type is one.
    inputs: Vec<Option<ConstantIndex>>,
    /// Every fact a case learned, each branch's after its parent's.
    facts: Vec<Fact>,
    /// A rule variable's level, by ordinal.
    bindings: Vec<Level>,
    /// The levels a left side's patterns still have to meet.
    pending: Vec<Level>,
    /// A right side's open nodes and the children each still waits for.
    open: Vec<(usize, usize)>,
    /// A right side's nodes in post-order.
    order: Vec<usize>,
    /// The values a leaf builds.
    built: Vec<Built>,
    /// The built values not yet read, as positions.
    stack: Vec<BuiltAt>,
    /// The fields, arguments and components the leaf reads, by slot.
    slots: Vec<BuiltAt>,
    /// The calls below the root, in post-order.
    calls: Vec<Call>,
    /// Each built value minted at the current depth, by position.
    minted: Vec<Option<ValueId>>,
    /// The built values left to mint, each with whether its fields are.
    work: Vec<(BuiltAt, bool)>,
    /// The minted values a constructor or a tuple reads.
    values: Vec<ValueId>,
}

/// Check that `body`, the definition at `position` declared at `declared`, is
/// the decision tree of `rules`.
///
/// # Specification
/// - requires: `rules` is non-empty and converges over `entries`, the
///   declarations admitted before `position`; `body` and `declared` live in
///   `arena`.
/// - ensures: `Ok(())` exactly when `body` is `thunk(fix. λ…λ. t)` with one
///   lambda per input and every leaf of `t` converts with the right side of a
///   rule whose left side matches the cases above it; `arena` holds what it
///   held on entry.
/// - provides: that the body computes what the rules compute.
/// - fails: [`OperationBodyFault`] for the first case or leaf that is not the
///   tree's.
/// - panics: none.
/// - measure: the tree's nodes, times the rules at each leaf.
///
/// # Errors
/// As `- fails:`.
///
/// # Adequacy
/// - hypothesis: L3 — the tree of `or`'s three rules is admitted, the same tree
///   with one leaf returning the other constructor is refused naming its rule,
///   and a body that is no fixpoint is refused for its shape; `add`'s tree over
///   the naturals, its call bound below `succ` or standing as the leaf, is
///   admitted, and a branch or input that is no lambda is refused for its
///   shape.
/// - witness: `ruled::tests::a_body_is_admitted_only_as_its_rules_decision_tree`
/// - witness: `ruled::tests::a_recursive_body_links_its_fields_and_calls`
#[spec(
    captures: before = arena.watermark(),
    ensures: arena.watermark() == before,
)]
pub fn link(
    arena: &mut TermArena,
    entries: &[AdmittedDeclaration],
    position: ConstantIndex,
    declared: ValueTypeId,
    body: ValueId,
    rules: &OperationRules,
) -> Result<(), OperationBodyFault>
{
    let arity = match rules.rules().first().and_then(|rule| rule.left().first()) {
        Some(&OperationNode::Operation { arity, .. }) => usize::from(arity),
        Some(
            &(OperationNode::Constructor { .. }
            | OperationNode::Results(_)
            | OperationNode::Variable(_)),
        )
        | None => return Err(OperationBodyFault::Shape),
    };
    let mut linker = Linker {
        entries,
        position,
        inputs: Vec::with_capacity(arity),
        facts: Vec::new(),
        bindings: Vec::new(),
        pending: Vec::new(),
        open: Vec::new(),
        order: Vec::new(),
        built: Vec::new(),
        stack: Vec::new(),
        slots: Vec::new(),
        calls: Vec::new(),
        minted: Vec::new(),
        work: Vec::new(),
        values: Vec::new(),
    };
    let Some(&ValueType::Thunk(mut signature)) = arena.value_type(declared)
    else {
        return Err(OperationBodyFault::Shape);
    };
    for _input in 0 .. arity {
        let Some(&CompType::Arrow { domain, codomain }) = arena.comp_type(signature)
        else {
            return Err(OperationBodyFault::Shape);
        };
        linker.inputs.push(family_of(arena, domain));
        signature = codomain;
    }
    let Some(&Value::Thunk(fixpoint)) = arena.value(body)
    else {
        return Err(OperationBodyFault::Shape);
    };
    let Some(&Computation::Fixpoint { body: mut tree, .. }) = arena.computation(fixpoint)
    else {
        return Err(OperationBodyFault::Shape);
    };
    for _input in 0 .. arity {
        let Some(&Computation::Lambda(inner)) = arena.computation(tree)
        else {
            return Err(OperationBodyFault::Shape);
        };
        tree = inner;
    }
    let root = Depth(1)
        .plus(Depth(arity))
        .ok_or(OperationBodyFault::Shape)?;
    let mut nodes: Vec<(ComputationId, Depth, Option<FactAt>)> = Vec::from([(tree, root, None)]);
    while let Some((node, depth, learned)) = nodes.pop() {
        let Some(level) = scrutinised(arena, node, depth)
        else {
            linker.leaf(arena, rules.rules(), node, depth, learned)?;
            continue;
        };
        let family = linker
            .family_at(arena, level, learned)
            .ok_or(OperationBodyFault::Shape)?;
        let Some(&Computation::DataCase { ref branches, .. }) = arena.computation(node)
        else {
            return Err(OperationBodyFault::Shape);
        };
        let Some(&DeclarationContent::Data {
            ref constructors, ..
        }) = entries
            .get(usize::from(family))
            .map(AdmittedDeclaration::content)
        else {
            return Err(OperationBodyFault::Shape);
        };
        if branches.len() != constructors.len() {
            return Err(OperationBodyFault::Shape);
        }
        for (tag, (&branch, fields)) in branches.iter().zip(constructors).enumerate() {
            let mut inner = branch;
            for _field in fields {
                let Some(&Computation::Lambda(under)) = arena.computation(inner)
                else {
                    return Err(OperationBodyFault::Shape);
                };
                inner = under;
            }
            let at = FactAt(linker.facts.len());
            linker.facts.push(Fact {
                scrutinee: level,
                family,
                tag: ConstructorTag::from(tag),
                fields: Level(depth.0),
                count: FieldCount::from(fields.len()),
                parent: learned,
            });
            let below = depth
                .plus(Depth(fields.len()))
                .ok_or(OperationBodyFault::Shape)?;
            nodes.push((inner, below, Some(at)));
        }
    }

    Ok(())
}

/// The data declaration `ty` applies, if it applies one.
///
/// # Specification
/// trivial.
fn family_of(
    arena: &TermArena,
    ty: ValueTypeId,
) -> Option<ConstantIndex>
{
    let &ValueType::Data { declaration, .. } = arena.value_type(ty)?
    else {
        return None;
    };
    Some(declaration)
}

/// The level `node` cases on, when it is a data case on a bound value at
/// `depth` binders.
///
/// # Specification
/// trivial.
fn scrutinised(
    arena: &TermArena,
    node: ComputationId,
    depth: Depth,
) -> Option<Level>
{
    let &Computation::DataCase { scrutinee, .. } = arena.computation(node)?
    else {
        return None;
    };
    let &Value::Variable(index) = arena.value(scrutinee)?
    else {
        return None;
    };
    let index = usize::try_from(u32::from(index)).ok()?;
    depth.0.checked_sub(index)?.checked_sub(1).map(Level)
}

/// The variable at `level` seen from `depth` binders.
///
/// # Specification
/// trivial.
fn variable(
    arena: &mut TermArena,
    level: Level,
    depth: Depth,
) -> Option<ValueId>
{
    let index = depth.0.checked_sub(level.0)?.checked_sub(1)?;
    let index = u32::try_from(index).ok()?;
    Some(arena.value_variable(DeBruijnIndex::from(index)))
}

impl Linker<'_>
{
    /// The data declaration of the value at `level`, as the inputs' types and
    /// the facts from `learned` up give it.
    ///
    /// # Specification
    /// trivial.
    fn family_at(
        &self,
        arena: &TermArena,
        level: Level,
        learned: Option<FactAt>,
    ) -> Option<ConstantIndex>
    {
        if let Some(input) = level.0.checked_sub(1)
            && let Some(&family) = self.inputs.get(input)
        {
            return family;
        }
        let mut at = learned;
        while let Some(FactAt(index)) = at {
            let fact = self.facts.get(index)?;
            if let Some(field) = level.0.checked_sub(fact.fields.0)
                && field < usize::from(fact.count)
            {
                let DeclarationContent::Data {
                    ref constructors, ..
                } = *self.entries.get(usize::from(fact.family))?.content()
                else {
                    return None;
                };
                let ty = *constructors.get(usize::from(fact.tag))?.get(field)?;
                return family_of(arena, ty);
            }
            at = fact.parent;
        }
        None
    }

    /// The nearest fact from `learned` up that the value at `level` met.
    ///
    /// # Specification
    /// trivial.
    fn split(
        &self,
        level: Level,
        learned: Option<FactAt>,
    ) -> Option<Fact>
    {
        let mut at = learned;
        while let Some(FactAt(index)) = at {
            let fact = *self.facts.get(index)?;
            if fact.scrutinee == level {
                return Some(fact);
            }
            at = fact.parent;
        }
        None
    }

    /// Bind the variables of `left` when its patterns match what the facts
    /// from `learned` up say of the inputs.
    ///
    /// # Specification
    /// - requires: `left` is a converged rule's left side.
    /// - ensures: something exactly when every constructor pattern meets a
    ///   value a case split into that constructor of that family; `bindings`
    ///   then holds each variable's level by ordinal.
    /// - panics: none.
    /// - executable: none — the walk's private state; the link's witness runs
    ///   it.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — `or(False, True)` is matched by the second rule
    ///   alone, which a match ignoring a pattern or a family would not keep.
    /// - witness: `ruled::tests::a_body_is_admitted_only_as_its_rules_decision_tree`
    fn matches(
        &mut self,
        left: &[OperationNode],
        learned: Option<FactAt>,
    ) -> Option<()>
    {
        self.bindings.clear();
        self.pending.clear();
        self.pending
            .extend((1 ..= self.inputs.len()).rev().map(Level));
        for &node in left.iter().skip(1) {
            let level = self.pending.pop()?;
            match node {
                OperationNode::Variable(variable) => {
                    let ordinal = usize::try_from(u32::from(variable)).ok()?;
                    if ordinal != self.bindings.len() {
                        return None;
                    }
                    self.bindings.push(level);
                },
                OperationNode::Constructor { family, tag } => {
                    let fact = self.split(level, learned)?;
                    if fact.family != family || fact.tag != tag {
                        return None;
                    }
                    self.pending.extend(
                        (0 .. usize::from(fact.count))
                            .rev()
                            .filter_map(|field| fact.fields.0.checked_add(field).map(Level)),
                    );
                },
                OperationNode::Operation { .. } | OperationNode::Results(_) => return None,
            }
        }
        self.pending.is_empty().then_some(())
    }

    /// Check one leaf at `depth` binders against every rule matching the
    /// facts from `learned` up.
    ///
    /// # Specification
    /// - requires: `rules` converged over the linker's entries.
    /// - ensures: `Ok(())` exactly when some matching rule's right side, minted
    ///   at `depth`, converts with `leaf`; `arena` holds what it held on entry.
    /// - fails: [`OperationBodyFault::Unmatched`] when no rule matches, and
    ///   [`OperationBodyFault::Apart`] naming the first matching rule when none
    ///   converts.
    /// - panics: none.
    /// - executable: none — the walk's private state; the link's witness runs
    ///   it.
    ///
    /// # Errors
    /// As `- fails:`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a leaf returning `False` where its rule returns
    ///   `True` is refused naming that rule, and the right leaf admits.
    /// - witness: `ruled::tests::a_body_is_admitted_only_as_its_rules_decision_tree`
    fn leaf(
        &mut self,
        arena: &mut TermArena,
        rules: &[OperationRule],
        leaf: ComputationId,
        depth: Depth,
        learned: Option<FactAt>,
    ) -> Result<(), OperationBodyFault>
    {
        let mut first = None;
        for (index, rule) in rules.iter().enumerate() {
            if self.matches(rule.left(), learned).is_none() {
                continue;
            }
            let _first = first.get_or_insert_with(|| RuleIndex::from(index));
            let watermark = arena.watermark();
            let converts = self
                .side(arena, rule.right(), depth)
                .is_some_and(|expected| {
                    crate::replay::convert(
                        arena,
                        &Unfoldings::default(),
                        ReplaySides::Computations(expected, leaf),
                        ReplayBudget::DEFAULT,
                    ) == KernelVerdict::Convertible
                });
            arena.truncate_to(watermark);
            if converts {
                return Ok(());
            }
        }
        Err(first.map_or(OperationBodyFault::Unmatched, OperationBodyFault::Apart))
    }

    /// The children `node` reads.
    ///
    /// # Specification
    /// trivial.
    fn children(
        &self,
        node: OperationNode,
    ) -> Option<FieldCount>
    {
        match node {
            OperationNode::Operation { arity, .. } => Some(arity),
            OperationNode::Results(count) => Some(count),
            OperationNode::Variable(_) => Some(FieldCount::from(0_usize)),
            OperationNode::Constructor { family, tag } => {
                let DeclarationContent::Data {
                    ref constructors, ..
                } = *self.entries.get(usize::from(family))?.content()
                else {
                    return None;
                };
                constructors
                    .get(usize::from(tag))
                    .map(|fields| FieldCount::from(fields.len()))
            },
        }
    }

    /// Order `right`'s nodes in post-order into `order`.
    ///
    /// # Specification
    /// - requires: `right` is a converged rule's right side.
    /// - ensures: something exactly when `right` is one well-formed term;
    ///   `order` then lists every node once, each after its children, the root
    ///   last.
    /// - panics: none.
    /// - executable: none — the walk's private state; the link's witness runs
    ///   it.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — `Succ(add(m, n))` mints its call before the
    ///   constructor that reads it, which a pre-order reading would not.
    /// - witness: `ruled::tests::a_body_is_admitted_only_as_its_rules_decision_tree`
    fn post_order(
        &mut self,
        right: &[OperationNode],
    ) -> Option<()>
    {
        self.open.clear();
        self.order.clear();
        for (index, &node) in right.iter().enumerate() {
            let children = usize::from(self.children(node)?);
            if children > 0 {
                self.open.push((index, children));
                continue;
            }
            self.order.push(index);
            while let Some(top) = self.open.last_mut() {
                top.1 = top.1.saturating_sub(1);
                if top.1 > 0 {
                    break;
                }
                self.order.push(top.0);
                self.open.pop();
            }
        }
        (self.open.is_empty() && self.order.len() == right.len() && self.order.last() == Some(&0))
            .then_some(())
    }

    /// Mint `right` at `depth` binders as the lowering mints a leaf: the calls
    /// below the root bound in post-order around the ending.
    ///
    /// # Specification
    /// - requires: `bindings` holds the variables of the rule `right` belongs
    ///   to.
    /// - ensures: the leaf, or nothing when `right` is not one term whose
    ///   results stand only at its root.
    /// - panics: none.
    /// - executable: none — the walk's private state; the link's witness runs
    ///   it.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — each leaf of `or` converts with the constructor its
    ///   rule returns and not with the other.
    /// - witness: `ruled::tests::a_body_is_admitted_only_as_its_rules_decision_tree`
    fn side(
        &mut self,
        arena: &mut TermArena,
        right: &[OperationNode],
        depth: Depth,
    ) -> Option<ComputationId>
    {
        self.post_order(right)?;
        self.built.clear();
        self.stack.clear();
        self.slots.clear();
        self.calls.clear();
        let mut ending = None;
        for step in 0 .. self.order.len() {
            let index = *self.order.get(step)?;
            let node = *right.get(index)?;
            let at_root = index == 0;
            match node {
                OperationNode::Variable(variable) => {
                    let ordinal = usize::try_from(u32::from(variable)).ok()?;
                    let level = *self.bindings.get(ordinal)?;
                    self.stack.push(BuiltAt(self.built.len()));
                    self.built.push(Built::Bound(level));
                },
                OperationNode::Constructor { family, tag } => {
                    let count = self.children(node)?;
                    let first = self.read(count)?;
                    self.stack.push(BuiltAt(self.built.len()));
                    self.built.push(Built::Constructed {
                        family,
                        tag,
                        first,
                        count,
                    });
                },
                OperationNode::Operation { constant, arity } => {
                    let first = self.read(arity)?;
                    let call = Call {
                        callee: constant,
                        first,
                        count: arity,
                    };
                    if at_root {
                        ending = Some(Ending::Tail(call));
                    }
                    else {
                        let level = Level(depth.plus(Depth(self.calls.len()))?.0);
                        self.calls.push(call);
                        self.stack.push(BuiltAt(self.built.len()));
                        self.built.push(Built::Bound(level));
                    }
                },
                OperationNode::Results(count) => {
                    if !at_root {
                        return None;
                    }
                    let first = self.read(count)?;
                    ending = Some(Ending::Deliver { first, count });
                },
            }
            if at_root && ending.is_none() {
                ending = Some(Ending::Return(self.stack.pop()?));
            }
        }
        let at = depth.plus(Depth(self.calls.len()))?;
        let mut chain = match ending? {
            Ending::Return(position) => {
                let value = self.value(arena, position, at)?;
                arena.computation_return(value)
            },
            Ending::Deliver { first, count } => {
                let components = self.slot_range(first, count)?;
                self.values.clear();
                for slot in components.0 {
                    let position = *self.slots.get(slot)?;
                    let value = self.value(arena, position, at)?;
                    self.values.push(value);
                }
                let tuple = arena.value_tuple(&self.values);
                arena.computation_return(tuple)
            },
            Ending::Tail(call) => self.call(arena, call, at)?,
        };
        for bound in (0 .. self.calls.len()).rev() {
            let call = *self.calls.get(bound)?;
            let called = self.call(arena, call, depth.plus(Depth(bound))?)?;
            chain = arena.computation_bind(called, chain);
        }

        Some(chain)
    }

    /// Move the last `count` unread values into the slot list, returning the
    /// first's slot.
    ///
    /// # Specification
    /// trivial.
    fn read(
        &mut self,
        count: FieldCount,
    ) -> Option<Slot>
    {
        let from = self.stack.len().checked_sub(usize::from(count))?;
        let first = Slot(self.slots.len());
        self.slots.extend(self.stack.drain(from ..));
        Some(first)
    }

    /// The slot list's positions from `first`, `count` of them.
    ///
    /// # Specification
    /// trivial.
    fn slot_range(
        &self,
        first: Slot,
        count: FieldCount,
    ) -> Option<SlotRange>
    {
        let end = first.0.checked_add(usize::from(count))?;
        (end <= self.slots.len()).then_some(SlotRange(first.0 .. end))
    }

    /// Mint `call` at `depth` binders: the callee forced, applied to each
    /// argument in order; the definition's own call is its fixpoint binder's.
    ///
    /// # Specification
    /// trivial.
    fn call(
        &mut self,
        arena: &mut TermArena,
        call: Call,
        depth: Depth,
    ) -> Option<ComputationId>
    {
        let function = if call.callee == self.position {
            variable(arena, Level(0), depth)?
        }
        else {
            arena.value_constant(call.callee)
        };
        let mut applied = arena.computation_force(function);
        for slot in self.slot_range(call.first, call.count)?.0 {
            let position = *self.slots.get(slot)?;
            let argument = self.value(arena, position, depth)?;
            applied = arena.computation_application(applied, argument);
        }
        Some(applied)
    }

    /// Mint the built value at `root` at `depth` binders, its fields first, by
    /// an explicit work stack.
    ///
    /// # Specification
    /// trivial.
    fn value(
        &mut self,
        arena: &mut TermArena,
        root: BuiltAt,
        depth: Depth,
    ) -> Option<ValueId>
    {
        self.minted.clear();
        self.minted.resize(self.built.len(), None);
        self.work.clear();
        self.work.push((root, false));
        while let Some((position, expanded)) = self.work.pop() {
            let value = match *self.built.get(position.0)? {
                Built::Bound(level) => variable(arena, level, depth)?,
                Built::Constructed {
                    family,
                    tag,
                    first,
                    count,
                } => {
                    let fields = self.slots.get(self.slot_range(first, count)?.0)?;
                    if !expanded {
                        self.work.push((position, true));
                        self.work.extend(fields.iter().map(|&field| (field, false)));
                        continue;
                    }
                    let mut values = Vec::with_capacity(fields.len());
                    for field in fields {
                        values.push((*self.minted.get(field.0)?)?);
                    }
                    let datatype = arena.value_type_data(family, Vec::new());
                    arena.value_constructor(datatype, tag, values)
                },
            };
            *self.minted.get_mut(position.0)? = Some(value);
        }
        *self.minted.get(root.0)?
    }
}
