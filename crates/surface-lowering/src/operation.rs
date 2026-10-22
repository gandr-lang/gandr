//! A data declaration's operations as declarations the module can call.
//!
//! `oper divmod(m : N, n : N) -> (q : N, r : N)` with its rules is, besides the
//! frame and the cells [`crate::desc_cells`] admits, a function of the module:
//! `divmod : +U (N -> N -> -F (N * N))`, called as `divmod(m, n)` from any
//! later declaration and bound with `run (q, r) <- divmod(m, n);`. The
//! collection pass plans each operation once its family is read; the mint pass
//! writes the plan into the core arena after the module's other declarations.
//!
//! # Decisions
//!
//! **Rules compile to a first-match decision tree.** The operation's rules,
//! top to bottom, are the arms of one match over its inputs: the first rule
//! whose patterns fit a column of constructors decides, and the tree switches
//! on the leftmost column the first remaining rule tests (Maranget, *Compiling
//! Pattern Matching to Good Decision Trees*, ML 2008). The alternative was to
//! run the cells themselves by rewriting at run time; the L machine runs core
//! terms, and a tree over core cases is what the checker already judges.
//!
//! **A many-out operation returns one tuple.** The results come back as one
//! positive tuple in output-port order, and a caller splits it with a tuple
//! binder. The record prefers a consumer frame with one continuation per output
//! (the cell store's own shape, Spivak, Garner and Fairbanks, *Functorial
//! aggregation*, JPAA 229, 2025), which the command intermediate language could
//! carry but no machine step runs today. Reversal: when the intermediate
//! language gains a many-consumer head and its machine step, a call delivers to
//! one continuation per output instead.
//!
//! **An operation runs only when every rule is admissible as code.** A route is
//! planned when the family is an unparameterised `data` family, every port is
//! sorted by such a family, the cell gate admitted the operation and declined
//! none of its rules, the rules cover every input, each pattern is a variable
//! or a constructor of its column's family, every right-hand variable is bound
//! by a pattern, and every call names the operation itself or an operation an
//! earlier family declared. Otherwise the operation stays a cell vocabulary
//! item only: its name is not callable and resolves as if unwritten. The
//! alternative, a refusal at every call, is reversible later; an operation
//! that never runs refuses nothing today.
//!
//! **Recursion is partial.** The function closes one fixpoint over its
//! operation's whole parameter list with [`FixpointEvidence::Partial`], so the
//! machine unfolds it and conversion never does. Structural evidence stages
//! one parameter, and every recursive call must stand below that parameter's
//! stage, which a multi-input operation's rules, descending on whichever
//! column they match, do not promise. Reversal: a stage per column in the
//! kernel.
//!
//! **Operation names resolve after declarations, before builtins.** An
//! operation is entered in no module namespace; a name the module declares
//! wins, and an operation named like a builtin (`add`) shadows the builtin for
//! the declarations after its family.

#[cfg(test)]
mod tests;

use alloc::collections::BTreeMap;
use alloc::vec;
use alloc::vec::Vec;

use anodized::spec;
use gandr_core_term::CompTypeId;
use gandr_core_term::ComputationId;
use gandr_core_term::ConstructorTag;
use gandr_core_term::CoreArena;
use gandr_core_term::ValueId;
use gandr_core_term::ValueTypeId;
use gandr_core_term::Zone;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::FixpointEvidence;
use gandr_theory_levitation::FreeTerm;
use gandr_theory_levitation::Name;
use gandr_theory_levitation::OperDesc;
use gandr_theory_levitation::RuleFace;
use gandr_theory_levitation::SortRef;
use gandr_theory_levitation::TermNode;
use gandr_theory_levitation::TermView;

use crate::origin::Origin;
use crate::origin::OriginTable;

/// A binder's position counted from the outside in: the operation's own
/// recursion binder is level zero and its inputs follow it.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Ord, PartialEq, PartialOrd)]
struct Level(usize);

/// How many binders enclose a point of the compiled body.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Ord, PartialEq, PartialOrd)]
struct Depth(usize);

/// How many values a constructor reads or a call, tuple or switch branch
/// binds.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Ord, PartialEq, PartialOrd)]
pub struct Width(usize);

impl From<usize> for Width
{
    /// Count `count` values.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(count: usize) -> Self
    {
        Self(count)
    }
}

/// One constructor a rule may match or build.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct RouteConstructor
{
    /// The constant of the family that declares it.
    pub family: ConstantIndex,
    /// Its position among the family's constructors.
    pub tag: ConstructorTag,
    /// How many fields it carries.
    pub fields: Width,
}

/// What a module offers an operation's rules: its families, their
/// constructors and the operations already callable.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct RouteTable
{
    /// The unparameterised families a port may be sorted by, by name.
    pub families: BTreeMap<Name, ConstantIndex>,
    /// Each such family's constructor field counts, in tag order.
    pub generators: BTreeMap<ConstantIndex, Vec<Width>>,
    /// Each such family's constructors, by name.
    pub constructors: BTreeMap<Name, RouteConstructor>,
    /// The operations planned before this one, by name.
    pub callees: BTreeMap<Name, ConstantIndex>,
}

/// Why an operation has no route: the first condition of the module's
/// [decisions](self) its rules miss.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum RouteFault
{
    /// A port's sort names no unparameterised family of the module.
    PortSort(Name),
    /// The operation has no rule.
    Unruled,
    /// A rule's left-hand side is not the operation over one pattern per
    /// input.
    Head,
    /// A pattern is neither a variable nor a constructor over its fields, or a
    /// built constructor's fields miscount.
    Pattern,
    /// A constructor of no family, or of a family other than its column's.
    Constructor(Name),
    /// An input no rule matches.
    Uncovered,
    /// A right-hand variable no pattern binds.
    Unbound(Name),
    /// A call to an operation not yet callable.
    Callee(Name),
    /// A result tuple below the right-hand side's root.
    Results,
    /// A right-hand side instantiating the variable named, which no port of a
    /// family's operation binds.
    Instantiated(Name),
}

/// The function an operation's call reaches.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Callee
{
    /// The operation itself, through its fixpoint binder.
    Itself,
    /// An operation planned before it, by constant.
    Earlier(ConstantIndex),
}

/// One instruction of a right-hand side, in post-order: the values an
/// instruction reads are the ones the instructions before it left.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Step
{
    /// The value a pattern bound at a level.
    Variable(Level),
    /// A constructor over the last values.
    Construct
    {
        /// The constant of the constructed family.
        family: ConstantIndex,
        /// The constructor.
        tag: ConstructorTag,
        /// How many values it reads.
        fields: Width,
    },
    /// A call below the root, whose result is bound for the steps after it.
    Call
    {
        /// The called function.
        callee: Callee,
        /// How many values it reads.
        arguments: Width,
    },
    /// A call at the root, whose results are the operation's.
    Tail
    {
        /// The called function.
        callee: Callee,
        /// How many values it reads.
        arguments: Width,
    },
    /// Return the last value.
    Return,
    /// Return the last values as one tuple.
    Deliver(Width),
}

/// A node's position in a plan's node list.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct NodeAt(usize);

/// One node of an operation's decision tree.
#[derive(Clone, Debug, Eq, PartialEq)]
enum PlanNode
{
    /// A case on the value at `level`, one branch per constructor in tag
    /// order, each binding that constructor's fields.
    Switch
    {
        /// The scrutinised value's level.
        level: Level,
        /// The binders around the case.
        depth: Depth,
        /// The constant of the family whose constructors the branches are.
        family: ConstantIndex,
        /// Each constructor's field count and branch.
        branches: Vec<(Width, NodeAt)>,
    },
    /// A rule's right-hand side.
    Leaf
    {
        /// The binders around the right-hand side.
        depth: Depth,
        /// Its instructions.
        steps: Vec<Step>,
    },
}

/// An operation's route: its port families and its decision tree, root first.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct OperationPlan
{
    /// The family of each input, in port order.
    inputs: Vec<ConstantIndex>,
    /// The family of each output, in port order.
    outputs: Vec<ConstantIndex>,
    /// The tree; a child follows its parent.
    nodes: Vec<PlanNode>,
    /// The rules the tree decides, over module positions, for the kernel to
    /// decide they converge.
    rules: gandr_kernel_term::OperationRules,
}

impl OperationPlan
{
    /// The rules the plan's tree decides, over module positions, the
    /// operation's own at the constant it was planned at.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn rules(&self) -> &gandr_kernel_term::OperationRules
    {
        &self.rules
    }
}

/// One pattern position of a rule: a written pattern, or a field no pattern
/// tests.
type Column<'face> = Option<TermNode<'face>>;

/// An undecided column's position among a row's columns.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct ColumnAt(usize);

/// A rule still in play at a node of the tree.
#[derive(Clone, Debug)]
struct Row<'face>
{
    /// Its patterns not yet decided.
    columns: Vec<Column<'face>>,
    /// The variables its decided patterns bound.
    bindings: Vec<(&'face Name, Level)>,
    /// Its position among the operation's rules.
    rule: usize,
}

/// A node of the tree still to plan.
struct Work<'face>
{
    /// Where the node goes.
    at: NodeAt,
    /// The binders around it.
    depth: Depth,
    /// The level of each undecided column.
    levels: Vec<Level>,
    /// The rules in play, in source order.
    rows: Vec<Row<'face>>,
}

/// Plan the operation `operation` over its rules `faces`, in source order, to
/// be admitted at `own`, the kernel reading `derived` beside them.
///
/// # Specification
/// - requires: `faces` are the operation's rules in source order; `derived` are
///   rules completion derived from the block's rules, each headed by
///   `operation`.
/// - ensures: a plan whose tree decides every input by the first rule of
///   `faces` that matches it, with a port family per port, carrying the rules
///   of `faces` and then of `derived` read over module positions: the
///   operation's own call at `own`, every callee at its constant, every
///   constructor at its family and tag.
/// - panics: none.
/// - executable: none — the plan's meaning is the function it mints, which the
///   witnesses run.
///
/// # Errors
/// [`RouteFault`].
///
/// # Adequacy
/// - hypothesis: L3 — a two-output operation over a helper runs to its results
///   in order, an operation missing a constructor has no route, and a call to a
///   later operation has no route.
/// - witness: `operation::tests::a_many_out_operation_lowers_to_a_function_the_checker_accepts`
/// - witness: `operation::tests::an_operation_whose_rules_miss_a_constructor_is_not_callable`
/// - witness: `operation::tests::an_operation_calling_a_later_one_is_not_callable`
/// - witness: `operation::tests::a_rule_of_another_arity_than_its_operation_routes_nothing`
pub fn plan_operation(
    operation: &OperDesc,
    faces: &[&RuleFace],
    derived: &[&(FreeTerm, FreeTerm)],
    (table, own): (&RouteTable, ConstantIndex),
) -> Result<OperationPlan, RouteFault>
{
    let inputs = families(&operation.arity.inputs, table)?;
    let outputs = families(&operation.arity.outputs, table)?;
    if faces.is_empty() {
        return Err(RouteFault::Unruled);
    }
    let mut rows = Vec::with_capacity(faces.len());
    for (rule, face) in faces.iter().enumerate() {
        let TermView::Op { name, args } = face.lhs.view()
        else {
            return Err(RouteFault::Head);
        };
        if *name != operation.name || args.len() != inputs.len() {
            return Err(RouteFault::Head);
        }
        rows.push(Row {
            columns: args.map(Some).collect(),
            bindings: Vec::new(),
            rule,
        });
    }
    let mut nodes: Vec<Option<PlanNode>> = vec![None];
    let mut work = vec![Work {
        at: NodeAt(0),
        depth: Depth(inputs.len().saturating_add(1)),
        levels: (1 ..= inputs.len()).map(Level).collect(),
        rows,
    }];
    while let Some(next) = work.pop() {
        let Some(first) = next.rows.first()
        else {
            return Err(RouteFault::Uncovered);
        };
        let tested = first
            .columns
            .iter()
            .position(|column| matches!(column.map(TermNode::view), Some(TermView::Ctor { .. })));
        let node = match tested {
            None => {
                let Some(face) = faces.get(first.rule)
                else {
                    return Err(RouteFault::Uncovered);
                };
                leaf(first, &next.levels, next.depth, face, operation, table)?
            },
            Some(column) => switch(&next, ColumnAt(column), table, &mut nodes, &mut work)?,
        };
        if let Some(entry) = nodes.get_mut(next.at.0) {
            *entry = Some(node);
        }
    }
    let nodes = nodes
        .into_iter()
        .collect::<Option<Vec<_>>>()
        .ok_or(RouteFault::Uncovered)?;

    let rules = faces
        .iter()
        .map(|face| (&face.lhs, &face.rhs))
        .chain(derived.iter().map(|&&(ref lhs, ref rhs)| (lhs, rhs)))
        .map(|sides| read_rule(sides, operation, (table, own)))
        .collect::<Result<Vec<_>, _>>()
        .map(gandr_kernel_term::OperationRules::new)?;
    Ok(OperationPlan {
        inputs,
        outputs,
        nodes,
        rules,
    })
}

/// One rule of the operation as the kernel reads it: both sides in pre-order
/// over module positions, its variables numbered by first occurrence on the
/// left.
///
/// # Specification
/// - requires: `lhs` and `rhs` are a rule of `operation`, which
///   [`plan_operation`] routed.
/// - ensures: the left side's head is `own` at the arity the rule writes; an
///   operation named `operation` reads as `own`, any other as the constant
///   `table` gives it; a constructor as its family and tag; a results tuple as
///   its width; a variable as its first occurrence's ordinal on the left.
/// - fails: [`RouteFault::Callee`], [`RouteFault::Constructor`] or
///   [`RouteFault::Unbound`] for a name the table or the left side does not
///   bind; [`RouteFault::Instantiated`] for an instantiation.
/// - panics: none.
///
/// # Errors
/// As `- fails:`.
///
/// # Adequacy
/// - hypothesis: L3 — every routed operation's rules cross to the kernel, which
///   admits the corpus's operations and refuses a forged pair.
/// - witness: `operation::tests::an_operations_rules_read_in_pre_order_over_module_positions`
#[spec(ensures: |ret| ret.as_ref().is_err() || ret.as_ref().is_ok_and(|rule| !rule.left().is_empty() && !rule.right().is_empty()))]
fn read_rule(
    (lhs, rhs): (&FreeTerm, &FreeTerm),
    operation: &OperDesc,
    (table, own): (&RouteTable, ConstantIndex),
) -> Result<gandr_kernel_term::OperationRule, RouteFault>
{
    use gandr_kernel_term::OperationNode;
    let mut bound: BTreeMap<&Name, gandr_kernel_term::RuleVariable> = BTreeMap::new();
    let mut sides: [Vec<OperationNode>; 2] = [Vec::new(), Vec::new()];
    let mut pending: Vec<TermNode<'_>> = Vec::new();
    let mut arguments: Vec<TermNode<'_>> = Vec::new();
    let roots = [(lhs.to_node(), true), (rhs.to_node(), false)];
    for (side, (root, binding)) in sides.iter_mut().zip(roots) {
        pending.push(root);
        while let Some(node) = pending.pop() {
            arguments.clear();
            let read = match node.view() {
                TermView::Var(variable) => {
                    let ordinal = match bound.get(variable) {
                        Some(&ordinal) => ordinal,
                        None if binding => {
                            let ordinal = u32::try_from(bound.len())
                                .map(gandr_kernel_term::RuleVariable::from)
                                .map_err(|_overflow| RouteFault::Unbound(variable.clone()))?;
                            bound.insert(variable, ordinal);
                            ordinal
                        },
                        None => return Err(RouteFault::Unbound(variable.clone())),
                    };
                    OperationNode::Variable(ordinal)
                },
                TermView::Ctor { name, args } => {
                    let built = constructor(table, name)?;
                    arguments.extend(args);
                    OperationNode::Constructor {
                        family: built.family,
                        tag: built.tag,
                    }
                },
                TermView::Op { name, args } => {
                    let constant = if *name == operation.name {
                        own
                    }
                    else {
                        table
                            .callees
                            .get(name)
                            .copied()
                            .ok_or_else(|| RouteFault::Callee(name.clone()))?
                    };
                    arguments.extend(args);
                    OperationNode::Operation {
                        constant,
                        arity: gandr_kernel_term::FieldCount::from(arguments.len()),
                    }
                },
                TermView::Results { args } => {
                    arguments.extend(args);
                    OperationNode::Results(gandr_kernel_term::FieldCount::from(arguments.len()))
                },
                TermView::Inst { name, .. } => return Err(RouteFault::Instantiated(name.clone())),
                TermView::Abs { .. } => return Err(RouteFault::Pattern),
            };
            side.push(read);
            pending.extend(arguments.iter().rev().copied());
            arguments.clear();
        }
    }
    let [left, right] = sides;
    Ok(gandr_kernel_term::OperationRule::new(
        left.into_boxed_slice(),
        right.into_boxed_slice(),
    ))
}

/// The family of each port of `ports`, in order.
///
/// # Specification
/// - requires: nothing.
/// - ensures: one family per port, looked up by its sort's name.
/// - fails: [`RouteFault::PortSort`] for the first port no family sorts.
/// - panics: none.
///
/// # Errors
/// [`RouteFault::PortSort`].
///
/// # Adequacy
/// - hypothesis: L3 — each port's family is found by its sort's name, so a
///   two-output operation returns a two-component tuple.
/// - witness: `operation::tests::a_many_out_operation_lowers_to_a_function_the_checker_accepts`
#[spec(ensures: |ret| ret.as_ref().is_err() || ret.as_ref().is_ok_and(|found| found.len() == ports.len()))]
fn families(
    ports: &[SortRef],
    table: &RouteTable,
) -> Result<Vec<ConstantIndex>, RouteFault>
{
    ports
        .iter()
        .map(|port| {
            table
                .families
                .get(&port.sort)
                .copied()
                .ok_or_else(|| RouteFault::PortSort(port.sort.clone()))
        })
        .collect()
}

/// Plan a case on the undecided column `column` of `next`: one child per
/// constructor of the family its first rule's constructor names.
///
/// # Specification
/// - requires: `next`'s first row writes a constructor at `column`.
/// - ensures: the switch's branches in tag order, each child pushed onto `work`
///   with the rows that fit its constructor and a reserved entry in `nodes`.
/// - fails: [`RouteFault::Constructor`] for a constructor of no family or of
///   another family; [`RouteFault::Pattern`] for a pattern that is neither a
///   variable nor a constructor over its fields.
/// - panics: none.
///
/// # Errors
/// [`RouteFault::Constructor`] and [`RouteFault::Pattern`].
///
/// # Adequacy
/// - hypothesis: L3 — as [`plan_operation`].
/// - witness: `operation::tests::a_many_out_operation_lowers_to_a_function_the_checker_accepts`
#[spec(
    captures: before = (nodes.len(), work.len()),
    ensures: |ret| ret.is_err() || (nodes.len() >= before.0 && work.len() >= before.1),
)]
fn switch<'face>(
    next: &Work<'face>,
    column: ColumnAt,
    table: &RouteTable,
    nodes: &mut Vec<Option<PlanNode>>,
    work: &mut Vec<Work<'face>>,
) -> Result<PlanNode, RouteFault>
{
    let tested = next
        .rows
        .first()
        .and_then(|first| first.columns.get(column.0).copied().flatten())
        .map(TermNode::view);
    let Some(TermView::Ctor { name, .. }) = tested
    else {
        return Err(RouteFault::Pattern);
    };
    let family = constructor(table, name)?.family;
    let (Some(generators), Some(&level)) =
        (table.generators.get(&family), next.levels.get(column.0))
    else {
        return Err(RouteFault::Constructor(name.clone()));
    };
    let mut branches = Vec::with_capacity(generators.len());
    for (tag, &fields) in generators.iter().enumerate() {
        let tag = ConstructorTag::from(tag);
        let mut rows = Vec::with_capacity(next.rows.len());
        for row in &next.rows {
            let mut columns: Vec<Column<'face>> = row
                .columns
                .iter()
                .enumerate()
                .filter(|&(position, _)| position != column.0)
                .map(|(_, &kept)| kept)
                .collect();
            let mut bindings = row.bindings.clone();
            match row
                .columns
                .get(column.0)
                .copied()
                .flatten()
                .map(TermNode::view)
            {
                None => columns.extend(core::iter::repeat_n(None, fields.0)),
                Some(TermView::Var(variable)) => {
                    bindings.push((variable, level));
                    columns.extend(core::iter::repeat_n(None, fields.0));
                },
                Some(TermView::Ctor { name: other, args }) => {
                    let matched = constructor(table, other)?;
                    if matched.family != family {
                        return Err(RouteFault::Constructor(other.clone()));
                    }
                    if matched.tag != tag {
                        continue;
                    }
                    if args.len() != fields.0 {
                        return Err(RouteFault::Pattern);
                    }
                    columns.extend(args.map(Some));
                },
                Some(
                    TermView::Op { .. }
                    | TermView::Results { .. }
                    | TermView::Inst { .. }
                    | TermView::Abs { .. },
                ) => {
                    return Err(RouteFault::Pattern);
                },
            }
            rows.push(Row {
                columns,
                bindings,
                rule: row.rule,
            });
        }
        let mut levels: Vec<Level> = next
            .levels
            .iter()
            .enumerate()
            .filter(|&(position, _)| position != column.0)
            .map(|(_, &kept)| kept)
            .collect();
        levels.extend((next.depth.0 .. next.depth.0.saturating_add(fields.0)).map(Level));
        let child = NodeAt(nodes.len());
        nodes.push(None);
        work.push(Work {
            at: child,
            depth: Depth(next.depth.0.saturating_add(fields.0)),
            levels,
            rows,
        });
        branches.push((fields, child));
    }

    Ok(PlanNode::Switch {
        level,
        depth: next.depth,
        family,
        branches,
    })
}

/// The constructor `name` names.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the table's entry for `name`.
/// - fails: [`RouteFault::Constructor`] when the table has none.
/// - panics: none.
///
/// # Errors
/// [`RouteFault::Constructor`].
///
/// # Adequacy
/// - hypothesis: L3 — each written constructor resolves to its table entry, so
///   the tree's cases switch on the right family.
/// - witness: `operation::tests::a_many_out_operation_lowers_to_a_function_the_checker_accepts`
#[spec(ensures: |ret| ret.as_ref().is_err() || ret.as_ref().ok() == table.constructors.get(name))]
fn constructor(
    table: &RouteTable,
    name: &Name,
) -> Result<RouteConstructor, RouteFault>
{
    table
        .constructors
        .get(name)
        .copied()
        .ok_or_else(|| RouteFault::Constructor(name.clone()))
}

/// Plan the leaf where `row` is the first rule left: its right-hand side over
/// what its patterns bound.
///
/// # Specification
/// - requires: every undecided column of `row` is a variable or untested;
///   `levels` gives each its level.
/// - ensures: a leaf at `depth` whose steps build the right-hand side of
///   `face`.
/// - fails: [`RouteFault::Pattern`] for an undecided operation or tuple
///   pattern; the right-hand side's faults from [`steps`].
/// - panics: none.
///
/// # Errors
/// [`RouteFault`].
///
/// # Adequacy
/// - hypothesis: L3 — as [`plan_operation`].
/// - witness: `operation::tests::a_many_out_operation_lowers_to_a_function_the_checker_accepts`
#[spec(ensures: |ret| ret.as_ref().is_err() || matches!(ret.as_ref(), Ok(PlanNode::Leaf { depth: at, .. }) if *at == depth))]
fn leaf(
    row: &Row<'_>,
    levels: &[Level],
    depth: Depth,
    face: &RuleFace,
    operation: &OperDesc,
    table: &RouteTable,
) -> Result<PlanNode, RouteFault>
{
    let mut bindings = row.bindings.clone();
    for (column, &level) in row.columns.iter().zip(levels) {
        match column.map(TermNode::view) {
            None => {},
            Some(TermView::Var(variable)) => bindings.push((variable, level)),
            Some(
                TermView::Ctor { .. }
                | TermView::Op { .. }
                | TermView::Results { .. }
                | TermView::Inst { .. }
                | TermView::Abs { .. },
            ) => {
                return Err(RouteFault::Pattern);
            },
        }
    }

    Ok(PlanNode::Leaf {
        depth,
        steps: steps(face.rhs.to_node(), &bindings, operation, table)?,
    })
}

/// A right-hand side's place in the walk that plans it.
#[derive(Clone, Copy)]
enum Visit<'face>
{
    /// Plan the node's arguments, then the node.
    Enter(TermNode<'face>, Rooted),
    /// Plan the node, its arguments planned.
    Exit(TermNode<'face>, Rooted),
}

/// Whether a right-hand node is the root, whose value the operation returns.
#[derive(Clone, Copy, Eq, PartialEq)]
enum Rooted
{
    /// The root.
    Root,
    /// An argument of another node.
    Inner,
}

/// The instructions that build `rhs` over the variables `bindings` bound.
///
/// # Specification
/// - requires: `bindings` holds each bound variable's level.
/// - ensures: post-order instructions ending in [`Step::Return`],
///   [`Step::Deliver`] or [`Step::Tail`].
/// - fails: [`RouteFault::Unbound`], [`RouteFault::Callee`],
///   [`RouteFault::Constructor`], [`RouteFault::Pattern`] for a constructor
///   over the wrong field count, [`RouteFault::Results`] for a tuple below the
///   root, and [`RouteFault::Instantiated`] for an instantiation.
/// - panics: none.
///
/// # Errors
/// [`RouteFault`].
///
/// # Adequacy
/// - hypothesis: L3 — as [`plan_operation`].
/// - witness: `operation::tests::a_many_out_operation_lowers_to_a_function_the_checker_accepts`
/// - witness: `operation::tests::an_operation_calling_a_later_one_is_not_callable`
#[spec(ensures: |ret| ret.as_ref().is_err() || ret.as_ref().is_ok_and(|planned| matches!(planned.last(), Some(Step::Return | Step::Deliver(_) | Step::Tail { .. }))))]
fn steps(
    rhs: TermNode<'_>,
    bindings: &[(&Name, Level)],
    operation: &OperDesc,
    table: &RouteTable,
) -> Result<Vec<Step>, RouteFault>
{
    let mut planned = Vec::new();
    let mut stack = vec![Visit::Enter(rhs, Rooted::Root)];
    while let Some(visit) = stack.pop() {
        match visit {
            Visit::Enter(node, rooted) => {
                stack.push(Visit::Exit(node, rooted));
                let arguments: Vec<TermNode<'_>> = match node.view() {
                    TermView::Var(_) => Vec::new(),
                    TermView::Ctor { args, .. }
                    | TermView::Op { args, .. }
                    | TermView::Results { args }
                    | TermView::Inst { args, .. }
                    | TermView::Abs { args, .. } => args.collect(),
                };
                stack.extend(
                    arguments
                        .into_iter()
                        .rev()
                        .map(|argument| Visit::Enter(argument, Rooted::Inner)),
                );
            },
            Visit::Exit(node, rooted) => match node.view() {
                TermView::Var(variable) => {
                    let Some(&(_, level)) =
                        bindings.iter().rev().find(|&&(bound, _)| bound == variable)
                    else {
                        return Err(RouteFault::Unbound(variable.clone()));
                    };
                    planned.push(Step::Variable(level));
                    if rooted == Rooted::Root {
                        planned.push(Step::Return);
                    }
                },
                TermView::Ctor { name, args } => {
                    let built = constructor(table, name)?;
                    if args.len() != built.fields.0 {
                        return Err(RouteFault::Pattern);
                    }
                    planned.push(Step::Construct {
                        family: built.family,
                        tag: built.tag,
                        fields: built.fields,
                    });
                    if rooted == Rooted::Root {
                        planned.push(Step::Return);
                    }
                },
                TermView::Op { name, args } => {
                    let callee = if *name == operation.name {
                        Callee::Itself
                    }
                    else {
                        table
                            .callees
                            .get(name)
                            .copied()
                            .map(Callee::Earlier)
                            .ok_or_else(|| RouteFault::Callee(name.clone()))?
                    };
                    let arguments = Width(args.len());
                    planned.push(match rooted {
                        Rooted::Root => Step::Tail { callee, arguments },
                        Rooted::Inner => Step::Call { callee, arguments },
                    });
                },
                TermView::Results { args } => {
                    if rooted == Rooted::Inner {
                        return Err(RouteFault::Results);
                    }
                    planned.push(Step::Deliver(Width(args.len())));
                },
                TermView::Inst { name, .. } => return Err(RouteFault::Instantiated(name.clone())),
                TermView::Abs { .. } => return Err(RouteFault::Pattern),
            },
        }
    }

    Ok(planned)
}

/// Where minting writes: the arena, the origin table and the origin every
/// node of one operation records.
struct Mint<'run>
{
    /// The arena.
    arena: &'run mut CoreArena,
    /// The origin table.
    origins: &'run mut OriginTable,
    /// The operation's origin: its name in its family's declaration.
    origin: Origin,
}

impl Mint<'_>
{
    /// Record `id`'s origin and return it.
    ///
    /// # Specification
    /// trivial.
    fn value(
        &mut self,
        id: ValueId,
    ) -> ValueId
    {
        self.origins.record_value(id, self.origin);
        id
    }

    /// Record `id`'s origin and return it.
    ///
    /// # Specification
    /// trivial.
    fn computation(
        &mut self,
        id: ComputationId,
    ) -> ComputationId
    {
        self.origins.record_computation(id, self.origin);
        id
    }

    /// Record `id`'s origin and return it.
    ///
    /// # Specification
    /// trivial.
    fn value_type(
        &mut self,
        id: ValueTypeId,
    ) -> ValueTypeId
    {
        self.origins.record_value_type(id, self.origin);
        id
    }

    /// Record `id`'s origin and return it.
    ///
    /// # Specification
    /// trivial.
    fn comp_type(
        &mut self,
        id: CompTypeId,
    ) -> CompTypeId
    {
        self.origins.record_comp_type(id, self.origin);
        id
    }

    /// The family `family` as a value type.
    ///
    /// # Specification
    /// trivial.
    fn family(
        &mut self,
        family: ConstantIndex,
    ) -> ValueTypeId
    {
        let minted = self.arena.value_type_data(family, Vec::new());
        self.value_type(minted)
    }

    /// The variable at `level` seen from `depth` binders.
    ///
    /// # Specification
    /// trivial.
    fn variable(
        &mut self,
        level: Level,
        depth: Depth,
    ) -> ValueId
    {
        let index = depth.0.saturating_sub(level.0).saturating_sub(1);
        let index = DeBruijnIndex::from(u32::try_from(index).unwrap_or(u32::MAX));
        let minted = self.arena.value_variable(Zone::Intuitionistic, index);
        self.value(minted)
    }
}

/// Mint `plan` as one declaration: its type and its body.
///
/// # Specification
/// - requires: `plan` came from [`plan_operation`]; every constant it names is
///   declared before the declaration it mints.
/// - ensures: `U (D₁ → … → Dₙ → F R)` with `R` the output family or the product
///   of the output families, and a thunk of one partial fixpoint over `n`
///   lambdas around the tree; every minted node records `origin`, and each case
///   the family it switches on.
/// - panics: none.
/// - executable: none — the minted terms' meaning is the checker's and the
///   machine's, which the witnesses run.
///
/// # Adequacy
/// - hypothesis: L3 — the function checks, and a leaf returns its results in
///   port order, which a swapped tuple or a dropped result would not.
/// - witness: `operation::tests::a_many_out_operation_lowers_to_a_function_the_checker_accepts`
/// - witness: `operation::tests::a_call_reaches_the_operation_before_a_builtin_of_its_name`
/// - witness: `operation::tests::a_leaf_delivers_its_results_in_port_order`
pub fn mint_operation(
    plan: &OperationPlan,
    arena: &mut CoreArena,
    origins: &mut OriginTable,
    origin: Origin,
) -> (ValueTypeId, ValueId)
{
    let mut mint = Mint {
        arena,
        origins,
        origin,
    };
    let outputs: Vec<ValueTypeId> = plan
        .outputs
        .iter()
        .map(|&family| mint.family(family))
        .collect();
    let result = match *outputs.as_slice() {
        [single] => single,
        ref several => {
            let minted = mint.arena.value_type_product(several);
            mint.value_type(minted)
        },
    };
    let returner = mint.arena.comp_type_returner(result);
    let motive = mint.comp_type(returner);
    let mut signature = motive;
    for &family in plan.inputs.iter().rev() {
        let domain = mint.family(family);
        let arrow = mint.arena.comp_type_arrow(domain, signature);
        signature = mint.comp_type(arrow);
    }
    let thunked = mint.arena.value_type_thunk(signature);
    let declared = mint.value_type(thunked);

    let mut minted: Vec<Option<ComputationId>> = vec![None; plan.nodes.len()];
    for (position, node) in plan.nodes.iter().enumerate().rev() {
        let computation = match *node {
            PlanNode::Leaf { depth, ref steps } => leaf_body(&mut mint, depth, steps),
            PlanNode::Switch {
                level,
                depth,
                family,
                ref branches,
            } => {
                let mut lowered = Vec::with_capacity(branches.len());
                for &(fields, child) in branches {
                    let mut branch = minted.get(child.0).copied().flatten();
                    for _field in 0 .. fields.0 {
                        branch = branch.map(|body| {
                            let lambda = mint.arena.computation_lambda(body);
                            mint.computation(lambda)
                        });
                    }
                    lowered.extend(branch);
                }
                let scrutinee = mint.variable(level, depth);
                let case = mint.arena.computation_data_case(scrutinee, motive, lowered);
                mint.origins.record_elimination(case, family);
                mint.computation(case)
            },
        };
        if let Some(entry) = minted.get_mut(position) {
            *entry = Some(computation);
        }
    }
    let mut body = minted.first().copied().flatten().unwrap_or_else(|| {
        let empty = mint.arena.value_tuple(&[]);
        let empty = mint.value(empty);
        let returned = mint.arena.computation_return(empty);
        mint.computation(returned)
    });
    for _input in &plan.inputs {
        let lambda = mint.arena.computation_lambda(body);
        body = mint.computation(lambda);
    }
    let fixpoint = mint
        .arena
        .computation_fixpoint(body, FixpointEvidence::Partial);
    let fixpoint = mint.computation(fixpoint);
    let thunk = mint.arena.value_thunk(fixpoint);

    (declared, mint.value(thunk))
}

/// A value's position among the values a leaf builds.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct BuiltAt(usize);

/// One value a leaf builds: a bound variable or a constructor over earlier
/// values, by position.
#[derive(Clone, Debug)]
enum Built
{
    /// The value at a level.
    Bound(Level),
    /// A constructor over the values at these positions.
    Constructed
    {
        /// The constructed family.
        family: ConstantIndex,
        /// The constructor.
        tag: ConstructorTag,
        /// Its fields' positions among the built values.
        fields: Vec<BuiltAt>,
    },
}

/// How a leaf ends.
enum Ending
{
    /// Return the value at a position.
    Return(BuiltAt),
    /// Return the values at these positions as one tuple.
    Deliver(Vec<BuiltAt>),
    /// Call a function on the values at these positions.
    Tail(Callee, Vec<BuiltAt>),
}

/// Mint a leaf's instructions at `depth` binders: each call below the root
/// bound in order, then the ending.
///
/// # Specification
/// - requires: `steps` came from [`steps`].
/// - ensures: the binds of the calls in post-order around the ending; an
///   instruction list without an ending mints the empty tuple's return.
/// - panics: none.
/// - executable: none — the minted terms' meaning is the checker's and the
///   machine's, which the witnesses run.
///
/// # Adequacy
/// - hypothesis: L3 — as [`mint_operation`].
/// - witness: `operation::tests::a_leaf_delivers_its_results_in_port_order`
fn leaf_body(
    mint: &mut Mint<'_>,
    depth: Depth,
    steps: &[Step],
) -> ComputationId
{
    let mut built: Vec<Built> = Vec::new();
    let mut stack: Vec<BuiltAt> = Vec::new();
    let mut calls: Vec<(Callee, Vec<BuiltAt>)> = Vec::new();
    let mut ending = Ending::Deliver(Vec::new());
    for &step in steps {
        match step {
            Step::Variable(level) => {
                stack.push(BuiltAt(built.len()));
                built.push(Built::Bound(level));
            },
            Step::Construct {
                family,
                tag,
                fields,
            } => {
                let fields = stack.split_off(stack.len().saturating_sub(fields.0));
                stack.push(BuiltAt(built.len()));
                built.push(Built::Constructed {
                    family,
                    tag,
                    fields,
                });
            },
            Step::Call { callee, arguments } => {
                let arguments = stack.split_off(stack.len().saturating_sub(arguments.0));
                let level = Level(depth.0.saturating_add(calls.len()));
                calls.push((callee, arguments));
                stack.push(BuiltAt(built.len()));
                built.push(Built::Bound(level));
            },
            Step::Tail { callee, arguments } => {
                let arguments = stack.split_off(stack.len().saturating_sub(arguments.0));
                ending = Ending::Tail(callee, arguments);
            },
            Step::Return => {
                ending = Ending::Return(stack.pop().unwrap_or(BuiltAt(usize::MAX)));
            },
            Step::Deliver(width) => {
                ending = Ending::Deliver(stack.split_off(stack.len().saturating_sub(width.0)));
            },
        }
    }
    let at = Depth(depth.0.saturating_add(calls.len()));
    let mut chain = match ending {
        Ending::Return(position) => {
            let value = built_value(mint, &built, position, at);
            let returned = mint.arena.computation_return(value);
            mint.computation(returned)
        },
        Ending::Deliver(positions) => {
            let components: Vec<ValueId> = positions
                .iter()
                .map(|&position| built_value(mint, &built, position, at))
                .collect();
            let tuple = mint.arena.value_tuple(&components);
            let tuple = mint.value(tuple);
            let returned = mint.arena.computation_return(tuple);
            mint.computation(returned)
        },
        Ending::Tail(callee, arguments) => call(mint, &built, callee, &arguments, at),
    };
    for (bound, &(callee, ref arguments)) in calls.iter().enumerate().rev() {
        let around = Depth(depth.0.saturating_add(bound));
        let called = call(mint, &built, callee, arguments, around);
        let bind = mint.arena.computation_bind(called, chain);
        chain = mint.computation(bind);
    }

    chain
}

/// Mint a call of `callee` on the built values at `arguments`, at `depth`
/// binders.
///
/// # Specification
/// - requires: `depth` counts the operation's own binder at level zero.
/// - ensures: the forced function applied to each argument in order.
/// - panics: none.
/// - executable: none — the minted terms' meaning is the checker's and the
///   machine's, which the witnesses run.
///
/// # Adequacy
/// - hypothesis: L3 — as [`mint_operation`].
/// - witness: `operation::tests::a_call_reaches_the_operation_before_a_builtin_of_its_name`
fn call(
    mint: &mut Mint<'_>,
    built: &[Built],
    callee: Callee,
    arguments: &[BuiltAt],
    depth: Depth,
) -> ComputationId
{
    let function = match callee {
        Callee::Itself => mint.variable(Level(0), depth),
        Callee::Earlier(constant) => {
            let minted = mint.arena.value_constant(constant);
            mint.value(minted)
        },
    };
    let forced = mint.arena.computation_force(function);
    let mut applied = mint.computation(forced);
    for &argument in arguments {
        let value = built_value(mint, built, argument, depth);
        let application = mint.arena.computation_application(applied, value);
        applied = mint.computation(application);
    }

    applied
}

/// Mint the built value at `root` at `depth` binders, its fields first, by
/// an explicit work stack.
///
/// # Specification
/// - requires: each constructed value's fields sit at earlier positions.
/// - ensures: the value, with each variable indexed from `depth`; a position
///   with no built value mints the empty tuple.
/// - panics: none.
/// - executable: none — the minted terms' meaning is the checker's and the
///   machine's, which the witnesses run.
///
/// # Adequacy
/// - hypothesis: L3 — as [`mint_operation`].
/// - witness: `operation::tests::a_leaf_delivers_its_results_in_port_order`
fn built_value(
    mint: &mut Mint<'_>,
    built: &[Built],
    root: BuiltAt,
    depth: Depth,
) -> ValueId
{
    let mut minted: BTreeMap<BuiltAt, ValueId> = BTreeMap::new();
    let mut stack = vec![(root, false)];
    while let Some((position, expanded)) = stack.pop() {
        let value = match built.get(position.0) {
            None => {
                let empty = mint.arena.value_tuple(&[]);
                mint.value(empty)
            },
            Some(&Built::Bound(level)) => mint.variable(level, depth),
            Some(&Built::Constructed {
                family,
                tag,
                ref fields,
            }) => {
                if !expanded {
                    stack.push((position, true));
                    stack.extend(fields.iter().map(|&field| (field, false)));
                    continue;
                }
                let datatype = mint.family(family);
                let values = fields
                    .iter()
                    .map(|field| minted.get(field).copied())
                    .collect::<Option<Vec<_>>>()
                    .unwrap_or_default();
                let constructed = mint.arena.value_constructor(datatype, tag, values);
                mint.value(constructed)
            },
        };
        minted.insert(position, value);
    }

    minted.get(&root).copied().unwrap_or_else(|| {
        let empty = mint.arena.value_tuple(&[]);
        mint.value(empty)
    })
}
