//! The body of each requested function as THIR of the fragment.
//!
//! The fragment is an integer literal, a read of the one parameter, `if`,
//! `return` and a call of a requested function. The read happens before the
//! build of MIR, which takes each body's THIR away. A node with no meaning for
//! the fragment is read through: a scope, a coercion to the never type, a
//! block with no statement and a tail, and a block whose one statement is an
//! expression of type `!` with no tail. Each other node stops the body, and
//! the staging names the first such node.
//!
//! The walk keeps a stack of its own, so a deep body overflows no stack. It
//! writes each node after its children, so a reader folds the nodes in order.

use std::collections::HashMap;
use std::collections::HashSet;

use gandr_runtime_rust_record::Body;
use gandr_runtime_rust_record::FunctionPath;
use gandr_runtime_rust_record::ItemPath;
use gandr_runtime_rust_record::Literal;
use gandr_runtime_rust_record::Magnitude;
use gandr_runtime_rust_record::Node;
use gandr_runtime_rust_record::NodeIndex;
use gandr_runtime_rust_record::NodeName;
use gandr_runtime_rust_record::Outside;
use gandr_runtime_rust_record::Sign;
use gandr_runtime_rust_record::Staging;
use rustc_ast::LitKind;
use rustc_hir::def_id::LocalDefId;
use rustc_middle::thir::ExprId;
use rustc_middle::thir::ExprKind;
use rustc_middle::thir::LocalVarId;
use rustc_middle::thir::PatKind;
use rustc_middle::thir::StmtKind;
use rustc_middle::thir::Thir;
use rustc_middle::ty;
use rustc_middle::ty::TyCtxt;

/// The staging of each requested function that the crate defines.
pub(crate) fn bodies(
    tcx: TyCtxt<'_>,
    local: &HashMap<String, LocalDefId>,
    paths: &[FunctionPath],
) -> HashMap<FunctionPath, Staging>
{
    let mut requested = HashMap::new();
    for path in paths {
        if let Some(&def_id) = local.get(path.as_ref()) {
            requested.insert(def_id.to_def_id(), path.clone());
        }
    }
    let mut bodies = HashMap::with_capacity(requested.len());
    for (&def_id, path) in &requested {
        let Some(local) = def_id.as_local()
        else {
            continue;
        };
        let staging = match tcx.thir_body(local) {
            Ok((thir, root)) => Walk {
                tcx,
                thir: &thir.borrow(),
                requested: &requested,
            }
            .stage(root),
            Err(_) => Staging::Outside(Outside::Node(NodeName::from("Body"))),
        };
        bodies.insert(path.clone(), staging);
    }
    bodies
}

/// One body's walk: the THIR it reads and the functions that a call may name.
struct Walk<'walk, 'tcx>
{
    /// The compiler's context, which prints an item's path.
    tcx: TyCtxt<'tcx>,
    /// The body's THIR.
    thir: &'walk Thir<'tcx>,
    /// The requested functions, each by its definition.
    requested: &'walk HashMap<rustc_hir::def_id::DefId, FunctionPath>,
}

/// A step of the walk: the first visit of a node, which pushes its
/// children, or the second, which writes it.
#[derive(Clone, Copy)]
enum Step
{
    /// Push the node's children, then the node's second visit.
    Enter(ExprId),
    /// Write the node, whose children stand written.
    Leave(ExprId),
}

impl Walk<'_, '_>
{
    /// The staging of the body whose root is `root`.
    fn stage(
        &self,
        root: ExprId,
    ) -> Staging
    {
        match self.nodes(root) {
            Ok(nodes) => Staging::Staged(Body { nodes }),
            Err(outside) => Staging::Outside(outside),
        }
    }

    /// The parameter's variable, when the function takes one parameter
    /// bound to a plain name.
    fn parameter(&self) -> Option<LocalVarId>
    {
        let [ref param] = *self.thir.params.raw
        else {
            return None;
        };
        match param.pat.as_deref()?.kind {
            PatKind::Binding {
                var,
                subpattern: None,
                ..
            } => Some(var),
            _ => None,
        }
    }

    /// The nodes of the body, each after its children, or the first node
    /// outside the fragment.
    fn nodes(
        &self,
        root: ExprId,
    ) -> Result<Vec<Node>, Outside>
    {
        let parameter = self.parameter();
        let mut nodes = Vec::new();
        let mut placed: HashMap<ExprId, NodeIndex> = HashMap::new();
        let mut entered: HashSet<ExprId> = HashSet::new();
        let mut stack = vec![Step::Enter(root)];
        while let Some(step) = stack.pop() {
            match step {
                Step::Enter(id) => {
                    let id = self.through(id)?;
                    if !entered.insert(id) {
                        continue;
                    }
                    stack.push(Step::Leave(id));
                    for &child in self.children(id)?.iter().rev() {
                        stack.push(Step::Enter(child));
                    }
                },
                Step::Leave(id) => {
                    if nodes.len() >= Body::CEILING {
                        return Err(Outside::Large);
                    }
                    let node = self.node(id, parameter, &placed)?;
                    let index = u32::try_from(nodes.len()).map_err(|_| Outside::Large)?;
                    placed.insert(id, NodeIndex::from(index));
                    nodes.push(node);
                },
            }
        }
        Ok(nodes)
    }

    /// The node that `id` stands for, past each wrapper.
    fn through(
        &self,
        mut id: ExprId,
    ) -> Result<ExprId, Outside>
    {
        loop {
            match self.thir.exprs[id].kind {
                ExprKind::Scope { value, .. } => id = value,
                ExprKind::NeverToAny { source } => id = source,
                ExprKind::Block { block } => {
                    let block = &self.thir.blocks[block];
                    match (&*block.stmts, block.expr) {
                        ([], Some(tail)) => id = tail,
                        (&[statement], None) => match self.thir.stmts[statement].kind {
                            StmtKind::Expr { expr, .. } if self.thir.exprs[expr].ty.is_never() => {
                                id = expr;
                            },
                            StmtKind::Expr { .. } | StmtKind::Let { .. } => {
                                return Err(named("Block"));
                            },
                        },
                        _ => return Err(named("Block")),
                    }
                },
                _ => return Ok(id),
            }
        }
    }

    /// The children of the fragment's node `id`, in written order.
    fn children(
        &self,
        id: ExprId,
    ) -> Result<Vec<ExprId>, Outside>
    {
        Ok(match self.thir.exprs[id].kind {
            ExprKind::If {
                cond,
                then,
                else_opt: Some(otherwise),
                ..
            } => vec![cond, then, otherwise],
            ExprKind::Return { value: Some(value) } => vec![value],
            ExprKind::Call { ref args, .. } => match **args {
                [argument] => vec![argument],
                _ => return Err(named("Call")),
            },
            _ => Vec::new(),
        })
    }

    /// The fragment's node for `id`, whose children stand at `placed`.
    fn node(
        &self,
        id: ExprId,
        parameter: Option<LocalVarId>,
        placed: &HashMap<ExprId, NodeIndex>,
    ) -> Result<Node, Outside>
    {
        let at = |child: ExprId| -> Result<NodeIndex, Outside> {
            let child = self.through(child)?;
            placed.get(&child).copied().ok_or_else(|| named("Shared"))
        };
        let expr = &self.thir.exprs[id];
        Ok(match expr.kind {
            ExprKind::Literal { lit, neg } => match lit.node {
                LitKind::Int(value, _) => Node::Literal(Literal {
                    sign: if neg { Sign::Minus } else { Sign::Plus },
                    magnitude: Magnitude::from(value.get()),
                }),
                _ => return Err(named("Literal")),
            },
            ExprKind::VarRef { id: var } if Some(var) == parameter => Node::Parameter,
            ExprKind::If {
                cond,
                then,
                else_opt: Some(otherwise),
                ..
            } => Node::If {
                condition: at(cond)?,
                then: at(then)?,
                otherwise: at(otherwise)?,
            },
            ExprKind::Return { value: Some(value) } => Node::Return(at(value)?),
            ExprKind::Call { fun, ref args, .. } => {
                let callee = self.callee(fun)?;
                let [argument] = **args
                else {
                    return Err(named("Call"));
                };
                Node::Call {
                    callee,
                    argument: at(argument)?,
                }
            },
            ref kind => return Err(Outside::Node(NodeName::from(kind_name(kind)))),
        })
    }

    /// The requested function that the call's callee `fun` names.
    fn callee(
        &self,
        fun: ExprId,
    ) -> Result<FunctionPath, Outside>
    {
        let fun = self.through(fun)?;
        let expr = &self.thir.exprs[fun];
        let (ExprKind::ZstLiteral { .. }, &ty::FnDef(def_id, args)) = (&expr.kind, expr.ty.kind())
        else {
            return Err(named("Call"));
        };
        match self.requested.get(&def_id) {
            Some(path) if args.skip_binder().is_empty() => Ok(path.clone()),
            _ => Err(Outside::Callee(ItemPath::from(
                self.tcx.def_path_str(def_id),
            ))),
        }
    }
}

/// The node of the fragment's own name `name`, outside the fragment.
fn named(name: &str) -> Outside
{
    Outside::Node(NodeName::from(name))
}

/// The name of a kind of node, as rustc's `ExprKind` spells its variant.
fn kind_name(kind: &ExprKind<'_>) -> String
{
    let spelled = format!("{kind:?}");
    spelled
        .split(|character: char| !character.is_alphanumeric() && character != '_')
        .next()
        .unwrap_or("Expr")
        .to_owned()
}
