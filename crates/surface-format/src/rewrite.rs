//! The rewrites between the explicit and the sugared spellings: a table of
//! named rewrites, each moving one form between its two spellings, applied on
//! the concrete syntax tree so every comment rides along.
//!
//! A form is respelled from its children: its operands, already respelled,
//! keep their own leaves and comments; its own tiles are replaced by the
//! other spelling's; its own comments are placed by the operand they
//! followed. An operand whose binding is looser than its new position admits
//! is parenthesised, and a parenthesised operand whose binding fits is
//! unwrapped, as the presentation printer writes them (`gandr-surface-pretty`,
//! § Two forms, one walk).

use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use alloc::vec::Vec;
use core::fmt;

use anodized::spec;
use gandr_surface_grammar::Pbg;
use gandr_surface_grammar::Spelling as GrammarSpelling;
use gandr_surface_grammar::UNRESTRICTED;
use gandr_surface_syntax::ByteOffset;
use gandr_surface_syntax::ByteSpan;
use gandr_surface_syntax::NodeIndex;
use gandr_surface_syntax::NodeLabel;
use gandr_surface_syntax::SourceFragment;
use gandr_surface_syntax::SyntaxTree;

use crate::Form;
use crate::composite::Motives;
use crate::composite::Spaced;
use crate::composite::Standing;
use crate::composite::Token;
use crate::leaf::Copied;
use crate::leaf::Documentation;
use crate::leaf::Leaf;
use crate::leaf::Material;
use crate::leaf::Owner;
use crate::leaf::copied;
use crate::linear::Runs;
use crate::tail::Exit;
use crate::tail::Tails;

#[cfg(test)]
mod tests;

/// Which way a rewrite moves a form.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Direction
{
    /// From the explicit spelling to the sugared one: [`Form::Sugared`].
    Sugar,
    /// From the sugared spelling to the explicit one: [`Form::Explicit`].
    Desugar,
}

/// The pair of spellings a rewrite moves between.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum RewriteName
{
    /// The eager product: `#{A, B}` and `A * B`.
    Product,
    /// The sum: `+{A, B}` and `A + B`.
    Sum,
    /// The lazy product: `&{C, D}` and `C & D`.
    LazyProduct,
    /// The tuple: `#{a, b}` and `(a, b)`.
    Tuple,
    /// The value function: `+U (A -> -F B)` and `A => B`.
    ValueFunction,
    /// The default grade of a thunk type: `+U[ω] B` and `+U B`, both forms
    /// leaving it unwritten as the printer does.
    DefaultGrade,
    /// The path composite: `transport(\y. Path(A, a, y), q, p)` and
    /// `p then q`.
    PathComposite,
    /// The path inverse: `transport(\y. Path(A, y, a), p, here(a))` and
    /// `back(p)`.
    PathInverse,
    /// A map's action on a path: `transport(\y. Path(B, f(a), f(y)), p,
    /// here(f(a)))` and `cong(f, p)`.
    PathAction,
    /// A tail's exit: `return v` where a path through a body ends, over a
    /// value, and `v`; only the sugared form moves it, leaving out the
    /// keyword the lowering infers.
    TailReturn,
    /// The value-function alias at its shortest: `(A) => B` and `A => B`, a
    /// binder nothing later reads left out; only the sugared form moves it.
    ShortAlias,
    /// A `run` statement that only sequences a call: `run x <- c ; f(x)` and
    /// `f(c)`, where the lowering finds the binder read once, first; only the
    /// sugared form moves it, and only beside a checker that elaborates both.
    LinearRun,
}

impl fmt::Display for RewriteName
{
    /// The rewrite's name, as a caller selects it.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        f.write_str(match *self {
            Self::Product => "product",
            Self::Sum => "sum",
            Self::LazyProduct => "lazy-product",
            Self::Tuple => "tuple",
            Self::ValueFunction => "value-function",
            Self::DefaultGrade => "default-grade",
            Self::PathComposite => "path-composite",
            Self::PathInverse => "path-inverse",
            Self::PathAction => "path-action",
            Self::TailReturn => "tail-return",
            Self::ShortAlias => "short-alias",
            Self::LinearRun => "linear-run",
        })
    }
}

/// The grammar rule a rewrite reads: the form it applies to.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct MoldName(pub &'static str);

/// A spelling as the table shows it.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct Spelling(pub &'static str);

/// Whether a rewrite runs under its form when the caller names none.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Enabled
{
    /// It runs.
    On,
    /// It runs only when named.
    Off,
}

/// One rewrite of the table.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct Rewrite
{
    /// The pair of spellings it moves between.
    pub name: RewriteName,
    /// Which way it moves them.
    pub direction: Direction,
    /// The form it applies to.
    pub mold: MoldName,
    /// The spelling it reads.
    pub from: Spelling,
    /// The spelling it writes.
    pub to: Spelling,
    /// Whether it runs under its form when the caller names none.
    pub enabled: Enabled,
}

/// Every rewrite, by name, then direction.
pub const REWRITES: [Rewrite; 21] = [
    Rewrite {
        name: RewriteName::Product,
        direction: Direction::Sugar,
        mold: MoldName("telescope_type"),
        from: Spelling("#{A, B, …}"),
        to: Spelling("A * B * …"),
        enabled: Enabled::On,
    },
    Rewrite {
        name: RewriteName::Product,
        direction: Direction::Desugar,
        mold: MoldName("product_type"),
        from: Spelling("A * B * …"),
        to: Spelling("#{A, B, …}"),
        enabled: Enabled::On,
    },
    Rewrite {
        name: RewriteName::Sum,
        direction: Direction::Sugar,
        mold: MoldName("labelled_sum_type"),
        from: Spelling("+{A, B, …}"),
        to: Spelling("A + B + …"),
        enabled: Enabled::On,
    },
    Rewrite {
        name: RewriteName::Sum,
        direction: Direction::Desugar,
        mold: MoldName("sum_type"),
        from: Spelling("A + B + …"),
        to: Spelling("+{A, B, …}"),
        enabled: Enabled::On,
    },
    Rewrite {
        name: RewriteName::LazyProduct,
        direction: Direction::Sugar,
        mold: MoldName("lazy_record_type"),
        from: Spelling("&{C, D, …}"),
        to: Spelling("C & D & …"),
        enabled: Enabled::On,
    },
    Rewrite {
        name: RewriteName::LazyProduct,
        direction: Direction::Desugar,
        mold: MoldName("lazy_product_type"),
        from: Spelling("C & D & …"),
        to: Spelling("&{C, D, …}"),
        enabled: Enabled::On,
    },
    Rewrite {
        name: RewriteName::Tuple,
        direction: Direction::Sugar,
        mold: MoldName("telescope_expression"),
        from: Spelling("#{a, b, …}"),
        to: Spelling("(a, b, …)"),
        enabled: Enabled::On,
    },
    Rewrite {
        name: RewriteName::Tuple,
        direction: Direction::Desugar,
        mold: MoldName("parenthesized_expression"),
        from: Spelling("(a, b, …)"),
        to: Spelling("#{a, b, …}"),
        enabled: Enabled::On,
    },
    Rewrite {
        name: RewriteName::ValueFunction,
        direction: Direction::Sugar,
        mold: MoldName("u_type"),
        from: Spelling("+U (A -> B -> -F C)"),
        to: Spelling("(A, B) => C"),
        enabled: Enabled::On,
    },
    Rewrite {
        name: RewriteName::ValueFunction,
        direction: Direction::Desugar,
        mold: MoldName("value_function_type"),
        from: Spelling("(A, B) => C"),
        to: Spelling("+U (A -> B -> -F C)"),
        enabled: Enabled::On,
    },
    Rewrite {
        name: RewriteName::DefaultGrade,
        direction: Direction::Sugar,
        mold: MoldName("u_type"),
        from: Spelling("+U[ω] B"),
        to: Spelling("+U B"),
        enabled: Enabled::On,
    },
    Rewrite {
        name: RewriteName::DefaultGrade,
        direction: Direction::Desugar,
        mold: MoldName("u_type"),
        from: Spelling("+U[ω] B"),
        to: Spelling("+U B"),
        enabled: Enabled::On,
    },
    Rewrite {
        name: RewriteName::PathComposite,
        direction: Direction::Sugar,
        mold: MoldName("call_expression"),
        from: Spelling("transport(\\y. Path(A, a, y), q, p)"),
        to: Spelling("p then q"),
        enabled: Enabled::On,
    },
    Rewrite {
        name: RewriteName::PathComposite,
        direction: Direction::Desugar,
        mold: MoldName("binary_expression.then"),
        from: Spelling("p then q"),
        to: Spelling("transport(\\y. Path(A, a, y), q, p)"),
        enabled: Enabled::On,
    },
    Rewrite {
        name: RewriteName::PathInverse,
        direction: Direction::Sugar,
        mold: MoldName("call_expression"),
        from: Spelling("transport(\\y. Path(A, y, a), p, here(a))"),
        to: Spelling("back(p)"),
        enabled: Enabled::On,
    },
    Rewrite {
        name: RewriteName::PathInverse,
        direction: Direction::Desugar,
        mold: MoldName("call_expression"),
        from: Spelling("back(p)"),
        to: Spelling("transport(\\y. Path(A, y, a), p, here(a))"),
        enabled: Enabled::On,
    },
    Rewrite {
        name: RewriteName::PathAction,
        direction: Direction::Sugar,
        mold: MoldName("call_expression"),
        from: Spelling("transport(\\y. Path(B, f(a), f(y)), p, here(f(a)))"),
        to: Spelling("cong(f, p)"),
        enabled: Enabled::On,
    },
    Rewrite {
        name: RewriteName::PathAction,
        direction: Direction::Desugar,
        mold: MoldName("call_expression"),
        from: Spelling("cong(f, p)"),
        to: Spelling("transport(\\y. Path(B, f(a), f(y)), p, here(f(a)))"),
        enabled: Enabled::On,
    },
    Rewrite {
        name: RewriteName::TailReturn,
        direction: Direction::Sugar,
        mold: MoldName("return_expression"),
        from: Spelling("return v"),
        to: Spelling("v"),
        enabled: Enabled::On,
    },
    Rewrite {
        name: RewriteName::ShortAlias,
        direction: Direction::Sugar,
        mold: MoldName("value_function_type"),
        from: Spelling("(x : A) => B"),
        to: Spelling("A => B"),
        enabled: Enabled::On,
    },
    Rewrite {
        name: RewriteName::LinearRun,
        direction: Direction::Sugar,
        mold: MoldName("block"),
        from: Spelling("run x <- c ; f(x)"),
        to: Spelling("f(c)"),
        enabled: Enabled::On,
    },
];

/// Which rewrites a form runs.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub enum Selection
{
    /// Every enabled rewrite of the form's direction.
    #[default]
    Every,
    /// The rewrites of the form's direction with these names, enabled or not.
    Only(&'static [RewriteName]),
}

/// The rewrites one formatting runs: a direction and a selection.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Chosen
{
    /// The direction the form names.
    direction: Direction,
    /// Which of that direction's rewrites run.
    selection: Selection,
}

impl Chosen
{
    /// The rewrites `form` selects through `selection`; none for
    /// [`Form::Source`].
    ///
    /// # Specification
    /// trivial.
    pub const fn of(
        form: Form,
        selection: Selection,
    ) -> Option<Self>
    {
        match form {
            Form::Source => None,
            Form::Sugared => Some(Self {
                direction: Direction::Sugar,
                selection,
            }),
            Form::Explicit => Some(Self {
                direction: Direction::Desugar,
                selection,
            }),
        }
    }

    /// The rewrites chosen for the form whose rule is `rule`, in the table's
    /// order: the form takes the first that reads its shape.
    ///
    /// # Specification
    /// trivial.
    fn rewrites(
        self,
        rule: MoldName,
    ) -> impl Iterator<Item = RewriteName>
    {
        REWRITES
            .iter()
            .filter(move |rewrite| {
                rewrite.direction == self.direction
                    && rewrite.mold == rule
                    && match self.selection {
                        Selection::Every => rewrite.enabled == Enabled::On,
                        Selection::Only(names) => names.contains(&rewrite.name),
                    }
            })
            .map(|rewrite| rewrite.name)
    }
}

/// What respelling a top-level form did.
#[derive(Debug)]
pub enum Respelled<'source>
{
    /// No rewrite applied; the form keeps its leaves.
    Kept,
    /// The form's leaves, rewritten.
    Changed(Vec<Leaf<'source>>),
}

/// How tightly a type binds, tightest first: the bands of the grammar's type
/// precedence the printer parenthesises by.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum Band
{
    /// A name, a braced or parenthesised form, an application.
    Atom,
    /// A bridge: `+U C`, `-F A`.
    Bridge,
    /// A product `A * B`.
    Product,
    /// A sum `A + B`.
    Sum,
    /// A lazy product `C & D`.
    Lazy,
    /// An arrow, and anything looser.
    Loose,
}

impl Band
{
    /// The loosest band an operand at `position` among the operands of a
    /// form of the rule `rule` admits unparenthesised.
    ///
    /// # Specification
    /// trivial.
    fn admitted(
        rule: MoldName,
        position: Position,
    ) -> Self
    {
        match (rule.0, position) {
            ("u_type" | "f_type" | "f_type.row" | "at_type" | "binary_expression.then", _)
            | ("send_session_type" | "receive_session_type", Position::First) => Self::Atom,
            ("product_type", _) => Self::Bridge,
            ("sum_type", _) => Self::Product,
            ("lazy_product_type", _) => Self::Sum,
            ("function_type" | "value_function_type", Position::First) => Self::Lazy,
            _ => Self::Loose,
        }
    }

    /// The band a form of the rule `rule` binds at.
    ///
    /// # Specification
    /// trivial.
    fn of(rule: MoldName) -> Self
    {
        match rule.0 {
            "u_type" | "f_type" | "f_type.row" | "at_type" => Self::Bridge,
            "product_type" => Self::Product,
            "sum_type" => Self::Sum,
            "lazy_product_type" => Self::Lazy,
            "binary_expression.then"
            | "function_type"
            | "value_function_type"
            | "forall_type"
            | "static_abstraction"
            | "union_type"
            | "intersection_type"
            | "equivalence_type"
            | "isomorphism_type"
            | "universe_flow_type"
            | "send_session_type"
            | "receive_session_type"
            | "mu_session_type" => Self::Loose,
            _ => Self::Atom,
        }
    }
}

/// An operand of a form: a tile standing alone, or a nested form.
#[derive(Clone, Copy, Debug)]
enum Child<'source>
{
    /// A tile of another rule, or a form copied as written.
    Leaf(Leaf<'source>),
    /// A nested form.
    Node(NodeIndex),
}

/// What one child of a form is, among its parts.
#[derive(Clone, Copy, Debug)]
enum Role<'source>
{
    /// One of the form's own tiles.
    Own(SourceFragment<'source>),
    /// An operand.
    Operand(Child<'source>),
    /// A comment the form owns.
    Comment,
}

/// One child of a form beside the layout the source wrote before it.
#[derive(Clone, Debug)]
struct Part<'source>
{
    /// The whitespace before it, within the form.
    before: Vec<Leaf<'source>>,
    /// What it is.
    role: Role<'source>,
    /// Its leaves as respelled: a tile's or a comment's one leaf, or an
    /// operand's.
    leaves: Vec<Leaf<'source>>,
}

/// Whether a form owns a comment among its own children.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Commented
{
    /// It owns none.
    No,
    /// It owns one.
    Yes,
}

/// Whether a form is open to rewrites: outside every declaration the meaning
/// check withdrew them from.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Open
{
    /// Rewrites may move it.
    Yes,
    /// It keeps its spelling.
    No,
}

/// Where a part of a form begins among the leaves written for it.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Start
{
    /// The index of the first leaf of the layout before the part.
    layout: usize,
    /// The index of the part's own first leaf.
    own: usize,
}

/// What a respelled form is, as a form around it reads it.
#[derive(Clone, Debug)]
enum Shape<'source>
{
    /// Anything else.
    Other,
    /// A parenthesised form: its entries, and whether any is a binder.
    Parenthesized
    {
        /// The entries, in order.
        entries: Vec<Child<'source>>,
        /// Whether an entry binds a name, `x : A`.
        binder: Binder,
        /// The entries read as a list of domains, each with the name it
        /// binds; empty when the list is not one.
        domains: Vec<Domain<'source>>,
    },
    /// An arrow `A -> C`.
    Arrow
    {
        /// The domain.
        domain: Child<'source>,
        /// The codomain.
        codomain: Child<'source>,
    },
    /// A pure returner `-F A`.
    Returner
    {
        /// The value type it returns.
        result: Child<'source>,
    },
}

/// Whether a parenthesised list binds a name.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Binder
{
    /// No entry does.
    None,
    /// An entry does.
    Some,
}

/// One entry of a parenthesised list of domains, `A` or `x : A`.
#[derive(Clone, Copy, Debug)]
struct Domain<'source>
{
    /// The name the entry binds, `x` in `x : A`.
    name: Option<Child<'source>>,
    /// The entry's type, `A`.
    ty: Child<'source>,
}

/// One form, respelled.
#[derive(Clone, Debug)]
struct Spelled<'source>
{
    /// Its leaves.
    leaves: Vec<Leaf<'source>>,
    /// How tightly it binds.
    band: Band,
    /// What it is.
    shape: Shape<'source>,
    /// Whether it owns a comment.
    commented: Commented,
    /// Whether a rewrite respelled it.
    rewritten: Changed,
}

/// An operand as a new position reads it: its leaves and band, and, for a
/// parenthesised operand of one entry and no comment, the entry's.
#[derive(Clone, Debug)]
struct Operand<'source>
{
    /// Its leaves.
    leaves: Vec<Leaf<'source>>,
    /// How tightly it binds.
    band: Band,
    /// The entry inside its parentheses, when they can go.
    inner: Option<(Vec<Leaf<'source>>, Band)>,
}

/// One top-level form's respelling.
struct Respelling<'run, 'source>
{
    /// The grammar the tree was parsed under.
    grammar: &'run Pbg,
    /// The tree.
    tree: &'run SyntaxTree<'source>,
    /// The form's leaves, in offset order, whitespace included.
    leaves: &'run [Leaf<'source>],
    /// The top-level form.
    form: NodeIndex,
    /// The rewrites that run.
    chosen: Chosen,
    /// The spans no rewrite enters: declarations whose meaning cannot be
    /// checked.
    refused: &'run [ByteSpan],
    /// The motive of each path composite, by its span.
    motives: &'source Motives,
    /// The `return` forms written as their value.
    tails: &'source Tails,
    /// The `run` statements written away, each call at its binder's read.
    runs: &'source Runs,
    /// Each nested form respelled, by position.
    spelled: BTreeMap<NodeIndex, Spelled<'source>>,
    /// Each node's extent: its first leaf's start to its last leaf's end.
    extents: BTreeMap<NodeIndex, ByteSpan>,
    /// Each nested form's parent within the top-level form.
    parents: BTreeMap<NodeIndex, NodeIndex>,
    /// Whether a rewrite applied.
    changed: Changed,
    /// The spans of the path composites kept, no motive derived for them.
    unspelled: Vec<ByteSpan>,
    /// The derived path operations the sugared form wrote, by node: those a
    /// transport kept as written spells as written again.
    derivations: BTreeSet<NodeIndex>,
}

/// Whether a respelling changed a form.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Changed
{
    /// It did not.
    No,
    /// It did.
    Yes,
}

/// Where a form stands in its parent, as a rewrite whose spelling reads
/// otherwise elsewhere asks.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Context
{
    /// A type: after a `:`, an operand of a type former, or a static
    /// abstraction's body. Every spelling of the value-function alias reads
    /// here.
    Type,
    /// After a rule's `<=>`: a parenthesised list there is the rule's
    /// outputs, never a tuple.
    Outputs,
    /// An operation's judgment in a theory, after its `:`: a parenthesised
    /// list there opens the judgment's own port group, so only the
    /// value-function alias over one bare domain reads as a type (#1329).
    Judgment,
    /// A call's argument: a thunk type there is written as its thunk, as
    /// the printer writes it.
    Argument,
    /// Anywhere else: a value or a computation, where `() => A` reads as an
    /// expression and `A => B` as the value-function alias.
    Value,
}

/// Where an operand stands among its form's operands.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Position
{
    /// First.
    First,
    /// After the first.
    Later,
}

/// Whether a traversal is entering or leaving a node.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Visit
{
    /// Entering: its children come first.
    Enter,
    /// Leaving: its children are respelled.
    Leave,
}

/// What one formatting's rewrites read: the rewrites chosen, the spans they
/// do not enter, the motives of the path composites the lowering derived, the
/// tails whose `return` it would infer and the `run` statements that only
/// sequence a call.
#[derive(Clone, Copy, Debug)]
pub struct Rewrites<'run, 'source>
{
    /// The rewrites that run.
    pub chosen: Chosen,
    /// The spans no rewrite enters: declarations whose meaning cannot be
    /// checked.
    pub withdrawn: &'run [ByteSpan],
    /// The motive of each path composite, by its span.
    pub motives: &'source Motives,
    /// The `return` forms written as their value.
    pub tails: &'source Tails,
    /// The `run` statements written away, each call at its binder's read.
    pub runs: &'source Runs,
}

/// The top-level form `form` of `tree`, whose leaves are `leaves`, respelled
/// by the rewrites `rewrites` chooses, outside the spans it withdraws.
///
/// # Specification
/// - requires: `tree` was parsed under `grammar`, `form` is one of its root's
///   children, the parser did not repair it, and `leaves` are its leaves from
///   its first to its last, whitespace included, in offset order.
/// - ensures: [`Respelled::Kept`] when no chosen rewrite applies to a form
///   inside `form`; otherwise its leaves with each form a chosen rewrite
///   applies to respelled bottom-up — its operands' leaves kept, its own tiles
///   the other spelling's, its comments after the operand they followed, an
///   operand parenthesised where its band is looser than its position admits
///   and unwrapped where a parenthesis it was written in is not needed. Beside
///   it, the span of each path composite the explicit form would enter but that
///   keeps its spelling, no motive derived for it.
/// - provides: the leaves [`crate::format`] lays out in place of a form's.
/// - fails: never.
/// - panics: none.
/// - intension: one post-order walk of the form with an explicit stack.
///
/// # Adequacy
/// - hypothesis: L3 — each rewrite at each direction over one golden source
///   holding every pair, nested and with comments, and the corpus sweep.
/// - witness: `tests::rewrite::each_rewrite_moves_its_pair_both_ways`
/// - witness: `tests::rewrite::the_path_composite_moves_both_ways`
/// - witness: `tests::rewrite::a_sugared_source_keeps_every_comment_with_its_construct`
/// - witness: `tests::rewrite::sweeps::every_source_formats_into_either_form_and_keeps_its_meaning`
#[spec(ensures: |ret| !matches!(ret.0, Respelled::Changed(ref written) if written.is_empty()))]
pub fn respell<'source>(
    grammar: &Pbg,
    tree: &SyntaxTree<'source>,
    form: NodeIndex,
    leaves: &[Leaf<'source>],
    rewrites: Rewrites<'_, 'source>,
) -> (Respelled<'source>, Unspelled)
{
    let mut respelling = Respelling {
        grammar,
        tree,
        leaves,
        form,
        chosen: rewrites.chosen,
        refused: rewrites.withdrawn,
        motives: rewrites.motives,
        tails: rewrites.tails,
        runs: rewrites.runs,
        spelled: BTreeMap::new(),
        extents: BTreeMap::new(),
        parents: BTreeMap::new(),
        changed: Changed::No,
        unspelled: Vec::new(),
        derivations: BTreeSet::new(),
    };
    let mut stack: Vec<(NodeIndex, Visit)> = Vec::from([(form, Visit::Enter)]);
    while let Some((at, visit)) = stack.pop() {
        match visit {
            Visit::Enter => {
                stack.push((at, Visit::Leave));
                for child in tree.children(at) {
                    if respelling.interior(child) == Interior::Yes {
                        let _first = respelling.parents.insert(child, at);
                        stack.push((child, Visit::Enter));
                    }
                }
            },
            Visit::Leave => respelling.leave(at),
        }
    }
    let respelled = match (respelling.changed, respelling.spelled.remove(&form)) {
        (Changed::Yes, Some(spelled)) => Respelled::Changed(spelled.leaves),
        (Changed::No, _) | (Changed::Yes, None) => Respelled::Kept,
    };
    (respelled, Unspelled(respelling.unspelled))
}

/// The spans of the path composites a respelling kept, no motive derived for
/// them, in the order it met them.
#[repr(transparent)]
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Unspelled(pub Vec<ByteSpan>);

/// Whether a node is respelled from its children.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Interior
{
    /// A form, or documentation: respelled from its children.
    Yes,
    /// A leaf, or a form copied as written.
    No,
}

impl<'source> Respelling<'_, 'source>
{
    /// Whether the node at `at` is respelled from its children.
    ///
    /// # Specification
    /// trivial.
    fn interior(
        &self,
        at: NodeIndex,
    ) -> Interior
    {
        match self.tree.node(at).map(gandr_surface_syntax::Node::label) {
            Some(NodeLabel::Meld(mold)) => match copied(self.grammar, mold) {
                Copied::Verbatim => Interior::No,
                Copied::LaidOut => Interior::Yes,
            },
            Some(NodeLabel::Doc) => Interior::Yes,
            Some(
                NodeLabel::Wald
                | NodeLabel::Tile(_)
                | NodeLabel::Grout { .. }
                | NodeLabel::GhostClose { .. }
                | NodeLabel::Space,
            )
            | None => Interior::No,
        }
    }

    /// The grammar rule the form at `at` realises.
    ///
    /// # Specification
    /// trivial.
    fn rule(
        &self,
        at: NodeIndex,
    ) -> Option<MoldName>
    {
        let (NodeLabel::Meld(mold) | NodeLabel::Tile(mold)) = self.tree.node(at)?.label()
        else {
            return None;
        };
        let rule = self.grammar.rule_of(mold).ok()?;
        RULES
            .iter()
            .copied()
            .find(|known| known.0 == rule.name().0)
            .or(Some(MoldName("")))
    }

    /// Where the form at `at` stands in its parent: after a rule's `<=>`, in
    /// a theory's judgment, in a type, or anywhere else.
    ///
    /// # Specification
    /// trivial.
    fn context(
        &self,
        at: NodeIndex,
    ) -> Context
    {
        let Some(&parent) = self.parents.get(&at)
        else {
            return Context::Value;
        };
        let name = |node: NodeIndex| {
            let (NodeLabel::Meld(mold) | NodeLabel::Tile(mold)) = self.tree.node(node)?.label()
            else {
                return None;
            };
            self.grammar.rule_of(mold).ok().map(|rule| rule.name().0)
        };
        let rule = name(parent);
        let mut preceding = None;
        for child in self.tree.children(parent) {
            if child == at {
                break;
            }
            if let Some(node) = self.tree.node(child)
                && matches!(node.label(), NodeLabel::Tile(_))
                && name(child) == rule
            {
                preceding = self.leaf(node.span()).map(|leaf| leaf.text);
            }
        }
        match (rule, preceding.map(<&str>::from)) {
            (_, Some("<=>")) => Context::Outputs,
            (Some("theory_declaration"), Some(":")) => Context::Judgment,
            (_, Some(":")) => Context::Type,
            (Some(rule), _) if rule.ends_with("_type") || rule == "static_abstraction" => {
                Context::Type
            },
            (Some("call_expression"), _) => Context::Argument,
            _ => Context::Value,
        }
    }

    /// Spell again as written each derived path operation the sugared form
    /// wrote among the operands of the call whose parts are `parts`, when
    /// that call is a `transport(…)` kept as written, and every one each of
    /// those holds so in turn: the printer writes a derived operation
    /// standing as a transport's operand as the transport it derives,
    /// nothing there stating the operation's type. Whether any was.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Termination
    /// Each node enters the stack only when removed from the derivations, so
    /// at most once, and leaves it once.
    fn unsugar_operands(
        &mut self,
        parts: &[Part<'source>],
    ) -> Changed
    {
        let mut stack: Vec<(NodeIndex, Visit)> = Vec::new();
        self.derived_operands(parts, &mut stack);
        if stack.is_empty() {
            return Changed::No;
        }
        while let Some((at, visit)) = stack.pop() {
            let (parts, _) = self.parts(at);
            match visit {
                Visit::Enter => {
                    stack.push((at, Visit::Leave));
                    self.derived_operands(&parts, &mut stack);
                },
                Visit::Leave => {
                    let Some(&extent) = self.extents.get(&at)
                    else {
                        continue;
                    };
                    let commented = if parts.iter().any(|part| matches!(part.role, Role::Comment)) {
                        Commented::Yes
                    }
                    else {
                        Commented::No
                    };
                    // A derived call opens no block: no statement to write away.
                    let spelled = self.kept(
                        MoldName("call_expression"),
                        &parts,
                        extent,
                        (commented, Open::No),
                    );
                    let _previous = self.spelled.insert(at, spelled);
                },
            }
        }
        Changed::Yes
    }

    /// Push onto `stack`, to enter, each derived path operation the sugared
    /// form wrote among the operands of the call whose parts are `parts`,
    /// when that call is a `transport(…)`, removing each from the
    /// derivations.
    ///
    /// # Specification
    /// trivial.
    fn derived_operands(
        &mut self,
        parts: &[Part<'source>],
        stack: &mut Vec<(NodeIndex, Visit)>,
    )
    {
        let (_, operands) = split(parts);
        let Some((&callee, arguments)) = operands.split_first()
        else {
            return;
        };
        if self
            .tokens(callee)
            .iter()
            .map(|&token| <&str>::from(token))
            .ne(["transport"])
        {
            return;
        }
        for &argument in arguments {
            if let Child::Node(node) = argument
                && self.derivations.remove(&node)
            {
                stack.push((node, Visit::Enter));
            }
        }
    }

    /// The leaf of the form's leaves spanning exactly `span`.
    ///
    /// # Specification
    /// trivial.
    fn leaf(
        &self,
        span: ByteSpan,
    ) -> Option<Leaf<'source>>
    {
        let at = self
            .leaves
            .partition_point(|leaf| leaf.span.start() < span.start());
        self.leaves
            .get(at ..)?
            .iter()
            .find(|leaf| leaf.span == span && leaf.material != Material::Whitespace)
            .copied()
    }

    /// The whitespace leaves of the form between `from` and `to`.
    ///
    /// # Specification
    /// trivial.
    fn between(
        &self,
        from: ByteOffset,
        to: ByteOffset,
    ) -> Vec<Leaf<'source>>
    {
        let at = self.leaves.partition_point(|leaf| leaf.span.start() < from);
        self.leaves
            .get(at ..)
            .unwrap_or_default()
            .iter()
            .take_while(|leaf| leaf.span.end() <= to)
            .filter(|leaf| leaf.material == Material::Whitespace)
            .copied()
            .collect()
    }

    /// The node at `at` as one of its parent's parts, and its extent.
    ///
    /// # Specification
    /// trivial.
    fn part(
        &self,
        parent: MoldName,
        at: NodeIndex,
    ) -> Option<(Role<'source>, Vec<Leaf<'source>>, ByteSpan)>
    {
        let node = self.tree.node(at)?;
        if self.interior(at) == Interior::Yes {
            let spelled = self.spelled.get(&at)?;
            let extent = *self.extents.get(&at)?;
            let role = if node.label() == NodeLabel::Doc {
                Role::Comment
            }
            else {
                Role::Operand(Child::Node(at))
            };
            return Some((role, spelled.leaves.clone(), extent));
        }
        let leaf = self.leaf(node.span())?;
        let role = match node.label() {
            NodeLabel::Space => Role::Comment,
            NodeLabel::Tile(_) if self.rule(at) == Some(parent) => Role::Own(leaf.text),
            NodeLabel::Wald
            | NodeLabel::Meld(_)
            | NodeLabel::Tile(_)
            | NodeLabel::Grout { .. }
            | NodeLabel::GhostClose { .. }
            | NodeLabel::Doc => Role::Operand(Child::Leaf(leaf)),
        };
        Some((role, Vec::from([leaf]), leaf.span))
    }

    /// The parts of the form at `at`, in source order, and its extent.
    ///
    /// # Specification
    /// trivial.
    fn parts(
        &self,
        at: NodeIndex,
    ) -> (Vec<Part<'source>>, Option<ByteSpan>)
    {
        let rule = self.rule(at).unwrap_or(MoldName(""));
        let mut parts: Vec<Part<'source>> = Vec::new();
        let mut extent: Option<ByteSpan> = None;
        for child in self.tree.children(at) {
            let Some((role, leaves, span)) = self.part(rule, child)
            else {
                continue;
            };
            let before =
                extent.map_or_else(Vec::new, |extent| self.between(extent.end(), span.start()));
            extent = Some(extent.map_or(span, |extent| extent.join(span)));
            parts.push(Part {
                before,
                role,
                leaves,
            });
        }
        (parts, extent)
    }

    /// Respell the node at `at`, its children respelled.
    ///
    /// # Specification
    /// trivial.
    fn leave(
        &mut self,
        at: NodeIndex,
    )
    {
        let (parts, extent) = self.parts(at);
        let Some(extent) = extent
        else {
            return;
        };
        let _known = self.extents.insert(at, extent);
        let rule = self.rule(at).unwrap_or(MoldName(""));
        let commented = if parts.iter().any(|part| matches!(part.role, Role::Comment)) {
            Commented::Yes
        }
        else {
            Commented::No
        };
        let open = if self
            .refused
            .iter()
            .any(|span| span.start() <= extent.start() && extent.end() <= span.end())
        {
            Open::No
        }
        else {
            Open::Yes
        };
        let chosen = self.chosen;
        let rewritten = if open == Open::Yes {
            chosen.rewrites(rule).find_map(|name| {
                self.rewrite(name, at, &parts, extent)
                    .map(|spelled| (name, spelled))
            })
        }
        else {
            None
        };
        let spelled = if let Some((name, spelled)) = rewritten {
            if chosen.direction == Direction::Sugar
                && matches!(
                    name,
                    RewriteName::PathComposite | RewriteName::PathInverse | RewriteName::PathAction
                )
            {
                let _first = self.derivations.insert(at);
            }
            spelled
        }
        else {
            let parts = match self.unsugar_operands(&parts) {
                Changed::Yes => self.parts(at).0,
                Changed::No => parts,
            };
            self.kept(rule, &parts, extent, (commented, open))
        };
        let _previous = self.spelled.insert(at, spelled);
    }

    /// A form no rewrite reads, its parts as written but for an operand a
    /// rewrite respelled: that one placed at the band its position admits,
    /// and a parenthesis around one alone dropped once the operand binds
    /// tightest. Where the form is `open` to rewrites and opens a block, each
    /// `run` statement the lowering lists as linear is written away
    /// ([`Self::linear`]).
    ///
    /// # Specification
    /// trivial.
    fn kept(
        &mut self,
        rule: MoldName,
        parts: &[Part<'source>],
        extent: ByteSpan,
        (commented, open): (Commented, Open),
    ) -> Spelled<'source>
    {
        let shape = shape(rule, parts);
        if let Shape::Parenthesized {
            ref entries,
            binder: Binder::None,
            ..
        } = shape
            && let &[Child::Node(entry)] = entries.as_slice()
            && commented == Commented::No
            && let Some(inner) = self.spelled.get(&entry)
            && inner.rewritten == Changed::Yes
            && inner.band == Band::Atom
        {
            self.changed = Changed::Yes;
            return inner.clone();
        }
        let mut out = Builder {
            leaves: Vec::new(),
            position: ByteSpan::new(extent.start(), extent.start()).unwrap_or(extent),
            owner: Owner::Form(self.form),
        };
        let mut index = Position::First;
        let mut starts = Vec::with_capacity(parts.len());
        for part in parts {
            let before = out.leaves.len();
            out.leaves.extend(part.before.iter().copied());
            starts.push(Start {
                layout: before,
                own: out.leaves.len(),
            });
            match part.role {
                Role::Operand(child @ Child::Node(at))
                    if self
                        .spelled
                        .get(&at)
                        .is_some_and(|spelled| spelled.rewritten == Changed::Yes) =>
                {
                    let operand = Operand {
                        inner: None,
                        ..self.operand(child)
                    };
                    out.place(&operand, Band::admitted(rule, index));
                },
                Role::Own(_) | Role::Operand(_) | Role::Comment => {
                    out.leaves.extend(part.leaves.iter().copied());
                },
            }
            if matches!(part.role, Role::Operand(_)) {
                index = Position::Later;
            }
        }
        if open == Open::Yes
            && !self.runs.calls().is_empty()
            && self
                .chosen
                .rewrites(MoldName("block"))
                .any(|name| name == RewriteName::LinearRun)
            && self.linear(parts, &starts, &mut out.leaves) == Changed::Yes
        {
            self.changed = Changed::Yes;
        }
        Spelled {
            leaves: out.leaves,
            band: Band::of(rule),
            shape,
            commented,
            rewritten: Changed::No,
        }
    }

    /// Write away, in `leaves`, the leaves of a form whose parts are `parts`,
    /// each `run x <- c ;` statement among the parts whose call the lowering
    /// lists as a linear run: the call's leaves written in place of the
    /// binder's read, which stands in a later part, and the statement left
    /// out. `starts` holds, for each part, where its layout and its own leaves
    /// begin in `leaves`.
    ///
    /// The lowering lists the statements ending a block whose binders the
    /// tail reads in their order; they are taken last first, so each
    /// statement's range is read before a later one moves. A statement with a
    /// comment among its parts, or whose read stands in no later part, stays,
    /// and so does every statement before it: written at its read past one
    /// that stays, its call would run after that one's.
    ///
    /// # Specification
    /// trivial.
    fn linear(
        &self,
        parts: &[Part<'source>],
        starts: &[Start],
        leaves: &mut Vec<Leaf<'source>>,
    ) -> Changed
    {
        let total = leaves.len();
        let end = |part: usize| {
            starts
                .get(part.saturating_add(1))
                .map_or(total, |next| next.layout)
        };
        let own = |part: usize, spelled: &str| {
            parts.get(part).is_some_and(
                |part| matches!(part.role, Role::Own(text) if <&str>::from(text) == spelled),
            )
        };
        let statements: Vec<(usize, ByteSpan)> = (0 .. parts.len())
            .filter_map(|first| {
                let Role::Operand(call) = parts.get(first.checked_add(3)?)?.role
                else {
                    return None;
                };
                let called = match call {
                    Child::Node(at) => self.extents.get(&at).copied()?,
                    Child::Leaf(leaf) => leaf.span,
                };
                (own(first, "run")
                    // The binder is a tile of a rule the table reads no
                    // rewrite of, so it may read as one of the form's own.
                    && !matches!(parts.get(first.checked_add(1)?)?.role, Role::Comment)
                    && own(first.checked_add(2)?, "<-")
                    && own(first.checked_add(4)?, ";")
                    && self.runs.calls().binary_search(&called).is_ok())
                .then_some((first, called))
            })
            .collect();
        let mut changed = Changed::No;
        // The first part of the statement last written away; none yet.
        let mut following: Option<usize> = None;
        for &(first, called) in statements.iter().rev() {
            let after = first.saturating_add(5);
            let adjacent = following.map_or_else(
                || !(after .. parts.len()).any(|part| own(part, "run")),
                |next| {
                    parts.get(after .. next).is_some_and(|between| {
                        between
                            .iter()
                            .all(|part| matches!(part.role, Role::Comment))
                    })
                },
            );
            if !adjacent {
                break;
            }
            let (Some(&Start { layout: from, .. }), Some(&Start { own: call, .. })) =
                (starts.get(first), starts.get(first.saturating_add(3)))
            else {
                break;
            };
            let (call_end, through) = (end(first.saturating_add(3)), end(first.saturating_add(4)));
            let Some(read) = leaves
                .get(through ..)
                .and_then(|after| {
                    after.iter().position(|leaf| {
                        leaf.material == Material::Token
                            && self.runs.read(leaf.span) == Some(called)
                    })
                })
                .map(|offset| through.saturating_add(offset))
            else {
                break;
            };
            let written: Vec<Leaf<'source>> =
                leaves.get(call .. call_end).unwrap_or_default().to_vec();
            drop(leaves.splice(read ..= read, written));
            drop(leaves.drain(from .. through));
            changed = Changed::Yes;
            following = Some(first);
        }
        changed
    }

    /// The operand `child` as a new position reads it.
    ///
    /// # Specification
    /// trivial.
    fn operand(
        &self,
        child: Child<'source>,
    ) -> Operand<'source>
    {
        let spelled = |child: Child<'source>| match child {
            Child::Leaf(leaf) => Some((Vec::from([leaf]), Band::Atom)),
            Child::Node(at) => self
                .spelled
                .get(&at)
                .map(|spelled| (spelled.leaves.clone(), spelled.band)),
        };
        let Some((leaves, band)) = spelled(child)
        else {
            return Operand {
                leaves: Vec::new(),
                band: Band::Loose,
                inner: None,
            };
        };
        let inner = self.unwrapped(child).and_then(spelled);
        Operand {
            leaves,
            band,
            inner,
        }
    }

    /// The entry of the parenthesised operand `child`, when it holds one
    /// entry, binds no name and owns no comment.
    ///
    /// # Specification
    /// trivial.
    fn unwrapped(
        &self,
        child: Child<'source>,
    ) -> Option<Child<'source>>
    {
        let Child::Node(at) = child
        else {
            return None;
        };
        let spelled = self.spelled.get(&at)?;
        match (&spelled.shape, spelled.commented) {
            (
                &Shape::Parenthesized {
                    ref entries,
                    binder: Binder::None,
                    ..
                },
                Commented::No,
            ) => match entries.as_slice() {
                &[only] => Some(only),
                _ => None,
            },
            _ => None,
        }
    }

    /// `child` with every parenthesis that holds one entry around it
    /// removed.
    ///
    /// # Specification
    /// trivial.
    fn stripped(
        &self,
        child: Child<'source>,
    ) -> Child<'source>
    {
        let mut child = child;
        while let Some(inner) = self.unwrapped(child) {
            child = inner;
        }
        child
    }

    /// The shape of `child`, as respelled.
    ///
    /// # Specification
    /// trivial.
    fn shape_of(
        &self,
        child: Child<'source>,
    ) -> Option<(&Shape<'source>, Commented)>
    {
        let Child::Node(at) = child
        else {
            return None;
        };
        self.spelled
            .get(&at)
            .map(|spelled| (&spelled.shape, spelled.commented))
    }

    /// The form at `at`, whose parts are `parts`, respelled by the rewrite
    /// `name`, or nothing when its shape is not the one `name` reads.
    ///
    /// # Specification
    /// trivial.
    fn rewrite(
        &mut self,
        name: RewriteName,
        at: NodeIndex,
        parts: &[Part<'source>],
        extent: ByteSpan,
    ) -> Option<Spelled<'source>>
    {
        let position = ByteSpan::new(extent.start(), extent.start()).ok()?;
        let mut out = Builder {
            leaves: Vec::new(),
            position,
            owner: Owner::Form(self.form),
        };
        let direction = self.chosen.direction;
        let band = match (name, direction) {
            (RewriteName::Product, Direction::Sugar) => {
                let listed = listed(parts, &[OPEN_TELESCOPE], CLOSE_BRACE)?;
                self.infix(&mut out, &listed, parts, Spelling(" * "), [
                    Band::Bridge,
                    Band::Bridge,
                ])?;
                Band::Product
            },
            (RewriteName::Sum, Direction::Sugar) => {
                let listed = listed(parts, &[PLUS, OPEN_BRACE], CLOSE_BRACE)?;
                self.infix(&mut out, &listed, parts, Spelling(" + "), [
                    Band::Product,
                    Band::Product,
                ])?;
                Band::Sum
            },
            (RewriteName::LazyProduct, Direction::Sugar) => {
                let listed = listed(parts, &[AMPERSAND, OPEN_BRACE], CLOSE_BRACE)?;
                self.infix(&mut out, &listed, parts, Spelling(" & "), [
                    Band::Sum,
                    Band::Sum,
                ])?;
                Band::Lazy
            },
            (RewriteName::Tuple, Direction::Sugar) => {
                let listed = listed(parts, &[OPEN_TELESCOPE], CLOSE_BRACE)?;
                if listed.len() < 2 {
                    return None;
                }
                self.braced(&mut out, &listed, parts, &[OPEN_PAREN], CLOSE_PAREN)?;
                Band::Atom
            },
            (RewriteName::Product, Direction::Desugar) => {
                let chain = self.chain(at, parts, STAR);
                self.braced(
                    &mut out,
                    &chain.operands,
                    &chain.parts,
                    &[OPEN_TELESCOPE],
                    CLOSE_BRACE,
                )?;
                Band::Atom
            },
            (RewriteName::Sum, Direction::Desugar) => {
                let chain = self.chain(at, parts, PLUS);
                self.braced(
                    &mut out,
                    &chain.operands,
                    &chain.parts,
                    &[PLUS, OPEN_BRACE],
                    CLOSE_BRACE,
                )?;
                Band::Atom
            },
            (RewriteName::LazyProduct, Direction::Desugar) => {
                let chain = self.chain(at, parts, AMPERSAND);
                self.braced(
                    &mut out,
                    &chain.operands,
                    &chain.parts,
                    &[AMPERSAND, OPEN_BRACE],
                    CLOSE_BRACE,
                )?;
                Band::Atom
            },
            (RewriteName::Tuple, Direction::Desugar) => {
                if self.context(at) == Context::Outputs {
                    return None;
                }
                let listed = listed(parts, &[OPEN_PAREN], CLOSE_PAREN)?;
                let separated = parts
                    .iter()
                    .any(|part| matches!(part.role, Role::Own(text) if <&str>::from(text) == ","));
                if listed.len() < 2 || !separated {
                    return None;
                }
                self.braced(&mut out, &listed, parts, &[OPEN_TELESCOPE], CLOSE_BRACE)?;
                Band::Atom
            },
            (RewriteName::ValueFunction, Direction::Sugar) => {
                self.alias(&mut out, parts, self.context(at))?;
                Band::Loose
            },
            (RewriteName::ValueFunction, Direction::Desugar) => {
                self.thunk(&mut out, parts)?;
                Band::Bridge
            },
            (RewriteName::DefaultGrade, Direction::Sugar | Direction::Desugar) => {
                self.ungraded(&mut out, parts)?;
                Band::Bridge
            },
            (RewriteName::PathComposite, Direction::Sugar) => {
                if self.motives.standing(extent) != Standing::Returned {
                    return None;
                }
                let Some(Operation::Composite { first, second }) = self.derived(parts)
                else {
                    return None;
                };
                out.place(&self.operand(first), Band::Atom);
                out.spaced(Spelling(" then "));
                out.place(&self.operand(second), Band::Atom);
                Band::Loose
            },
            (RewriteName::PathInverse, Direction::Sugar) => {
                if self.motives.standing(extent) != Standing::Returned {
                    return None;
                }
                let Some(Operation::Inverse { path }) = self.derived(parts)
                else {
                    return None;
                };
                out.token(BACK);
                out.token(OPEN_PAREN);
                out.place(&self.operand(path), Band::Loose);
                out.token(CLOSE_PAREN);
                Band::Atom
            },
            (RewriteName::PathAction, Direction::Sugar) => {
                if self.motives.standing(extent) != Standing::Returned {
                    return None;
                }
                let Some(Operation::Action { map, path }) = self.derived(parts)
                else {
                    return None;
                };
                out.token(CONG);
                out.token(OPEN_PAREN);
                out.place(&self.operand(map), Band::Loose);
                out.token(COMMA);
                out.gap(Spelling(" "));
                out.place(&self.operand(path), Band::Loose);
                out.token(CLOSE_PAREN);
                Band::Atom
            },
            (RewriteName::PathComposite, Direction::Desugar) => {
                if self.motives.standing(extent) == Standing::Flows {
                    return None;
                }
                let (owns, operands) = split(parts);
                let (&[then], &[first, second]) = (owns.as_slice(), operands.as_slice())
                else {
                    return None;
                };
                if <&str>::from(then) != "then"
                    || parts.iter().any(|part| matches!(part.role, Role::Comment))
                {
                    return None;
                }
                self.transport(&mut out, extent, second, Moved::Written(first))?;
                Band::Atom
            },
            (RewriteName::PathInverse, Direction::Desugar) => {
                let &[path] = self.called(parts, BACK)?.as_slice()
                else {
                    return None;
                };
                self.transport(&mut out, extent, path, Moved::Derived)?;
                Band::Atom
            },
            (RewriteName::PathAction, Direction::Desugar) => {
                let &[_, path] = self.called(parts, CONG)?.as_slice()
                else {
                    return None;
                };
                self.transport(&mut out, extent, path, Moved::Derived)?;
                Band::Atom
            },
            (RewriteName::TailReturn, Direction::Sugar) => {
                if self.tails.exit(extent) != Exit::Inferred {
                    return None;
                }
                self.unreturned(&mut out, parts)?
            },
            (RewriteName::ShortAlias, Direction::Sugar) => {
                self.shortened(&mut out, parts, self.context(at))?;
                Band::Loose
            },
            // The linear run moves a form opening a block in `kept`, whatever
            // its rule.
            (RewriteName::TailReturn | RewriteName::ShortAlias, Direction::Desugar)
            | (RewriteName::LinearRun, Direction::Sugar | Direction::Desugar) => return None,
        };
        self.changed = Changed::Yes;
        Some(Spelled {
            leaves: out.leaves,
            band,
            shape: Shape::Other,
            commented: Commented::No,
            rewritten: Changed::Yes,
        })
    }

    /// Write `operands` joined by `infix`, the first operand placed at the
    /// first band of `fits` and every later one at the second, each comment
    /// of `parts` before the operand it preceded.
    ///
    /// # Specification
    /// trivial.
    fn infix(
        &self,
        out: &mut Builder<'source>,
        operands: &[Child<'source>],
        parts: &[Part<'source>],
        infix: Spelling,
        fits: [Band; 2],
    ) -> Option<()>
    {
        if operands.len() < 2 {
            return None;
        }
        let comments = comments_by_operand(parts);
        for (index, &child) in operands.iter().enumerate() {
            if index > 0 {
                out.spaced(infix);
            }
            out.comments(comments.get(index).map_or(&[][..], Vec::as_slice));
            let band = if index == 0 { fits[0] } else { fits[1] };
            out.place(&self.operand(child), band);
        }
        out.comments(comments.get(operands.len()).map_or(&[][..], Vec::as_slice));
        Some(())
    }

    /// Write `operands` between `open` and `close`, separated by commas, each
    /// unwrapped from a parenthesis it does not need, each comment of
    /// `parts` before the operand it preceded.
    ///
    /// # Specification
    /// trivial.
    fn braced(
        &self,
        out: &mut Builder<'source>,
        operands: &[Child<'source>],
        parts: &[Part<'source>],
        open: &[Spelling],
        close: Spelling,
    ) -> Option<()>
    {
        if operands.is_empty() {
            return None;
        }
        let comments = comments_by_operand(parts);
        for &tile in open {
            out.token(tile);
        }
        for (index, &child) in operands.iter().enumerate() {
            if index > 0 {
                out.token(COMMA);
                out.gap(Spelling(" "));
            }
            out.comments(comments.get(index).map_or(&[][..], Vec::as_slice));
            out.place(&self.operand(child), Band::Loose);
        }
        out.comments(comments.get(operands.len()).map_or(&[][..], Vec::as_slice));
        out.token(close);
        Some(())
    }

    /// The operands of the chain of `infix` forms the form at `at` heads,
    /// whose parts are `parts`: each form of the chain's rule written as the
    /// right operand of the one before, unparenthesised, joins it, so `A * B *
    /// C` is one product of three, as the lowering reads it.
    ///
    /// # Specification
    /// trivial.
    fn chain(
        &self,
        at: NodeIndex,
        parts: &[Part<'source>],
        infix: Spelling,
    ) -> Chain<'source>
    {
        let rule = self.rule(at);
        let mut chain = Chain {
            operands: Vec::new(),
            parts: Vec::new(),
        };
        let mut pending: Vec<Part<'source>> = parts.to_vec();
        loop {
            let last = pending
                .iter()
                .rposition(|part| matches!(part.role, Role::Operand(_)));
            let continues = last.and_then(|last| match pending.get(last).map(|part| part.role) {
                Some(Role::Operand(Child::Node(next))) if self.rule(next) == rule => {
                    Some((last, next))
                },
                _ => None,
            });
            let Some((last, next)) = continues
            else {
                chain.extend(pending, infix);
                return chain;
            };
            let tail = pending.split_off(last);
            chain.extend(pending, infix);
            let (next_parts, _) = self.parts(next);
            pending = next_parts;
            if let Some(Part { before, .. }) = tail.into_iter().next()
                && let Some(first) = pending.first_mut()
            {
                let mut joined = before;
                joined.append(&mut first.before);
                first.before = joined;
            }
        }
    }

    /// Write the value-function alias the thunk type whose parts are `parts`
    /// spells, its grade the default `ω` whether written or not, or nothing
    /// when its body is not a chain of arrows ending in a pure returner or
    /// its grade is another. A domain that binds a name keeps it, `(x : A, …)
    /// => C`, where a later domain or the result reads it, and is written
    /// bare otherwise, as the printer writes the dependent alias. Outside a
    /// type only the alias over one bare domain, `A => B`, is written, as
    /// the printer writes it there, and none as a call's argument: the
    /// printer writes a thunk type standing there, a transport's family, as
    /// its thunk, and `() => A` reads as an expression outside a type. A
    /// theory's judgment writes `A => B` too and no other alias, its `(`
    /// opening the judgment's port group.
    ///
    /// # Specification
    /// trivial.
    fn alias(
        &self,
        out: &mut Builder<'source>,
        parts: &[Part<'source>],
        context: Context,
    ) -> Option<()>
    {
        let (owns, operands) = split(parts);
        let &[thunked] = operands.as_slice()
        else {
            return None;
        };
        if default_grade(&owns)? == Grade::Written
            && parts.iter().any(|part| matches!(part.role, Role::Comment))
        {
            return None;
        }
        let mut domains: Vec<Domain<'source>> = Vec::new();
        let mut link = self.stripped(thunked);
        let result = loop {
            match self.shape_of(link)? {
                (&Shape::Arrow { domain, codomain }, Commented::No) => {
                    domains.push(match self.shape_of(domain) {
                        Some((
                            &Shape::Parenthesized {
                                binder: Binder::Some,
                                ref domains,
                                ..
                            },
                            Commented::No,
                        )) => match domains.as_slice() {
                            &[only @ Domain { name: Some(_), .. }] => only,
                            _ => return None,
                        },
                        Some((
                            &Shape::Parenthesized {
                                binder: Binder::Some,
                                ..
                            },
                            _,
                        )) => return None,
                        Some(_) | None => Domain {
                            name: None,
                            ty: domain,
                        },
                    });
                    link = self.stripped(codomain);
                },
                (&Shape::Returner { result }, Commented::No) => break result,
                _ => return None,
            }
        };
        self.aliased(out, domains, result, context)
    }

    /// Write the value-function alias over `domains` and `result`, as
    /// [`Self::alias`] says: a domain's binder kept where a later domain or
    /// the result reads it, one bare domain unparenthesised, and outside a
    /// type only that one-domain alias, never as a call's argument.
    ///
    /// # Specification
    /// trivial.
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            linear_search_in_loop,
            reason = "bounded: `named` holds the tokens of one binder's name, searched once per token of one arrow's later domains"
        )
    )]
    fn aliased(
        &self,
        out: &mut Builder<'source>,
        mut domains: Vec<Domain<'source>>,
        result: Child<'source>,
        context: Context,
    ) -> Option<()>
    {
        for index in 0 .. domains.len() {
            let Some(&Domain {
                name: Some(name), ..
            }) = domains.get(index)
            else {
                continue;
            };
            let named = self.tokens(name);
            let read = domains
                .iter()
                .skip(index.saturating_add(1))
                .map(|later| later.ty)
                .chain([result])
                .any(|later| {
                    self.tokens(later)
                        .iter()
                        .any(|&token| named.contains(&token))
                });
            if !read && let Some(domain) = domains.get_mut(index) {
                domain.name = None;
            }
        }
        match domains.as_slice() {
            &[Domain { name: None, ty }] if context != Context::Argument => {
                out.place(&self.operand(ty), Band::Lazy);
            },
            _ if context != Context::Type => return None,
            &[] => {
                out.token(OPEN_PAREN);
                out.token(CLOSE_PAREN);
            },
            many => {
                out.token(OPEN_PAREN);
                for (index, domain) in many.iter().enumerate() {
                    if index > 0 {
                        out.token(COMMA);
                        out.gap(Spelling(" "));
                    }
                    if let Some(name) = domain.name {
                        out.place(&self.operand(name), Band::Atom);
                        out.spaced(Spelling(" : "));
                    }
                    out.place(&self.operand(domain.ty), Band::Loose);
                }
                out.token(CLOSE_PAREN);
            },
        }
        out.spaced(Spelling(" => "));
        out.place(&self.operand(result), Band::Loose);
        Some(())
    }

    /// Write the value-function alias whose parts are `parts` at its shortest,
    /// as [`Self::aliased`] writes it: one domain unparenthesised and a binder
    /// nothing later reads left out; or nothing when it is already so
    /// written, or a comment stands among its parts or its domains.
    ///
    /// # Specification
    /// trivial.
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            linear_search_in_loop,
            reason = "bounded: `named` holds the tokens of one binder's name, searched once per token of one alias's domains"
        )
    )]
    fn shortened(
        &self,
        out: &mut Builder<'source>,
        parts: &[Part<'source>],
        context: Context,
    ) -> Option<()>
    {
        if parts.iter().any(|part| matches!(part.role, Role::Comment)) {
            return None;
        }
        let (owns, operands) = split(parts);
        let (&[arrow], &[domain, result]) = (owns.as_slice(), operands.as_slice())
        else {
            return None;
        };
        if <&str>::from(arrow) != "=>" {
            return None;
        }
        let domains: Vec<Domain<'source>> = match self.shape_of(domain) {
            Some((
                &Shape::Parenthesized {
                    ref entries,
                    binder: Binder::None,
                    ..
                },
                Commented::No,
            )) => entries
                .iter()
                .map(|&ty| Domain {
                    name: None,
                    ty: self.stripped(ty),
                })
                .collect(),
            Some((
                &Shape::Parenthesized {
                    binder: Binder::Some,
                    ref domains,
                    ..
                },
                Commented::No,
            )) => domains.clone(),
            Some(_) | None => return None,
        };
        let unread = domains.iter().any(|domain| {
            domain.name.is_some_and(|name| {
                let named = self.tokens(name);
                !domains
                    .iter()
                    .map(|later| later.ty)
                    .chain([result])
                    .any(|later| {
                        self.tokens(later)
                            .iter()
                            .any(|&token| named.contains(&token))
                    })
            })
        });
        let bare = matches!(domains.as_slice(), &[Domain { name: None, .. }]);
        if !bare && !unread {
            return None;
        }
        self.aliased(out, domains, result, context)
    }

    /// Write the thunk type whose parts are `parts`, written at the default
    /// grade `+U[ω] B`, as `+U B`, or nothing when it writes another grade,
    /// none, or a comment among its tiles.
    ///
    /// # Specification
    /// trivial.
    fn ungraded(
        &self,
        out: &mut Builder<'source>,
        parts: &[Part<'source>],
    ) -> Option<()>
    {
        if parts.iter().any(|part| matches!(part.role, Role::Comment)) {
            return None;
        }
        let (owns, operands) = split(parts);
        let (Some(Grade::Written), &[body]) = (default_grade(&owns), operands.as_slice())
        else {
            return None;
        };
        out.token(Spelling("+U"));
        out.gap(Spelling(" "));
        out.place(&self.operand(body), Band::Atom);
        Some(())
    }

    /// Write the `return` whose parts are `parts` as the value it returns,
    /// answering the value's band, or nothing when a comment stands among its
    /// parts.
    ///
    /// # Specification
    /// trivial.
    fn unreturned(
        &self,
        out: &mut Builder<'source>,
        parts: &[Part<'source>],
    ) -> Option<Band>
    {
        if parts.iter().any(|part| matches!(part.role, Role::Comment)) {
            return None;
        }
        let (owns, operands) = split(parts);
        let (&[keyword], &[value]) = (owns.as_slice(), operands.as_slice())
        else {
            return None;
        };
        if <&str>::from(keyword) != "return" {
            return None;
        }
        let operand = self.operand(value);
        out.place(&operand, Band::Loose);
        Some(operand.band)
    }

    /// Write the thunk of arrows the value-function alias whose parts are
    /// `parts` stands for: a domain that binds a name as `(x : A) ->`, every
    /// other bare.
    ///
    /// # Specification
    /// trivial.
    fn thunk(
        &self,
        out: &mut Builder<'source>,
        parts: &[Part<'source>],
    ) -> Option<()>
    {
        if parts.iter().any(|part| matches!(part.role, Role::Comment)) {
            return None;
        }
        let (owns, operands) = split(parts);
        let (&[arrow], &[domain, codomain]) = (owns.as_slice(), operands.as_slice())
        else {
            return None;
        };
        if <&str>::from(arrow) != "=>" {
            return None;
        }
        let domains = match self.shape_of(domain) {
            Some((
                &Shape::Parenthesized {
                    ref entries,
                    binder: Binder::None,
                    ..
                },
                Commented::No,
            )) => entries
                .iter()
                .map(|&ty| Domain { name: None, ty })
                .collect(),
            Some((
                &Shape::Parenthesized {
                    binder: Binder::Some,
                    ref domains,
                    ..
                },
                Commented::No,
            )) if !domains.is_empty() => domains.clone(),
            Some((&Shape::Parenthesized { .. }, _)) => return None,
            Some(_) | None => Vec::from([Domain {
                name: None,
                ty: domain,
            }]),
        };
        out.token(Spelling("+U"));
        out.gap(Spelling(" "));
        out.token(OPEN_PAREN);
        for domain in &domains {
            match domain.name {
                Some(name) => {
                    out.token(OPEN_PAREN);
                    out.place(&self.operand(name), Band::Atom);
                    out.spaced(Spelling(" : "));
                    out.place(&self.operand(domain.ty), Band::Loose);
                    out.token(CLOSE_PAREN);
                },
                None => out.place(&self.operand(domain.ty), Band::Lazy),
            }
            out.spaced(Spelling(" -> "));
        }
        out.token(Spelling("-F"));
        out.gap(Spelling(" "));
        out.place(&self.operand(codomain), Band::Atom);
        out.token(CLOSE_PAREN);
        Some(())
    }

    /// The tokens `child` writes, whitespace and comments left out.
    ///
    /// # Specification
    /// trivial.
    fn tokens(
        &self,
        child: Child<'source>,
    ) -> Vec<SourceFragment<'source>>
    {
        self.operand(child)
            .leaves
            .iter()
            .filter(|leaf| leaf.material == Material::Token)
            .map(|leaf| leaf.text)
            .collect()
    }

    /// The derived path operation the transport call whose parts are `parts`
    /// spells, when its motive `\y. Path(A, l, r)` is one the lowering
    /// derives: `p then q` for `transport(\y. Path(A, a, y), q, p)`, `back(p)`
    /// for `transport(\y. Path(A, y, a), p, here(a))` and `cong(f, p)` for
    /// `transport(\y. Path(B, f(a), f(y)), p, here(f(a)))`, where neither the
    /// carrier, the fixed endpoint nor the map names `y`.
    ///
    /// # Specification
    /// trivial.
    fn derived(
        &self,
        parts: &[Part<'source>],
    ) -> Option<Operation<'source>>
    {
        if parts.iter().any(|part| matches!(part.role, Role::Comment)) {
            return None;
        }
        let (_, operands) = split(parts);
        let &[callee, Child::Node(motive), along, moved] = operands.as_slice()
        else {
            return None;
        };
        if self
            .tokens(callee)
            .iter()
            .map(|&token| <&str>::from(token))
            .ne(["transport"])
        {
            return None;
        }
        if self.rule(motive) != Some(MoldName("static_abstraction")) {
            return None;
        }
        let (abstraction, _) = self.parts(motive);
        let (owns, body) = split(&abstraction);
        let (&[_, binder, _], &[Child::Node(body)]) = (owns.as_slice(), body.as_slice())
        else {
            return None;
        };
        if self.rule(body) != Some(MoldName("path_type")) {
            return None;
        }
        let (typed, _) = self.parts(body);
        // The endpoints by their tokens and the operands they hold, split at
        // the type's own commas: a carrier the grammar keeps as its own tile,
        // as `Type`, is one too.
        let mut endpoints: Vec<(Vec<SourceFragment<'source>>, Vec<Child<'source>>)> = Vec::new();
        let mut opened = false;
        for part in &typed {
            match part.role {
                Role::Own(text) => match <&str>::from(text) {
                    "(" if !opened => {
                        opened = true;
                        endpoints.push((Vec::new(), Vec::new()));
                    },
                    "," => endpoints.push((Vec::new(), Vec::new())),
                    ")" => {},
                    _ if opened => endpoints.last_mut()?.0.push(text),
                    _ => {},
                },
                Role::Operand(child) => {
                    let endpoint = endpoints.last_mut()?;
                    endpoint.0.extend(self.tokens(child));
                    endpoint.1.push(child);
                },
                Role::Comment => return None,
            }
        }
        let &[(ref carrier, _), (ref left, _), (ref right, ref holds)] = endpoints.as_slice()
        else {
            return None;
        };
        if carrier.contains(&binder) {
            return None;
        }
        if right.as_slice() == [binder] && !left.contains(&binder) {
            return Some(Operation::Composite {
                first: moved,
                second: along,
            });
        }
        // An inverse and an action move the reflexivity at the fixed
        // endpoint.
        let moved = self.tokens(moved);
        let reflexive = |fixed: &[SourceFragment<'source>]| match moved.as_slice() {
            &[here, open, ref inner @ .., close] => {
                <&str>::from(here) == "here"
                    && <&str>::from(open) == "("
                    && <&str>::from(close) == ")"
                    && inner == fixed
            },
            _ => false,
        };
        if left.as_slice() == [binder] && !right.contains(&binder) && reflexive(right) {
            return Some(Operation::Inverse { path: along });
        }
        let &[Child::Node(applied)] = holds.as_slice()
        else {
            return None;
        };
        if self.rule(applied) != Some(MoldName("call_expression")) {
            return None;
        }
        let (call, _) = self.parts(applied);
        let (_, called) = split(&call);
        let &[map, argument] = called.as_slice()
        else {
            return None;
        };
        let mapped = self.tokens(map);
        // The fixed endpoint is the map applied, `f(a)`, as the action
        // derives it.
        let applied = matches!(
            left.strip_prefix(mapped.as_slice()),
            Some(&[open, .., close]) if <&str>::from(open) == "(" && <&str>::from(close) == ")"
        );
        (self.tokens(argument).as_slice() == [binder]
            && !mapped.contains(&binder)
            && applied
            && !left.contains(&binder)
            && reflexive(left))
        .then_some(Operation::Action { map, path: along })
    }

    /// The operands after the head of the call whose parts are `parts`, when
    /// its head is the name `head` alone.
    ///
    /// # Specification
    /// trivial.
    fn called(
        &self,
        parts: &[Part<'source>],
        head: Spelling,
    ) -> Option<Vec<Child<'source>>>
    {
        if parts.iter().any(|part| matches!(part.role, Role::Comment)) {
            return None;
        }
        let (_, operands) = split(parts);
        let (&callee, arguments) = operands.split_first()?;
        self.tokens(callee)
            .iter()
            .map(|&token| <&str>::from(token))
            .eq([head.0])
            .then(|| arguments.to_vec())
    }

    /// Write the transport the derived path operation at `extent` stands
    /// for, its motive as the lowering derived it, moving `moved` along
    /// `along`, or nothing when the lowering derived none the printer spells.
    ///
    /// # Specification
    /// trivial.
    fn transport(
        &mut self,
        out: &mut Builder<'source>,
        extent: ByteSpan,
        along: Child<'source>,
        moved: Moved<'source>,
    ) -> Option<()>
    {
        let motives = self.motives;
        let (Some(motive), Some(value)) = (motives.of(extent), motives.value(extent))
        else {
            self.unspelled.push(extent);
            return None;
        };
        out.token(Spelling("transport"));
        out.token(OPEN_PAREN);
        written(out, motive);
        out.token(COMMA);
        out.gap(Spelling(" "));
        out.place(&self.operand(along), Band::Loose);
        out.token(COMMA);
        out.gap(Spelling(" "));
        match moved {
            Moved::Written(moved) => out.place(&self.operand(moved), Band::Loose),
            Moved::Derived => written(out, value),
        }
        out.token(CLOSE_PAREN);
        Some(())
    }
}

/// Write `tokens`, as the printer spaced them, into `out`.
///
/// # Specification
/// trivial.
fn written<'source>(
    out: &mut Builder<'source>,
    tokens: &'source [Token],
)
{
    for token in tokens {
        if token.spaced == Spaced::Yes {
            out.gap(Spelling(" "));
        }
        out.fragment(SourceFragment::from(token.text.as_str()));
    }
}

/// A derived path operation a transport call spells, by the operands of
/// the call its sugared spelling writes.
#[derive(Clone, Copy)]
enum Operation<'source>
{
    /// `p then q`.
    Composite
    {
        /// `p`, the transported value.
        first: Child<'source>,
        /// `q`, the path it moves along.
        second: Child<'source>,
    },
    /// `back(p)`.
    Inverse
    {
        /// `p`.
        path: Child<'source>,
    },
    /// `cong(f, p)`.
    Action
    {
        /// `f`.
        map: Child<'source>,
        /// `p`.
        path: Child<'source>,
    },
}

/// The value the transport a derived path operation stands for moves.
#[derive(Clone, Copy)]
enum Moved<'source>
{
    /// An operand as the source writes it: a composite's first path.
    Written(Child<'source>),
    /// The reflexivity the lowering derived: an inverse's and an action's.
    Derived,
}

/// The operands of an infix chain, with every part of every form in it.
struct Chain<'source>
{
    /// The operands, in order.
    operands: Vec<Child<'source>>,
    /// The parts, in order: the comments among them are placed.
    parts: Vec<Part<'source>>,
}

impl<'source> Chain<'source>
{
    /// Add `parts`, one form's parts up to its right operand, to the chain:
    /// its operands, and every part but its `infix` tiles.
    ///
    /// # Specification
    /// trivial.
    fn extend(
        &mut self,
        parts: Vec<Part<'source>>,
        infix: Spelling,
    )
    {
        for part in parts {
            match part.role {
                Role::Operand(child) => self.operands.push(child),
                Role::Own(text) if <&str>::from(text) == infix.0 => continue,
                Role::Own(_) | Role::Comment => {},
            }
            self.parts.push(part);
        }
    }
}

/// The grammar rules this module reads, so a rule's name is a
/// [`MoldName`].
const RULES: [MoldName; 28] = [
    MoldName("telescope_type"),
    MoldName("product_type"),
    MoldName("labelled_sum_type"),
    MoldName("sum_type"),
    MoldName("lazy_record_type"),
    MoldName("lazy_product_type"),
    MoldName("telescope_expression"),
    MoldName("parenthesized_expression"),
    MoldName("parenthesized_type"),
    MoldName("u_type"),
    MoldName("f_type"),
    MoldName("f_type.row"),
    MoldName("at_type"),
    MoldName("function_type"),
    MoldName("value_function_type"),
    MoldName("forall_type"),
    MoldName("static_abstraction"),
    MoldName("union_type"),
    MoldName("intersection_type"),
    MoldName("equivalence_type"),
    MoldName("isomorphism_type"),
    MoldName("universe_flow_type"),
    MoldName("call_expression"),
    MoldName("path_type"),
    MoldName("binary_expression.then"),
    MoldName("send_session_type"),
    MoldName("receive_session_type"),
    MoldName("return_expression"),
];

/// `#{`.
const OPEN_TELESCOPE: Spelling = Spelling("#{");

/// `{`.
const OPEN_BRACE: Spelling = Spelling("{");

/// `}`.
const CLOSE_BRACE: Spelling = Spelling("}");

/// `(`.
const OPEN_PAREN: Spelling = Spelling("(");

/// `)`.
const CLOSE_PAREN: Spelling = Spelling(")");

/// `,`.
const COMMA: Spelling = Spelling(",");

/// `back`.
const BACK: Spelling = Spelling("back");

/// `cong`.
const CONG: Spelling = Spelling("cong");

/// `+`.
const PLUS: Spelling = Spelling("+");

/// `&`.
const AMPERSAND: Spelling = Spelling("&");

/// `*`.
const STAR: Spelling = Spelling("*");

/// The shape a form of `rule` whose parts are `parts` has, as a form around
/// it reads it.
///
/// # Specification
/// trivial.
fn shape<'source>(
    rule: MoldName,
    parts: &[Part<'source>],
) -> Shape<'source>
{
    let (owns, operands) = split(parts);
    let spelled: Vec<&str> = owns.iter().map(|&text| <&str>::from(text)).collect();
    match (rule.0, spelled.as_slice(), operands.as_slice()) {
        ("parenthesized_type" | "parenthesized_expression", &["(", .., ")"], _) => {
            let binder = if spelled.contains(&":") {
                Binder::Some
            }
            else {
                Binder::None
            };
            Shape::Parenthesized {
                entries: operands,
                binder,
                domains: domains(parts).unwrap_or_default(),
            }
        },
        ("function_type", &["->"], &[domain, codomain]) => Shape::Arrow { domain, codomain },
        ("f_type", &["-F"], &[result]) => Shape::Returner { result },
        _ => Shape::Other,
    }
}

/// The entries of the parenthesised list whose parts are `parts`, each `A`
/// or `x : A`, or nothing when an entry is spelled otherwise.
///
/// # Specification
/// trivial.
fn domains<'source>(parts: &[Part<'source>]) -> Option<Vec<Domain<'source>>>
{
    let mut domains = Vec::new();
    let mut name = None;
    let mut ty = None;
    for part in parts {
        match part.role {
            Role::Own(text) => match <&str>::from(text) {
                "(" => {},
                ":" if name.is_none() => name = Some(ty.take()?),
                "," | ")" => {
                    domains.push(Domain {
                        name: name.take(),
                        ty: ty.take()?,
                    });
                },
                _ => return None,
            },
            Role::Operand(child) if ty.is_none() => ty = Some(child),
            Role::Operand(_) => return None,
            Role::Comment => {},
        }
    }
    Some(domains)
}

/// The own tiles and the operands of `parts`, in order.
///
/// # Specification
/// trivial.
fn split<'source>(parts: &[Part<'source>]) -> (Vec<SourceFragment<'source>>, Vec<Child<'source>>)
{
    let mut owns = Vec::new();
    let mut operands = Vec::new();
    for part in parts {
        match part.role {
            Role::Own(text) => owns.push(text),
            Role::Operand(child) => operands.push(child),
            Role::Comment => {},
        }
    }
    (owns, operands)
}

/// How a thunk type writes the default grade `ω`.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Grade
{
    /// `+U B`.
    Unwritten,
    /// `+U[ω] B`, or `+U[inf] B` in ASCII.
    Written,
}

/// How the own tiles `owns` of a thunk type write its grade, or nothing when
/// they are no thunk type's or write a grade other than the default `ω`.
///
/// # Specification
/// trivial.
fn default_grade(owns: &[SourceFragment<'_>]) -> Option<Grade>
{
    match *owns {
        [bridge] if <&str>::from(bridge) == "+U" => Some(Grade::Unwritten),
        [bridge, open, grade, close]
            if <&str>::from(bridge) == "+U"
                && <&str>::from(open) == "["
                && [GrammarSpelling::Unicode, GrammarSpelling::Ascii]
                    .into_iter()
                    .any(|spelling| UNRESTRICTED.written(spelling).0 == <&str>::from(grade))
                && <&str>::from(close) == "]" =>
        {
            Some(Grade::Written)
        },
        _ => None,
    }
}

/// The entries of a list written `open … close`, separated by commas, a comma
/// after the last allowed, or nothing when `parts` spell anything else.
///
/// # Specification
/// trivial.
fn listed<'source>(
    parts: &[Part<'source>],
    open: &[Spelling],
    close: Spelling,
) -> Option<Vec<Child<'source>>>
{
    let mut operands = Vec::new();
    let mut opened = 0_usize;
    let mut expecting = Expecting::Entry;
    let mut closed = Closed::No;
    for part in parts {
        match part.role {
            Role::Comment => {},
            _ if closed == Closed::Yes => return None,
            Role::Own(text) if opened < open.len() => {
                if open
                    .get(opened)
                    .is_none_or(|tile| tile.0 != <&str>::from(text))
                {
                    return None;
                }
                opened = opened.saturating_add(1);
            },
            Role::Operand(_) if opened < open.len() => return None,
            Role::Operand(child) => {
                if expecting != Expecting::Entry {
                    return None;
                }
                operands.push(child);
                expecting = Expecting::Separator;
            },
            Role::Own(text) => match <&str>::from(text) {
                "," if expecting == Expecting::Separator => expecting = Expecting::Entry,
                text if text == close.0 => closed = Closed::Yes,
                _ => return None,
            },
        }
    }
    (closed == Closed::Yes && opened == open.len()).then_some(operands)
}

/// What a list expects next.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Expecting
{
    /// An entry.
    Entry,
    /// A comma, or the closer.
    Separator,
}

/// Whether a list's closer was read.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Closed
{
    /// Not yet.
    No,
    /// It was.
    Yes,
}

/// The comment parts of `parts`, grouped by how many operands precede each.
///
/// # Specification
/// trivial.
fn comments_by_operand<'parts, 'source>(
    parts: &'parts [Part<'source>]
) -> Vec<Vec<&'parts Part<'source>>>
{
    let mut grouped: Vec<Vec<&Part<'source>>> = Vec::from([Vec::new()]);
    for part in parts {
        match part.role {
            Role::Operand(_) => grouped.push(Vec::new()),
            Role::Comment => {
                if let Some(group) = grouped.last_mut() {
                    group.push(part);
                }
            },
            Role::Own(_) => {},
        }
    }
    grouped
}

/// The leaves a rewrite writes, in order.
struct Builder<'source>
{
    /// The leaves so far.
    leaves: Vec<Leaf<'source>>,
    /// Where a leaf the rewrite writes stands: the form's start, no bytes
    /// wide.
    position: ByteSpan,
    /// The top-level form the leaves belong to.
    owner: Owner,
}

impl<'source> Builder<'source>
{
    /// A leaf the rewrite writes.
    ///
    /// # Specification
    /// trivial.
    fn written(
        &self,
        text: SourceFragment<'source>,
        material: Material,
    ) -> Leaf<'source>
    {
        Leaf {
            span: self.position,
            text,
            material,
            owner: self.owner,
            documentation: Documentation::Outside,
        }
    }

    /// Write the token `text`.
    ///
    /// # Specification
    /// trivial.
    fn token(
        &mut self,
        text: Spelling,
    )
    {
        self.fragment(SourceFragment::from(text.0));
    }

    /// Write the token `text`, written outside the source.
    ///
    /// # Specification
    /// trivial.
    fn fragment(
        &mut self,
        text: SourceFragment<'source>,
    )
    {
        let leaf = self.written(text, Material::Token);
        self.leaves.push(leaf);
    }

    /// Write the whitespace `text`, unless whitespace ends the leaves already.
    ///
    /// # Specification
    /// trivial.
    fn gap(
        &mut self,
        text: Spelling,
    )
    {
        if self
            .leaves
            .last()
            .is_some_and(|leaf| leaf.material == Material::Whitespace)
        {
            return;
        }
        let leaf = self.written(SourceFragment::from(text.0), Material::Whitespace);
        self.leaves.push(leaf);
    }

    /// Write the token `text` between two spaces: `spaced` spells it padded,
    /// ` * `.
    ///
    /// # Specification
    /// trivial.
    fn spaced(
        &mut self,
        spaced: Spelling,
    )
    {
        self.gap(Spelling(" "));
        self.token(Spelling(spaced.0.trim()));
        self.gap(Spelling(" "));
    }

    /// Write `comments`, each after the whitespace the source wrote before
    /// it, and a line break after each the source broke the line after.
    ///
    /// # Specification
    /// trivial.
    fn comments(
        &mut self,
        comments: &[&Part<'source>],
    )
    {
        for comment in comments {
            if let Some(last) = self.leaves.last()
                && last.material == Material::Whitespace
                && !comment.before.is_empty()
            {
                let _replaced = self.leaves.pop();
            }
            self.leaves.extend(comment.before.iter().copied());
            self.leaves.extend(comment.leaves.iter().copied());
            let line = comment.leaves.iter().any(|leaf| {
                leaf.material == Material::LineComment || <&str>::from(leaf.text).starts_with("//")
            });
            let broken = comment
                .before
                .iter()
                .any(|leaf| <&str>::from(leaf.text).contains('\n'));
            if line || broken {
                self.gap(Spelling("\n"));
            }
            else {
                self.gap(Spelling(" "));
            }
        }
    }

    /// Write `operand` where a form binding at `fits` or tighter stands:
    /// unwrapped from its parenthesis when its entry fits, as written when it
    /// fits, parenthesised otherwise.
    ///
    /// # Specification
    /// trivial.
    fn place(
        &mut self,
        operand: &Operand<'source>,
        fits: Band,
    )
    {
        if let Some((ref inner, band)) = operand.inner
            && band <= fits
        {
            self.leaves.extend(inner.iter().copied());
            return;
        }
        if operand.band <= fits {
            self.leaves.extend(operand.leaves.iter().copied());
            return;
        }
        self.token(OPEN_PAREN);
        self.leaves.extend(operand.leaves.iter().copied());
        self.token(CLOSE_PAREN);
    }
}
