//! The entry gate: every term, binder and written-type node of every corpus
//! source has a type-table entry at exactly its span, and the entry the hover
//! answers at every byte is the innermost such node's.
//!
//! The nodes are the tree's own: each form and each atom whose grammar sort is
//! an expression, a type or a pattern. Every kind — the sort and the label of
//! the tile that names it — stands in `KINDS`: by design, with the reason the
//! node needs no entry of its own, or owed, its count of nodes without one
//! pinned so it only shrinks. A kind in neither fails, as does a pin that no
//! longer matches and a by-design kind whose every node has its entry. A few
//! nodes are by design whatever their kind, by where they stand — inside an
//! attribute, inside a declaration the lowering or the checker refused,
//! heading a call, or the value a `run _ <-` discards — and `Placed` names
//! them.
//!
//! Every pull-request profile walks a stated sample, where an owed count is
//! held only to at most its pin; the `sweeps` and nightly profiles walk the
//! corpus whole and hold the census exactly.
//!
//! The gate, in a `cfg(test)` module so the crate's lint wall reads it as
//! test code rather than as shipping code.

use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use core::convert::Infallible;
use core::ops::ControlFlow;
use std::path::Path;
use std::path::PathBuf;

use gandr_surface_dispatcher::Composed;
use gandr_surface_dispatcher::Declared;
use gandr_surface_dispatcher::Lowered;
use gandr_surface_dispatcher::LoweringCount;
use gandr_surface_dispatcher::Pool;
use gandr_surface_dispatcher::Step;
use gandr_surface_dispatcher::TypeTable;
use gandr_surface_dispatcher::Walk;
use gandr_surface_dispatcher::Width;
use gandr_surface_dispatcher::lay_out;
use gandr_surface_dispatcher::lower_unit_source;
use gandr_surface_grammar::MoldDef;
use gandr_surface_grammar::Pbg;
use gandr_surface_grammar::Sort;
use gandr_surface_grammar::built_in;
use gandr_surface_parser::parse;
use gandr_surface_pretty::Form;
use gandr_surface_pretty::PageWidth;
use gandr_surface_syntax::ByteOffset;
use gandr_surface_syntax::ByteSpan;
use gandr_surface_syntax::MoldId;
use gandr_surface_syntax::Node;
use gandr_surface_syntax::NodeIndex;
use gandr_surface_syntax::NodeLabel;
use gandr_surface_syntax::SourceText;
use gandr_surface_syntax::SyntaxTree;
use quenchant_shape::shape::Maybe;

/// Where a kind stands.
#[derive(Clone, Copy, Debug)]
enum Standing
{
    /// The node needs no entry of its own, for this reason.
    Design(&'static str),
    /// The node is owed an entry; this many nodes of the kind lack one.
    Owed(usize),
}

/// An exit's reason: the keyword heads the computation its operand ends.
const EXIT: &str = "an exit keyword ends the computation its operand gives: the operand \
                        answers, and the enclosing body at its type";

/// Every kind of node the corpus writes, by sort and naming label, with
/// where it stands. An owed count only shrinks: lower it with the change
/// that gives the nodes their entries.
const KINDS: &[(&str, Standing)] = &[
    ("Expression !=", Standing::Owed(0)),
    ("Expression \"", Standing::Owed(0)),
    ("Expression #{", Standing::Owed(0)),
    ("Expression &", Standing::Owed(0)),
    ("Expression ( application", Standing::Owed(0)),
    (
        "Expression ( group",
        Standing::Design("a parenthesised group: the node inside answers"),
    ),
    ("Expression *", Standing::Owed(0)),
    ("Expression +", Standing::Owed(0)),
    ("Expression -", Standing::Owed(0)),
    ("Expression .", Standing::Owed(0)),
    (
        "Expression ;",
        Standing::Design(
            "the `;` ending a root statement that is no declaration: the refused stray answers",
        ),
    ),
    ("Expression <", Standing::Owed(0)),
    ("Expression <=", Standing::Owed(0)),
    ("Expression ==", Standing::Owed(0)),
    ("Expression >", Standing::Owed(0)),
    ("Expression >=", Standing::Owed(0)),
    ("Expression ?", Standing::Owed(0)),
    (
        "Expression [",
        Standing::Design(
            "an annotation on a head — a stratum or a descent claim: the call it heads answers",
        ),
    ),
    ("Expression _", Standing::Owed(0)),
    ("Expression abort", Standing::Owed(0)),
    ("Expression access", Standing::Owed(0)),
    ("Expression as", Standing::Owed(0)),
    ("Expression become", Standing::Design(EXIT)),
    (
        "Expression bind",
        Standing::Design(
            "an abstraction in a rule term: its atom is no term, and its body answers at its \
             port's sort",
        ),
    ),
    ("Expression break", Standing::Design(EXIT)),
    ("Expression case", Standing::Owed(0)),
    ("Expression character", Standing::Owed(0)),
    ("Expression close", Standing::Owed(0)),
    ("Expression co", Standing::Owed(0)),
    ("Expression constructor", Standing::Owed(0)),
    ("Expression continue", Standing::Owed(0)),
    ("Expression drop", Standing::Owed(0)),
    ("Expression false", Standing::Owed(0)),
    ("Expression fn", Standing::Owed(0)),
    ("Expression for", Standing::Owed(0)),
    ("Expression force", Standing::Owed(0)),
    ("Expression forget", Standing::Owed(0)),
    ("Expression handle", Standing::Owed(0)),
    ("Expression hold", Standing::Owed(0)),
    // #2968: the instance name in a call a theory scope's laws rewrite.
    ("Expression identifier", Standing::Owed(4)),
    ("Expression if", Standing::Owed(0)),
    ("Expression loop", Standing::Owed(0)),
    ("Expression migrate", Standing::Owed(0)),
    ("Expression number", Standing::Owed(0)),
    ("Expression offer", Standing::Owed(0)),
    ("Expression pack", Standing::Owed(0)),
    ("Expression pure", Standing::Design(EXIT)),
    ("Expression resume", Standing::Owed(0)),
    ("Expression return", Standing::Owed(0)),
    ("Expression run", Standing::Owed(0)),
    ("Expression select", Standing::Owed(0)),
    ("Expression send", Standing::Owed(0)),
    ("Expression then", Standing::Owed(0)),
    ("Expression thunk", Standing::Owed(0)),
    ("Expression true", Standing::Owed(0)),
    (
        "Expression type(",
        Standing::Design("a type quote: the type inside answers, quoted where the value is read"),
    ),
    ("Expression typed_number", Standing::Owed(0)),
    ("Expression unit", Standing::Owed(0)),
    ("Expression while", Standing::Owed(0)),
    (
        "Expression {",
        Standing::Design("a block: the computation it holds answers"),
    ),
    ("Expression ~", Standing::Owed(0)),
    ("Expression ∷", Standing::Owed(0)),
    ("Pattern #{", Standing::Owed(0)),
    ("Pattern (", Standing::Owed(0)),
    ("Pattern +", Standing::Owed(0)),
    ("Pattern [", Standing::Owed(0)),
    ("Pattern _", Standing::Owed(0)),
    ("Pattern as", Standing::Owed(0)),
    ("Pattern constructor", Standing::Owed(0)),
    ("Pattern false", Standing::Owed(0)),
    ("Pattern identifier", Standing::Owed(0)),
    ("Pattern number", Standing::Owed(0)),
    ("Pattern true", Standing::Owed(0)),
    ("Pattern unit", Standing::Owed(0)),
    ("Pattern |", Standing::Owed(0)),
    ("Type !", Standing::Owed(0)),
    ("Type #{", Standing::Owed(0)),
    ("Type &", Standing::Owed(0)),
    (
        "Type ( group",
        Standing::Design(
            "a parenthesised group or parameter list: the type inside or around answers",
        ),
    ),
    ("Type *", Standing::Owed(0)),
    ("Type +", Standing::Owed(0)),
    ("Type +U", Standing::Owed(0)),
    ("Type ->", Standing::Owed(0)),
    ("Type -F", Standing::Owed(0)),
    ("Type .", Standing::Owed(0)),
    ("Type =>", Standing::Owed(0)),
    ("Type ?", Standing::Owed(0)),
    ("Type Buf", Standing::Owed(0)),
    ("Type Cap", Standing::Owed(0)),
    ("Type Char", Standing::Owed(0)),
    ("Type Integer", Standing::Owed(0)),
    ("Type Path", Standing::Owed(0)),
    ("Type String", Standing::Owed(0)),
    ("Type Type", Standing::Owed(0)),
    ("Type Type+", Standing::Owed(0)),
    ("Type Unit", Standing::Owed(0)),
    ("Type Void", Standing::Owed(0)),
    ("Type [", Standing::Owed(0)),
    ("Type \\", Standing::Owed(0)),
    (
        "Type at",
        Standing::Design("a scoped capability: the capability it scopes answers, at its scope"),
    ),
    ("Type end", Standing::Owed(0)),
    ("Type f64", Standing::Owed(0)),
    ("Type i32", Standing::Owed(0)),
    ("Type i64", Standing::Owed(0)),
    ("Type mu", Standing::Owed(0)),
    ("Type number", Standing::Owed(0)),
    (
        "Type sort",
        Standing::Design("a manifest sort's binding: the type it fixes the sort to answers"),
    ),
    // #2969: a theory operation's binder sorts and index terms.
    ("Type type_identifier", Standing::Owed(3)),
    ("Type type_variable", Standing::Owed(12)),
    ("Type u32", Standing::Owed(0)),
    ("Type u64", Standing::Owed(0)),
    (
        "Type with",
        Standing::Design("a manifest model type: the model type whose sorts it fixes answers"),
    ),
    ("Type ⇝", Standing::Owed(0)),
    ("Type ≃", Standing::Owed(0)),
    ("Type ≅", Standing::Owed(0)),
];

/// The names of the primitive formers a call can head: the call is one
/// core node, and its head names the former rather than a term.
const FORMERS: &[&str] = &[
    "abandon",
    "arrow",
    "back",
    "bisim",
    "cong",
    "cons",
    "decompose",
    "dialogue",
    "equiv",
    "flowProduct",
    "forward",
    "funext",
    "here",
    "pathProduct",
    "recorded",
    "ride",
    "sim",
    "stay",
    "transport",
    "ua",
];

/// The moves a run literal `recorded(m₀, …, mₙ)` or a dialogue literal
/// `dialogue(left(m₀), right(m₁), …)` is written in, a dialogue's each under
/// the endpoint it is made at. A move is read by its shape, never resolved:
/// the literal is the core node, and a payload inside a move is a term of its
/// own.
const MOVES: &[&str] = &[
    "closed", "left", "offered", "received", "right", "selected", "sent",
];

/// The literals whose arguments are moves.
const LITERALS: &[&str] = &["dialogue", "recorded"];

/// Where a node stands relative to a run literal.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Run
{
    /// Outside every run literal.
    Outside,
    /// Among a run literal's moves.
    Moves,
    /// Inside a move that names a label, `selected(l)` or `offered(l)`.
    Labelled,
}

/// The corpus directory `name`, under the corpus crate.
///
/// # Specification
/// trivial.
fn root(name: &Path) -> PathBuf
{
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("..")
        .join("surface-corpus")
        .join(name)
}

/// The first child of `position` that is no layout.
///
/// # Specification
/// trivial.
fn first(
    tree: &SyntaxTree<'_>,
    position: NodeIndex,
) -> Option<NodeIndex>
{
    tree.children(position).find(|&child| {
        tree.node(child)
            .is_some_and(|node| node.label() != NodeLabel::Space)
    })
}

/// The kind key of a gated node: its sort and naming label, as `def`
/// gives them, a `(` form split into the group it is when its first child
/// is the `(` itself and the application it is otherwise.
///
/// # Specification
/// trivial.
fn kind(
    grammar: &Pbg,
    tree: &SyntaxTree<'_>,
    position: NodeIndex,
    def: MoldDef,
) -> String
{
    let grouped = |child: NodeIndex| {
        matches!(tree.node(child).map(Node::label), Some(NodeLabel::Tile(mold))
                if grammar.mold(mold).is_ok_and(|def| def.label == "("))
    };
    let melded = matches!(
        tree.node(position).map(Node::label),
        Some(NodeLabel::Meld(_))
    );
    let (sort, label) = (def.sort, def.label);
    if label == "(" && melded && !matches!(sort, Sort::Pattern) {
        let shape = if first(tree, position).is_some_and(grouped) {
            "group"
        }
        else {
            "application"
        };
        return format!("{sort:?} ( {shape}");
    }
    format!("{sort:?} {label}")
}

/// Why a node needs no entry of its own by where it stands, whatever its
/// kind: inside an attribute or documentation, inside a declaration the
/// lowering refused, as the head of a former's call, as a count of the
/// stratum a head's annotation writes, as the module a path qualifies, as
/// a run literal's move, as an inner link of a product, a sum or a lazy
/// product chain, as the value a discarded bind drops, as an arrow of a data
/// family's kind, as the sort of a stage binder or the binder a call
/// supplies, as the sort of a region binder, as the theory a model type
/// names, as the module and the model type a pack names, as a variable a
/// binding port binds or an abstracting operation in a theory's rule, as
/// the head or the type of an `Eq.generic(T)` or of one of its laws, or as a
/// node of the tactic a splice runs.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Placed
{
    /// An attribute or documentation, which holds no term.
    Quoted,
    /// A declaration the lowering or the checker refused: the judgement
    /// stopped at the refusal, which answers.
    Refused,
    /// The head of a constructor's or a primitive former's call, or of an
    /// annotation, a constructor qualified by its family among them: the call
    /// is the one core node, and answers.
    Head,
    /// A count of the stratum an annotation on a head writes, `1` and `4`
    /// in `ua[1, 4](a, b, f, g)`: the degree and the catalogue bound the
    /// former reads off the literal's digits, never a term, so the call
    /// the annotation heads answers (#298).
    Stratum,
    /// The module or the builtin namespace a path selects from, `M` in `M.x`
    /// or `M.T`, `M.N` in `M.N.x`, `limits.hard` in `limits.hard.note`, and
    /// `int` in `int.div(c, 64)`: a namespace, neither a term nor a type, so
    /// the path answers (#1170). Or the model implicit a path reads a
    /// component of, `s` in `s.x` or `s.C` (#2364): the model is its
    /// components, never a value, so the path, the component's variable,
    /// answers.
    Qualifier,
    /// A move of a run literal, its head, or the label it names: read by
    /// its shape, never resolved, so the run answers.
    Move,
    /// An unparenthesised product inside another, `B * C` in `A * B * C`, a
    /// sum inside another, `B + C` in `A + B + C`, or a lazy product inside
    /// another, `D & E` in `C & D & E`: the chain is one product, one sum or
    /// one lazy product of every operand, however it associates, and the
    /// outermost link answers.
    Chained,
    /// The value a `run _ <- c` discards, where `c` gives it with `pure`:
    /// `r` in `run _ <- case p { Succ(r) => pure r, … }`, or a `run x <- c`
    /// whose binder no later statement of the block reads (#2325). The
    /// lowering commutes the bind into each arm of `c` and drops a value
    /// nothing reads, so no core node holds it for a judgement to type; the
    /// lowering's result is the term the program means, and the case around
    /// the value answers.
    Discarded,
    /// An arrow of the kind a data family writes after its parameters,
    /// `Nat -> Type` in `data Vec(a : Type) : Nat -> Type { … }`, and each
    /// arrow down its codomain: the lowering reads the kind as the family's
    /// index classifiers before its universe, never as a type it forms, so
    /// each classifier and the universe answer.
    Kind,
    /// The sort `Size` a stage binder of a function's telescope is read at,
    /// `Size` in `def predAt @[i : Size] (…)`: the lowering reads the binder
    /// as a stage of the signature and forms no type for its sort, so the
    /// staged types naming the binder answer. Or a stage binder a call
    /// supplies by name, `j` in `applyAt[i = j](f, x)`: the stage is erased
    /// from the core, so no node holds it, and the call answers.
    Stage,
    /// The sort `Region` a region binder of a function's telescope is read
    /// at, `Region` in `def read @[r : Region] (…)`: the lowering reads the
    /// binder as a region of the signature and forms no type for its sort,
    /// so the kept types naming the binder answer.
    /// Or a row's label naming a region, as a label names its function's
    /// region binder, `r` in `[r : Console]` beside `@[r : Region]`, or the
    /// function's instance from a row other than its result's: a region, no
    /// term, so the row answers (#2390).
    Region,
    /// The theory a model type is written over, `T` in `Model(T)`: the name
    /// of a presentation, neither a term the checker judges nor a type the
    /// lowering forms, the record it derives located there and inserted, so
    /// the model type answers.
    Theory,
    /// The module a pack packs and the model type it states, `M` and
    /// `Model(T)` in `pack M at Model(T)`, the module or the caller's model
    /// implicit a call supplies a model implicit by, `M` or `t` in `f[s =
    /// M]` and `f[s = t]` (#2364), or the model type a written
    /// forgetting map states, `Model(T)` in `forget[sort C = A](m) at
    /// Model(T)` (#2218): the module is a namespace and the model type names
    /// the theory whose record the pack builds or whose map the call applies,
    /// neither a core node of its own, so the pack or the call answers.
    Packed,
    /// A variable a binding port binds, `t` in `rule zeta : let(u, t) <=>
    /// t(u)` and in `t(u)`, one a rule writes bare at a binding port under
    /// another name, `l` in `ext(m, l)` (#2360), or an abstracting operation
    /// applied in a theory's rule, `nu` in `nu(bind a . p)`: the variable is
    /// written without the field its port binds, and no core type states a
    /// `bind` port, so these names answer nowhere, and the application around
    /// answers at its sort.
    Unstated,
    /// The head and the type of a derived equality or law, `Eq.generic` and
    /// `T` in `def eq = Eq.generic(T)` or `def refl = Eq.generic.refl(T)`
    /// (#2302): the declaration is derived whole from `T`'s signature, so
    /// neither the prelude's member nor the data type is a core node of the
    /// definition, and the call, located at the derived body, answers.
    Generic,
    /// A node of the tactic a splice runs, `intro(assumption)` in
    /// `~intro(assumption)` (#2762): the checker runs the tactic at the
    /// splice's goal and judges the term it answers, so the tactic is no
    /// core term of its own, and the splice, located at the answered term,
    /// answers.
    Tactic,
}

/// What the lowering knows of a source's models: each model implicit a
/// declaration's telescope writes, by the bytes the declaration covers, and
/// every name along the path of each module the source's lowering holds.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Default)]
struct Models
{
    /// Each model implicit's name, beside the bytes its declaration covers.
    implicits: Vec<((usize, usize), String)>,
    /// Every name along each module's path, `limits` and `hard` for
    /// `limits.hard`.
    modules: BTreeSet<String>,
}

/// Every gated node of `tree` with its kind, its span and where it stands.
///
/// # Specification
/// trivial.
fn gated(
    grammar: &Pbg,
    tree: &SyntaxTree<'_>,
    refused: &BTreeSet<gandr_surface_syntax::NodeKey>,
    models: &Models,
) -> Vec<(String, ByteSpan, Option<Placed>)>
{
    let source: &str = tree.source().into();
    // The namespaces the builtin primitives are written under, each proper
    // prefix of a primitive's name, as the lowering seeds them.
    let namespaces: BTreeSet<&str> = gandr_core_term::primitive::PRELUDE
        .iter()
        .flat_map(|primitive| {
            let name: &'static str = primitive.name().into();
            name.match_indices('.')
                .filter_map(move |(at, _)| name.get(.. at))
        })
        .collect();
    // The module names a path can select from: every name along the path of
    // each module the lowering holds, and of each module an import names,
    // `text` and `greet` in `import text.greet (greeting);`.
    let modules: BTreeSet<&str> = models
        .modules
        .iter()
        .map(String::as_str)
        .chain(
            source
                .match_indices("import ")
                .filter_map(|(at, _)| {
                    let after = source.get(at.saturating_add(7) ..)?;
                    let end = after
                        .find(|letter: char| {
                            !(letter.is_alphanumeric() || letter == '_' || letter == '.')
                        })
                        .unwrap_or(after.len());
                    after.get(.. end)
                })
                .flat_map(|path| path.split('.')),
        )
        .filter(|name| !name.is_empty())
        .collect();
    // The stage binders the source declares, `j` in `@[j : Size]`, by name.
    let stages: BTreeSet<&str> = source
        .match_indices(": Size")
        .filter_map(|(at, _)| {
            let before = source.get(.. at)?.trim_end();
            let start = before
                .rfind(|letter: char| !(letter.is_alphanumeric() || letter == '_'))
                .map_or(0_usize, |at| at.saturating_add(1));
            before.get(start ..)
        })
        .collect();
    // The name `before` ends with, as a stage binder's is read.
    let named = |before: &'_ str| {
        let before = before.trim_end();
        let start = before
            .rfind(|letter: char| !(letter.is_alphanumeric() || letter == '_'))
            .map_or(0_usize, |at| at.saturating_add(1));
        before.get(start ..).map(str::to_owned)
    };
    // The ports that bind or abstract, `t` in `t : pi+ (x : Tm) . Tm` and `p`
    // in `p : bind (a : Name) . Proc`, and the operations declaring an
    // abstracting one, `nu` in `oper nu : (p : bind …) --> Proc`, by name; and
    // the bytes of every rule a theory writes, `rule` to its `;`.
    let binding: BTreeSet<String> = source
        .match_indices(": pi+")
        .map(|(at, _)| (at, false))
        .chain(source.match_indices(": bind").map(|(at, _)| (at, true)))
        .flat_map(|(at, abstracting)| {
            let before = source.get(.. at).unwrap_or("");
            let operation = before
                .rfind("oper ")
                .filter(|_| abstracting)
                .and_then(|oper| {
                    let after = before.get(oper.saturating_add(5) ..)?;
                    named(after.get(.. after.find(char::is_whitespace)?)?)
                });
            [named(before), operation]
        })
        .flatten()
        .collect();
    // The region binders a telescope writes, `r` in `@[r : Region]`, by name.
    let regions: BTreeSet<String> = source
        .match_indices(": Region")
        .filter_map(|(at, _)| named(source.get(.. at).unwrap_or("")))
        .collect();
    let rules: Vec<(usize, usize)> = source
        .match_indices("rule ")
        .filter_map(|(at, _)| {
            let end = source.get(at ..)?.find(';')?;
            Some((at, at.saturating_add(end)))
        })
        .collect();
    // The parts of the parenthesised list opening at `open`, each its bytes,
    // split at the commas no nested parenthesis holds.
    let parts = |open: usize| {
        let mut parts = Vec::new();
        let mut depth = 0_usize;
        let mut from = open.saturating_add(1);
        for (offset, letter) in source.get(open ..).unwrap_or("").char_indices() {
            let at = open.saturating_add(offset);
            match letter {
                '(' => depth = depth.saturating_add(1),
                ')' => {
                    depth = depth.saturating_sub(1);
                    if depth == 0 {
                        parts.push((from, at));
                        break;
                    }
                },
                ',' if depth == 1 => {
                    parts.push((from, at));
                    from = at.saturating_add(1);
                },
                _ => {},
            }
        }
        parts
    };
    // Each variable a rule writes bare at a binding port, `l` in `ext(m, l)`
    // for `oper ext : (m : C, k : pi+ (x : V) . C)`, by where it starts: the
    // variable the port binds, whatever the rule names it. An application's
    // operation is the one the last declaration of its name before the rule
    // declares.
    let bare: BTreeSet<usize> = rules
        .iter()
        .flat_map(|&(start, end)| {
            source
                .get(start .. end)
                .unwrap_or("")
                .match_indices('(')
                .map(move |(offset, _)| start.saturating_add(offset))
        })
        .flat_map(|open| {
            let rule = rules
                .iter()
                .find(|&&(start, end)| start <= open && open < end)
                .map_or(0_usize, |&(start, _)| start);
            let declared = named(source.get(.. open).unwrap_or(""))
                .filter(|name| name.starts_with(char::is_alphabetic))
                .and_then(|name| {
                    let before = source.get(.. rule)?;
                    before
                        .rmatch_indices("oper ")
                        .map(|(at, _)| at)
                        .find(|&at| {
                            before
                                .get(at.saturating_add(5) ..)
                                .and_then(|after| after.strip_prefix(name.as_str()))
                                .is_some_and(|after| after.starts_with(" :"))
                        })
                })
                .and_then(|oper| {
                    source
                        .get(oper ..)?
                        .find('(')
                        .map(|offset| oper.saturating_add(offset))
                });
            let binds: Vec<bool> = declared.map_or_else(Vec::new, |ports| {
                parts(ports)
                    .into_iter()
                    .map(|(from, to)| {
                        source
                            .get(from .. to)
                            .is_some_and(|port| port.contains(": pi+") || port.contains(": bind"))
                    })
                    .collect()
            });
            parts(open)
                .into_iter()
                .zip(binds)
                .filter_map(|((from, to), binds)| {
                    let written = source.get(from .. to)?;
                    let variable = written.trim();
                    (binds
                        && !variable.is_empty()
                        && variable
                            .chars()
                            .all(|letter| letter.is_alphanumeric() || letter == '_'))
                    .then(|| {
                        from.saturating_add(
                            written.len().saturating_sub(written.trim_start().len()),
                        )
                    })
                })
                .collect::<Vec<usize>>()
        })
        .collect();
    let mut gated = Vec::new();
    let mut stack = vec![(
        tree.root(),
        None::<Placed>,
        None::<(MoldId, &str, bool, bool, bool)>,
        Run::Outside,
        false,
    )];
    let spelled = |at: Option<NodeIndex>| {
        at.and_then(|at| tree.node(at))
            .and_then(|node| {
                source.get(usize::from(node.span().start()) .. usize::from(node.span().end()))
            })
            .unwrap_or("")
    };
    let mut children: Vec<NodeIndex> = Vec::new();
    let mut binds: Vec<bool> = Vec::new();
    while let Some((position, placed, parent, run, discarding)) = stack.pop() {
        let Some(node) = tree.node(position)
        else {
            continue;
        };
        let placed = placed.or_else(|| {
            tree.key(position)
                .filter(|key| refused.contains(key))
                .map(|_| Placed::Refused)
        });
        let (mold, def) = match node.label() {
            NodeLabel::Meld(mold) | NodeLabel::Tile(mold) => match grammar.mold(mold) {
                Ok(def) => (mold, def),
                Err(_) => continue,
            },
            NodeLabel::Doc => {
                stack.extend(
                    tree.children(position)
                        .map(|child| (child, Some(Placed::Quoted), None, run, discarding)),
                );
                continue;
            },
            NodeLabel::Wald
            | NodeLabel::Grout { .. }
            | NodeLabel::GhostClose { .. }
            | NodeLabel::Space => {
                stack.extend(
                    tree.children(position)
                        .map(|child| (child, placed, None, run, discarding)),
                );
                continue;
            },
        };
        let melded = matches!(node.label(), NodeLabel::Meld(_));
        if !melded {
            let atom = !bool::from(grammar.mold_has_predecessor(mold))
                && !bool::from(grammar.mold_has_successor(mold))
                && parent.is_none_or(|(held, ..)| held != mold);
            if !atom {
                continue;
            }
        }
        let placed = placed.or_else(|| def.label.starts_with('@').then_some(Placed::Quoted));
        let opener = first(tree, position);
        let applied = melded && def.label == "(" && def.sort == Sort::Expression;
        let called = if applied { spelled(opener) } else { "" };
        let within = match run {
            _ if LITERALS.contains(&called) => Run::Moves,
            Run::Moves if called == "selected" || called == "offered" => Run::Labelled,
            held @ (Run::Outside | Run::Moves | Run::Labelled) => held,
        };
        let span = node.span();
        let text = source
            .get(usize::from(span.start()) .. usize::from(span.end()))
            .unwrap_or("");
        // A bind's tiles stand among its block's children: the computation
        // after `run _ <-` is discarded, and so is the one after a named
        // binder no later child of the block reads (#2325); the one after a
        // binder the rest reads is kept, and every other child stands as its
        // parent does.
        children.clear();
        children.extend(tree.children(position).filter(|&child| {
            tree.node(child)
                .is_some_and(|node| node.label() != NodeLabel::Space)
        }));
        binds.clear();
        let mut bound = None::<bool>;
        for (at, &child) in children.iter().enumerate() {
            let previous = |back: usize| {
                at.checked_sub(back)
                    .and_then(|before| children.get(before))
                    .map_or("", |&before| spelled(Some(before)))
            };
            let discarded = bound.take().unwrap_or(discarding);
            if spelled(Some(child)) == "<-" && previous(2) == "run" {
                let binder = previous(1);
                let read = children
                    .get(at.saturating_add(2) ..)
                    .unwrap_or_default()
                    .iter()
                    .any(|&later| {
                        spelled(Some(later))
                            .split(|c: char| !(c.is_alphanumeric() || c == '_'))
                            .any(|word| word == binder)
                    });
                bound = Some(binder == "_" || !read);
            }
            binds.push(discarded);
        }
        let last = children.last().copied();
        // An arrow of a data family's kind: the operand the declaration writes
        // after its colon, or the codomain of such an arrow.
        let kinded = melded
            && def.label == "->"
            && def.sort == Sort::Type
            && parent.is_some_and(|(_, label, .., spine)| label == "data" || spine);
        // The theory a model type names: every child of `Model(…)` in a type
        // but its head.
        let modelled = melded && def.sort == Sort::Type && spelled(opener) == "Model";
        // The head and the type of a derived equality or law: every child of
        // an `Eq.generic(T)`, `Eq.generic.refl(T)` or `Eq.generic.sym(T)` call.
        let deriving = applied
            && matches!(
                spelled(opener),
                "Eq.generic" | "Eq.generic.refl" | "Eq.generic.sym"
            );
        // The module and the model type a pack names: every child of a
        // `pack M at Model(T)`, its third child the `at` tile.
        let packing = melded
            && def.label == "pack"
            && def.sort == Sort::Expression
            && spelled(children.get(2).copied()) == "at";
        // The model type a written forgetting map states: the last child of a
        // `forget[…](m) at Model(T)`, the `at` tile before it.
        let stating = melded
            && def.label == "forget"
            && def.sort == Sort::Expression
            && spelled(
                children
                    .len()
                    .checked_sub(2_usize)
                    .and_then(|before| children.get(before))
                    .copied(),
            ) == "at";
        stack.extend(
            children
                .iter()
                .zip(binds.iter().copied())
                .map(|(&child, discards)| {
                    let headed = melded
                        && opener == Some(child)
                        && (def.label == "[" || (def.label == "(" && def.sort == Sort::Expression));
                    let qualifying = melded && opener == Some(child) && def.label == ".";
                    (
                        child,
                        if deriving {
                            placed.or(Some(Placed::Generic))
                        }
                        else if melded && def.label == "~" && def.sort == Sort::Expression {
                            placed.or(Some(Placed::Tactic))
                        }
                        else if modelled && opener != Some(child) {
                            placed.or(Some(Placed::Theory))
                        }
                        else if packing || (stating && Some(child) == last) {
                            placed.or(Some(Placed::Packed))
                        }
                        else {
                            placed
                        },
                        Some((
                            mold,
                            def.label,
                            headed,
                            qualifying,
                            kinded && Some(child) == last,
                        )),
                        within,
                        discards,
                    )
                }),
        );
        if !matches!(def.sort, Sort::Expression | Sort::Type | Sort::Pattern) {
            continue;
        }
        // A constructor qualified by its family heading its call,
        // `Term.App(…)`, stands as a bare one does.
        let qualified = melded
            && def.label == "."
            && text
                .rsplit('.')
                .next()
                .is_some_and(|member| member.trim_start().starts_with(char::is_uppercase));
        let head = parent.is_some_and(|(_, label, headed, ..)| {
            headed
                && if melded {
                    label == "(" && qualified
                }
                else {
                    label == "[" || def.label == "constructor" || FORMERS.contains(&text)
                }
        });
        // A model implicit's name, read inside the declaration whose
        // telescope writes it.
        let modelled = models.implicits.iter().any(|&((start, end), ref name)| {
            name == text.trim()
                && start <= usize::from(span.start())
                && usize::from(span.end()) <= end
        });
        let qualifier = parent.is_some_and(|(_, _, _, qualifying, _)| qualifying)
            && if melded {
                def.label == "."
                    && (text.split('.').next().is_some_and(|head| {
                        let head = head.trim();
                        head.starts_with(char::is_uppercase) || modules.contains(head)
                    }) || namespaces.contains(text.trim()))
            }
            else {
                def.label == "constructor"
                    || def.label == "type_identifier"
                    || (def.label == "identifier"
                        && (namespaces.contains(text) || modules.contains(text.trim())))
                    || ((def.label == "identifier" || def.label == "type_variable") && modelled)
            };
        // A module or a model implicit a call supplies a model implicit by,
        // `M` in `f[s = M]` and `t` in `f[s = t]`.
        let packed = !melded
            && ((def.label == "constructor" && models.modules.contains(text.trim()))
                || (def.label == "identifier" && modelled))
            && parent.is_some_and(|(held, ..)| {
                grammar
                    .mold(held)
                    .is_ok_and(|resident| resident.sort == Sort::Instantiation)
            });
        let moved = match run {
            Run::Outside => false,
            Run::Moves => {
                (applied && MOVES.contains(&called)) || (!melded && MOVES.contains(&text))
            },
            Run::Labelled => !melded && def.label == "identifier",
        };
        let chained = melded
            && (def.label == "*" || def.label == "+" || def.label == "&")
            && def.sort == Sort::Type
            && parent.is_some_and(|(held, ..)| held == mold);
        let dropped = discarding
            && !melded
            && def.label == "identifier"
            && parent.is_some_and(|(_, label, ..)| label == "pure");
        let counted = !melded
            && def.label == "number"
            && parent.is_some_and(|(_, label, headed, ..)| label == "[" && !headed);
        let sized = !melded
            && def.label == "type_identifier"
            && text == "Size"
            && parent.is_some_and(|(_, label, ..)| label == "def");
        let regioned = !melded
            && def.label == "type_identifier"
            && text == "Region"
            && parent.is_some_and(|(_, label, ..)| label == "def");
        // A row's label that names a region rather than binding an instance:
        // one naming a region binder, `r` in `[r : Console]` beside `@[r :
        // Region]`, or one in a row other than a function's result, `o` in a
        // parameter's `+U (-F [o : Console] Unit)`.
        let naming = !melded
            && def.label == "type_variable"
            && source
                .get(usize::from(span.end()) ..)
                .is_some_and(|after| after.trim_start().starts_with(':'))
            && source
                .get(.. usize::from(span.start()))
                .and_then(|before| {
                    let open = before.rfind('[')?;
                    let inside = before.get(open.saturating_add(1) ..)?;
                    if inside.contains(['(', ')', ']', '@']) {
                        return None;
                    }
                    let lead = before.get(.. open)?.trim_end();
                    let returned = lead.strip_suffix("-F").map(str::trim_end);
                    if !lead.ends_with("->") && returned.is_none() {
                        return None;
                    }
                    let result = lead.ends_with("->")
                        || returned.is_some_and(|returned| returned.ends_with("->"));
                    Some(!result || regions.contains(text.trim()))
                })
                .unwrap_or(false);
        let supplied = !melded
            && def.label == "identifier"
            && stages.contains(text.trim())
            && parent.is_some_and(|(held, ..)| {
                grammar
                    .mold(held)
                    .is_ok_and(|resident| resident.sort == Sort::Instantiation)
            });
        let unstated = !melded
            && def.label == "identifier"
            && (bare.contains(&usize::from(span.start()))
                || (binding.contains(text.trim())
                    && rules.iter().any(|&(start, end)| {
                        start <= usize::from(span.start()) && usize::from(span.end()) <= end
                    })));
        let placed = placed
            .or_else(|| head.then_some(Placed::Head))
            .or_else(|| counted.then_some(Placed::Stratum))
            .or_else(|| qualifier.then_some(Placed::Qualifier))
            .or_else(|| moved.then_some(Placed::Move))
            .or_else(|| chained.then_some(Placed::Chained))
            .or_else(|| dropped.then_some(Placed::Discarded))
            .or_else(|| kinded.then_some(Placed::Kind))
            .or_else(|| (sized || supplied).then_some(Placed::Stage))
            .or_else(|| (regioned || naming).then_some(Placed::Region))
            .or_else(|| unstated.then_some(Placed::Unstated))
            .or_else(|| packed.then_some(Placed::Packed));
        gated.push((kind(grammar, tree, position, *def), span, placed));
    }
    gated
}

/// A splice's tactic and a lowercase module path, nested or imported, stand
/// placed, so the census reads only the nodes the program holds, while the
/// splice and the path themselves answer (#2959).
#[test]
fn a_tactic_and_a_lowercase_module_path_stand_placed_2959()
{
    let grammar = built_in().expect("the built-in grammar builds");
    let source = "import text.greet (greeting);\ndef id : Integer => Integer = \
                  ~intro(assumption);\ndef note = limits.hard.note;\ndef welcome = \
                  text.greet.greeting;\n";
    let tree = parse(&grammar, SourceText::from(source))
        .expect("the source parses")
        .into_tree();
    let models = Models {
        implicits: Vec::new(),
        modules: BTreeSet::from([String::from("limits"), String::from("hard")]),
    };
    let gated: Vec<(&str, Option<Placed>)> = gated(&grammar, &tree, &BTreeSet::new(), &models)
        .into_iter()
        .filter_map(|(_, span, placed)| {
            source
                .get(usize::from(span.start()) .. usize::from(span.end()))
                .map(|text| (text, placed))
        })
        .collect();
    let stands = |text: &str, placed: Option<Placed>| {
        gated
            .iter()
            .any(|&(written, held)| written == text && held == placed)
    };
    for (text, placed) in [
        ("~intro(assumption)", None),
        ("intro(assumption)", Some(Placed::Tactic)),
        ("assumption", Some(Placed::Tactic)),
        ("limits.hard.note", None),
        ("limits.hard", Some(Placed::Qualifier)),
        ("limits", Some(Placed::Qualifier)),
        ("text.greet.greeting", None),
        ("text.greet", Some(Placed::Qualifier)),
        ("text", Some(Placed::Qualifier)),
    ] {
        assert!(
            stands(text, placed),
            "`{text}` stands {placed:?}: {gated:?}"
        );
    }
}

/// The entry sweep: the gate over the corpus's sources.
mod sweeps
{
    use gandr_workflow_sweep::Coverage;
    use gandr_workflow_sweep::Sample;
    use gandr_workflow_sweep::SampleName;
    use gandr_workflow_sweep::SampleSize;
    use gandr_workflow_sweep::Sweep;

    use super::*;

    /// The sample: thirty-two sources, ranked by their BLAKE3 digest under
    /// this name, at least one of each corpus class — `strict` and each
    /// family under the top-level `corpus` — and every source the change adds
    /// or modifies (`gandr-workflow-sweep`), each walked as its own path. A
    /// sampled run holds each node and each byte to the gate, and each owed
    /// kind to at most its pin. The `sweeps` and nightly profiles walk the
    /// roots whole and hold the census exactly: every pin met, every by-design
    /// kind seen without its entry, every listed kind written.
    const SAMPLE: Sample = Sample {
        name: SampleName("every_judged_node_answers_at_its_own_span"),
        size: SampleSize(32),
    };

    #[test]
    fn every_judged_node_answers_at_its_own_span()
    {
        let grammar = built_in().expect("the built-in grammar builds");
        let page = PageWidth::from(80_u32);
        let standings: BTreeMap<&str, Standing> = KINDS.iter().copied().collect();
        let mut missing: BTreeMap<String, (usize, String)> = BTreeMap::new();
        let mut met = BTreeSet::new();
        let mut astray = Vec::new();
        let mut nodes = 0_usize;
        let sweep = Sweep::asked().expect("the run's sweep resolves");
        let whole = sweep.coverage() == Coverage::Full;
        let paths: Vec<PathBuf> = if whole {
            let corpus = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
                .join("../..")
                .join("corpus");
            vec![
                root(Path::new("strict")),
                corpus.join("classifier"),
                corpus.join("fragment"),
                corpus.join("model"),
                corpus.join("pathological"),
                corpus.join("pending"),
                corpus.join("surface"),
            ]
        }
        else {
            let visited = sweep.visit(
                SAMPLE,
                &gandr_workflow_sweep::corpus::sources().expect("the corpus reads"),
            );
            assert!(
                visited.len() >= SAMPLE.size.0,
                "the sample is drawn: {}",
                visited.len()
            );
            visited.into_iter().map(|source| source.path).collect()
        };
        let walk = Walk::new(paths);
        let ControlFlow::Continue(_report) = walk.visit(
            &Pool::new(Width::SERIAL),
            |step| -> ControlFlow<Infallible> {
                let Step::Source {
                    path,
                    root,
                    text,
                    base,
                    composed,
                    ..
                } = step
                else {
                    return ControlFlow::Continue(());
                };
                if path.components().any(|part| part.as_os_str() == "pending") {
                    return ControlFlow::Continue(());
                }
                // A source is typed over the prelude and its closure, as the
                // hover types it: the table and the tree are its own text's,
                // the lowering the closure's. The walk judged it in its
                // component, so a judged declaration is matched to the
                // closure's by where it starts in the source's own text.
                let Some(own) = <&str>::from(text).get(usize::from(base) ..)
                else {
                    return ControlFlow::Continue(());
                };
                let laid = lay_out(&grammar, path, root, SourceText::from(own));
                let unit = SourceText::from(laid.text.as_str());
                let (table, lowering, laid_base) = (
                    TypeTable::of_unit(&grammar, unit, &laid.unit, laid.base),
                    lower_unit_source(&grammar, unit, &laid.unit, &mut LoweringCount::default()),
                    usize::from(laid.base),
                );
                let text = SourceText::from(own);
                let (Ok(table), Ok(parsed)) = (table, parse(&grammar, text))
                else {
                    return ControlFlow::Continue(());
                };
                let tree = parsed.into_tree();
                let mut refused: BTreeSet<_> = table
                    .declarations(page, Form::Sugared.into())
                    .filter(|entry| matches!(entry.1, Maybe::Present(Declared::Refused(_))))
                    .map(|(key, _)| key)
                    .collect();
                let judged_refused: BTreeSet<usize> = match composed {
                    Composed::Settled { ref report, .. } => report
                        .declarations()
                        .iter()
                        .filter(|declaration| {
                            matches!(declaration.produced().refusal(), Maybe::Present(_))
                        })
                        .filter_map(|declaration| {
                            usize::from(declaration.span().start()).checked_sub(usize::from(base))
                        })
                        .collect(),
                    Composed::Refused(_) => BTreeSet::new(),
                };
                let mut models = Models::default();
                if let Ok(lowering) = lowering
                    && let Lowered::Module { ref module, .. } = lowering.into_lowered()
                {
                    for declaration in module.declarations() {
                        let written =
                            usize::from(declaration.span().start()).checked_sub(laid_base);
                        if written.is_some_and(|at| judged_refused.contains(&at)) {
                            for half in [declaration.signature(), declaration.definition()] {
                                if let Maybe::Present(key) = half {
                                    let _new = refused.insert(key.form());
                                }
                            }
                        }
                        let covered = written
                            .zip(usize::from(declaration.span().end()).checked_sub(laid_base));
                        for slot in module.model_slots(declaration.constant()) {
                            if let Some(covered) = covered {
                                models
                                    .implicits
                                    .push((covered, String::from(slot.name.as_ref())));
                            }
                        }
                    }
                    models.modules.extend(
                        module
                            .structures()
                            .iter()
                            .flat_map(gandr_surface_lowering::LoweredStructure::path)
                            .map(|name| String::from(name.as_ref())),
                    );
                }
                let spans: BTreeSet<ByteSpan> = table.spans().collect();
                let mut innermost: Vec<Option<ByteSpan>> = vec![None; <&str>::from(text).len()];
                let mut held = Vec::new();
                for (key, span, placed) in gated(&grammar, &tree, &refused, &models) {
                    if placed.is_some() {
                        continue;
                    }
                    nodes = nodes.saturating_add(1);
                    let _first = met.insert(key.clone());
                    if spans.contains(&span) {
                        held.push(span);
                        continue;
                    }
                    let at = format!("{}@{}", path.display(), usize::from(span.start()));
                    let tally = missing.entry(key).or_insert((0, at));
                    tally.0 = tally.0.saturating_add(1);
                }
                held.sort_by_key(|span| {
                    core::cmp::Reverse(
                        usize::from(span.end()).saturating_sub(usize::from(span.start())),
                    )
                });
                for span in held {
                    for byte in usize::from(span.start()) .. usize::from(span.end()) {
                        if let Some(slot) = innermost.get_mut(byte) {
                            *slot = Some(span);
                        }
                    }
                }
                for (byte, inner) in innermost.into_iter().enumerate() {
                    let Some(inner) = inner
                    else {
                        continue;
                    };
                    let answered = table.answering(ByteOffset::from(byte));
                    if !answered.is_some_and(|span| {
                        span.start() >= inner.start() && span.end() <= inner.end()
                    }) {
                        astray.push(format!(
                            "{}@{byte}: answers {answered:?} inside {inner:?}",
                            path.display()
                        ));
                    }
                }
                ControlFlow::Continue(())
            },
        );
        let mut failures = Vec::new();
        for key in &met {
            match standings.get(key.as_str()) {
                None => failures.push(format!("unclassified kind `{key}`")),
                Some(&Standing::Design(reason)) => {
                    if whole && !missing.contains_key(key) {
                        failures.push(format!(
                            "`{key}` stands by design ({reason}), yet every node has its entry: pin it owed at 0"
                        ));
                    }
                },
                Some(&Standing::Owed(pinned)) => {
                    let (count, ref at) = missing.get(key).cloned().unwrap_or((0, String::new()));
                    if count > pinned || (whole && count != pinned) {
                        failures.push(format!(
                        "`{key}`: {count} nodes without an entry, pinned at {pinned}; first at {at}"
                    ));
                    }
                },
            }
        }
        if whole {
            for &(key, _) in KINDS {
                if !met.contains(key) {
                    failures.push(format!("`{key}` names no kind the corpus writes"));
                }
            }
        }
        assert!(nodes > 0, "the corpus holds gated nodes");
        assert_eq!(
            failures,
            Vec::<String>::new(),
            "every kind stands where it is classified"
        );
        assert_eq!(
            astray,
            Vec::<String>::new(),
            "the hover answers the innermost node"
        );
    }
}
