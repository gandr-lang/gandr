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
use gandr_surface_dispatcher::Step;
use gandr_surface_dispatcher::TypeTable;
use gandr_surface_dispatcher::Walk;
use gandr_surface_dispatcher::Width;
use gandr_surface_dispatcher::lay_out;
use gandr_surface_dispatcher::lower_source;
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
    ("Expression <=", Standing::Owed(0)),
    ("Expression >", Standing::Owed(0)),
    ("Expression >=", Standing::Owed(0)),
    ("Expression ?", Standing::Owed(0)),
    (
        "Expression [",
        Standing::Design(
            "an annotation on a head — a stratum or a descent claim: the call it heads answers",
        ),
    ),
    ("Expression abort", Standing::Owed(0)),
    ("Expression access", Standing::Owed(0)),
    ("Expression become", Standing::Design(EXIT)),
    ("Expression break", Standing::Design(EXIT)),
    ("Expression case", Standing::Owed(0)),
    ("Expression close", Standing::Owed(0)),
    ("Expression constructor", Standing::Owed(0)),
    ("Expression continue", Standing::Owed(0)),
    ("Expression fn", Standing::Owed(0)),
    ("Expression for", Standing::Owed(0)),
    ("Expression force", Standing::Owed(0)),
    ("Expression handle", Standing::Owed(0)),
    ("Expression hold", Standing::Owed(0)),
    ("Expression identifier", Standing::Owed(0)),
    ("Expression loop", Standing::Owed(0)),
    ("Expression migrate", Standing::Owed(0)),
    ("Expression number", Standing::Owed(0)),
    ("Expression offer", Standing::Owed(0)),
    ("Expression pure", Standing::Design(EXIT)),
    ("Expression resume", Standing::Owed(0)),
    ("Expression return", Standing::Owed(0)),
    ("Expression run", Standing::Owed(0)),
    ("Expression select", Standing::Owed(0)),
    ("Expression send", Standing::Owed(0)),
    ("Expression then", Standing::Owed(0)),
    ("Expression thunk", Standing::Owed(0)),
    ("Expression unit", Standing::Owed(0)),
    ("Expression while", Standing::Owed(0)),
    (
        "Expression {",
        Standing::Design("a block: the computation it holds answers"),
    ),
    ("Expression ∷", Standing::Owed(0)),
    ("Pattern #{", Standing::Owed(0)),
    ("Pattern (", Standing::Owed(0)),
    ("Pattern +", Standing::Owed(0)),
    ("Pattern _", Standing::Owed(0)),
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
    ("Type Cap", Standing::Owed(0)),
    ("Type Integer", Standing::Owed(0)),
    ("Type Path", Standing::Owed(0)),
    ("Type String", Standing::Owed(0)),
    ("Type Type", Standing::Owed(0)),
    ("Type Type+", Standing::Owed(0)),
    ("Type Unit", Standing::Owed(0)),
    ("Type Void", Standing::Owed(0)),
    ("Type \\", Standing::Owed(0)),
    (
        "Type at",
        Standing::Design("a scoped capability: the capability it scopes answers, at its scope"),
    ),
    ("Type end", Standing::Owed(0)),
    ("Type mu", Standing::Owed(0)),
    ("Type number", Standing::Owed(0)),
    ("Type type_identifier", Standing::Owed(0)),
    ("Type type_variable", Standing::Owed(0)),
    ("Type ⇝", Standing::Owed(0)),
    ("Type ≃", Standing::Owed(0)),
    ("Type ≅", Standing::Owed(0)),
];

/// The names of the primitive formers a call can head: the call is one
/// core node, and its head names the former rather than a term.
const FORMERS: &[&str] = &[
    "arrow",
    "back",
    "bisim",
    "cong",
    "cons",
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

/// The moves a run literal `recorded(m₀, …, mₙ)` is written in. A move is
/// read by its shape, never resolved: the run literal is the core node,
/// and a payload inside a move is a term of its own.
const MOVES: &[&str] = &["closed", "offered", "received", "selected", "sent"];

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
/// a run literal's move, as an inner link of a product or a sum chain, as
/// the value a discarded bind drops, or as an arrow of a data family's kind.
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
    /// annotation: the call is the one core node, and answers.
    Head,
    /// A count of the stratum an annotation on a head writes, `1` and `4`
    /// in `ua[1, 4](a, b, f, g)`: the degree and the catalogue bound the
    /// former reads off the literal's digits, never a term, so the call
    /// the annotation heads answers (#298).
    Stratum,
    /// The module a path selects from, `M` in `M.x` or `M.T`: a
    /// namespace, neither a term nor a type, so the path answers.
    Qualifier,
    /// A move of a run literal, its head, or the label it names: read by
    /// its shape, never resolved, so the run answers.
    Move,
    /// An unparenthesised product inside another, `B * C` in `A * B * C`,
    /// or a sum inside another, `B + C` in `A + B + C`: the chain is one
    /// product or one sum of every operand, however it associates, and
    /// the outermost link answers.
    Chained,
    /// The value a `run _ <- c` discards, where `c` gives it with `pure`:
    /// `r` in `run _ <- case p { Succ(r) => pure r, … }`. The lowering
    /// commutes the bind into each arm of `c` and drops a value nothing
    /// reads, so no core node holds it for a judgement to type; the
    /// lowering's result is the term the program means, and the case
    /// around the value answers.
    Discarded,
    /// An arrow of the kind a data family writes after its parameters,
    /// `Nat -> Type` in `data Vec(a : Type) : Nat -> Type { … }`, and each
    /// arrow down its codomain: the lowering reads the kind as the family's
    /// index classifiers before its universe, never as a type it forms, so
    /// each classifier and the universe answer.
    Kind,
}

/// Every gated node of `tree` with its kind, its span and where it stands.
///
/// # Specification
/// trivial.
fn gated(
    grammar: &Pbg,
    tree: &SyntaxTree<'_>,
    refused: &BTreeSet<gandr_surface_syntax::NodeKey>,
) -> Vec<(String, ByteSpan, Option<Placed>)>
{
    let source: &str = tree.source().into();
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
            _ if called == "recorded" => Run::Moves,
            Run::Moves if called == "selected" || called == "offered" => Run::Labelled,
            held @ (Run::Outside | Run::Moves | Run::Labelled) => held,
        };
        let span = node.span();
        let text = source
            .get(usize::from(span.start()) .. usize::from(span.end()))
            .unwrap_or("");
        // A bind's tiles stand among its block's children: the computation
        // after `run _ <-` is discarded, the one after a named binder's
        // `<-` kept; every other child stands as its parent does.
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
                bound = Some(previous(1) == "_");
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
                        placed,
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
        let head = !melded
            && parent.is_some_and(|(_, label, headed, ..)| {
                headed && (label == "[" || def.label == "constructor" || FORMERS.contains(&text))
            });
        let qualifier = !melded
            && parent.is_some_and(|(_, _, _, qualifying, _)| qualifying)
            && (def.label == "constructor" || def.label == "type_identifier");
        let moved = match run {
            Run::Outside => false,
            Run::Moves => {
                (applied && MOVES.contains(&called)) || (!melded && MOVES.contains(&text))
            },
            Run::Labelled => !melded && def.label == "identifier",
        };
        let chained = melded
            && (def.label == "*" || def.label == "+")
            && def.sort == Sort::Type
            && parent.is_some_and(|(held, ..)| held == mold);
        let dropped = discarding
            && !melded
            && def.label == "identifier"
            && parent.is_some_and(|(_, label, ..)| label == "pure");
        let counted = !melded
            && def.label == "number"
            && parent.is_some_and(|(_, label, headed, ..)| label == "[" && !headed);
        let placed = placed
            .or_else(|| head.then_some(Placed::Head))
            .or_else(|| counted.then_some(Placed::Stratum))
            .or_else(|| qualifier.then_some(Placed::Qualifier))
            .or_else(|| moved.then_some(Placed::Move))
            .or_else(|| chained.then_some(Placed::Chained))
            .or_else(|| dropped.then_some(Placed::Discarded))
            .or_else(|| kinded.then_some(Placed::Kind));
        gated.push((kind(grammar, tree, position, *def), span, placed));
    }
    gated
}

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
    let walk = Walk::new(vec![root(Path::new("strict")), root(Path::new("fixture"))]);
    let ControlFlow::Continue(_report) =
        walk.visit(Width::SERIAL, |step| -> ControlFlow<Infallible> {
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
            // An importer is typed over its closure, as the hover types it:
            // the table and the tree are its own text's, the lowering the
            // closure's. The walk judged it in its component, so a judged
            // declaration is matched to the closure's by where it starts in
            // the source's own text.
            let Some(own) = <&str>::from(text).get(usize::from(base) ..)
            else {
                return ControlFlow::Continue(());
            };
            let laid = lay_out(&grammar, path, root, SourceText::from(own));
            let (table, lowering, laid_base) = match laid {
                Maybe::Present(ref laid) => {
                    let unit = SourceText::from(laid.text.as_str());
                    (
                        TypeTable::of_unit(&grammar, unit, &laid.unit, laid.base),
                        lower_unit_source(
                            &grammar,
                            unit,
                            &laid.unit,
                            &mut LoweringCount::default(),
                        ),
                        usize::from(laid.base),
                    )
                },
                Maybe::Absent(_) => {
                    let alone = SourceText::from(own);
                    (
                        TypeTable::of(&grammar, alone),
                        lower_source(&grammar, alone, &mut LoweringCount::default()),
                        0_usize,
                    )
                },
            };
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
            if let Ok(lowering) = lowering
                && let Lowered::Module { ref module, .. } = lowering.into_lowered()
            {
                for declaration in module.declarations() {
                    let written = usize::from(declaration.span().start()).checked_sub(laid_base);
                    if written.is_some_and(|at| judged_refused.contains(&at)) {
                        for half in [declaration.signature(), declaration.definition()] {
                            if let Maybe::Present(key) = half {
                                let _new = refused.insert(key.form());
                            }
                        }
                    }
                }
            }
            let spans: BTreeSet<ByteSpan> = table.spans().collect();
            let mut innermost: Vec<Option<ByteSpan>> = vec![None; <&str>::from(text).len()];
            let mut held = Vec::new();
            for (key, span, placed) in gated(&grammar, &tree, &refused) {
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
                if !answered
                    .is_some_and(|span| span.start() >= inner.start() && span.end() <= inner.end())
                {
                    astray.push(format!(
                        "{}@{byte}: answers {answered:?} inside {inner:?}",
                        path.display()
                    ));
                }
            }
            ControlFlow::Continue(())
        });
    let mut failures = Vec::new();
    for key in &met {
        match standings.get(key.as_str()) {
            None => failures.push(format!("unclassified kind `{key}`")),
            Some(&Standing::Design(reason)) => {
                if !missing.contains_key(key) {
                    failures.push(format!(
                            "`{key}` stands by design ({reason}), yet every node has its entry: pin it owed at 0"
                        ));
                }
            },
            Some(&Standing::Owed(pinned)) => {
                let (count, ref at) = missing.get(key).cloned().unwrap_or((0, String::new()));
                if count != pinned {
                    failures.push(format!(
                        "`{key}`: {count} nodes without an entry, pinned at {pinned}; first at {at}"
                    ));
                }
            },
        }
    }
    for &(key, _) in KINDS {
        if !met.contains(key) {
            failures.push(format!("`{key}` names no kind the corpus writes"));
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
