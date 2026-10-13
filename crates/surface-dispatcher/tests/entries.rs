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
//! attribute, inside a declaration the lowering or the checker refused, or
//! heading a call — and `Placed` names them.

extern crate alloc;

/// The gate, in a `cfg(test)` module so the crate's lint wall reads it as
/// test code rather than as shipping code.
#[cfg(test)]
mod entries
{
    use alloc::collections::BTreeMap;
    use alloc::collections::BTreeSet;
    use std::path::Path;
    use std::path::PathBuf;

    use gandr_kernel_term::ConstantIndex;
    use gandr_surface_corpus::DeclarationReport;
    use gandr_surface_dispatcher::Composed;
    use gandr_surface_dispatcher::Declared;
    use gandr_surface_dispatcher::Lowered;
    use gandr_surface_dispatcher::LoweringCount;
    use gandr_surface_dispatcher::Step;
    use gandr_surface_dispatcher::TypeTable;
    use gandr_surface_dispatcher::Walk;
    use gandr_surface_dispatcher::lower_source;
    use gandr_surface_grammar::MoldDef;
    use gandr_surface_grammar::Pbg;
    use gandr_surface_grammar::Sort;
    use gandr_surface_grammar::built_in;
    use gandr_surface_parser::parse;
    use gandr_surface_pretty::PageWidth;
    use gandr_surface_syntax::ByteOffset;
    use gandr_surface_syntax::ByteSpan;
    use gandr_surface_syntax::MoldId;
    use gandr_surface_syntax::Node;
    use gandr_surface_syntax::NodeIndex;
    use gandr_surface_syntax::NodeLabel;
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

    /// A pattern's reason: it is matched, not judged.
    const MATCHED: &str = "a pattern is matched, not judged: the scrutinee answers at its type, \
                           and a binder at its uses";

    /// An exit's reason: the keyword heads the computation its operand ends.
    const EXIT: &str = "an exit keyword ends the computation its operand gives: the operand \
                        answers, and the enclosing body at its type";

    /// Every kind of node the corpus writes, by sort and naming label, with
    /// where it stands. An owed count only shrinks: lower it with the change
    /// that gives the nodes their entries.
    const KINDS: &[(&str, Standing)] = &[
        ("Expression \"", Standing::Owed(0)),
        ("Expression #{", Standing::Owed(0)),
        ("Expression &", Standing::Owed(0)),
        ("Expression ( application", Standing::Owed(66)),
        (
            "Expression ( group",
            Standing::Design("a parenthesised group: the node inside answers"),
        ),
        ("Expression +", Standing::Owed(14)),
        ("Expression .", Standing::Owed(8)),
        ("Expression >", Standing::Owed(0)),
        ("Expression ?", Standing::Owed(0)),
        (
            "Expression [",
            Standing::Design(
                "an annotation on a head — a stratum or a descent claim: the call it heads answers",
            ),
        ),
        ("Expression become", Standing::Design(EXIT)),
        ("Expression break", Standing::Design(EXIT)),
        ("Expression case", Standing::Owed(0)),
        ("Expression close", Standing::Owed(0)),
        ("Expression constructor", Standing::Owed(23)),
        ("Expression continue", Standing::Design(EXIT)),
        ("Expression fn", Standing::Owed(0)),
        ("Expression force", Standing::Owed(0)),
        ("Expression handle", Standing::Owed(0)),
        ("Expression identifier", Standing::Owed(198)),
        ("Expression loop", Standing::Owed(0)),
        ("Expression number", Standing::Owed(1)),
        ("Expression offer", Standing::Owed(0)),
        ("Expression pure", Standing::Design(EXIT)),
        ("Expression return", Standing::Design(EXIT)),
        ("Expression run", Standing::Owed(3)),
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
        ("Pattern #{", Standing::Design(MATCHED)),
        ("Pattern (", Standing::Design(MATCHED)),
        ("Pattern +", Standing::Design(MATCHED)),
        ("Pattern _", Standing::Design(MATCHED)),
        ("Pattern constructor", Standing::Design(MATCHED)),
        ("Pattern false", Standing::Design(MATCHED)),
        ("Pattern identifier", Standing::Design(MATCHED)),
        ("Pattern number", Standing::Design(MATCHED)),
        ("Pattern true", Standing::Design(MATCHED)),
        ("Pattern |", Standing::Design(MATCHED)),
        ("Type !", Standing::Owed(30)),
        ("Type #{", Standing::Owed(0)),
        ("Type &", Standing::Owed(13)),
        (
            "Type ( group",
            Standing::Design(
                "a parenthesised group or parameter list: the type inside or around answers",
            ),
        ),
        ("Type *", Standing::Owed(3)),
        ("Type +", Standing::Owed(13)),
        ("Type +U", Standing::Owed(0)),
        ("Type ->", Standing::Owed(0)),
        ("Type -F", Standing::Owed(0)),
        ("Type .", Standing::Owed(4)),
        ("Type =>", Standing::Owed(0)),
        ("Type ?", Standing::Owed(0)),
        ("Type Cap", Standing::Owed(0)),
        ("Type Integer", Standing::Owed(0)),
        ("Type Path", Standing::Owed(0)),
        ("Type String", Standing::Owed(0)),
        ("Type Type", Standing::Owed(0)),
        ("Type Unit", Standing::Owed(0)),
        ("Type Void", Standing::Owed(0)),
        ("Type \\", Standing::Owed(0)),
        ("Type end", Standing::Owed(25)),
        ("Type mu", Standing::Owed(12)),
        ("Type number", Standing::Owed(0)),
        ("Type type_identifier", Standing::Owed(55)),
        ("Type type_variable", Standing::Owed(133)),
    ];

    /// The names of the primitive formers a call can head: the call is one
    /// core node, and its head names the former rather than a term.
    const FORMERS: &[&str] = &[
        "arrow",
        "back",
        "cong",
        "cons",
        "equiv",
        "flowProduct",
        "forward",
        "funext",
        "here",
        "pathProduct",
        "stay",
        "transport",
        "ua",
    ];

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
    /// lowering refused, or as the head of a former's call.
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
        let mut stack = vec![(tree.root(), None::<Placed>, None::<(MoldId, &str, bool)>)];
        while let Some((position, placed, parent)) = stack.pop() {
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
                | NodeLabel::Meld(mold) | NodeLabel::Tile(mold) => match grammar.mold(mold) {
                    | Ok(def) => (mold, def),
                    | Err(_) => continue,
                },
                | NodeLabel::Doc => {
                    stack.extend(
                        tree.children(position)
                            .map(|child| (child, Some(Placed::Quoted), None)),
                    );
                    continue;
                },
                | _ => {
                    stack.extend(tree.children(position).map(|child| (child, placed, None)));
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
            stack.extend(tree.children(position).map(|child| {
                let headed = melded
                    && opener == Some(child)
                    && (def.label == "[" || (def.label == "(" && def.sort == Sort::Expression));
                (child, placed, Some((mold, def.label, headed)))
            }));
            if !matches!(def.sort, Sort::Expression | Sort::Type | Sort::Pattern) {
                continue;
            }
            let span = node.span();
            let text = source
                .get(usize::from(span.start()) .. usize::from(span.end()))
                .unwrap_or("");
            let head = !melded
                && parent.is_some_and(|(_, label, headed)| {
                    headed
                        && (label == "[" || def.label == "constructor" || FORMERS.contains(&text))
                });
            let placed = placed.or_else(|| head.then_some(Placed::Head));
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
        let mut walk = Walk::new(vec![root(Path::new("strict")), root(Path::new("fixture"))]);
        while let Maybe::Present(step) = walk.step() {
            let Step::Source {
                path,
                text,
                composed,
                ..
            } = step
            else {
                continue;
            };
            if path.components().any(|part| part.as_os_str() == "pending") {
                continue;
            }
            let (Ok(table), Ok(parsed)) = (TypeTable::of(&grammar, text), parse(&grammar, text))
            else {
                continue;
            };
            let tree = parsed.into_tree();
            let mut refused: BTreeSet<_> = table
                .declarations(page)
                .filter(|entry| matches!(entry.1, Maybe::Present(Declared::Refused(_))))
                .map(|(key, _)| key)
                .collect();
            let judged_refused: BTreeSet<ConstantIndex> = match composed {
                | Composed::Settled { ref report, .. } => report
                    .declarations()
                    .iter()
                    .filter(|declaration| {
                        matches!(declaration.produced().refusal(), Maybe::Present(_))
                    })
                    .map(DeclarationReport::constant)
                    .collect(),
                | _ => BTreeSet::new(),
            };
            if let Ok(lowering) = lower_source(&grammar, text, &mut LoweringCount::default())
                && let Lowered::Module { ref module, .. } = lowering.into_lowered()
            {
                for declaration in module.declarations() {
                    if judged_refused.contains(&declaration.constant()) {
                        for half in [declaration.signature(), declaration.definition()] {
                            if let Maybe::Present(key) = half {
                                let _new = refused.insert(key);
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
        }
        let mut failures = Vec::new();
        for key in &met {
            match standings.get(key.as_str()) {
                | None => failures.push(format!("unclassified kind `{key}`")),
                | Some(&Standing::Design(reason)) => {
                    if !missing.contains_key(key) {
                        failures.push(format!(
                            "`{key}` stands by design ({reason}), yet every node has its entry: pin it owed at 0"
                        ));
                    }
                },
                | Some(&Standing::Owed(pinned)) => {
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
}
