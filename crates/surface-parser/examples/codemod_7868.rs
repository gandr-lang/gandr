//! Throwaway codemod for #7868: `! T . S`, `! T >> S` → `T >! S`; `? …` →
//! `T >? S`; `mu X . S` → `rec X => S`. Reads each file with the grammar of
//! this tree and rewrites only the bytes of those forms. Deleted after use.
#![allow(clippy::all, clippy::pedantic, clippy::restriction, missing_docs)]

use gandr_surface_grammar::Pbg;
use gandr_surface_grammar::built_in;
use gandr_surface_parser::parse;
use gandr_surface_syntax::NodeIndex;
use gandr_surface_syntax::NodeLabel;
use gandr_surface_syntax::SourceText;
use gandr_surface_syntax::SyntaxTree;

const ARROW_LEVEL: &[&str] = &[
    "function_type",
    "linear_function_type",
    "send_session_type",
    "receive_session_type",
    "mu_session_type",
];

struct Ctx<'a, 't>
{
    pbg: &'a Pbg,
    tree: &'a SyntaxTree<'t>,
    src: &'a str,
    skipped: Vec<String>,
    rewritten: usize,
}

impl Ctx<'_, '_>
{
    fn span(
        &self,
        at: NodeIndex,
    ) -> (usize, usize)
    {
        let span = self.tree.node(at).expect("node").span();
        (usize::from(span.start()), usize::from(span.end()))
    }

    fn rule(
        &self,
        at: NodeIndex,
    ) -> Option<&'static str>
    {
        match self.tree.node(at)?.label() {
            NodeLabel::Meld(mold) => self.pbg.rule_of(mold).ok().map(|rule| rule.name),
            _ => None,
        }
    }

    fn tile(
        &self,
        at: NodeIndex,
    ) -> Option<&'static str>
    {
        match self.tree.node(at)?.label() {
            NodeLabel::Tile(mold) => self.pbg.mold(mold).ok().map(|held| held.label),
            _ => None,
        }
    }

    fn significant(
        &self,
        at: NodeIndex,
    ) -> Vec<NodeIndex>
    {
        self.tree
            .children(at)
            .filter(|&child| {
                !matches!(
                    self.tree.node(child).map(|node| node.label()),
                    Some(NodeLabel::Space)
                )
            })
            .collect()
    }

    /// The text of `at` with each send, receive and `mu` below it rewritten.
    fn render(
        &mut self,
        at: NodeIndex,
    ) -> String
    {
        if let Some(new) = self.target(at) {
            return new;
        }
        let (start, end) = self.span(at);
        let mut out = String::new();
        let mut cursor = start;
        let mut children: Vec<NodeIndex> = self.tree.children(at).collect();
        children.sort_by_key(|&child| self.span(child));
        for child in children {
            let (child_start, child_end) = self.span(child);
            let structural = matches!(
                self.tree.node(child).map(|node| node.label()),
                Some(NodeLabel::Meld(_) | NodeLabel::Tile(_))
            );
            if child_start < cursor || child_end > end {
                if !structural && (child_end <= cursor || child_start >= end) {
                    continue;
                }
                panic!(
                    "child {child_start}..{child_end} outside cursor {cursor} under {start}..{end}: {:?} {:?} in {:?}",
                    self.tree.node(child).map(|node| node.label()),
                    self.rule(at),
                    &self.src[start .. end]
                );
            }
            out.push_str(&self.src[cursor .. child_start]);
            out.push_str(&self.render(child));
            cursor = child_end;
        }
        out.push_str(&self.src[cursor .. end]);
        out
    }

    /// The text after the tile `tile` up to the start of `next`: the layout
    /// the source wrote after the old step.
    fn gap(
        &self,
        tile: NodeIndex,
        next: NodeIndex,
    ) -> String
    {
        let (_, tile_end) = self.span(tile);
        let (next_start, _) = self.span(next);
        let gap = &self.src[tile_end .. next_start];
        if gap.is_empty() {
            " ".to_owned()
        }
        else {
            gap.to_owned()
        }
    }

    fn target(
        &mut self,
        at: NodeIndex,
    ) -> Option<String>
    {
        let rule = self.rule(at)?;
        let parts = self.significant(at);
        match rule {
            "send_session_type" | "receive_session_type" => {
                let [lead, payload, step, rest] = parts[..]
                else {
                    self.skip(at, "not four parts");
                    return None;
                };
                let op = match self.tile(lead) {
                    Some("!") => ">!",
                    Some("?") => ">?",
                    other => {
                        self.skip(at, &format!("lead {other:?}"));
                        return None;
                    },
                };
                if !matches!(self.tile(step), Some("." | ">>")) {
                    self.skip(at, "no step tile");
                    return None;
                }
                let mut left = self.render(payload);
                if self
                    .rule(payload)
                    .is_some_and(|inner| ARROW_LEVEL.contains(&inner))
                {
                    left = format!("({left})");
                }
                let gap = self.gap(step, rest);
                let right = self.render(rest);
                self.rewritten += 1;
                Some(format!("{left} {op}{gap}{right}"))
            },
            "mu_session_type" => {
                let [lead, variable, dot, body] = parts[..]
                else {
                    return None;
                };
                if self.tile(lead) != Some("mu") {
                    return None;
                }
                let (variable_start, variable_end) = self.span(variable);
                let name = self.src[variable_start .. variable_end].to_owned();
                let gap = self.gap(dot, body);
                let right = self.render(body);
                self.rewritten += 1;
                Some(format!("rec {name} =>{gap}{right}"))
            },
            _ => None,
        }
    }

    fn skip(
        &mut self,
        at: NodeIndex,
        why: &str,
    )
    {
        let (start, end) = self.span(at);
        let line = self.src[.. start].matches('\n').count() + 1;
        self.skipped
            .push(format!("line {line}: {why}: {}", &self.src[start .. end]));
    }
}

fn main()
{
    let pbg = built_in().expect("the grammar assembles");
    let mut total = 0;
    for path in std::env::args().skip(1) {
        let src = std::fs::read_to_string(&path).expect("read");
        let result = match parse(&pbg, SourceText::from(src.as_str())) {
            Ok(result) => result,
            Err(error) => {
                eprintln!("{path}: no parse: {error:?}");
                continue;
            },
        };
        let tree = result.tree();
        let mut ctx = Ctx {
            pbg: &pbg,
            tree,
            src: &src,
            skipped: Vec::new(),
            rewritten: 0,
        };
        if std::env::var_os("DUMP").is_some() {
            let mut stack = vec![(tree.root(), 0_usize)];
            while let Some((at, depth)) = stack.pop() {
                let (start, end) = ctx.span(at);
                let what = match tree.node(at).map(|node| node.label()) {
                    Some(NodeLabel::Meld(mold)) => format!(
                        "meld {} [{}]",
                        pbg.rule_of(mold).map_or("?", |rule| rule.name),
                        pbg.mold(mold).map_or("?", |held| held.label)
                    ),
                    Some(NodeLabel::Tile(mold)) => format!(
                        "tile {} [{}]",
                        pbg.mold(mold).map_or("?", |held| held.label),
                        pbg.rule_of(mold).map_or("?", |rule| rule.name)
                    ),
                    Some(NodeLabel::Space) => continue,
                    other => format!("{other:?}"),
                };
                println!(
                    "{:indent$}{what} {:?}",
                    "",
                    &src[start .. end],
                    indent = depth * 2
                );
                let mut children: Vec<NodeIndex> = tree.children(at).collect();
                children.reverse();
                stack.extend(children.into_iter().map(|child| (child, depth + 1)));
            }
            continue;
        }
        let (root_start, root_end) = ctx.span(tree.root());
        let out = format!(
            "{}{}{}",
            &src[.. root_start],
            ctx.render(tree.root()),
            &src[root_end ..]
        );
        for skipped in &ctx.skipped {
            eprintln!("{path}: skipped {skipped}");
        }
        if ctx.rewritten > 0 {
            if std::env::var_os("WRITE").is_some() {
                std::fs::write(&path, &out).expect("write");
            }
            println!("{path}: {} forms", ctx.rewritten);
            total += ctx.rewritten;
        }
    }
    println!("total: {total} forms");
}
