//! The mold highlighter over the built-in surface and the language corpus:
//! every mold's role, the role goldens, the span partition, layout, and the
//! highlighter's refusals.

use alloc::collections::BTreeSet;
use core::error::Error;
use core::fmt::Display;
use core::fmt::Error as FmtError;
use core::fmt::Formatter;
use core::fmt::Result as FmtResult;
use core::fmt::Write as _;
use std::ffi::OsStr;
use std::path::Path;
use std::path::PathBuf;

use anodized::spec;
use expect_test::expect_file;
use gandr_surface_grammar::HighlightError;
use gandr_surface_grammar::Pbg;
use gandr_surface_grammar::RCtxStep;
use gandr_surface_grammar::Regex;
use gandr_surface_grammar::RoleTable;
use gandr_surface_grammar::Rule;
use gandr_surface_grammar::RuleName;
use gandr_surface_grammar::Sort;
use gandr_surface_grammar::StepSym;
use gandr_surface_grammar::TileLabel;
use gandr_surface_grammar::built_in;
use gandr_surface_parser::parse;
use gandr_surface_render_remote::ByteRange;
use gandr_surface_render_remote::HlRole;
use gandr_surface_render_remote::HlSpan;
use gandr_surface_syntax::ByteOffset;
use gandr_surface_syntax::ByteSpan;
use gandr_surface_syntax::MoldId;
use gandr_surface_syntax::Node;
use gandr_surface_syntax::NodeLabel;
use gandr_surface_syntax::SourceText;
use gandr_surface_syntax::SyntaxTree;
use gandr_surface_syntax::TreeBuilder;
use gandr_theory_graphs::Assoc;
use gandr_theory_graphs::Dir;
use gandr_theory_graphs::PrecDag;
use gandr_theory_graphs::PrecSpec;

/// The language's source corpus, which the corpus crate owns: the strict
/// root, the fixture root and its pending set.
///
/// # Specification
/// trivial.
fn corpus_root() -> PathBuf
{
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../surface-corpus")
}

/// The directory the role goldens live in, mirroring the corpus tree.
///
/// # Specification
/// trivial.
fn golden_root() -> PathBuf
{
    Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/highlight")
}

/// Every file under `dir` with extension `extension`, sorted.
///
/// # Specification
/// - ensures: a walk of `dir` and its subdirectories, unreadable entries
///   skipped, the paths sorted so a run is deterministic.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: For the checked-in corpus and golden trees, L3 path-correlated
///   role observations catch wrong extension selection and unstable ordering.
///   The predicate observes lexical containment, extensions and ordering
///   without another filesystem walk; unreadable directories, concurrent
///   mutations and symlink cycles are outside the witnesses.
/// - witness: `tests::highlight::corpus_roles_match_the_golden`
#[spec(ensures: |ret| ret.is_sorted() && ret.iter().all(|path| path.starts_with(dir) && path.extension() == Some(extension)))]
fn files_under(
    dir: &Path,
    extension: &OsStr,
) -> Vec<PathBuf>
{
    let mut out = Vec::new();
    let mut pending = vec![dir.to_path_buf()];
    while let Some(next_dir) = pending.pop() {
        if let Ok(entries) = std::fs::read_dir(next_dir) {
            for entry in entries.flatten() {
                let path = entry.path();
                if path.is_dir() {
                    pending.push(path);
                }
                else if path.extension() == Some(extension) {
                    out.push(path);
                }
            }
        }
    }
    out.sort();
    out
}

/// Every source of both corpus roots, strict before fixture and sorted within
/// each root, including the pending set.
///
/// # Specification
/// - requires: nothing.
/// - ensures: strict sources then fixture sources, each in lexical path order.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: For the checked-in corpus, L3 per-source goldens observe both
///   root families and catch omitted or misclassified sources. The predicate
///   checks the root order and each root's lexical order; filesystem
///   completeness under read errors or concurrent changes is not established.
/// - witness: `tests::highlight::corpus_roles_match_the_golden`
#[spec(ensures: |ret| { let root = Path::new(concat!(env!("CARGO_MANIFEST_DIR"), "/../surface-corpus")); let is_fixture = |path: &Path| { let relative = path.strip_prefix(root).ok()?; let component = relative.components().next()?; let name = component.as_os_str(); if name == OsStr::new("strict") { Some(false) } else if name == OsStr::new("fixture") { Some(true) } else { None } }; ret.iter().all(|path| is_fixture(path).is_some() && path.extension() == Some(OsStr::new("gandr"))) && ret.is_sorted_by(|left, right| (is_fixture(left), left) <= (is_fixture(right), right)) })]
fn corpus_sources() -> Vec<PathBuf>
{
    let root = corpus_root();
    let mut sources = files_under(&root.join("strict"), OsStr::new("gandr"));
    sources.extend(files_under(&root.join("fixture"), OsStr::new("gandr")));
    sources
}

/// A grammar of one item rule whose form is the single tile `x`: one mold,
/// and a fingerprint other than the built-in surface's.
///
/// # Specification
/// - ensures: returns the grammar.
/// - fails: a gate refuses the form, which a single tile never meets.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: For the grammar-mismatch fixture, L2 typed refusal observes a
///   distinct one-tile grammar rather than another copy of the built-in
///   surface. The predicate checks its rule and mold inventory; resource
///   failures are outside the witness.
/// - witness: `tests::highlight::a_tree_under_another_grammar_is_refused`
#[spec(ensures: |ret| ret.as_ref().is_ok_and(|pbg| pbg.rules().len() == 1 && pbg.rules().first().is_some_and(|rule| rule.name().0 == "only" && rule.sort() == Sort::Item) && pbg.iter_molds().map(|(_, def)| def.label).eq(["x"])))]
fn one_tile_grammar() -> Result<Pbg, Box<dyn Error>>
{
    let mut spec = PrecSpec::new();
    let atom = spec.insert("atom", Assoc::Non)?;
    let dag = PrecDag::build(&spec)?;
    Ok(Pbg::build(dag, vec![Rule::new(
        RuleName("only"),
        Sort::Item,
        atom,
        Regex::tile(TileLabel("x")),
    )])?)
}

/// The text of one span of `source`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the exact UTF-8 slice, or empty text for an invalid range.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: For parser-produced corpus spans, L3 quoted text and L2
///   span-partition observations catch wrong endpoints or slices. The predicate
///   also observes the invalid-range fallback; invalid ranges are not exhausted
///   by the corpus.
/// - witness: `tests::highlight::corpus_roles_match_the_golden`
/// - witness: `tests::highlight::spans_partition_the_tile_bytes`
#[spec(ensures: |ret| <&str>::from(ret) == <&str>::from(source).get(usize::from(range.start())..usize::from(range.end())).unwrap_or_default())]
fn text_of(
    source: SourceText<'_>,
    range: ByteRange,
) -> SourceText<'_>
{
    let text = <&str>::from(source);
    SourceText::from(
        text.get(usize::from(range.start()) .. usize::from(range.end()))
            .unwrap_or_default(),
    )
}

/// A role, written by its variant's name.
#[repr(transparent)]
struct RoleName(HlRole);

impl Display for RoleName
{
    /// Writes the variant's name.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: writes the role variant's name.
    /// - fails: the formatter refuses a write.
    /// - panics: none.
    /// - executable: none — Formatter exposes neither written text nor sink
    ///   capacity, so successful emission and refusal have no predicate
    ///   observer.
    ///
    /// # Adequacy
    /// - hypothesis: For roles reached by the built-in inventory, L3 role
    ///   goldens catch changed names and wrong variant selection. Other role
    ///   variants and formatter refusal are not exhausted.
    /// - witness: `tests::highlight::corpus_roles_match_the_golden`
    fn fmt(
        &self,
        f: &mut Formatter<'_>,
    ) -> FmtResult
    {
        f.write_str(match self.0 {
            | HlRole::Keyword => "Keyword",
            | HlRole::Operator => "Operator",
            | HlRole::FunctionDef => "FunctionDef",
            | HlRole::FunctionCall => "FunctionCall",
            | HlRole::VariableDef => "VariableDef",
            | HlRole::VariableParam => "VariableParam",
            | HlRole::Member => "Member",
            | HlRole::Variable => "Variable",
            | HlRole::Constructor => "Constructor",
            | HlRole::Type => "Type",
            | HlRole::TypeBuiltin => "TypeBuiltin",
            | HlRole::TypeVariable => "TypeVariable",
            | HlRole::Number => "Number",
            | HlRole::Boolean => "Boolean",
            | HlRole::Character => "Character",
            | HlRole::StringLit => "StringLit",
            | HlRole::Escape => "Escape",
            | HlRole::Comment => "Comment",
            | HlRole::Hole => "Hole",
            | HlRole::Label => "Label",
            | HlRole::Path => "Path",
            | HlRole::Directive => "Directive",
            | HlRole::Other => "Other",
        })
    }
}

/// One golden line per span: its byte range, its role and its text, quoted
/// and escaped.
///
/// # Specification
/// - ensures: `start..end Role "text"` per span, in the order given.
/// - fails: never; writing into a string does not fail.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: For corpus spans, L3 complete line goldens catch wrong ranges,
///   roles, escaping and order. The predicate observes one ordered range per
///   line and successful string formatting; arbitrary span sequences and
///   control-character combinations are not exhausted.
/// - witness: `tests::highlight::corpus_roles_match_the_golden`
#[spec(ensures: |ret| ret.as_ref().is_ok_and(|rendered| { let mut lines = rendered.lines(); spans.iter().all(|span| lines.next().is_some_and(|line| line.split_once(' ').and_then(|(range, _)| range.split_once("..")).is_some_and(|(start, end)| start.parse::<usize>().ok() == Some(usize::from(span.range.start())) && end.parse::<usize>().ok() == Some(usize::from(span.range.end()))) && line.ends_with('"'))) && lines.next().is_none() }))]
fn role_lines(
    tree: &SyntaxTree<'_>,
    spans: &[HlSpan],
) -> Result<String, FmtError>
{
    let mut out = String::new();
    for span in spans {
        let text = <&str>::from(text_of(tree.source(), span.range));
        writeln!(
            out,
            "{}..{} {} \"{}\"",
            usize::from(span.range.start()),
            usize::from(span.range.end()),
            RoleName(span.role),
            text.escape_debug()
        )?;
    }
    Ok(out)
}

/// The symbols one side of a context can step across, deduplicated, tiles
/// by label and holes by sort.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the sorted, deduplicated textual symbols joined by spaces.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: For built-in contexts, L3 unexercised-mold goldens catch
///   missing, duplicated or reordered symbols. The predicate observes each
///   input's text and the exact empty-output boundary; arbitrary labels
///   containing whitespace are not exhausted.
/// - witness: `tests::highlight::corpus_roles_match_the_golden`
#[spec(ensures: |ret| ret.is_empty() == steps.iter().all(|step| matches!(step.crossed, StepSym::Tile(""))) && steps.iter().all(|step| match step.crossed { StepSym::Tile(label) => ret.contains(label), StepSym::Sort(sort) => ret.contains(sort.name().0) }))]
fn side_of(steps: &[RCtxStep]) -> String
{
    let crossed: BTreeSet<String> = steps
        .iter()
        .map(|step| match step.crossed {
            | StepSym::Tile(label) => label.to_owned(),
            | StepSym::Sort(sort) => format!("<{}>", sort.name().0),
        })
        .collect();
    crossed.into_iter().collect::<Vec<_>>().join(" ")
}

/// One golden line per mold no corpus tile exercises: its id, role, rule's
/// named kind, label, and the symbols beside it.
///
/// # Specification
/// - ensures: one line per mold of `pbg` absent from `exercised`, in id order.
/// - fails: a lookup the grammar refuses, which a built grammar never does.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: For the built-in inventory and corpus coverage set, L3
///   complete goldens catch wrong omissions, roles, context text and order. The
///   predicate observes concrete error families, ordered omitted ids and the
///   all-covered empty case; arbitrary metadata containing line breaks is not
///   exhausted.
/// - witness: `tests::highlight::corpus_roles_match_the_golden`
#[spec(ensures: |ret| ret.as_ref().map_or_else(|error| error.downcast_ref::<HighlightError>().is_some() || error.downcast_ref::<gandr_surface_grammar::PbgError>().is_some() || error.downcast_ref::<FmtError>().is_some(), |rendered| { let mut expected = pbg.iter_molds().filter(|&(id, _)| !exercised.contains(&id)).peekable(); let empty = expected.peek().is_none(); let mut lines = rendered.lines(); rendered.is_empty() == empty && expected.all(|(id, _)| lines.by_ref().any(|line| line.split_once(' ').is_some_and(|(prefix, _)| prefix.parse::<u32>().ok() == Some(u32::from(id))))) }))]
fn unexercised_lines(
    pbg: &Pbg,
    table: &RoleTable,
    exercised: &BTreeSet<MoldId>,
) -> Result<String, Box<dyn Error>>
{
    let mut out = String::new();
    for (id, def) in pbg.iter_molds() {
        if exercised.contains(&id) {
            continue;
        }
        let role = RoleName(table.role_of(id)?);
        let kind = pbg.named_kind(id)?;
        let left = pbg.step(def.rctx, Dir::Left)?;
        let right = pbg.step(def.rctx, Dir::Right)?;
        writeln!(
            out,
            "{} {role} {} {} L[{}] R[{}]",
            u32::from(id),
            kind.0,
            def.label,
            side_of(left),
            side_of(right)
        )?;
    }
    Ok(out)
}

/// Every mold of the built-in surface has a role: `role_of` answers every id
/// of the inventory, so no mold falls outside the classification, and two
/// tables built from one grammar agree mold for mold.
#[test]
fn every_mold_has_a_role() -> Result<(), Box<dyn Error>>
{
    let pbg = built_in()?;
    let table = RoleTable::build(&pbg)?;
    let roles = pbg
        .iter_molds()
        .map(|(id, _def)| table.role_of(id))
        .collect::<Result<Vec<HlRole>, _>>()?;
    assert_eq!(pbg.mold_count().0, roles.len(), "one role per mold");
    assert_eq!(
        RoleTable::build(&pbg)?,
        table,
        "the roles are a function of the grammar"
    );
    Ok(())
}

/// The role golden. Each corpus source, both roots and the pending set, has
/// a golden of its spans under `tests/highlight/` at its path in the corpus;
/// the molds no corpus tile exercises are named in `unexercised.roles` with
/// their role and context, so every mold's role stands in some golden line.
/// A golden whose source is gone fails the suite. `UPDATE_EXPECT=1`
/// rewrites the goldens and deletes those whose source is gone, so a source
/// added, moved between roots or removed is one rerun.
#[test]
fn corpus_roles_match_the_golden() -> Result<(), Box<dyn Error>>
{
    let pbg = built_in()?;
    let table = RoleTable::build(&pbg)?;
    let corpus = corpus_root();
    let goldens = golden_root();
    let update = std::env::var_os("UPDATE_EXPECT").is_some();
    let mut exercised: BTreeSet<MoldId> = BTreeSet::new();
    let mut expected: BTreeSet<PathBuf> = BTreeSet::new();
    for path in corpus_sources() {
        let source = std::fs::read_to_string(&path)?;
        let parsed = parse(&pbg, SourceText::from(source.as_str()))?;
        let tree = parsed.tree();
        exercised.extend(
            tree.positions()
                .filter_map(|position| tree.node(position).map(Node::label))
                .filter_map(|label| match label {
                    | NodeLabel::Tile(mold) => Some(mold),
                    | _ => None,
                }),
        );
        let spans = table.highlight(tree)?;
        let golden = goldens
            .join(path.strip_prefix(&corpus)?)
            .with_extension("roles");
        if update && let Some(parent) = golden.parent() {
            std::fs::create_dir_all(parent)?;
        }
        expect_file![golden.clone()].assert_eq(&role_lines(tree, &spans)?);
        expected.insert(golden);
    }

    let unexercised = goldens.join("unexercised.roles");
    expect_file![unexercised.clone()].assert_eq(&unexercised_lines(&pbg, &table, &exercised)?);
    expected.insert(unexercised);

    let orphans: Vec<PathBuf> = files_under(&goldens, OsStr::new("roles"))
        .into_iter()
        .filter(|golden| !expected.contains(golden))
        .collect();
    if update {
        for orphan in &orphans {
            std::fs::remove_file(orphan)?;
        }
        return Ok(());
    }
    assert!(
        orphans.is_empty(),
        "goldens with no corpus source, to delete or rewrite with `UPDATE_EXPECT=1`: {orphans:?}"
    );
    Ok(())
}

/// Over every corpus source the spans are exactly the tree's tiles and its
/// comments, in source order: sorted, pairwise disjoint, each span's range a
/// tile's or a comment's, a comment or shebang role exactly on layout, and
/// every byte outside every span whitespace.
#[test]
fn spans_partition_the_tile_bytes() -> Result<(), Box<dyn Error>>
{
    let pbg = built_in()?;
    let table = RoleTable::build(&pbg)?;
    for path in corpus_sources() {
        let source = std::fs::read_to_string(&path)?;
        let parsed = parse(&pbg, SourceText::from(source.as_str()))?;
        let tree = parsed.tree();
        let spans = table.highlight(tree)?;
        let shown = path.display();
        let blank = |from: usize, to: usize| {
            source
                .get(from .. to)
                .is_some_and(|gap| gap.chars().all(char::is_whitespace))
        };

        let mut tiles: Vec<(usize, usize)> = Vec::new();
        let mut layout: BTreeSet<(usize, usize)> = BTreeSet::new();
        for position in tree.positions() {
            let Some(node) = tree.node(position)
            else {
                continue;
            };
            let bytes = (
                usize::from(node.span().start()),
                usize::from(node.span().end()),
            );
            match node.label() {
                | NodeLabel::Tile(_) => tiles.push(bytes),
                | NodeLabel::Space if !blank(bytes.0, bytes.1) => {
                    tiles.push(bytes);
                    layout.insert(bytes);
                },
                | _ => {},
            }
        }
        tiles.sort_unstable();
        let ranges: Vec<(usize, usize)> = spans
            .iter()
            .map(|span| {
                (
                    usize::from(span.range.start()),
                    usize::from(span.range.end()),
                )
            })
            .collect();
        assert_eq!(
            tiles, ranges,
            "{shown}: one span per tile and per comment, in order"
        );
        assert!(
            ranges
                .iter()
                .zip(ranges.iter().skip(1))
                .all(|(earlier, later)| earlier.1 <= later.0),
            "{shown}: the spans are disjoint"
        );
        for span in &spans {
            let bytes = (
                usize::from(span.range.start()),
                usize::from(span.range.end()),
            );
            assert_eq!(
                layout.contains(&bytes),
                matches!(span.role, HlRole::Comment | HlRole::Directive),
                "{shown}: {}..{} takes a layout role exactly when it is layout",
                bytes.0,
                bytes.1
            );
        }
        let mut cursor = 0_usize;
        for &(start, end) in &ranges {
            assert!(
                blank(cursor, start),
                "{shown}: bytes {cursor}..{start} outside every span are whitespace"
            );
            cursor = end;
        }
        assert!(
            blank(cursor, source.len()),
            "{shown}: the bytes after the last span are whitespace"
        );
    }
    Ok(())
}

/// A shebang is a directive, a line comment and a nested block comment are
/// comments, and whitespace — between them and between tiles — takes no
/// span; the first tile after the layout keeps its own role.
#[test]
fn layout_takes_a_role_only_as_a_comment_or_a_shebang() -> Result<(), Box<dyn Error>>
{
    let pbg = built_in()?;
    let table = RoleTable::build(&pbg)?;
    let source = SourceText::from(
        "#!/usr/bin/env gandr\n// a note\n  /* outer /* inner */ */\n\ndef x = 1;\n",
    );
    let parsed = parse(&pbg, source)?;
    let spans = table.highlight(parsed.tree())?;
    let read: Vec<(&str, HlRole)> = spans
        .iter()
        .map(|span| (<&str>::from(text_of(source, span.range)), span.role))
        .collect();
    assert_eq!(
        Some(
            &[
                ("#!/usr/bin/env gandr", HlRole::Directive),
                ("// a note", HlRole::Comment),
                ("/* outer /* inner */ */", HlRole::Comment),
                ("def", HlRole::Keyword),
            ][..]
        ),
        read.get(.. 4),
        "the layout spans, then the first tile"
    );
    assert!(
        read.iter().all(|&(text, _role)| !text.trim().is_empty()),
        "no span is whitespace: {read:?}"
    );
    Ok(())
}

/// A tree molded under another grammar is refused with both fingerprints,
/// never read through a table whose mold ids mean other tiles.
#[test]
fn a_tree_under_another_grammar_is_refused() -> Result<(), Box<dyn Error>>
{
    let pbg = built_in()?;
    let other = one_tile_grammar()?;
    assert_ne!(pbg.fingerprint(), other.fingerprint(), "two grammars");
    let table = RoleTable::build(&other)?;
    let parsed = parse(&pbg, SourceText::from("def x = 1;"))?;
    assert_eq!(
        Err(HighlightError::GrammarMismatch {
            tree: pbg.fingerprint(),
            table: other.fingerprint(),
        }),
        table.highlight(parsed.tree())
    );
    Ok(())
}

/// Under the table's own grammar, a tile naming the table's last mold
/// answers with its role, and a tile naming the first id past the table is
/// refused with that id.
#[test]
fn a_tile_past_the_table_is_refused() -> Result<(), Box<dyn Error>>
{
    let grammar = one_tile_grammar()?;
    let table = RoleTable::build(&grammar)?;
    let count = u32::try_from(grammar.mold_count().0)?;
    let last = MoldId::from(count.checked_sub(1).ok_or("the grammar has a mold")?);
    let past = MoldId::from(count);
    let source = SourceText::from("x");
    let span = ByteSpan::new(ByteOffset::from(0_usize), ByteOffset::from(1_usize))?;
    let tree_of = |mold: MoldId| -> Result<SyntaxTree<'_>, Box<dyn Error>> {
        let mut builder = TreeBuilder::new(source, grammar.fingerprint())?;
        let tile = builder.node(NodeLabel::Tile(mold), span, &[])?;
        let root = builder.node(NodeLabel::Wald, span, &[tile])?;
        Ok(builder.finish(root)?)
    };

    let range = ByteRange::new(
        gandr_surface_render_remote::ByteOffset::from(0_usize),
        gandr_surface_render_remote::ByteOffset::from(1_usize),
    )?;
    assert_eq!(
        Ok(vec![HlSpan {
            range,
            role: HlRole::Other,
        }]),
        table.highlight(&tree_of(last)?),
        "the last mold answers"
    );
    assert_eq!(
        Err(HighlightError::UnknownMold { id: past }),
        table.highlight(&tree_of(past)?),
        "the first id past the table is refused"
    );
    Ok(())
}

#[test]
fn highlight_preserves_overlapping_tile_spans() -> Result<(), Box<dyn Error>>
{
    let grammar = built_in()?;
    let table = RoleTable::build(&grammar)?;
    let &mold = grammar
        .candidates(TileLabel("number"))
        .first()
        .expect("number mold");
    let outer = ByteSpan::new(ByteOffset::from(0_usize), ByteOffset::from(2_usize))?;
    let inner = ByteSpan::new(ByteOffset::from(1_usize), ByteOffset::from(2_usize))?;
    let mut builder = TreeBuilder::new(SourceText::from("12"), grammar.fingerprint())?;
    let first = builder.node(NodeLabel::Tile(mold), inner, &[])?;
    let second = builder.node(NodeLabel::Tile(mold), outer, &[])?;
    let third = builder.node(NodeLabel::Tile(mold), inner, &[])?;
    let root = builder.node(NodeLabel::Wald, outer, &[first, second, third])?;
    let tree = builder.finish(root)?;
    let outer_range = ByteRange::new(
        gandr_surface_render_remote::ByteOffset::from(0_usize),
        gandr_surface_render_remote::ByteOffset::from(2_usize),
    )?;
    let inner_range = ByteRange::new(
        gandr_surface_render_remote::ByteOffset::from(1_usize),
        gandr_surface_render_remote::ByteOffset::from(2_usize),
    )?;
    assert_eq!(
        Ok(vec![
            HlSpan {
                range: outer_range,
                role: HlRole::Number
            },
            HlSpan {
                range: inner_range,
                role: HlRole::Number
            },
            HlSpan {
                range: inner_range,
                role: HlRole::Number
            },
        ]),
        table.highlight(&tree)
    );
    Ok(())
}
