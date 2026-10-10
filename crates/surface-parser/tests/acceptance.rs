//! Acceptance: the parser meeting real gandr text.
//!
//! These exercise the whole front end (`label → mold → push → commit`) against
//! the language's corpus sources, the recovery fixtures, and curated malformed
//! programs.

use core::error::Error;
use core::fmt;
use std::path::Path;
use std::path::PathBuf;

use anodized::spec;
use gandr_surface_grammar::Pbg;
use gandr_surface_parser::Expected;
use gandr_surface_parser::Lexeme;
use gandr_surface_parser::MeldState;
use gandr_surface_parser::Molder;
use gandr_surface_parser::Oblig;
use gandr_surface_parser::SpaceText;
use gandr_surface_parser::TileText;
use gandr_surface_parser::label;
use gandr_surface_parser::parse;
use gandr_surface_syntax::ByteOffset;
use gandr_surface_syntax::MoldId;
use gandr_surface_syntax::NodeIndex;
use gandr_surface_syntax::NodeLabel;
use gandr_surface_syntax::SourceFragment;
use gandr_surface_syntax::SourceText;
use gandr_surface_syntax::SyntaxTree;

use crate::common::built;
use crate::common::children;
use crate::common::corpus_root;
use crate::common::gandr_files;
use crate::common::label_of;
use crate::common::root_digest;
use crate::common::significant_children;
use crate::common::span;
use crate::common::text;

/// Number of labeled tokens to push from a source prefix.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
struct TokenPrefixLen(usize);

impl TokenPrefixLen
{
    /// Push every labeled token.
    const MAX: Self = Self(usize::MAX);
}

impl From<usize> for TokenPrefixLen
{
    /// Adopt a prefix length.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(count: usize) -> Self
    {
        Self(count)
    }
}

impl From<TokenPrefixLen> for usize
{
    /// Read the prefix length back.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(count: TokenPrefixLen) -> Self
    {
        count.0
    }
}

/// File-read failure with path context retained for corpus and fixture reads.
#[derive(Debug)]
struct ReadSourceError
{
    /// The file that failed to read.
    path: PathBuf,
    /// The underlying failure.
    source: std::io::Error,
}

impl fmt::Display for ReadSourceError
{
    /// # Specification
    /// - ensures: writes the failed path and underlying IO failure.
    /// - fails: propagates a formatter refusal.
    /// - executable: none — `Formatter` exposes neither its sink nor written
    ///   bytes for a postcondition; both observations require an external sink.
    ///
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a real directory-read error retains path and cause in
    ///   its display; a refusing `fmt::Write` sink must return `fmt::Error`.
    ///   Exact incidental wording is not pinned.
    /// - witness: `tests::acceptance::source_inventory_and_reads_preserve_context`
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        write!(f, "failed to read {}: {}", self.path.display(), self.source)
    }
}

impl Error for ReadSourceError
{
    /// # Specification
    /// trivial.
    fn source(&self) -> Option<&(dyn Error + 'static)>
    {
        Some(&self.source)
    }
}

#[test]
fn tree_readers_preserve_preorder_and_missing_nodes() -> Result<(), Box<dyn Error>>
{
    let pbg = built();
    let source = "def a = (x); def x = 0;";
    let result = parse(pbg, SourceText::from(source))?;
    assert!(bool::from(result.is_clean()));
    let tree = result.tree();
    let root = tree.root();
    assert_eq!(descendant_tiles(tree, root), [
        "def", "a", "=", "(", "x", ")", ";", "def", "x", "=", "0", ";"
    ]);
    let group = find_meld_with_tile(tree, root, TileText::from("x"))
        .expect("the nested group precedes the later binder");
    assert_eq!(direct_tiles(tree, group), ["(", "x", ")"]);
    let first_x = tree
        .positions()
        .find(|&at| {
            matches!(label_of(tree, at), Some(NodeLabel::Tile(_)))
                && span(tree, at).is_some_and(|span| {
                    usize::from(span.start()) == source.find('x').expect("first x")
                })
        })
        .expect("the first source x has a tile");
    let Some(NodeLabel::Tile(first_mold)) = label_of(tree, first_x)
    else {
        panic!("the selected node is a tile");
    };
    assert_eq!(mold_of(tree, root, TileText::from("x")), Some(first_mold));
    assert_eq!(
        mold_label_of(pbg, tree, root, TileText::from("x")).as_deref(),
        Some("identifier")
    );
    assert_eq!(
        mold_sort_of(pbg, tree, root, TileText::from("x")),
        Some(gandr_surface_grammar::Sort::Expression)
    );
    assert_eq!(descendant_tiles(tree, first_x), ["x"]);
    assert!(descendant_grout_ends(tree, root).is_empty());
    let top = significant_children(tree, root);
    assert_eq!(top.len(), 2);
    assert_eq!(direct_tiles(tree, top[0]), ["def", "a", "=", ";"]);
    assert_eq!(direct_tiles(tree, top[1]), ["def", "x", "=", "0", ";"]);
    let absent = NodeIndex::from(usize::MAX);
    for start in [root, absent] {
        assert_eq!(
            find_meld_with_tile(tree, start, TileText::from("absent")),
            None
        );
        assert_eq!(mold_of(tree, start, TileText::from("absent")), None);
        assert_eq!(
            mold_label_of(pbg, tree, start, TileText::from("absent")),
            None
        );
        assert_eq!(
            mold_sort_of(pbg, tree, start, TileText::from("absent")),
            None
        );
    }
    assert!(children(tree, absent).is_empty());
    assert!(significant_children(tree, absent).is_empty());
    assert!(direct_tiles(tree, absent).is_empty());
    assert!(descendant_tiles(tree, absent).is_empty());
    assert!(descendant_grout_ends(tree, absent).is_empty());
    assert_eq!(text(tree, absent), "");
    let unicode = parse(pbg, SourceText::from("\"é\""))?;
    assert_eq!(text(unicode.tree(), unicode.tree().root()), "\"é\"");
    Ok(())
}

#[test]
fn source_inventory_and_reads_preserve_context() -> Result<(), Box<dyn Error>>
{
    struct RefusingSink;
    impl fmt::Write for RefusingSink
    {
        /// # Specification
        /// trivial.
        fn write_str(
            &mut self,
            _text: &str,
        ) -> fmt::Result
        {
            Err(fmt::Error)
        }
    }
    let root = corpus_root();
    let paths = gandr_files(&root);
    assert!(paths.contains(&root.join("strict/values.gandr")));
    assert!(paths.contains(&root.join("fixture/surface/typed-holes.gandr")));
    assert!(
        paths
            .iter()
            .all(|path| path.starts_with(&root)
                && path.extension().is_some_and(|ext| ext == "gandr"))
    );
    assert!(
        paths
            .windows(2)
            .all(|pair| matches!(pair, [left, right] if left <= right))
    );
    assert!(gandr_files(&root.join("strict/values.gandr/child")).is_empty());
    assert_eq!(
        read_source(&root.join("strict/values.gandr"))?,
        include_str!("../../surface-corpus/strict/values.gandr")
    );
    let error = read_source(&root).expect_err("directories are not UTF-8 source files");
    assert_eq!(error.path, root);
    assert!(
        error
            .source()
            .and_then(|cause| cause.downcast_ref::<std::io::Error>())
            .is_some_and(|cause| core::ptr::eq(&raw const error.source, &raw const *cause))
    );
    let rendered = error.to_string();
    assert!(rendered.contains(&root.display().to_string()));
    assert!(rendered.contains(&error.source.to_string()));

    assert_eq!(
        fmt::write(&mut RefusingSink, format_args!("{error}")),
        Err(fmt::Error)
    );
    Ok(())
}

#[test]
fn core_forms_are_clean() -> Result<(), Box<dyn Error>>
{
    // The molder molds the core self-contained gandr forms with ZERO
    // obligations — value/function definitions, control, data literals,
    // operators, and strings (over the forms the greedy
    // molder resolves).
    let pbg = built();
    let clean: &[&str] = &[
        "def greeting = \"the value zone\";",
        "ret greeting",
        "def answer = 42;",
        "1 + 2 * 3",
        "- x",
        "ret -y",
        "def id = x;",
        "def nested = comp(id(a), f);",
    ];
    for &src in clean {
        let result = parse(pbg, SourceText::from(src))?;
        assert!(
            bool::from(result.is_clean()),
            "core form {src:?} molds clean; obligations: {:?}",
            result
                .obligations()
                .iter()
                .map(|o| o.class)
                .collect::<Vec<_>>()
        );
    }

    Ok(())
}

/// A declaration-local `@[...]` prefix is typed syntax, not an attribute.
///
/// The binder types stay in source order even when the first binder refers to
/// the later explicit `xs` parameter. That dependency is intentionally left
/// for lowering; the parse contract is the lossless ordered surface form.
#[test]
fn declaration_prefix_telescope_preserves_forward_reference_order() -> Result<(), Box<dyn Error>>
{
    let source = r#"def nth @[A : Type, i : Fin(length(xs))] (xs : List(A)) -> A {
  ret xs
}
"#;
    let result = parse(built(), SourceText::from(source))?;
    assert!(
        bool::from(result.is_clean()),
        "the typed declaration prefix molds cleanly: {:?}",
        result.obligations()
    );
    let item = find_meld_with_tile(result.tree(), result.tree().root(), TileText::from("nth"))
        .expect("the declaration remains one top-level meld");
    assert_eq!(source.trim_end(), text(result.tree(), item));

    let tiles = descendant_tiles(result.tree(), item);
    let first_a = tiles
        .iter()
        .position(|tile| tile == "A")
        .expect("the first implicit binder name is preserved");
    let implicit_i = tiles
        .iter()
        .position(|tile| tile == "i")
        .expect("the second implicit binder name is preserved");
    let xs_positions: Vec<usize> = tiles
        .iter()
        .enumerate()
        .filter_map(|(index, tile)| (tile == "xs").then_some(index))
        .collect();
    assert!(
        xs_positions.len() >= 2,
        "the forward reference and explicit binder both survive: {tiles:?}"
    );
    assert!(
        first_a < implicit_i && implicit_i < xs_positions[0] && xs_positions[0] < xs_positions[1],
        "prefix binders and the forward reference retain source order: {tiles:?}"
    );
    Ok(())
}

/// Empty typed prefixes and ordinary declaration attributes remain distinct.
#[test]
fn empty_prefix_does_not_change_ordinary_attribute_spelling() -> Result<(), Box<dyn Error>>
{
    let source = r#"@[doc("d")]
def tagged @[] (x : Type) -> Type { ret x }
"#;
    let result = parse(built(), SourceText::from(source))?;
    assert!(
        bool::from(result.is_clean()),
        "ordinary attributes plus an empty typed prefix mold cleanly: {:?}",
        result.obligations()
    );
    let item = find_meld_with_tile(
        result.tree(),
        result.tree().root(),
        TileText::from("tagged"),
    )
    .expect("the attributed declaration remains one top-level meld");
    let tiles = descendant_tiles(result.tree(), item);
    assert_eq!(
        2,
        tiles.iter().filter(|tile| tile.as_str() == "@[").count(),
        "one ordinary attribute and one empty typed prefix remain visible: {tiles:?}"
    );
    assert!(
        tiles.iter().any(|tile| tile == "doc"),
        "the ordinary attribute name remains visible: {tiles:?}"
    );
    assert!(
        tiles.iter().any(|tile| tile == "tagged"),
        "the declaration name remains visible: {tiles:?}"
    );
    Ok(())
}

/// A malformed prefix reports recovery without absorbing the next definition.
#[test]
fn malformed_prefix_recovers_at_the_next_declaration() -> Result<(), Box<dyn Error>>
{
    let source = r#"def bad @[A : Type, broken] (x : Type) -> Type { ret x }
def good @[B : Type] (y : Type) -> Type { ret y }
"#;
    let result = parse(built(), SourceText::from(source))?;
    assert!(
        !bool::from(result.is_clean()),
        "the malformed prefix retains a recovery obligation"
    );
    let good = find_meld_with_tile(result.tree(), result.tree().root(), TileText::from("good"))
        .expect("the later valid definition survives prefix recovery");
    assert_eq!(
        "def good @[B : Type] (y : Type) -> Type { ret y }",
        text(result.tree(), good),
        "the surviving declaration is not absorbed by the malformed prefix"
    );
    Ok(())
}

#[test]
fn command_substitution_molds_with_zero_obligations() -> Result<(), Box<dyn Error>>
{
    let source = "#!{ echo $!{ printf nested; }; }";
    let result = parse(built(), SourceText::from(source))?;
    assert!(
        bool::from(result.is_clean()),
        "the command-substitution form must reach lowering without parser repair: {:?}",
        result.obligations()
    );
    Ok(())
}

#[test]
fn value_statement_uses_val_keyword() -> Result<(), Box<dyn Error>>
{
    let pbg = built();
    let renamed = [
        "val value = expression;",
        "def use() -> -F Integer { val value = expression; ret value }",
    ];
    for src in renamed {
        let result = parse(pbg, SourceText::from(src))?;
        assert!(
            bool::from(result.is_clean()),
            "`val PAT = E;` molds clean in {src:?}; obligations: {:?}",
            result
                .obligations()
                .iter()
                .map(|obligation| obligation.class)
                .collect::<Vec<_>>()
        );
    }

    let retired = parse(pbg, SourceText::from("let value = expression;"))?;
    assert!(
        !bool::from(retired.is_clean()),
        "the retired `let PAT = E;` spelling must require repair"
    );
    Ok(())
}

#[test]
fn bind_statement_uses_run_keyword() -> Result<(), Box<dyn Error>>
{
    let pbg = built();
    let renamed = [
        "run value <- action;",
        "def bind() -> -F Integer { run value <- action; ret value }",
    ];
    for src in renamed {
        let result = parse(pbg, SourceText::from(src))?;
        assert!(
            bool::from(result.is_clean()),
            "`run PAT <- E;` molds clean in {src:?}; obligations: {:?}",
            result
                .obligations()
                .iter()
                .map(|obligation| obligation.class)
                .collect::<Vec<_>>()
        );
    }

    let retired = parse(pbg, SourceText::from("let value <- action;"))?;
    assert!(
        !bool::from(retired.is_clean()),
        "the retired `let PAT <- E;` spelling must require repair"
    );

    let bare = parse(pbg, SourceText::from("value <- action;"))?;
    assert!(
        !bool::from(bare.is_clean()),
        "a binding arrow without the `run` lead must require repair"
    );
    Ok(())
}

#[test]
fn eliminator_answer_types_mold_clean() -> Result<(), Box<dyn Error>>
{
    // The optional `-> T` slot sits after the scrutinee on both check-only
    // eliminators, on the nested `else if` tail as well as the head, and past
    // the reserved `with` view on `case`. The bare spellings are unchanged.
    let pbg = built();
    let annotated = [
        "if flag -> -F Integer { ret 1 } else { ret 2 }",
        "if flag -> -F Integer { ret 1 } else if other -> -F Integer { ret 2 } else { ret 3 }",
        "if flag { ret 1 } else if other -> -F Integer { ret 2 } else { ret 3 }",
        "case subject -> -F Integer { Inl(x) => ret x, Inr(y) => ret y }",
        "case subject with view -> -F Integer { Inl(x) => ret x, Inr(y) => ret y }",
        "case subject -> -F Integer { }",
        "if flag -> +U[1] (-F Integer) -> -F Integer { ret f } else { ret g }",
    ];
    for src in annotated {
        let result = parse(pbg, SourceText::from(src))?;
        assert!(
            bool::from(result.is_clean()),
            "the answer-type slot molds clean in {src:?}; obligations: {:?}",
            result
                .obligations()
                .iter()
                .map(|obligation| obligation.class)
                .collect::<Vec<_>>()
        );
    }

    let bare = [
        "if flag { ret 1 } else { ret 2 }",
        "case subject { Inl(x) => ret x, Inr(y) => ret y }",
    ];
    for src in bare {
        let result = parse(pbg, SourceText::from(src))?;
        assert!(
            bool::from(result.is_clean()),
            "the unannotated eliminator still molds clean in {src:?}; obligations: {:?}",
            result
                .obligations()
                .iter()
                .map(|obligation| obligation.class)
                .collect::<Vec<_>>()
        );
    }

    // The slot sits between the scrutinee and the body: an answer type written
    // after the body requires repair. A missing scrutinee is a hole the molder
    // fills without an obligation, so its refusal belongs to lowering, not to
    // the parser.
    let rejected = ["if flag { ret 1 } -> -F Integer else { ret 2 }"];
    for src in rejected {
        let result = parse(pbg, SourceText::from(src))?;
        assert!(
            !bool::from(result.is_clean()),
            "an answer type outside its slot must require repair in {src:?}"
        );
    }
    Ok(())
}

#[test]
fn run_binder_annotation_molds_clean() -> Result<(), Box<dyn Error>>
{
    // `run PAT : B <- E ;` names the bound computation's type. No pattern form
    // carries a top-level `:`, so the annotated and bare spellings discriminate
    // on the tile after the pattern.
    let pbg = built();
    let annotated = [
        "run value : -F Integer <- action;",
        "def bind() -> -F Integer { run value : -F Integer <- action; ret value }",
        "def bind() -> -F Integer { run (left, right) : -F Integer <- action; ret left }",
    ];
    for src in annotated {
        let result = parse(pbg, SourceText::from(src))?;
        assert!(
            bool::from(result.is_clean()),
            "`run PAT : B <- E;` molds clean in {src:?}; obligations: {:?}",
            result
                .obligations()
                .iter()
                .map(|obligation| obligation.class)
                .collect::<Vec<_>>()
        );
    }

    // The annotation rides the computation bind alone: the value bind keeps the
    // unannotated spelling the binder lane landed.
    let rejected = parse(pbg, SourceText::from("val value : Integer = expression;"))?;
    assert!(
        !bool::from(rejected.is_clean()),
        "the value bind takes no annotation slot"
    );
    Ok(())
}
/// The circuit block form molds to a **zero-obligation** reading, over its
/// worked examples plus one case per rung of the surface: the empty interface,
/// the occurrence label, the pinned-endpoint binder, the invertible face, and
/// the reserved glyph — which **parses** here and is declined downstream, not
/// at the parser.
#[test]
fn circuit_block_form_molds_zero_obligation() -> Result<(), Box<dyn Error>>
{
    let pbg = built();
    let cases: &[&str] = &[
        // The congruence cell, members `;`-terminated.
        r#"sign Nat {
  sort Nat : Type;
  data Zero : Nat;
  data Succ : Nat --> Nat;
  oper add : (Nat, Nat) --> Nat;

  rule cong2 : (
    rule p : Nat ==> Nat,
    rule q : Nat ==> Nat,
    data x : Nat,
    data y : Nat
  ) ==> (z : Nat) {
    node : p(x) ==> (x′);
    node : q(y) ==> (y′);
    node : add(x′, y′) --> (z);
  };
}
"#,
        // The first stateful wheel.
        r#"oper accumulate : (stream : Stream(Nat)) --> (out2 : Stream(Nat)) {
  node : zip(stream, state) --> (next, out2);
  feed : (next) --> (state);
}
"#,
        // The sugar ladder's named-port normal form, including `()` and `_`.
        r#"sign N {
  sort Nat : Type;
  data Zero : () --> (_ : Nat);
  data Succ : (_ : Nat) --> (_ : Nat);
}
"#,
        // Occurrence labels and the pinned-endpoint binder.
        r#"sign L {
  rule twice : (rule p : x ==> x′, data x : Nat) ==> (o : Nat) {
    node w1 : p(x) ==> (m);
    node w2 : step(m) --> (o);
  };
}
"#,
        // The invertible face, and the reserved reversible glyph.
        "sign I { rule involutive : (b : Bit) <=> (c : Bit); }",
        "sign R { oper negate : (b : Bit) <-> (c : Bit); }",
        // A top-level `rule` declaration beside the top-level `oper`.
        "rule step : (x : Nat) ==> (y : Nat)",
    ];
    for &src in cases {
        let result = parse(pbg, SourceText::from(src))?;
        assert!(
            bool::from(result.is_clean()),
            "circuit form {src:?} molds clean; obligations: {:?}",
            result
                .obligations()
                .iter()
                .map(|obligation| (obligation.class, obligation.span))
                .collect::<Vec<_>>()
        );
    }
    Ok(())
}

/// A data-spelled `oper` inside `codata` molds whole so the description reader
/// can decline that one member without repair swallowing its siblings.
#[test]
fn codata_oper_decline_region_molds_zero_obligation() -> Result<(), Box<dyn Error>>
{
    let source = "codata S : Type { head : Nat; oper tail(s : S) -> S; rule head ==> head; }";
    let result = parse(built(), SourceText::from(source))?;
    assert!(
        bool::from(result.is_clean()),
        "the decline region and both siblings mold cleanly: {:?}",
        result
            .obligations()
            .iter()
            .map(|obligation| (obligation.class, obligation.span))
            .collect::<Vec<_>>()
    );
    Ok(())
}

/// A data-spelled `oper` inside `sign` molds as one member so its localized
/// decline cannot consume the next ruled judgment.
#[test]
fn sign_data_oper_decline_region_molds_zero_obligation() -> Result<(), Box<dyn Error>>
{
    let source = r#"sign Theory { sort Nat : Type; oper add(m : Nat, n : Nat) -> Nat; oper succ : (n : Nat) --> Nat; }"#;
    let result = parse(built(), SourceText::from(source))?;
    assert!(
        bool::from(result.is_clean()),
        "the declined member and valid sibling mold cleanly: {:?}",
        result
            .obligations()
            .iter()
            .map(|obligation| (obligation.class, obligation.span))
            .collect::<Vec<_>>()
    );
    Ok(())
}

/// The arrow grid does not disturb the shorter tiles it extends: a case arm's
/// `=>`, a bind statement's `<-`, and the `<=` / `==` comparisons all still
/// mold exactly as before. This is the parser half of the lexical check; the
/// labeler half is
/// `label::tests::circuit_arrows_munch_past_the_shorter_tiles_they_extend`.
#[test]
fn circuit_arrows_leave_the_shorter_tiles_alone() -> Result<(), Box<dyn Error>>
{
    let pbg = built();
    let unchanged: &[&str] = &[
        "case x { A => 1, B => 2 }",
        "run value <- action;",
        "def le() -> -F Boolean { ret a <= b }",
        "def eq() -> -F Boolean { ret a == b }",
        "def arrow : A -> B;",
    ];
    for &src in unchanged {
        let result = parse(pbg, SourceText::from(src))?;
        assert!(
            bool::from(result.is_clean()),
            "{src:?} is unaffected by the arrow grid; obligations: {:?}",
            result
                .obligations()
                .iter()
                .map(|obligation| obligation.class)
                .collect::<Vec<_>>()
        );
    }
    // The grid glyph and the tile it extends are distinct melds, not one
    // absorbing the other: a `-->` never appears where a `->` was written.
    let term = parse(pbg, SourceText::from("def arrow : A -> B;"))?;
    assert!(
        find_meld_with_tile(term.tree(), term.tree().root(), TileText::from("-->")).is_none(),
        "a term function arrow molds `->`, never the circuit former"
    );
    let circuit = parse(pbg, SourceText::from("oper f : (a : A) --> (b : B)"))?;
    assert!(
        find_meld_with_tile(circuit.tree(), circuit.tree().root(), TileText::from("->")).is_none(),
        "a circuit interface molds `-->`, never the term function arrow"
    );
    Ok(())
}

/// A top-level circuit declaration keeps its whole signature, and a bare-sort
/// side there is **declined** rather than silently dropped.
///
/// An Item-sort form that can end in a sort hole does not close: the melder has
/// no following tile of an enclosing form to close it against, so a bare-sort
/// side detaches and the declaration silently keeps only its prefix — a clean
/// parse of the wrong tree, which the zero-obligation corpus gate cannot see.
/// The top-level form therefore requires parenthesized sides, and this test
/// pins both halves: the ruled shape keeps its arrow *inside* the declaration
/// meld, and the bare-sort shape now flags a repair instead of regrouping.
#[test]
fn a_top_level_circuit_declaration_keeps_its_whole_signature() -> Result<(), Box<dyn Error>>
{
    let pbg = built();
    // Clean parses are not enough: `is_clean()` was true for the shattered
    // reading too. The load-bearing assertion is that the arrow is a
    // *descendant* of the one top-level meld, not a sibling of it.
    let whole: &[&str] = &[
        "oper f : (a : A) --> (b : B)",
        "rule step : (x : Nat) ==> (y : Nat)",
        r#"oper accumulate : (stream : Stream(Nat)) --> (out2 : Stream(Nat)) {
  node : zip(stream, state) --> (next, out2);
  feed : (next) --> (state);
}
"#,
    ];
    for &src in whole {
        let result = parse(pbg, SourceText::from(src))?;
        assert!(bool::from(result.is_clean()), "{src:?} molds clean");
        let significant = significant_children(result.tree(), result.tree().root());
        assert_eq!(
            1,
            significant.len(),
            "{src:?} is ONE top-level item, not a shattered run: {significant:?}"
        );
        let Some(&item) = significant.first()
        else {
            panic!("a top-level item was counted but not readable");
        };
        assert!(
            descendant_tiles(result.tree(), item)
                .iter()
                .any(|tile| tile == "-->" || tile == "==>"),
            "{src:?} keeps its arrow inside the declaration"
        );
    }
    // A bare-sort side at item position is declined, not silently dropped. The
    // sugar ladder's bare rungs stay available inside a `sign` block, where the
    // member's sort hole is form-interior.
    for &src in &[
        "oper f : Nat --> Nat",
        "oper f : (a : A) --> Nat",
        "oper f : Nat",
    ] {
        let result = parse(pbg, SourceText::from(src))?;
        assert!(
            !bool::from(result.is_clean()),
            "{src:?} must flag a repair rather than regroup silently"
        );
    }
    let member = parse(
        pbg,
        SourceText::from(
            "sign S { data Zero : Nat; data Succ : Nat --> Nat; oper add : (Nat, Nat) --> Nat; }",
        ),
    )?;
    assert!(
        bool::from(member.is_clean()),
        "the bare-sort rungs stay available as `sign` members"
    );
    Ok(())
}

/// The circuit form's **contextual** leads still bind as ordinary names.
///
/// Only the two item-position leads (`sign` and `oper`) reserve globally. The
/// member keyword `sort` and the body statements `node` / `feed` are
/// `≐`-successors of an open circuit block and inadmissible at every other
/// lowercase-word slot, so the pre-filter drops their keyword mold there and a
/// program may still bind them — which is the claim this test is here to keep
/// honest, because reserving a fourth, fifth, or sixth word would be a silent
/// source break.
#[test]
fn circuit_contextual_keywords_still_bind_as_names() -> Result<(), Box<dyn Error>>
{
    let pbg = built();
    let binding: &[&str] = &[
        "def sort = 1;",
        "def node = 1;",
        "def feed = 1;",
        "def use() -> -F Integer { val node = 1; ret node }",
        "def project(sort: Integer) -> -F Integer { ret sort }",
        "def record = #{ node = 1, feed = 2 };",
    ];
    for &src in binding {
        let result = parse(pbg, SourceText::from(src))?;
        assert!(
            bool::from(result.is_clean()),
            "{src:?} still binds a contextual circuit keyword; obligations: {:?}",
            result
                .obligations()
                .iter()
                .map(|obligation| obligation.class)
                .collect::<Vec<_>>()
        );
    }
    // Contextual is not the same as inadmissible-elsewhere, and the bound
    // matters: inside a `sign` block, the positions where a member's *typed*
    // ports sit are past the member lead's slot, so a type variable spelled
    // `sort` molds as a type there.
    let inside: &[&str] = &[
        "sign S { oper f : (a : sort) --> (b : Nat); sort Bit : Type; }",
        "sign S { rule r : (rule p : sort ==> other, data x : Nat) ==> (z : Nat); }",
        "sign S { oper f : node --> Nat; }",
        "sign S { oper f : (a : feed) --> (b : Nat); }",
    ];
    for &src in inside {
        let result = parse(pbg, SourceText::from(src))?;
        assert!(
            bool::from(result.is_clean()),
            "{src:?} molds clean inside a circuit block; obligations: {:?}",
            result
                .obligations()
                .iter()
                .map(|obligation| obligation.class)
                .collect::<Vec<_>>()
        );
    }
    Ok(())
}

/// An application repeating a port name — `add(x, x)` — molds clean, so the
/// linearity refusal downstream is reachable from source. Every `sign` member
/// is `;`-terminated: after a member's trailing sort hole only `;` is
/// admissible, which never competes with hole content, so the member can no
/// longer collapse into one repaired region.
#[test]
fn a_repeated_port_name_application_molds_clean() -> Result<(), Box<dyn Error>>
{
    let pbg = built();
    let cases: &[&str] = &[
        // The headline shape: one wire consumed twice in a redex line.
        r#"sign Copy {
  sort Nat : Type;
  oper add : (l : Nat, r : Nat) --> (s : Nat);
  rule copy2 : (data x : Nat) ==> (z : Nat) {
    node : add(x, x) --> (z);
  };
}
"#,
        // The same reading with distinct names, and the sugar ladder's
        // unnamed-port rungs.
        r#"sign Copy {
  sort Nat : Type;
  oper add : (Nat, Nat) --> Nat;
  rule copy2 : (data x : Nat, data y : Nat) ==> (z : Nat) {
    node : add(x, y) --> (z);
  };
}
"#,
        // A body-less rule member ahead of the closing brace.
        r#"sign B {
  sort Nat : Type;
  oper add : (Nat, Nat) --> Nat;
  rule copy2 : (data x : Nat) ==> (z : Nat);
}
"#,
    ];
    for &src in cases {
        let result = parse(pbg, SourceText::from(src))?;
        assert!(
            bool::from(result.is_clean()),
            "repeated-name application {src:?} molds clean; obligations: {:?}",
            result
                .obligations()
                .iter()
                .map(|obligation| (obligation.class, obligation.span))
                .collect::<Vec<_>>()
        );
    }
    // The terminator is load-bearing, not merely admitted: an unterminated
    // member flags a repair rather than silently closing against the next
    // member's lead.
    let unterminated = parse(
        pbg,
        SourceText::from(
            r#"sign S {
  sort Nat : Type
  sort T : Type;
}
"#,
        ),
    )?;
    assert!(
        !bool::from(unterminated.is_clean()),
        "a member without its `;` terminator must flag a repair"
    );
    Ok(())
}

/// `sort S : Type ;` followed by a blank line loses nothing — the block molds
/// to its intended form. The `;` closes the member's trailing sort hole
/// decisively, so trailing layout (a blank line, several, a comment, or the
/// closing brace) can no longer break the parse.
#[test]
fn a_blank_line_after_a_terminated_member_molds_clean() -> Result<(), Box<dyn Error>>
{
    let pbg = built();
    let cases: &[&str] = &[
        r#"sign S {
  sort S : Type;

}
"#,
        r#"sign S {
  sort S : Type;

  sort T : Type;
}
"#,
        r#"sign S {
  sort S : Type;

  oper f : (S) --> S;

  rule r : (data x : S) ==> (z : S) {
    node : f(x) --> (z);
  };
}
"#,
        r#"sign S {

  sort S : Type;

  // a comment between members

  sort T : Type;

}

"#,
    ];
    for &src in cases {
        let result = parse(pbg, SourceText::from(src))?;
        assert!(
            bool::from(result.is_clean()),
            "blank-line shape {src:?} molds clean; obligations: {:?}",
            result
                .obligations()
                .iter()
                .map(|obligation| (obligation.class, obligation.span))
                .collect::<Vec<_>>()
        );
    }
    Ok(())
}

/// A `sign` block may be named with a primitive-type spelling (`sign
/// Unknown`). The labeler's uppercase-word reservation is a disambiguation
/// preference at slots where the reserved tile molds, never a ban on
/// declaration names: at a slot that admits only `type_identifier` the molder
/// falls back to the word's generic labels.
#[test]
fn a_sign_block_may_be_named_with_a_primitive_type_spelling() -> Result<(), Box<dyn Error>>
{
    let pbg = built();
    let cases: &[&str] = &[
        r#"sign Unknown {
  sort Nat : Type;
}
"#,
        r#"sign Boolean {
  sort Bit : Type;
}
"#,
        r#"sign Any {
  sort Nat : Type;
}
"#,
    ];
    for &src in cases {
        let result = parse(pbg, SourceText::from(src))?;
        assert!(
            bool::from(result.is_clean()),
            "primitive-named sign block {src:?} molds clean; obligations: {:?}",
            result
                .obligations()
                .iter()
                .map(|obligation| (obligation.class, obligation.span))
                .collect::<Vec<_>>()
        );
    }
    // The reservation still owns the type slots it disambiguates: `Unknown`
    // in type position molds the primitive-type atom, never a spurious
    // `type_identifier`.
    let typed = parse(pbg, SourceText::from("def x : Unknown;"))?;
    assert!(
        bool::from(typed.is_clean()),
        "the reserved spelling still molds at a type slot"
    );
    assert_eq!(
        Some("Unknown".to_owned()),
        mold_label_of(
            pbg,
            typed.tree(),
            typed.tree().root(),
            TileText::from("Unknown")
        ),
        "a type slot keeps the primitive-type atom"
    );
    // And the name slot of a primitive-named block reads the word as the
    // generic class — the two readings of one spelling, separated by position.
    let named = parse(pbg, SourceText::from("sign Unknown { sort Nat : Type; }"))?;
    assert_eq!(
        Some("type_identifier".to_owned()),
        mold_label_of(
            pbg,
            named.tree(),
            named.tree().root(),
            TileText::from("Unknown")
        ),
        "a declaration-name slot falls back to the generic label"
    );
    Ok(())
}

/// The zero-obligation gate over the language's corpus: the candidate
/// pre-filter and the grammar mold **every** corpus source to a
/// globally-consistent **zero-obligation** reading — zero total obligations,
/// no named residual. The corpus crate's runner reports how many sources each
/// root holds; nothing here pins the number.
#[test]
fn corpus_molds_to_zero_obligations() -> Result<(), Box<dyn Error>>
{
    let pbg = built();
    let corpus = corpus_root();
    let files = gandr_files(&corpus);
    assert!(!files.is_empty(), "the corpus sources are present");
    let mut total = 0_usize;
    let mut dirty: Vec<(String, Vec<String>)> = Vec::new();
    for path in &files {
        let src = read_source(path)?;
        let result = parse(pbg, SourceText::from(src.as_str()))?;
        total = total.saturating_add(result.obligations().len());
        if !bool::from(result.is_clean()) {
            dirty.push((
                path.strip_prefix(&corpus)
                    .unwrap_or(path)
                    .to_string_lossy()
                    .into_owned(),
                result
                    .obligations()
                    .iter()
                    .map(|obligation| format!("{:?} @ {:?}", obligation.class, obligation.span))
                    .collect(),
            ));
        }
    }
    assert!(
        dirty.is_empty(),
        "every corpus source molds to zero obligations; residual: {dirty:?}"
    );
    assert_eq!(0, total, "the corpus carries zero total obligations");
    Ok(())
}
#[test]
fn incomplete_input_flags_statement_local_obligations() -> Result<(), Box<dyn Error>>
{
    let pbg = built();
    let fixture_root = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures");
    for name in ["incomplete-input.gandr", "parser-recovery.gandr"] {
        let fixture_path = fixture_root.join(name);
        let src = read_source(&fixture_path)?;
        let result = parse(pbg, SourceText::from(src.as_str()))?;
        assert!(
            !bool::from(result.is_clean()),
            "{name} is incomplete input and must flag obligations"
        );
        // Every obligation span is inside the source (statement-local, never
        // dangling past the buffer).
        let len = ByteOffset::from(src.len());
        for obligation in result.obligations() {
            assert!(
                obligation.span.start() <= len && obligation.span.end() <= len,
                "{name} obligation span {:?} is within the source",
                (obligation.span.start(), obligation.span.end())
            );
        }
    }
    Ok(())
}
#[test]
fn mixed_set_precedence_requires_obligation_and_commits() -> Result<(), Box<dyn Error>>
{
    // The set surface is split into pairwise-incomparable
    // union, intersection, and lazy-product groups. A mixed set chain such as
    // `A /\ B | C` therefore requires explicit parentheses. The current
    // recovery path's exact repair class and span are incidental; the stable
    // contract is non-clean parsing with a committed tree.
    let pbg = built();
    let result = parse(pbg, SourceText::from("def t : A /\\ B | C;"))?;
    assert!(
        !bool::from(result.is_clean()),
        "mixed set operators require a disambiguating obligation"
    );
    assert!(
        !result.obligations().is_empty(),
        "mixed set operators must report at least one obligation"
    );
    // Totality: the parse still commits.
    assert_eq!(
        Some(NodeLabel::Wald),
        label_of(result.tree(), result.tree().root())
    );
    Ok(())
}
#[test]
fn malformed_programs_repair_predictably() -> Result<(), Box<dyn Error>>
{
    let pbg = built();
    // (source, at-least-one obligation class expected in the repair).
    let cases: &[(&str, Oblig)] = &[
        // An unclosed bracket force-closes with a ghost delimiter.
        ("def x = ( 1 ;", Oblig::MissingTile),
        // A trailing operator has no right operand — the operator's missing
        // operand is a convex grout ([`Oblig::MissingMeld`]). (The former
        // `def x = 1 + ;` fixture now force-closes the factored def value at
        // the `;` instead, flagging a `MissingTile`; the operator-completion
        // path is exercised directly here, where it is the sole repair.)
        ("ret 1 +", Oblig::MissingMeld),
        // A stray byte the grammar has no tile for.
        ("def x = 1 ~ 2;", Oblig::UnmoldedTok),
        // An unterminated string force-closes.
        ("def x = \"open", Oblig::MissingTile),
    ];
    for &(src, expected_class) in cases {
        let result = parse(pbg, SourceText::from(src))?;
        assert!(
            !bool::from(result.is_clean()),
            "malformed {src:?} must flag a repair obligation"
        );
        assert!(
            result
                .obligations()
                .iter()
                .any(|o| o.class == expected_class),
            "malformed {src:?} repair should include {expected_class:?}; got {:?}",
            result
                .obligations()
                .iter()
                .map(|o| o.class)
                .collect::<Vec<_>>()
        );
        // Totality: every malformed program still commits to a Wald.
        assert_eq!(
            Some(NodeLabel::Wald),
            label_of(result.tree(), result.tree().root())
        );
    }
    Ok(())
}
/// An unclosed value delimiter must be repaired at the declaration boundary,
/// so a following definition remains a distinct top-level item.
///
/// The absorbing behaviour this pins against is not merely "one item instead of
/// two": the melder's repair for an unclosed `(` is a ghost end tile appended
/// wherever the form finally closes, so an unbounded repair puts that ghost —
/// and the whole `def good` declaration it swallowed — inside the first
/// definition's meld. Each half is asserted separately: the first declaration
/// carries every ghost and every obligation, and the second carries none and
/// covers exactly the text it was written with.
#[test]
fn unclosed_definition_delimiter_does_not_absorb_following_definition() -> Result<(), Box<dyn Error>>
{
    let source = "def bad = ( 1 ;\ndef good = 2;";
    let result = parse(built(), SourceText::from(source))?;
    let significant = significant_children(result.tree(), result.tree().root());
    assert_eq!(
        2,
        significant.len(),
        "the malformed and valid definitions remain distinct items"
    );
    let second_start = ByteOffset::from(source.find("def good").unwrap_or(source.len()));

    // The damaged declaration: it holds `bad`, it stops at the boundary, and
    // every ghost the repair minted lands inside it.
    let damaged = span(result.tree(), significant[0]).expect("the damaged item is held");
    let damaged_ghosts = descendant_grout_ends(result.tree(), significant[0]);
    assert!(
        descendant_tiles(result.tree(), significant[0])
            .iter()
            .any(|tile| tile == "bad"),
        "the first item remains the `bad` definition"
    );
    assert!(
        damaged.end() <= second_start,
        "the repaired first definition must not extend past the declaration boundary"
    );
    assert!(
        !bool::from(result.is_clean()),
        "the malformed first definition retains a recovery obligation"
    );
    assert!(
        !damaged_ghosts.is_empty(),
        "the repair must mint a ghost end for the unclosed delimiter"
    );
    assert!(
        damaged_ghosts.iter().all(|&end| end <= second_start),
        "every ghost the repair minted stays before the valid sibling"
    );
    assert!(
        result
            .obligations()
            .iter()
            .all(|obligation| obligation.span.end() <= second_start),
        "recovery obligations stay before the valid sibling"
    );

    // The surviving declaration: whole, ghost-free, and starting exactly where
    // the damaged one stopped.
    let survivor = span(result.tree(), significant[1]).expect("the surviving item is held");
    assert_eq!(
        second_start,
        survivor.start(),
        "the valid sibling starts at the declaration boundary"
    );
    assert_eq!(
        "def good = 2;",
        text(result.tree(), significant[1]),
        "the valid sibling covers exactly the text it was written with"
    );
    assert!(
        descendant_tiles(result.tree(), significant[1])
            .iter()
            .any(|tile| tile == "good"),
        "the second item remains the `good` definition"
    );
    assert!(
        descendant_grout_ends(result.tree(), significant[1]).is_empty(),
        "no ghost may reach into the valid sibling"
    );
    Ok(())
}
/// The declaration boundary belongs to item position, not to the `def`
/// keyword: a repair bounded before a surviving `def` must be bounded before
/// every other declaration head too.
///
/// Every row keeps the same damaged first declaration and varies only the
/// family that follows it. A boundary rule keyed on the literal label `def`
/// passes the first row and absorbs every other one into the damaged
/// definition, so this is what distinguishes the declaration-head trigger from
/// a `def`-only trigger.
#[test]
fn an_unclosed_delimiter_yields_to_every_declaration_family() -> Result<(), Box<dyn Error>>
{
    for survivor in [
        "def good = 2;",
        "data Good { }",
        "codata Good { }",
        "module Good { }",
        "sign Good { }",
        "import \"good\" as good ;",
    ] {
        let source = format!("def bad = ( 1 ;\n{survivor}");
        let result = parse(built(), SourceText::from(source.as_str()))?;
        let significant = significant_children(result.tree(), result.tree().root());
        assert_eq!(
            2,
            significant.len(),
            "the damaged definition must not absorb a following {survivor:?}"
        );
        let boundary = ByteOffset::from(source.len().saturating_sub(survivor.len()));
        let damaged = span(result.tree(), significant[0]).expect("the damaged item is held");
        let surviving = span(result.tree(), significant[1]).expect("the surviving item is held");
        assert!(
            damaged.end() <= boundary,
            "the repair must stop at the boundary before {survivor:?}"
        );
        assert_eq!(
            boundary,
            surviving.start(),
            "the surviving {survivor:?} must start at the declaration boundary"
        );
        assert_eq!(
            survivor,
            text(result.tree(), significant[1]),
            "the surviving declaration must cover exactly its own text"
        );
        assert!(
            descendant_grout_ends(result.tree(), significant[1]).is_empty(),
            "no ghost may reach into the surviving {survivor:?}"
        );
        assert!(
            !bool::from(result.is_clean()),
            "the damaged definition must still carry its recovery obligation"
        );
    }
    Ok(())
}
#[test]
fn malformed_input_continues_into_a_later_definition() -> Result<(), Box<dyn Error>>
{
    let source = "def bad = 1 ~ 2;\ndef good = 2;";
    let first = parse(built(), SourceText::from(source))?;
    assert!(
        first
            .obligations()
            .iter()
            .any(|obligation| obligation.class == Oblig::UnmoldedTok),
        "the stray token remains an explicit recovery obligation"
    );
    let root = first.tree().root();
    assert_eq!(
        Some(NodeLabel::Wald),
        label_of(first.tree(), root),
        "recovery still commits the documented Wald root"
    );
    let declarations: Vec<(NodeIndex, Vec<String>)> = children(first.tree(), root)
        .into_iter()
        .filter(|&id| matches!(label_of(first.tree(), id), Some(NodeLabel::Meld(_))))
        .map(|id| (id, direct_tiles(first.tree(), id)))
        .collect();
    let bad_index = declarations.iter().position(|entry| {
        entry.1.iter().any(|tile| tile == "def") && entry.1.iter().any(|tile| tile == "bad")
    });
    let good_index = declarations.iter().position(|entry| {
        entry.1.iter().any(|tile| tile == "def") && entry.1.iter().any(|tile| tile == "good")
    });
    assert!(
        bad_index.is_some() && good_index.is_some(),
        "the malformed and recovered definitions remain top-level melds: {declarations:?}"
    );
    assert!(
        bad_index < good_index,
        "the recovered `def good` follows the malformed `def bad` boundary"
    );
    assert!(
        find_meld_with_tile(first.tree(), first.tree().root(), TileText::from("good")).is_some(),
        "recovery must preserve the later definition instead of forming a parse wall"
    );
    let second = parse(built(), SourceText::from(source))?;
    assert_eq!(
        first.obligations(),
        second.obligations(),
        "recovery obligations are deterministic"
    );
    assert_eq!(
        root_digest(first.tree()),
        root_digest(second.tree()),
        "the recovered tree is deterministic"
    );
    Ok(())
}

#[test]
fn corpus_parses_totally() -> Result<(), Box<dyn Error>>
{
    // Every corpus source parses totally — no panic, a well-formed tree
    // recording the grammar fingerprint under a Wald root. The stronger
    // zero-obligation gate is `corpus_molds_to_zero_obligations`; this test
    // is the weaker totality floor.
    let pbg = built();
    let files = gandr_files(&corpus_root());
    assert!(!files.is_empty(), "the corpus sources are present");
    for path in &files {
        let src = read_source(path)?;
        let result = parse(pbg, SourceText::from(src.as_str()))?;
        assert_eq!(result.tree().grammar(), pbg.fingerprint());
        assert_eq!(
            Some(NodeLabel::Wald),
            label_of(result.tree(), result.tree().root()),
            "{:?} roots a Wald",
            path.file_name()
        );
    }
    Ok(())
}
#[test]
fn corpus_files_cold_parse_within_p99_latency_budget() -> Result<(), Box<dyn Error>>
{
    // The p99 of a corpus source's cold parse is fast. Every `parse` is stateless
    // (no incremental reuse), so each call is a cold parse; per file we keep
    // the MINIMUM over a few iterations — the minimum is the least-noise
    // estimate of the true cost, so a loaded runner inflates individual
    // samples but not this gate.
    //
    // The budget is profile-aware: a 1 ms p99 release cold-parse, enforced
    // under an optimized build (`not(debug_assertions)`), and under the
    // unoptimized test profile, where the parse is roughly fifteen to twenty
    // times slower, a coarse regression budget that still trips on an
    // order-of-magnitude blow-up. The p99 is dominated by
    // `data-operation-members.gandr`, whose reserved `oper` / `rule` members
    // cost the molder super-linearly — a standing performance residual.
    use std::time::Instant;

    /// Timed iterations per file; the per-file cost is the minimum.
    const ITERS: u32 = 16;
    /// Nearest-rank percentile numerator for the p99 gate.
    const P99_NUMERATOR: usize = 99;
    /// Percent scale denominator for the p99 gate.
    const PERCENTILE_DENOMINATOR: usize = 100;
    /// The p99 cold-parse budget, in nanoseconds. Release: the 1 ms task
    /// target. Dev: a coarse regression budget (the unoptimized parse is
    /// ~15-20x slower, so a 1 ms budget is unreachable there).
    #[cfg(not(debug_assertions))]
    const P99_BUDGET_NANOS: u128 = 1_000_000;
    #[cfg(debug_assertions)]
    const P99_BUDGET_NANOS: u128 = 100_000_000;

    let pbg = built();
    let files = gandr_files(&corpus_root());
    assert!(!files.is_empty(), "the corpus sources are present");

    let mut per_file_nanos: Vec<(u128, PathBuf)> = Vec::with_capacity(files.len());
    for path in &files {
        let src = read_source(path)?;
        let mut best = u128::MAX;
        for _iter in 0 .. ITERS {
            let start = Instant::now();
            let result = parse(pbg, SourceText::from(src.as_str()))?;
            let elapsed = start.elapsed().as_nanos();
            // Keep the optimizer from eliding the timed parse.
            let _kept = core::hint::black_box(&result);
            best = best.min(elapsed);
        }
        per_file_nanos.push((best, path.clone()));
    }

    per_file_nanos.sort_by_key(|&(nanos, _)| nanos);
    // Nearest-rank p99 over the per-file minima.
    let rank = per_file_nanos
        .len()
        .saturating_mul(P99_NUMERATOR)
        .div_ceil(PERCENTILE_DENOMINATOR)
        .saturating_sub(1)
        .min(per_file_nanos.len().saturating_sub(1));
    let p99 = &per_file_nanos[rank];
    let max = per_file_nanos.last().expect("non-empty corpus");
    assert!(
        p99.0 < P99_BUDGET_NANOS,
        "p99 corpus cold-parse {} ns (file {:?}) exceeds the {P99_BUDGET_NANOS} ns \
             budget; slowest {} ns (file {:?})",
        p99.0,
        p99.1.file_name(),
        max.0,
        max.1.file_name()
    );
    Ok(())
}
#[test]
fn expected_agrees_with_committed_finalize() -> Result<(), Box<dyn Error>>
{
    // The completion `expected()` reports bounds the obligation material a
    // committed finalize inserts: at every token prefix of each source, every
    // obligation the commit returns is buffered or named by the query, and
    // the query's only excess is a missing operand for an operator whose
    // operand is a form still open — which the commit's force-close turns
    // into that operand.
    let pbg = built();
    let sources = [
        "def x = 1;".to_owned(),
        "fn(a) { ret a }".to_owned(),
        "if c { ret 1 } else { ret 2 }".to_owned(),
        "ret 1 +".to_owned(),
        "ret ( 1 +".to_owned(),
        read_source(&corpus_root().join("fixture/surface/string-interpolation.gandr"))?,
    ];
    let mut excess_seen = 0_usize;
    for src in &sources {
        let source = SourceFragment::from(src.as_str());
        let tokens = label(source);
        for upto in 0 ..= tokens.len() {
            let state = push_prefix(pbg, source, TokenPrefixLen::from(upto));
            let completion = state.expected();
            let mut excess: Vec<Oblig> = state
                .obligations()
                .iter()
                .chain(completion.obligations())
                .map(|obligation| obligation.class)
                .collect();
            let prefix_end = upto
                .checked_sub(1)
                .and_then(|last| tokens.get(last))
                .map_or(0, |token| usize::try_from(token.end).unwrap_or(usize::MAX));
            let prefix = src.get(.. prefix_end).unwrap_or_default();
            let (_tree, committed) = state.commit_with_obligations(SourceText::from(prefix))?;
            for obligation in &committed {
                let named = excess.iter().position(|&class| class == obligation.class);
                assert!(
                    named.is_some(),
                    "the commit's {:?} is named by the query for prefix {upto} of {src:?}",
                    obligation.class
                );
                if let Some(at) = named {
                    let _named = excess.swap_remove(at);
                }
            }
            assert!(
                excess.iter().all(|&class| class == Oblig::MissingMeld),
                "the query's excess {excess:?} for prefix {upto} of {src:?} is only missing operands"
            );
            excess_seen = excess_seen.saturating_add(excess.len());
        }
    }
    assert!(
        excess_seen > 0,
        "the sources reach an operator whose operand is an open form"
    );
    Ok(())
}
#[test]
fn minimization_prefers_clean_readings() -> Result<(), Box<dyn Error>>
{
    // Every clean corpus source has a zero-obligation molding, and the molder
    // finds it — the minimization never introduces an obligation (least of all
    // an AmbiguousPrec) when a clean reading exists.
    let pbg = built();
    let files = gandr_files(&corpus_root());
    assert!(!files.is_empty(), "the corpus sources are present");
    for path in &files {
        let src = read_source(path)?;
        let result = parse(pbg, SourceText::from(src.as_str()))?;
        assert!(
            result
                .obligations()
                .iter()
                .all(|o| o.class != Oblig::AmbiguousPrec),
            "{:?} molds without introducing ambiguity",
            path.file_name()
        );
    }
    Ok(())
}

#[test]
fn remolding_makes_dash_prefix_or_infix_by_context() -> Result<(), Box<dyn Error>>
{
    // The same `-` token molds infix with a left operand and
    // prefix at expression start (paper Fig. 5) — the molder's context
    // discrimination, over one lexical token stream.
    let pbg = built();
    // With a left operand, `-` molds infix: the `-` meld melds two operands
    // and the operator (three children).
    let infix = parse(pbg, SourceText::from("x - y"))?;
    let infix_meld = find_meld_with_tile(infix.tree(), infix.tree().root(), TileText::from("-"))
        .expect("a `-` meld");
    assert!(
        direct_tiles(infix.tree(), infix_meld).contains(&"-".to_owned()),
        "the infix meld carries the `-` operator tile"
    );
    assert_eq!(
        3,
        children(infix.tree(), infix_meld).len(),
        "infix `-` melds two operands and the operator"
    );

    // At expression start (`ret -y`, `-y`), `-` molds prefix (unary): the
    // meld carries the operator and its single right operand (two children),
    // and the parse is clean — no missing-left obligation.
    for src in ["ret -y", "-y"] {
        let prefix = parse(pbg, SourceText::from(src))?;
        let prefix_meld =
            find_meld_with_tile(prefix.tree(), prefix.tree().root(), TileText::from("-"))
                .expect("a `-` meld");
        assert_eq!(
            2,
            children(prefix.tree(), prefix_meld).len(),
            "prefix `-` melds one operand and the operator in {src:?}"
        );
        assert!(
            bool::from(prefix.is_clean()),
            "prefix remolding of {src:?} is clean"
        );
    }
    assert!(bool::from(infix.is_clean()), "the infix remolding is clean");
    Ok(())
}

/// The user-hole positions each mold to a **zero-obligation**
/// reading, and no hole meld ever absorbs the tile that closes an enclosing
/// form — a `?` / `?name` hole is a complete operand and the following
/// terminator (`;`), block closer (`}`), call comma / closer (`,` / `)`),
/// and infix operator (`+`) stay flat siblings.
///
/// The regression: before the melder learned the grammar LAST set, `?`
/// opened a form that demanded its optional `hole_name`, so a bare `?`
/// buffered a spurious `MissingTile` and its meld absorbed the following
/// `;` / `}`, structurally breaking block recovery downstream. Both
/// properties are witnessed here: zero obligations, and the closer sitting
/// outside the hole meld.
#[test]
fn hole_positions_mold_zero_obligation() -> Result<(), Box<dyn Error>>
{
    let pbg = built();
    // (source, the tile that must NOT be absorbed into the hole meld).
    let cases: &[(&str, &str)] = &[
        ("def ho = ret ?name;", ";"),
        ("thunk { ? }", "}"),
        ("thunk { ret ?seed }", "}"),
        ("? + 1", "+"),
        ("f(?, 2)", ","),
        ("def ho = ret ?;", ";"),
        ("def x = ?;", ";"),
        ("ret ?name", "name"),
    ];
    for &(src, closer) in cases {
        let result = parse(pbg, SourceText::from(src))?;
        // (a) Zero obligations — a legitimate hole is not incomplete input.
        assert!(
            bool::from(result.is_clean()),
            "hole source {src:?} molds clean; obligations: {:?}",
            result
                .obligations()
                .iter()
                .map(|o| o.class)
                .collect::<Vec<_>>()
        );
        // Totality: the parse commits to a well-formed root.
        assert_eq!(
            Some(NodeLabel::Wald),
            label_of(result.tree(), result.tree().root()),
            "hole source {src:?} commits to a Wald"
        );
        // (b) The hole meld never absorbs a tile that closes an enclosing
        // form: the `;` / `}` / `,` closer is a flat sibling, not a
        // descendant of the `?` meld.
        let hole_meld =
            find_meld_with_tile(result.tree(), result.tree().root(), TileText::from("?"))
                .expect("a `?` hole meld");
        let inside = descendant_tiles(result.tree(), hole_meld);
        if closer == "name" {
            // The named hole's name attaches as the meld's `hole_name` tail.
            assert!(
                inside.iter().any(|tile| tile == "name"),
                "{src:?}: the hole name attaches to the hole meld; tiles {inside:?}"
            );
        }
        else {
            assert!(
                !inside.iter().any(|tile| tile == closer),
                "{src:?}: the closer {closer:?} must stay a flat sibling, not be \
                     absorbed into the hole meld; hole-meld tiles {inside:?}"
            );
        }
    }
    Ok(())
}

/// The `unknown_type` rule: `?` molds as a Type-sort atom with zero
/// obligations at every type position, while the Expression-sort hole and the
/// receive-session prefix keep their own readings of the same tile.
#[test]
fn unknown_type_molds_zero_obligation() -> Result<(), Box<dyn Error>>
{
    use gandr_surface_grammar::Sort;

    let pbg = built();
    // `?` at every type position molds clean.
    let clean: &[&str] = &[
        // Bare ascription: the sort-free signature position.
        "def f : ?;",
        // The returner payload is a value position: `-F ?` is the pure
        // returner over the value unknown, NOT the computation top.
        "def f : -F ?;",
        // Arrow result, thunk body, lazy-product member: computation
        // positions.
        "def f : Integer -> ?;",
        "def f : +U ?;",
        "def f : -F Unit & ?;",
        // Product member: the `?`-led infix shape must not confuse the
        // classifier (the atom completes, the `*` continues the type).
        "def f : ? * Integer;",
        // Parenthesized.
        "def f : (?);",
        // The legacy keyword keeps its value-primitive reading beside the
        // atom.
        "def f : -F Unknown;",
        // The receive-session prefix keeps its own `?`-led reading: a type,
        // `.`, and a session tail following the `?` selects `?T.S`.
        "def s : ? Integer . end;",
        // The term hole (Expression sort) is untouched by the new atom.
        "def x = ?;",
        "def x = ?goal;",
    ];
    for &src in clean {
        let result = parse(pbg, SourceText::from(src))?;
        assert!(
            bool::from(result.is_clean()),
            "unknown-type source {src:?} molds clean; obligations: {:?}",
            result
                .obligations()
                .iter()
                .map(|o| o.class)
                .collect::<Vec<_>>()
        );
    }

    // The atom's `?` carries a Type-sort mold; the term hole's an
    // Expression-sort one. Same tile, different sorts — the disambiguation
    // the ruled spelling rests on.
    let typed = parse(pbg, SourceText::from("def f : ?;"))?;
    assert_eq!(
        Some(Sort::Type),
        mold_sort_of(pbg, typed.tree(), typed.tree().root(), TileText::from("?")),
        "a type-slot `?` molds at the Type sort"
    );
    let holed = parse(pbg, SourceText::from("def x = ?;"))?;
    assert_eq!(
        Some(Sort::Expression),
        mold_sort_of(pbg, holed.tree(), holed.tree().root(), TileText::from("?")),
        "an expression-slot `?` keeps the hole mold"
    );

    // The receive-session reading wins when its continuation follows: the
    // meld carrying the `?` also carries the received type and the `.`
    // sequencer (the session tail sits outside that meld's own span).
    let session = parse(pbg, SourceText::from("def s : ? Integer . end;"))?;
    let session_meld =
        find_meld_with_tile(session.tree(), session.tree().root(), TileText::from("?"))
            .expect("a `?`-led meld");
    let inside = descendant_tiles(session.tree(), session_meld);
    for tile in ["Integer", "."] {
        assert!(
            inside.iter().any(|t| t == tile),
            "the receive-session meld keeps {tile:?}; tiles {inside:?}"
        );
    }
    Ok(())
}

#[test]
fn melder_closes_multi_hole_forms() -> Result<(), Box<dyn Error>>
{
    // The melder is correct: given a form's `≐`-connected molds, it closes a
    // multi-hole form (`def id = E ;`) with ZERO obligations — a focused unit
    // check of the melder in isolation from the molder's mold-selection.
    use gandr_surface_grammar::Regex;
    use gandr_surface_grammar::Rule;
    use gandr_surface_grammar::RuleName;
    use gandr_surface_grammar::Sort;
    use gandr_surface_grammar::TileLabel;
    use gandr_surface_parser::MoldedTile;
    use gandr_surface_syntax::MoldId;
    use gandr_theory_graphs::Assoc;
    use gandr_theory_graphs::PrecDag;
    use gandr_theory_graphs::PrecSpec;

    let mut spec = PrecSpec::new();
    let item = spec.insert("item", Assoc::Non)?;
    let atom = spec.insert("atom", Assoc::Non)?;
    let dag = PrecDag::build(&spec)?;
    let pbg = Pbg::build(dag, vec![
        Rule::new(
            RuleName("defval"),
            Sort::Item,
            item,
            Regex::seq([
                Regex::tile(TileLabel("def")),
                Regex::tile(TileLabel("id")),
                Regex::tile(TileLabel("=")),
                Regex::sort(Sort::Expression),
                Regex::tile(TileLabel(";")),
            ]),
        ),
        Rule::new(
            RuleName("num"),
            Sort::Expression,
            atom,
            Regex::tile(TileLabel("n")),
        ),
    ])?;
    let only = |label: &'static str| -> MoldId {
        let molds = pbg.candidates(TileLabel(label));
        assert_eq!(1, molds.len(), "one mold for {label}");
        molds[0]
    };
    let mut state = MeldState::new(&pbg);
    for (mold, text) in [
        ("def", "def"),
        ("id", "x"),
        ("=", "="),
        ("n", "1"),
        (";", ";"),
    ] {
        state.push(&MoldedTile::new(only(mold), TileText::from(text)));
    }
    let (tree, obligations) = state.commit_with_obligations(SourceText::from("defx=1;"))?;
    assert!(
        obligations.is_empty(),
        "the melder closes `def x = 1 ;` cleanly given the right molds"
    );
    // The whole form is one Item meld with five children.
    let root_children = children(&tree, tree.root());
    assert_eq!(1, root_children.len(), "one top-level form");
    assert_eq!(5, children(&tree, root_children[0]).len(), "def id = 1 ;");
    Ok(())
}

#[test]
fn expected_completion_names_the_next_tile_or_hole()
{
    let pbg = built();
    // An open bracket expects its closer; an unsaturated infix expects a
    // right-hand hole.
    let open = push_prefix(pbg, SourceFragment::from("( x"), TokenPrefixLen::MAX);
    let open_completion = open.expected();
    assert!(
        !bool::from(open_completion.is_complete()),
        "`( x` is incomplete"
    );
    assert!(
        open_completion
            .expected()
            .iter()
            .any(|item| matches!(item, Expected::Tile(_))),
        "an open form expects a continuing tile"
    );

    let complete = push_prefix(pbg, SourceFragment::from("x"), TokenPrefixLen::MAX);
    assert!(
        bool::from(complete.expected().is_complete()),
        "a bare atom is complete"
    );
}

/// Read a UTF-8 source fixture while retaining its path on failure.
///
/// # Specification
/// - ensures: successful reads preserve UTF-8 text, including layout.
/// - fails: a read or UTF-8 failure retains the supplied path and cause.
///
/// # Errors
/// The read failure, carrying `path`.
///
/// # Adequacy
/// - hypothesis: L3 — a committed UTF-8 fixture is compared byte-for-byte with
///   its compile-time contents; reading a directory refuses with the original
///   path and IO cause. Message context and a refusing formatter distinguish
///   error erasure and swallowed sink failures.
/// - witness: `tests::acceptance::source_inventory_and_reads_preserve_context`
#[spec(ensures: |ret| ret.as_ref().map_or_else(|error| error.path == path, |_| true))]
fn read_source(path: &Path) -> Result<String, ReadSourceError>
{
    std::fs::read_to_string(path).map_err(|source| ReadSourceError {
        path: path.to_path_buf(),
        source,
    })
}

/// The first form (any depth, pre-order) whose direct tiles include `wanted`.
///
/// # Specification
/// - ensures: returns the first pre-order Meld or Wald whose direct Tile
///   children include wanted; returns None when no such form exists.
///
///
/// # Adequacy
/// - hypothesis: L3 — a nested group containing x precedes a later definition
///   whose direct binder is also x. Exact selected direct tiles reject
///   breadth-first search, ancestor matching and reversed child order; absent
///   text and an invalid start index cover refusal. The predicate checks a
///   returned match; the witness additionally checks first-match selection.
/// - witness: `tests::acceptance::tree_readers_preserve_preorder_and_missing_nodes`
#[spec(ensures: |ret| ret.is_none_or(|found| matches!(tree.node(found).map(gandr_surface_syntax::Node::label), Some(NodeLabel::Meld(_) | NodeLabel::Wald)) && tree.children(found).any(|child| matches!(tree.node(child).map(gandr_surface_syntax::Node::label), Some(NodeLabel::Tile(_))) && tree.fragment(child).is_some_and(|fragment| <&str>::from(fragment) == <&str>::from(wanted)))))]
fn find_meld_with_tile(
    tree: &SyntaxTree<'_>,
    id: NodeIndex,
    wanted: TileText<'_>,
) -> Option<NodeIndex>
{
    let wanted = <&str>::from(wanted);
    let mut pending = vec![id];
    while let Some(next) = pending.pop() {
        if matches!(
            label_of(tree, next),
            Some(NodeLabel::Meld(_) | NodeLabel::Wald)
        ) && direct_tiles(tree, next).iter().any(|tile| tile == wanted)
        {
            return Some(next);
        }
        pending.extend(children(tree, next).into_iter().rev());
    }
    None
}

/// The texts of a form's direct tiles, left to right.
///
/// # Specification
/// - ensures: returns the fragments of direct Tile children, in child order;
///   nested tiles and layout are excluded.
///
///
/// # Adequacy
/// - hypothesis: L3 — a group nested before a later definition separates direct
///   children from descendants and depth-first from breadth-first traversal.
///   Missing indices and absent text exercise the empty boundaries.
/// - witness: `tests::acceptance::tree_readers_preserve_preorder_and_missing_nodes`
#[spec(ensures: |ret| ret.iter().map(String::as_str).eq(tree.children(id).filter(|&child| matches!(tree.node(child).map(gandr_surface_syntax::Node::label), Some(NodeLabel::Tile(_)))).map(|child| tree.fragment(child).map_or("", <&str>::from))))]
fn direct_tiles(
    tree: &SyntaxTree<'_>,
    id: NodeIndex,
) -> Vec<String>
{
    children(tree, id)
        .into_iter()
        .filter(|&child| matches!(label_of(tree, child), Some(NodeLabel::Tile(_))))
        .map(|child| text(tree, child))
        .collect()
}

/// The texts of every tile under `id` (any depth), in pre-order.
///
/// # Specification
/// - ensures: returns Tile fragments in pre-order, including id itself when it
///   is a tile; missing indices produce an empty sequence.
///
///
/// # Adequacy
/// - hypothesis: L3 — exact nested-group and later-definition tile sequences
///   expose breadth-first order, skipped children and accidental layout
///   inclusion. A tile root and an absent index cover traversal boundaries; the
///   predicate independently checks root coverage and missing-node behavior.
/// - witness: `tests::acceptance::tree_readers_preserve_preorder_and_missing_nodes`
#[spec(ensures: |ret| ret.len() <= tree.positions().filter(|&at| matches!(tree.node(at).map(gandr_surface_syntax::Node::label), Some(NodeLabel::Tile(_)))).count() && (id != tree.root() || ret.len() == tree.positions().filter(|&at| matches!(tree.node(at).map(gandr_surface_syntax::Node::label), Some(NodeLabel::Tile(_)))).count()) && (tree.node(id).is_some() || ret.is_empty()))]
fn descendant_tiles(
    tree: &SyntaxTree<'_>,
    id: NodeIndex,
) -> Vec<String>
{
    let mut out = Vec::new();
    let mut pending = vec![id];
    while let Some(next) = pending.pop() {
        if matches!(label_of(tree, next), Some(NodeLabel::Tile(_))) {
            out.push(text(tree, next));
        }
        pending.extend(children(tree, next).into_iter().rev());
    }
    out
}

/// The end offset of every piece of grout and every minted close under `id`,
/// in pre-order.
///
/// A repair's extent is only visible through what it minted: the melder
/// appends a minted end for each form it force-closes, so where those land is
/// what "bounded at the declaration boundary" means concretely.
///
/// # Specification
/// - ensures: returns span ends of Grout and `GhostClose` nodes in pre-order;
///   ordinary tiles, layout and absent indices contribute nothing.
///
///
/// # Adequacy
/// - hypothesis: L3 — malformed declarations followed by valid definitions
///   expose repair positions at the declaration boundary, including nested
///   forced closes; moving a repair into the next declaration changes its
///   endpoint. Root coverage and absent indices are checked independently.
/// - witness: `tests::acceptance::unclosed_definition_delimiter_does_not_absorb_following_definition`
/// - witness: `tests::acceptance::tree_readers_preserve_preorder_and_missing_nodes`
#[spec(ensures: |ret| ret.len() <= tree.positions().filter(|&at| matches!(tree.node(at).map(gandr_surface_syntax::Node::label), Some(NodeLabel::Grout { .. } | NodeLabel::GhostClose { .. }))).count() && (id != tree.root() || ret.len() == tree.positions().filter(|&at| matches!(tree.node(at).map(gandr_surface_syntax::Node::label), Some(NodeLabel::Grout { .. } | NodeLabel::GhostClose { .. }))).count()) && (tree.node(id).is_some() || ret.is_empty()))]
fn descendant_grout_ends(
    tree: &SyntaxTree<'_>,
    id: NodeIndex,
) -> Vec<ByteOffset>
{
    let mut out = Vec::new();
    let mut pending = vec![id];
    while let Some(next) = pending.pop() {
        if matches!(
            label_of(tree, next),
            Some(NodeLabel::Grout { .. } | NodeLabel::GhostClose { .. })
        ) && let Some(at) = span(tree, next)
        {
            out.push(at.end());
        }
        pending.extend(children(tree, next).into_iter().rev());
    }
    out
}

/// The mold of the first tile under `id` (pre-order) whose text is `wanted`.
///
/// # Specification
/// - ensures: returns the mold of the first pre-order Tile with wanted text;
///   missing text or an absent starting node returns None.
///
///
/// # Adequacy
/// - hypothesis: L3 — repeated x text in a nested expression and a later binder
///   has context-dependent molds; exact first-match identity detects reversed
///   or breadth-first traversal. Missing text and indices cover None.
/// - witness: `tests::acceptance::tree_readers_preserve_preorder_and_missing_nodes`
#[spec(ensures: |ret| ret.is_none_or(|mold| tree.positions().any(|at| tree.node(at).map(gandr_surface_syntax::Node::label) == Some(NodeLabel::Tile(mold)) && tree.fragment(at).is_some_and(|fragment| <&str>::from(fragment) == <&str>::from(wanted)))))]
fn mold_of(
    tree: &SyntaxTree<'_>,
    id: NodeIndex,
    wanted: TileText<'_>,
) -> Option<MoldId>
{
    let wanted = <&str>::from(wanted);
    let mut pending = vec![id];
    while let Some(next) = pending.pop() {
        if let Some(NodeLabel::Tile(mold)) = label_of(tree, next)
            && text(tree, next) == wanted
        {
            return Some(mold);
        }
        pending.extend(children(tree, next).into_iter().rev());
    }
    None
}

/// The grammar label of the first tile under `id` whose text is `wanted`.
///
/// # Specification
/// - ensures: returns the grammar label of the first matching pre-order Tile;
///   absent text, node or grammar mold returns None.
///
///
/// # Adequacy
/// - hypothesis: L3 — the first repeated token is read in expression rather
///   than binder context. Its known grammar label and sort, plus absent text
///   and indices, reject wrong mold lookup and lost optional failure.
/// - witness: `tests::acceptance::tree_readers_preserve_preorder_and_missing_nodes`
#[spec(ensures: |ret| ret.as_ref().is_none_or(|value| tree.positions().any(|at| match tree.node(at).map(gandr_surface_syntax::Node::label) { Some(NodeLabel::Tile(mold)) => tree.fragment(at).is_some_and(|fragment| <&str>::from(fragment) == <&str>::from(wanted)) && pbg.mold(mold).is_ok_and(|definition| definition.label == value.as_str()), _ => false })))]
fn mold_label_of(
    pbg: &Pbg,
    tree: &SyntaxTree<'_>,
    id: NodeIndex,
    wanted: TileText<'_>,
) -> Option<String>
{
    let mold = mold_of(tree, id, wanted)?;
    pbg.mold(mold).ok().map(|def| def.label.to_owned())
}

/// The grammar sort of the first tile under `id` whose text is `wanted`.
///
/// # Specification
/// - ensures: returns the grammar sort of the first matching pre-order Tile;
///   absent text, node or grammar mold returns None.
///
///
/// # Adequacy
/// - hypothesis: L3 — the first repeated token is read in expression rather
///   than binder context. Its known grammar label and sort, plus absent text
///   and indices, reject wrong mold lookup and lost optional failure.
/// - witness: `tests::acceptance::tree_readers_preserve_preorder_and_missing_nodes`
#[spec(ensures: |ret| ret.as_ref().is_none_or(|value| tree.positions().any(|at| match tree.node(at).map(gandr_surface_syntax::Node::label) { Some(NodeLabel::Tile(mold)) => tree.fragment(at).is_some_and(|fragment| <&str>::from(fragment) == <&str>::from(wanted)) && pbg.mold(mold).is_ok_and(|definition| definition.sort == *value), _ => false })))]
fn mold_sort_of(
    pbg: &Pbg,
    tree: &SyntaxTree<'_>,
    id: NodeIndex,
    wanted: TileText<'_>,
) -> Option<gandr_surface_grammar::Sort>
{
    let mold = mold_of(tree, id, wanted)?;
    pbg.mold(mold).ok().map(|def| def.sort)
}

/// The melder state after molding the first `upto` tokens of `src`.
///
/// # Specification
/// - ensures: molds at most upto labeled tokens, preserving layout; any exposed
///   open-form mold belongs to pbg. An oversized prefix means all tokens.
/// - panics: none.
///
///
/// # Adequacy
/// - hypothesis: L3 — every token prefix of real source compares
///   non-destructive completion with committed finalization. Empty, complete
///   and oversized prefixes reject off-by-one cutoff and dropped layout; the
///   predicate checks the observable open-form grammar identity without cloning
///   state.
/// - witness: `tests::acceptance::expected_agrees_with_committed_finalize`
/// - witness: `tests::acceptance::expected_completion_names_the_next_tile_or_hole`
#[spec(ensures: |ret| ret.open_form_mold().is_none_or(|mold| pbg.mold(mold).is_ok()))]
fn push_prefix<'pbg>(
    pbg: &'pbg Pbg,
    source: SourceFragment<'_>,
    upto: TokenPrefixLen,
) -> MeldState<'pbg>
{
    let source_text = SourceText::from(<&str>::from(source));
    let mut molder = Molder::new(pbg);
    let mut state = MeldState::new(pbg);
    for token in label(source).into_iter().take(usize::from(upto)) {
        if token.lexeme == Lexeme::Space {
            let text = token.text(&source);
            state.space(SpaceText::from(<&str>::from(text)));
        }
        else {
            molder.mold(&mut state, token, source_text);
        }
    }
    state
}
