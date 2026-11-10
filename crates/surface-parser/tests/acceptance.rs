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
use crate::common::corpus_sources;
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
    let absent = NodeIndex::at(
        gandr_surface_syntax::LayoutBlock::from(usize::MAX),
        gandr_surface_syntax::BlockOffset::from(usize::MAX),
    );
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
    let sources = corpus_sources();
    assert!(
        sources
            .iter()
            .any(|&(_, ref name)| name.as_str() == "strict/values.gandr"),
        "the strict root is inventoried"
    );
    assert!(
        sources
            .iter()
            .any(|&(_, ref name)| name.as_str() == "fixture/surface/typed-holes.gandr"),
        "the fixture families are inventoried"
    );
    assert!(
        sources
            .windows(2)
            .all(|pair| matches!(pair, [left, right] if left.1 <= right.1))
    );
    assert!(gandr_files(Path::new("strict/values.gandr/child")).is_empty());
    let strict = Path::new(env!("CARGO_MANIFEST_DIR")).join("../surface-corpus/strict");
    assert_eq!(
        read_source(&strict.join("values.gandr"))?,
        include_str!("../../surface-corpus/strict/values.gandr")
    );
    let error = read_source(&strict).expect_err("directories are not UTF-8 source files");
    assert_eq!(error.path, strict);
    assert!(
        error
            .source()
            .and_then(|cause| cause.downcast_ref::<std::io::Error>())
            .is_some_and(|cause| core::ptr::eq(&raw const error.source, &raw const *cause))
    );
    let rendered = error.to_string();
    assert!(rendered.contains(&strict.display().to_string()));
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
        "pure greeting",
        "def answer = 42;",
        "1 + 2 * 3",
        "- x",
        "pure - y",
        "def id = x;",
        "def nested = comp (id a) f;",
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

/// A declaration-local `[...]` prefix is typed syntax, not an attribute.
///
/// The binder types stay in source order even when the first binder refers to
/// the later explicit `xs` parameter. That dependency is intentionally left
/// for lowering; the parse contract is the lossless ordered surface form.
#[test]
fn declaration_prefix_telescope_preserves_forward_reference_order() -> Result<(), Box<dyn Error>>
{
    let source = include_str!(
        "acceptance/fixtures/declaration-prefix-telescope-preserves-forward-reference-order.gandr"
    );
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
    let source = include_str!(
        "acceptance/unformatted/empty-prefix-does-not-change-ordinary-attribute-spelling.gandr"
    );
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
        (1, 1),
        (
            tiles.iter().filter(|tile| tile.as_str() == "@[").count(),
            tiles.iter().filter(|tile| tile.as_str() == "[").count()
        ),
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
    let source = include_str!(
        "acceptance/unformatted/malformed-prefix-recovers-at-the-next-declaration.gandr"
    );
    let result = parse(built(), SourceText::from(source))?;
    assert!(
        !bool::from(result.is_clean()),
        "the malformed prefix retains a recovery obligation"
    );
    let good = find_meld_with_tile(result.tree(), result.tree().root(), TileText::from("good"))
        .expect("the later valid definition survives prefix recovery");
    assert_eq!(
        "def good[B : Type](y : Type) -> Type { pure y }",
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
fn value_statement_uses_let_keyword() -> Result<(), Box<dyn Error>>
{
    let pbg = built();
    let written = [
        "def use() -> -F Integer { let value = expression; pure value }",
        "def use() -> -F Integer { let value : Integer = expression; pure value }",
        "def use() -> -F Integer { let *{a, b} = expression; pure a }",
    ];
    for src in written {
        let result = parse(pbg, SourceText::from(src))?;
        assert!(
            bool::from(result.is_clean()),
            "`let PAT (: A)? = E;` molds clean in {src:?}; obligations: {:?}",
            result
                .obligations()
                .iter()
                .map(|obligation| obligation.class)
                .collect::<Vec<_>>()
        );
    }
    Ok(())
}

#[test]
fn retired_binding_spellings_require_repair() -> Result<(), Box<dyn Error>>
{
    let pbg = built();
    for src in [
        "def bind() -> -F Integer { run value <- action; pure value }",
        "def bind() -> -F Integer { run value : -F Integer <- action; pure value }",
        "let value <- action;",
        "value <- action;",
    ] {
        let result = parse(pbg, SourceText::from(src))?;
        assert!(
            !bool::from(result.is_clean()),
            "the retired binding spelling {src:?} must require repair"
        );
    }
    Ok(())
}

#[test]
fn eliminator_answer_types_mold_clean() -> Result<(), Box<dyn Error>>
{
    // The optional `-> T` slot sits after the scrutinee on both check-only
    // eliminators, on the nested `else if` tail as well as the head, and past
    // the reserved `with` view on `match`. The bare spellings are unchanged.
    let pbg = built();
    let annotated = [
        "if flag -> -F Integer { pure 1 } else { pure 2 }",
        "if flag -> -F Integer { pure 1 } else if other -> -F Integer { pure 2 } else { pure 3 }",
        "if flag { pure 1 } else if other -> -F Integer { pure 2 } else { pure 3 }",
        "match subject -> -F Integer { | Inl(x) => pure x | Inr(y) => pure y }",
        "match subject with view -> -F Integer { | Inl(x) => pure x | Inr(y) => pure y }",
        "match subject -> -F Integer { }",
        "if flag -> +U[1] (-F Integer) -> -F Integer { pure f } else { pure g }",
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
        "if flag { pure 1 } else { pure 2 }",
        "match subject { | Inl(x) => pure x | Inr(y) => pure y }",
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
    let rejected = ["if flag { pure 1 } -> -F Integer else { pure 2 }"];
    for src in rejected {
        let result = parse(pbg, SourceText::from(src))?;
        assert!(
            !bool::from(result.is_clean()),
            "an answer type outside its slot must require repair in {src:?}"
        );
    }
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
        include_str!("acceptance/fixtures/circuit-block-form-molds-zero-obligation-1.gandr"),
        // The first stateful wheel.
        include_str!("acceptance/fixtures/circuit-block-form-molds-zero-obligation-2.gandr"),
        // The sugar ladder's named-port normal form, including `()` and `_`.
        include_str!("acceptance/fixtures/circuit-block-form-molds-zero-obligation-3.gandr"),
        // Occurrence labels and the pinned-endpoint binder.
        include_str!("acceptance/fixtures/circuit-block-form-molds-zero-obligation-4.gandr"),
        // The invertible face, and the reserved reversible glyph.
        "theory I where { rule involutive : (b : Bit) <=> (c : Bit); }",
        "theory R where { oper negate : (b : Bit) <-> (c : Bit); }",
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
    let source =
        "codata S : Type where { head : Nat; oper tail : (s : S) --> S; rule : head ==> head; }";
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

/// A data-spelled `oper` inside `theory` molds as one member so its localized
/// decline cannot consume the next ruled judgment.
#[test]
fn theory_data_oper_decline_region_molds_zero_obligation() -> Result<(), Box<dyn Error>>
{
    let source = r#"theory Theory where { sort Nat : Type; oper add(m : Nat, n : Nat) -> Nat; oper succ : (n : Nat) --> Nat; }"#;
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
/// `=>`, a `let` statement's `=`, and the `<=` / `==` comparisons all still
/// mold exactly as before. This is the parser half of the lexical check; the
/// labeler half is
/// `label::tests::a_run_is_one_token_cut_only_at_whitespace_and_delimiters`.
#[test]
fn circuit_arrows_leave_the_shorter_tiles_alone() -> Result<(), Box<dyn Error>>
{
    let pbg = built();
    let unchanged: &[&str] = &[
        "match x { | A => 1 | B => 2 }",
        "def bind() -> -F Integer { let value = action; pure value }",
        "def le() -> -F Boolean { return a <= b }",
        "def eq() -> -F Boolean { return a == b }",
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
        include_str!("acceptance/fixtures/circuit-block-form-molds-zero-obligation-2.gandr"),
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
    // sugar ladder's bare rungs stay available inside a `theory` block, where the
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
            "theory S where { data Zero : Nat; data Succ : Nat --> Nat; oper add : (Nat, Nat) --> Nat; }",
        ),
    )?;
    assert!(
        bool::from(member.is_clean()),
        "the bare-sort rungs stay available as `theory` members"
    );
    Ok(())
}

/// The circuit form's **contextual** leads still bind as ordinary names.
///
/// Only the two item-position leads (`theory` and `oper`) reserve globally. The
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
        "def use() -> -F Integer { let node = 1; pure node }",
        "def project(sort : Integer) -> -F Integer { return sort }",
        "def record = *{ node = 1, feed = 2 };",
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
    // matters: inside a `theory` block, the positions where a member's *typed*
    // ports sit are past the member lead's slot, so a type variable spelled
    // `sort` molds as a type there.
    let inside: &[&str] = &[
        "theory S where { oper f : (a : sort) --> (b : Nat); sort Bit : Type; }",
        "theory S where { rule r : (rule p : sort ==> other, data x : Nat) ==> (z : Nat); }",
        "theory S where { oper f : node --> Nat; }",
        "theory S where { oper f : (a : feed) --> (b : Nat); }",
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
/// linearity refusal downstream is reachable from source. Every `theory` member
/// is `;`-terminated: after a member's trailing sort hole only `;` is
/// admissible, which never competes with hole content, so the member can no
/// longer collapse into one repaired region.
#[test]
fn a_repeated_port_name_application_molds_clean() -> Result<(), Box<dyn Error>>
{
    let pbg = built();
    let cases: &[&str] = &[
        // The headline shape: one wire consumed twice in a redex line.
        include_str!(
            "acceptance/fixtures/a-repeated-port-name-application-molds-clean-cases.gandr"
        ),
        // The same reading with distinct names, and the sugar ladder's
        // unnamed-port rungs.
        include_str!("acceptance/fixtures/a-repeated-port-name-application-molds-clean-1.gandr"),
        // A body-less rule member ahead of the closing brace.
        include_str!("acceptance/fixtures/a-repeated-port-name-application-molds-clean-2.gandr"),
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
    // member's lead. Members on their own lines are separated by their
    // column, so the two share a line here.
    let unterminated = parse(
        pbg,
        SourceText::from(include_str!(
            "acceptance/unformatted/a-repeated-port-name-application-molds-clean-unterminated.gandr"
        )),
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
        include_str!(
            "acceptance/unformatted/a-blank-line-after-a-terminated-member-molds-clean-cases.gandr"
        ),
        include_str!(
            "acceptance/unformatted/a-blank-line-after-a-terminated-member-molds-clean-1.gandr"
        ),
        include_str!(
            "acceptance/unformatted/a-blank-line-after-a-terminated-member-molds-clean-2.gandr"
        ),
        include_str!(
            "acceptance/unformatted/a-blank-line-after-a-terminated-member-molds-clean-3.gandr"
        ),
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

/// A `theory` block may be named with a primitive-type spelling (`theory
/// Unknown`). The labeler's uppercase-word reservation is a disambiguation
/// preference at slots where the reserved tile molds, never a ban on
/// declaration names: at a slot that admits only `type_identifier` the molder
/// falls back to the word's generic labels.
#[test]
fn a_theory_block_may_be_named_with_a_primitive_type_spelling() -> Result<(), Box<dyn Error>>
{
    let pbg = built();
    let cases: &[&str] = &[
        include_str!(
            "acceptance/fixtures/a-theory-block-may-be-named-with-a-primitive-type-spelling-cases.gandr"
        ),
        include_str!(
            "acceptance/fixtures/a-theory-block-may-be-named-with-a-primitive-type-spelling-1.gandr"
        ),
        include_str!(
            "acceptance/fixtures/a-theory-block-may-be-named-with-a-primitive-type-spelling-2.gandr"
        ),
    ];
    for &src in cases {
        let result = parse(pbg, SourceText::from(src))?;
        assert!(
            bool::from(result.is_clean()),
            "primitive-named theory block {src:?} molds clean; obligations: {:?}",
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
    let named = parse(
        pbg,
        SourceText::from("theory Unknown where { sort Nat : Type; }"),
    )?;
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

/// The corpus sources whose point is a parse error, each with the obligations
/// it owes and the source text each stands over: a pathological fixture that
/// pins a recovery is held to exactly that recovery.
const PARSE_ERRORS: &[(&str, &[(Oblig, &str)])] = &[
    (
        "fixture/pathological/modules/theory-sort-classified-by-a-keyword.gandr",
        &[(Oblig::UnmoldedTok, "type")],
    ),
    // The strays a root holds among its declarations, each refused alone
    // (#1058).
    ("fixture/pathological/modules/stray-root-child.gandr", &[
        (Oblig::UnmoldedTok, "mu"),
        (Oblig::UnmoldedTok, "\u{1}"),
        (Oblig::MissingTile, "|"),
        (Oblig::MissingTile, "=>"),
        (Oblig::MissingTile, "def"),
        (Oblig::MissingTile, "="),
        (Oblig::MissingTile, ";"),
    ]),
    // The retired constructor block, `data D(a) { C, … }`: a family's
    // members open after `where`, each on its bar.
    (
        "fixture/pathological/data/constructor-block-retired.gandr",
        &[
            (Oblig::MissingTile, ")"),
            (Oblig::MissingTile, "{"),
            (Oblig::MissingTile, ","),
        ],
    ),
];

/// The zero-obligation gate over the language's corpus: the candidate
/// pre-filter and the grammar mold **every** corpus source to a
/// globally-consistent **zero-obligation** reading — zero total obligations,
/// no named residual — but the sources [`PARSE_ERRORS`] names, each of which
/// owes exactly the obligations listed there. The corpus crate's runner
/// reports how many sources each root holds; nothing here pins the number.
#[test]
fn corpus_molds_to_zero_obligations() -> Result<(), Box<dyn Error>>
{
    let pbg = built();
    let sources = corpus_sources();
    assert!(!sources.is_empty(), "the corpus sources are present");
    let mut dirty: Vec<(String, Vec<String>)> = Vec::new();
    let mut pinned = 0_usize;
    for &(ref path, ref relative) in &sources {
        let src = read_source(path)?;
        let result = parse(pbg, SourceText::from(src.as_str()))?;
        let owed = || {
            result.obligations().iter().map(|obligation| {
                (
                    obligation.class,
                    src.get(
                        usize::from(obligation.span.start()) .. usize::from(obligation.span.end()),
                    )
                    .unwrap_or_default(),
                )
            })
        };
        let expected = PARSE_ERRORS
            .iter()
            .find(|&&(source, _)| source == relative)
            .map_or(&[][..], |&(_, owes)| owes);
        pinned = pinned.saturating_add(usize::from(!expected.is_empty()));
        if !owed().eq(expected.iter().copied()) {
            dirty.push((
                relative.clone(),
                owed()
                    .map(|(class, written)| format!("{class:?} @ {written:?}"))
                    .collect(),
            ));
        }
    }
    assert!(
        dirty.is_empty(),
        "every corpus source molds to zero obligations, or to exactly the ones its pin \
         names; residual: {dirty:?}"
    );
    assert_eq!(
        pinned,
        PARSE_ERRORS.len(),
        "every pinned parse error names a corpus source"
    );
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

/// #1391: a definition's missing `}` is a ghost brace past the last token its
/// body writes, not at the `{` that opens the body.
#[test]
fn a_missing_brace_stands_past_the_body_it_closes_1391() -> Result<(), Box<dyn Error>>
{
    let pbg = built();
    let path = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/unclosed-body.gandr");
    let src = read_source(&path)?;
    let result = parse(pbg, SourceText::from(src.as_str()))?;
    let tree = result.tree();
    let ghosts: Vec<(usize, usize)> = tree
        .positions()
        .filter_map(|position| {
            let node = tree.node(position)?;
            matches!(node.label(), NodeLabel::GhostClose { .. }).then(|| {
                (
                    usize::from(node.span().start()),
                    usize::from(node.span().end()),
                )
            })
        })
        .collect();
    let end = src.trim_end().len();
    assert_eq!(ghosts, [(end, end)], "one ghost brace, past `return n + 1`");
    Ok(())
}

#[test]
fn mixed_set_precedence_requires_obligation_and_commits() -> Result<(), Box<dyn Error>>
{
    // The set surface is split into pairwise-incomparable union and
    // lazy-product groups. A mixed set chain such as `A & B | C` therefore
    // requires explicit parentheses. The current recovery path's exact repair
    // class and span are incidental; the stable contract is non-clean parsing
    // with a committed tree.
    let pbg = built();
    let result = parse(pbg, SourceText::from("def t : A & B | C;"))?;
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
        ("pure 1 +", Oblig::MissingMeld),
        // A stray run the grammar has no tile for.
        ("def x = 1 ′ 2;", Oblig::UnmoldedTok),
        // An unterminated string force-closes.
        ("def x = \"open", Oblig::MissingTile),
        // A tile standing where its form's earlier tiles are absent: an `=`
        // after a closed signature begins a partial value form whose head is
        // missing, never a clean one.
        ("def s : Integer ; = s;", Oblig::MissingTile),
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

/// A keyword written where a declaration's classifier belongs stands in the
/// classifier slot as an unmolded token: the member stays the member and the
/// block stays whole, and the parse owes one obligation, at the keyword.
#[test]
fn a_keyword_in_a_classifier_slot_stands_there_unmolded() -> Result<(), Box<dyn Error>>
{
    let pbg = built();
    let written = include_str!(
        "acceptance/unformatted/a-keyword-in-a-classifier-slot-stands-there-unmolded-written.gandr"
    );
    let result = parse(pbg, SourceText::from(written))?;
    let start = written.find("type").ok_or("the keyword is written")?;
    assert_eq!(
        result
            .obligations()
            .iter()
            .map(|obligation| (
                obligation.class,
                usize::from(obligation.span.start()),
                usize::from(obligation.span.end())
            ))
            .collect::<Vec<_>>(),
        [(Oblig::UnmoldedTok, start, start.saturating_add(4))],
        "one obligation, over the keyword's own bytes"
    );
    let tree = result.tree();
    let [block] = *significant_children(tree, tree.root()).as_slice()
    else {
        panic!("the block is the one form of the source");
    };
    let tiles: Vec<String> = significant_children(tree, block)
        .into_iter()
        .filter(|&child| matches!(label_of(tree, child), Some(NodeLabel::Tile(_))))
        .map(|child| text(tree, child))
        .collect();
    assert_eq!(
        tiles,
        ["theory", "Magma", "where", "{", "sort", "M", ":", ";", "}"],
        "the member's terminator and the block's closer are the block's own tiles"
    );
    let spelled = parse(
        pbg,
        SourceText::from(include_str!(
            "acceptance/unformatted/a-keyword-in-a-classifier-slot-stands-there-unmolded-spelled.gandr"
        )),
    )?;
    assert!(
        bool::from(spelled.is_clean()),
        "the classifier spelled `Type` owes nothing"
    );
    Ok(())
}

/// #722, #2460: a keyword written where a declaration's name belongs stands in
/// the name slot as an unmolded token, at a top-level definition, a theory's
/// operation and a theory's rule alike, whether the keyword's own form is a
/// type (`mu`) or an expression the slot's sort admits (`drop`, `dup`,
/// `send`). The parse's first obligation lies over the keyword's own bytes
/// and the declaration after it owes nothing, where the keyword's form used to
/// open there and read the rest of the source inside it, owing a missing
/// closer at the end.
#[test]
fn a_keyword_in_a_name_slot_stands_there_unmolded_722() -> Result<(), Box<dyn Error>>
{
    let pbg = built();
    for keyword in ["mu", "drop", "dup", "send"] {
        for written in [
            format!(
                include_str!(
                    "acceptance/unformatted/a-keyword-in-a-name-slot-stands-there-unmolded-722-1.gandr"
                ),
                keyword = keyword
            ),
            format!(
                include_str!(
                    "acceptance/unformatted/a-keyword-in-a-name-slot-stands-there-unmolded-722-2.gandr"
                ),
                keyword = keyword
            ),
            format!(
                include_str!(
                    "acceptance/unformatted/a-keyword-in-a-name-slot-stands-there-unmolded-722-3.gandr"
                ),
                keyword = keyword
            ),
        ] {
            let result = parse(pbg, SourceText::from(written.as_str()))?;
            let start = written
                .find(&format!(" {keyword} :"))
                .ok_or("the keyword is written")?
                .saturating_add(1);
            let next = written
                .find("def ok")
                .ok_or("the next declaration is written")?;
            let owed: Vec<_> = result
                .obligations()
                .iter()
                .map(|obligation| {
                    (
                        obligation.class,
                        usize::from(obligation.span.start()),
                        usize::from(obligation.span.end()),
                    )
                })
                .collect();
            assert_eq!(
                owed.first().copied(),
                Some((
                    Oblig::UnmoldedTok,
                    start,
                    start.saturating_add(keyword.len())
                )),
                "{written:?} owes its first obligation over the keyword's own bytes; got {owed:?}"
            );
            assert!(
                owed.iter().all(|&(_, from, _)| from < next),
                "{written:?} owes nothing in the declaration after the keyword's; got {owed:?}"
            );
        }
    }
    let named = parse(
        pbg,
        SourceText::from(include_str!(
            "acceptance/unformatted/a-keyword-in-a-name-slot-stands-there-unmolded-722-named.gandr"
        )),
    )?;
    assert!(
        bool::from(named.is_clean()),
        "a name that is no keyword owes nothing"
    );
    Ok(())
}

/// #1090: a statement that lost its `=` closes at the next statement keyword,
/// which starts the next statement. Every obligation the parse owes lies at or
/// before that keyword. Read inside the broken statement, the keyword would
/// swallow the next statement and owe its `:` and `=` and the handler's
/// `with` after it.
#[test]
fn a_statement_keyword_starts_the_next_statement_1090() -> Result<(), Box<dyn Error>>
{
    let source = include_str!(
        "acceptance/fixtures/a-statement-keyword-starts-the-next-statement-1090.gandr"
    );
    let result = parse(built(), SourceText::from(source))?;
    let next = source
        .find("let f")
        .ok_or("the next statement is written")?;
    let owed: Vec<_> = result
        .obligations()
        .iter()
        .map(|obligation| {
            (
                obligation.class,
                usize::from(obligation.span.start()),
                usize::from(obligation.span.end()),
            )
        })
        .collect();
    assert!(!owed.is_empty(), "the statement missing its `=` owes it");
    assert!(
        owed.iter().all(|&(_, _, end)| end <= next),
        "every obligation lies at or before the next statement's keyword; got {owed:?}"
    );
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
    let source = include_str!(
        "acceptance/unformatted/unclosed-definition-delimiter-does-not-absorb-following-definition.gandr"
    );
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
        "data Good  where { }",
        "codata Good where { }",
        "module Good where { }",
        "theory Good where { }",
        "import \"good\" as good ;",
    ] {
        let source = format!(
            include_str!(
                "acceptance/unformatted/an-unclosed-delimiter-yields-to-every-declaration-family.gandr"
            ),
            survivor = survivor
        );
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

/// A `def` that lost its `=`, whose body nests applications, recovers as it
/// does at the end of the input, whatever declaration follows it.
///
/// The separator before the next declaration reads, as it stands, as an
/// operator of the sort of an expression. Its reduction against the body,
/// which reads as a type, costs an inconsistent meld. A window from inside
/// the body meets that cost, and it turns the reading of the body from types
/// to expressions. The source then recovers with 12 obligations where the
/// declaration alone recovers with 1 (#5747). Each row keeps the damaged
/// declaration, with strings, names or numbers as its arguments, and varies
/// the declaration that follows it: a bare `def`, a `def` with a
/// documentation line and an attribute, and a `data` declaration.
#[test]
fn a_declaration_recovers_as_at_the_end_whatever_follows_5747() -> Result<(), Box<dyn Error>>
{
    let documented = include_str!("acceptance/unformatted/a-documented-follower-5747.gandr");
    for (first, second) in [("\"x\"", "\"n\""), ("x", "n"), ("8", "9")] {
        let damaged = |follower: &str| {
            format!(
                include_str!(
                    "acceptance/unformatted/a-declaration-recovers-as-at-the-end-whatever-follows-5747.gandr"
                ),
                first = first,
                second = second,
                follower = follower
            )
        };
        let alone = damaged("");
        let alone = parse(built(), SourceText::from(alone.as_str()))?;
        assert_eq!(
            1,
            alone.obligations().len(),
            "the damaged declaration alone owes only its `=`"
        );
        for follower in ["def g() -> A = b;", documented, "data G where { }"] {
            let source = damaged(follower);
            let result = parse(built(), SourceText::from(source.as_str()))?;
            assert_eq!(
                alone.obligations(),
                result.obligations(),
                "the damaged declaration before {follower:?} owes what it owes alone"
            );
        }
    }
    Ok(())
}

/// A `def rec` that lost its `=` after a juxtaposed result type, whose body is
/// a `match`, recovers with its `=` alone, whatever declaration follows it.
///
/// The `match` opens a value and no type. So the result type `Prog e a` closes
/// before it, as the call `Prog(e, a)` closes at its `)`. Open under the body,
/// the type met the head of the next declaration in a window from the last
/// arm. That cost turned the ascription `Prog e a` of the arm into a call
/// form. The source then owed 6 obligations where the call form owes 1
/// (#6101).
#[test]
fn a_value_opener_ends_a_juxtaposed_type_6101() -> Result<(), Box<dyn Error>>
{
    let documented = include_str!("acceptance/unformatted/a-documented-follower-5747.gandr");
    let damaged = |follower: &str| {
        format!(
            include_str!("acceptance/unformatted/a-value-opener-ends-a-juxtaposed-type-6101.gandr"),
            follower = follower
        )
    };
    for follower in [
        "",
        "pub def g() -> A = b;",
        "def g() -> A = b;",
        documented,
        "data G where { }",
    ] {
        let source = damaged(follower);
        let result = parse(built(), SourceText::from(source.as_str()))?;
        let owed: Vec<Oblig> = result
            .obligations()
            .iter()
            .map(|obligation| obligation.class)
            .collect();
        assert_eq!(
            vec![Oblig::MissingTile],
            owed,
            "the damaged declaration before {follower:?} owes only its `=`"
        );
    }
    Ok(())
}

/// A group pattern whose first label has no dot recovers with the one
/// missing tile, and the declaration around it stays one form.
///
/// The missing `.` leaves the positional group `(rem` open, and the `=` after
/// `rem` starts the entry with a label as a fragment whose head is absent.
/// When the closer of the group ends only the fragment, the group stays open,
/// the `=` of the `let` starts a second fragment, and the declaration
/// recovers with 8 obligations and loses its name (#5795). The closer ends
/// the group as well.
#[test]
fn a_split_group_closes_at_its_written_closer_5795() -> Result<(), Box<dyn Error>>
{
    let declaration = |entries: &str| {
        format!(
            include_str!(
                "acceptance/unformatted/a-split-group-closes-at-its-written-closer-5795.gandr"
            ),
            entries = entries
        )
    };
    let whole = declaration(".rem = r, .quot = q");
    let whole = parse(built(), SourceText::from(whole.as_str()))?;
    assert!(
        bool::from(whole.is_clean()),
        "the group with both labels molds whole"
    );
    let source = declaration("rem = r, .quot = q");
    let result = parse(built(), SourceText::from(source.as_str()))?;
    let equals = source
        .find("rem =")
        .map(|at| at.saturating_add("rem ".len()))
        .ok_or("the first entry is written")?;
    let owed: Vec<(Oblig, usize)> = result
        .obligations()
        .iter()
        .map(|obligation| (obligation.class, usize::from(obligation.span.start())))
        .collect();
    assert_eq!(
        vec![(Oblig::MissingTile, equals)],
        owed,
        "the split group owes only the head of its entry with a label"
    );
    let root = result.tree().root();
    let declarations: Vec<String> = children(result.tree(), root)
        .into_iter()
        .filter(|&id| matches!(label_of(result.tree(), id), Some(NodeLabel::Meld(_))))
        .map(|id| text(result.tree(), id))
        .collect();
    assert_eq!(
        vec![source.trim_end()],
        declarations,
        "the declaration stays one form, its `let` whole"
    );
    Ok(())
}

/// A juxtaposed type whose group a dropped token tears keeps the group as
/// the operand of its application, and the declaration stays one form.
///
/// A dropped `Path` leaves `[.A = Rung]`, whose `=` opens a form of its own
/// and takes the `]`. The `)` of the group then ends the run that the `[`
/// opens, and the `(` stays on the slope with no form around it. The
/// application of `Dyad` took no operand there, so the parse owed a
/// `MissingMeld` at `Dyad ⟦⟧(`, and the declaration fell apart (#6029). The
/// call form `Dyad(` owed no such meld. A `?` dropped from a result type tears
/// the group of `Run` in the same way.
#[test]
fn a_torn_group_stays_the_operand_of_its_juxtaposition_6029() -> Result<(), Box<dyn Error>>
{
    for (source, owed) in [
        (
            include_str!(
                "acceptance/unformatted/a-torn-group-stays-the-operand-of-its-juxtaposition-6029-pair.gandr"
            ),
            1_usize,
        ),
        (
            include_str!(
                "acceptance/unformatted/a-torn-group-stays-the-operand-of-its-juxtaposition-6029-run.gandr"
            ),
            4_usize,
        ),
    ] {
        let result = parse(built(), SourceText::from(source))?;
        assert!(
            result
                .obligations()
                .iter()
                .all(|obligation| obligation.class != Oblig::MissingMeld),
            "no application of a torn group owes its operand in {source:?}: {:?}",
            result.obligations()
        );
        assert_eq!(
            owed,
            result.obligations().len(),
            "the drop owes no more than the call form owes in {source:?}: {:?}",
            result.obligations()
        );
        let root = result.tree().root();
        let declarations: Vec<String> = children(result.tree(), root)
            .into_iter()
            .filter(|&id| matches!(label_of(result.tree(), id), Some(NodeLabel::Meld(_))))
            .map(|id| text(result.tree(), id))
            .collect();
        assert_eq!(
            vec![source.trim_end()],
            declarations,
            "the declaration stays one form"
        );
    }
    Ok(())
}

/// A `def rec` that lost the `)` of its parameters keeps its reading when a
/// declaration follows it: one minted `)` before its `->`, and the declaration
/// after it whole.
///
/// The frontier of the `def rec` stays in its parameters, whose next tile can
/// be their `)`. When the close at the separator ends the `def rec` there, it
/// mints the end of the `def rec` and one more missing tile, and the `def rec`
/// falls apart into loose tiles (#5911). The separator stays in the
/// declaration, and the repair at its end mints the `)` where the rest parses.
#[test]
fn a_def_without_its_closer_keeps_its_reading_5911() -> Result<(), Box<dyn Error>>
{
    let source = include_str!(
        "acceptance/unformatted/a-def-without-its-closer-keeps-its-reading-5911.gandr"
    );
    let result = parse(built(), SourceText::from(source))?;
    let tree = result.tree();
    assert!(
        matches!(result.obligations(), [repair] if repair.class == Oblig::MissingTile),
        "the damaged `def` owes only its `)`: {:?}",
        result.obligations()
    );
    let closer = source
        .find("x : Bool")
        .map(|at| at.saturating_add("x : Bool".len()))
        .ok_or("the parameter is written")?;
    let minted: Vec<usize> = tree
        .positions()
        .filter_map(|position| tree.node(position))
        .filter(|node| matches!(node.label(), NodeLabel::GhostClose { .. }))
        .map(|node| usize::from(node.span().start()))
        .collect();
    assert_eq!(
        vec![closer],
        minted,
        "the `)` is minted after the parameter's type, before the `->`"
    );
    let declarations: Vec<String> = children(tree, tree.root())
        .into_iter()
        .filter(|&id| matches!(label_of(tree, id), Some(NodeLabel::Meld(_))))
        .map(|id| text(tree, id))
        .collect();
    let written: Vec<&str> = source.split("\n\n").map(str::trim_end).collect();
    assert_eq!(
        written, declarations,
        "each declaration stays one form, the damaged one and the one after it"
    );
    Ok(())
}

/// A form torn before a juxtaposed type ends at the next separator or
/// declaration head as it ends before the type written as a call.
///
/// The type `Stream a` spells the call `Stream(a)`, and its zero-width tile is
/// an operator that is still open when the next `;` or declaration head
/// arrives. The tile is of the sort of a type, and the `;` and the head are
/// not. The `)` of the call closes the type before them, so the meeting owes
/// no obligation either way (#6027). Each row tears one form and writes its
/// types each way: a codata field without its name, and a `def` without its
/// `=` before a `pub` declaration.
#[test]
fn a_torn_form_ends_before_a_juxtaposed_type_as_before_its_call_6027() -> Result<(), Box<dyn Error>>
{
    let field = |stream: &str| {
        format!(
            include_str!("acceptance/unformatted/a-torn-field-ends-at-its-separator-6027.gandr"),
            stream = stream
        )
    };
    let definition = |list: &str| {
        format!(
            include_str!(
                "acceptance/unformatted/a-def-without-its-equals-ends-at-the-next-head-6027.gandr"
            ),
            list = list
        )
    };
    let owed = |source: &str| -> Result<Vec<Oblig>, Box<dyn Error>> {
        Ok(parse(built(), SourceText::from(source))?
            .obligations()
            .iter()
            .map(|obligation| obligation.class)
            .collect())
    };
    for (juxtaposed, call) in [
        (field("Stream a"), field("Stream(a)")),
        (definition("List a"), definition("List(a)")),
    ] {
        let called = owed(&call)?;
        assert!(
            !called.is_empty(),
            "the torn form owes its repair: {call:?}"
        );
        assert_eq!(
            called,
            owed(&juxtaposed)?,
            "the juxtaposed type owes what its call owes: {juxtaposed:?}"
        );
    }
    Ok(())
}

/// A token left out before the group of a juxtaposed type in a binder owes
/// what the call form owes, and the intact result type owes nothing.
///
/// A `?` left out of `Run (?(Seat.Dispatch). end)` leaves the `.` of a type
/// path open in the binder. The slot below `Run` in the result type then
/// reads as the slot of an expression, and the group of `Run` read as an
/// expression. Three of its tiles each owed a repair (#6102). The call form
/// `Run(` opens a form whose slot holds a type, so it owed none. The argument
/// of a juxtaposition takes the sort of its head. Each row leaves out one
/// token and writes both types each way.
#[test]
fn a_token_left_out_before_a_juxtaposed_type_s_group_owes_what_its_call_owes_6102()
-> Result<(), Box<dyn Error>>
{
    let declaration = |binder: &str, result: &str| {
        format!(
            include_str!(
                "acceptance/unformatted/a-token-left-out-before-a-juxtaposed-type-s-group-6102.gandr"
            ),
            binder = binder,
            result = result
        )
    };
    let owed = |source: &str| -> Result<Vec<(Oblig, usize)>, Box<dyn Error>> {
        Ok(parse(built(), SourceText::from(source))?
            .obligations()
            .iter()
            .map(|obligation| (obligation.class, usize::from(obligation.span.start())))
            .collect())
    };
    for (juxtaposed, call) in [
        (
            declaration("Run ((Seat.Dispatch). end)", "Run (?(Seat.Dispatch). end)"),
            declaration("Run((Seat.Dispatch). end)", "Run(?(Seat.Dispatch). end)"),
        ),
        (
            declaration("Run (?(Seat.). end)", "Run (?(Seat.Dispatch). end)"),
            declaration("Run(?(Seat.). end)", "Run(?(Seat.Dispatch). end)"),
        ),
    ] {
        let called = owed(&call)?;
        assert!(!called.is_empty(), "the binder owes its repair: {call:?}");
        let applied = owed(&juxtaposed)?;
        assert_eq!(
            called.iter().map(|&(class, _)| class).collect::<Vec<_>>(),
            applied.iter().map(|&(class, _)| class).collect::<Vec<_>>(),
            "the juxtaposed type owes what its call owes: {juxtaposed:?}"
        );
        let arrow = juxtaposed.find("->").ok_or("the result type is written")?;
        assert!(
            applied.iter().all(|&(_, at)| at < arrow),
            "the result type owes nothing: {juxtaposed:?} owes {applied:?}"
        );
    }
    Ok(())
}

#[test]
fn malformed_input_continues_into_a_later_definition() -> Result<(), Box<dyn Error>>
{
    let source = include_str!(
        "acceptance/unformatted/malformed-input-continues-into-a-later-definition.gandr"
    );
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
    let files: Vec<PathBuf> = corpus_sources().into_iter().map(|(path, _)| path).collect();
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

/// Comments are owned by forms across the corpus without reaching an identity
/// or losing a byte: every source still reads back from its leaves in offset
/// order, and blanking every comment leaves the root digest unchanged.
#[test]
fn comments_reach_no_digest_and_lose_no_byte() -> Result<(), Box<dyn Error>>
{
    let pbg = built();
    let mut comments = 0_usize;
    let mut read_back = String::new();
    let mut blanked = String::new();
    let mut leaves: Vec<(usize, String)> = Vec::new();
    for &(ref path, _) in &corpus_sources() {
        let src = read_source(path)?;
        let result = parse(pbg, SourceText::from(src.as_str()))?;
        let tree = result.tree();
        leaves.clear();
        leaves.extend(
            tree.positions()
                .filter(|&at| {
                    tree.node(at)
                        .is_some_and(|node| bool::from(node.label().carries_text()))
                })
                .map(|at| {
                    span(tree, at).map_or((0, String::new()), |bytes| {
                        (usize::from(bytes.start()), text(tree, at))
                    })
                }),
        );
        leaves.sort_unstable();
        read_back.clear();
        for &(_, ref written) in &leaves {
            read_back.push_str(written);
        }
        assert_eq!(
            read_back,
            src,
            "{} reads back byte for byte",
            path.display()
        );
        blanked.clear();
        for token in label(SourceFragment::from(src.as_str())) {
            let start = usize::try_from(token.start)?;
            let end = usize::try_from(token.end)?;
            let written = src.get(start .. end).unwrap_or_default();
            if token.lexeme == Lexeme::Space
                && (written.starts_with("//") || written.starts_with("/*"))
            {
                comments = comments.saturating_add(1);
                blanked.extend(
                    written
                        .chars()
                        .map(|character| if character == '\n' { '\n' } else { ' ' }),
                );
            }
            else {
                blanked.push_str(written);
            }
        }
        let bare = parse(pbg, SourceText::from(blanked.as_str()))?;
        assert_eq!(
            root_digest(tree),
            root_digest(bare.tree()),
            "{}'s comments reach no digest",
            path.display()
        );
    }
    assert!(comments > 0, "the corpus writes comments");
    Ok(())
}
// A wall-clock budget measures the parser, not its predicates: under
// `anodized_panic` every `#[spec]` predicate runs inside the timed parse, so
// the enforcing lane is not a timing lane and this assertion stays out of it.
// CI's plain lane runs it by name (`mise run check:tests-plain-only`). The
// budget gates only with `GANDR_WALL_CLOCK_GATES=1`, which CI sets; without it
// the test measures and prints, since a loaded host times its load, not the
// parser.
#[cfg(not(anodized_panic))]
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
    let files: Vec<PathBuf> = corpus_sources().into_iter().map(|(path, _)| path).collect();
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
    if std::env::var_os("GANDR_WALL_CLOCK_GATES").is_none_or(|gates| gates != "1") {
        println!(
            "p99 corpus cold-parse {} ns (file {:?}) against the {P99_BUDGET_NANOS} ns budget; \
             slowest {} ns (file {:?}); not gated without GANDR_WALL_CLOCK_GATES=1",
            p99.0,
            p99.1.file_name(),
            max.0,
            max.1.file_name()
        );
        return Ok(());
    }
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
#[cfg_attr(
    dylint_lib = "quenchant_dylints",
    expect(
        linear_search_in_loop,
        reason = "bounded: `excess` holds one prefix's obligation classes, matched off one by one as a multiset"
    )
)]
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
        "fun(a) { pure a }".to_owned(),
        "if c { pure 1 } else { pure 2 }".to_owned(),
        "pure 1 +".to_owned(),
        "pure ( 1 +".to_owned(),
        read_source(&corpus_root().join("surface/string-interpolation.gandr"))?,
    ];
    let mut excess_seen = 0_usize;
    let mut excess: Vec<Oblig> = Vec::new();
    for src in &sources {
        let source = SourceFragment::from(src.as_str());
        let tokens = label(source);
        for upto in 0 ..= tokens.len() {
            let state = push_prefix(pbg, source, TokenPrefixLen::from(upto));
            let completion = state.expected();
            assert!(
                !completion
                    .obligations()
                    .iter()
                    .any(|obligation| obligation.class == Oblig::MissingTile)
                    || !bool::from(completion.is_complete()),
                "an owed tile is expected material at prefix {upto} of {src:?}"
            );
            excess.clear();
            excess.extend(
                state
                    .obligations()
                    .iter()
                    .chain(completion.obligations())
                    .map(|obligation| obligation.class),
            );
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
    let files: Vec<PathBuf> = corpus_sources().into_iter().map(|(path, _)| path).collect();
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

/// A product opens with its own sign, `*{`: a record, a record type, a module
/// signature, a pattern and a sub-record selection alike, and the retired
/// spelling `#{` owes a repair. The sum and the lazy record open with `+{`
/// and `&{`, one tile each (#4853).
#[test]
fn a_product_opens_with_its_own_sign() -> Result<(), Box<dyn Error>>
{
    let pbg = built();
    let labels = |source: &str| -> Result<Vec<String>, Box<dyn Error>> {
        let parsed = parse(pbg, SourceText::from(source))?;
        assert!(
            bool::from(parsed.is_clean()),
            "{source:?} molds clean: {:?}",
            parsed.obligations()
        );
        let tree = parsed.tree();
        Ok(tree
            .positions()
            .filter_map(|position| tree.node(position))
            .map(|node| format!("{:?}", node.label()))
            .collect())
    };
    for source in [
        "def point = *{.x = 1, .y = 2};",
        "def pair : *{Integer, Integer};",
        "module M : *{ x : Integer } where { def x = 1; }",
        "def first(p : *{Integer, Integer}) -> -F Integer { match p { | *{a, b} => return a } }",
        "def picked = r.*{ .a };",
    ] {
        labels(source)?;
        let retired = source.replace("*{", "#{");
        assert!(
            !bool::from(parse(pbg, SourceText::from(retired.as_str()))?.is_clean()),
            "the retired spelling {retired:?} owes a repair"
        );
    }
    for source in [
        "def ok = +{.ok = 1};",
        "def sum : +{ok : Integer, err : String};",
        "def lazy = &{.get => pure 1};",
    ] {
        labels(source)?;
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

    // At expression start (`pure - y`, `- y`), `-` molds prefix (unary): the
    // meld carries the operator and its single right operand (two children),
    // and the parse is clean — no missing-left obligation. The operator is
    // spaced from its operand, which `-y` would read as one name.
    for src in ["pure - y", "- y"] {
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
        ("def ho = pure ?name;", ";"),
        ("thunk { ? }", "}"),
        ("thunk { return ?seed }", "}"),
        ("? + 1", "+"),
        ("f(?, 2)", ","),
        ("def ho = pure ?;", ";"),
        ("def x = ?;", ";"),
        ("pure ?name", "name"),
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
    assert_eq!(
        open_completion.expected(),
        [Expected::Tile(")")],
        "an open bracket expects its closer"
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

/// `run` is an inline run wherever it stands — at a statement's start, in a
/// statement's expression, in a body, and in an argument list, where a
/// declaration head would otherwise close the declaration around it.
#[test]
fn run_reads_as_an_inline_run_wherever_it_stands() -> Result<(), Box<dyn Error>>
{
    let pbg = built();
    for (src, inline) in [
        (
            "def g() -> -F Integer { run f x; pure 0 }",
            [true].as_slice(),
        ),
        ("def g() -> -F Integer { let v = run f x; pure v }", &[true]),
        (
            "def g() -> -F Integer { let r = f (run h x); pure g (run f r) r }",
            &[true, true],
        ),
        ("def g() -> -F Nat { Succ (run plus n p) }", &[true]),
    ] {
        let result = parse(pbg, SourceText::from(src))?;
        assert!(
            bool::from(result.is_clean()),
            "{src:?} molds clean; obligations: {:?}",
            result.obligations()
        );
        let tree = result.tree();
        let read: Vec<bool> = tree
            .positions()
            .filter(|&node| text(tree, node) == "run")
            .filter_map(|node| match label_of(tree, node) {
                Some(NodeLabel::Tile(mold)) => pbg
                    .rule_of(mold)
                    .ok()
                    .map(|rule| rule.name == "run_expression"),
                _ => None,
            })
            .collect();
        assert_eq!(read, inline, "{src:?} reads each `run` as an inline run");
    }
    Ok(())
}
