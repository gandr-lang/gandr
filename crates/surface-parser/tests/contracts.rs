//! Contracts: the melder's paper traces, totality over arbitrary streams,
//! checkpoint resume, and the module and hole surfaces.

use core::error::Error;
use core::fmt::Write as _;

use gandr_surface_grammar::Pbg;
use gandr_surface_grammar::Regex;
use gandr_surface_grammar::Rule;
use gandr_surface_grammar::RuleName;
use gandr_surface_grammar::Sort;
use gandr_surface_grammar::TileLabel;
use gandr_surface_grammar::built_in;
use gandr_surface_parser::Checkpoint;
use gandr_surface_parser::CheckpointBytesRef;
use gandr_surface_parser::MeldState;
use gandr_surface_parser::MoldedTile;
use gandr_surface_parser::Oblig;
use gandr_surface_parser::TileText;
use gandr_surface_parser::parse;
use gandr_surface_syntax::ByteOffset;
use gandr_surface_syntax::MoldId;
use gandr_surface_syntax::NodeIndex;
use gandr_surface_syntax::NodeLabel;
use gandr_surface_syntax::SourceText;
use gandr_surface_syntax::SyntaxTree;
use gandr_theory_graphs::Assoc;
use gandr_theory_graphs::PrecDag;
use gandr_theory_graphs::PrecSpec;
use proptest::prelude::*;

use crate::common::built;
use crate::common::children;
use crate::common::label_of;
use crate::common::root_digest;
use crate::common::significant_children;
use crate::common::span;
use crate::common::text;

/// Count of tree nodes reachable from a root.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
struct ReachableNodeCount(usize);

impl From<ReachableNodeCount> for usize
{
    /// # Specification
    /// trivial.
    #[inline]
    fn from(count: ReachableNodeCount) -> Self
    {
        count.0
    }
}

/// Whether a direct tile lookup found its target.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
struct TilePresence(bool);

impl From<TilePresence> for bool
{
    /// # Specification
    /// trivial.
    #[inline]
    fn from(presence: TilePresence) -> Self
    {
        presence.0
    }
}

/// Number of grammar molds available to the fuzz strategy.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
struct MoldCount(u32);

impl From<u32> for MoldCount
{
    /// # Specification
    /// trivial.
    #[inline]
    fn from(count: u32) -> Self
    {
        Self(count)
    }
}

impl From<MoldCount> for u32
{
    /// # Specification
    /// trivial.
    #[inline]
    fn from(count: MoldCount) -> Self
    {
        count.0
    }
}

#[test]
fn module_declarations_mold_zero_obligation() -> Result<(), Box<dyn Error>>
{
    let pbg = built();
    let cases = [
        "module M { def x = 1; def y : Integer; }",
        r#"module M : #{ x: Integer, f: F Integer } {
  def x = 1;
  def f(a: Integer) -> F Integer { ret a }
}"#,
    ];
    for src in cases {
        let result = parse(pbg, SourceText::from(src))?;
        assert!(
            bool::from(result.is_clean()),
            "module source {src:?} molds clean; obligations: {:?}",
            result
                .obligations()
                .iter()
                .map(|o| o.class)
                .collect::<Vec<_>>()
        );
        assert_eq!(result.tree().grammar(), pbg.fingerprint());
        assert_eq!(
            Some(NodeLabel::Wald),
            label_of(result.tree(), result.tree().root()),
            "module source {src:?} commits to a Wald"
        );
    }
    Ok(())
}

/// Prefix type formers must keep their recursive operand inside the form.
///
/// The positive cases separate real operands from typed-hole operands and
/// exercise both a comma-separated generic argument list and a declaration
/// value. The negative cases keep a missing operand loud, including inside a
/// comma-separated list.
#[test]
fn prefix_type_formers_group_required_operands() -> Result<(), Box<dyn Error>>
{
    let pbg = built();
    let cases: [(&str, bool); 9] = [
        ("F Integer", true),
        ("U Integer", true),
        ("F ?", true),
        ("U ?", true),
        ("def suspended : U ?;", true),
        ("List(F Integer, U ?)", true),
        ("Integer -> Integer", true),
        ("F", false),
        ("List(F, U)", false),
    ];
    for (src, expected_clean) in cases {
        let result = parse(pbg, SourceText::from(src))?;
        assert_eq!(
            expected_clean,
            bool::from(result.is_clean()),
            "prefix-former source {src:?} cleanliness mismatch; obligations: {:?}",
            result.obligations()
        );
        if !expected_clean {
            assert!(
                !result.obligations().is_empty(),
                "missing prefix operand {src:?} must remain an explicit obligation"
            );
        }
    }
    Ok(())
}

#[test]
fn nested_module_members_mold_zero_obligation() -> Result<(), Box<dyn Error>>
{
    let pbg = built_in()?;
    let src = r#"module Outer : #{ before: Integer, inner: #{ answer: Integer }, after: Integer } {
  def before = 0;
  module inner : #{ answer: Integer } { def answer = 42; }
  def after = inner.answer;
}"#;
    let result = parse(&pbg, SourceText::from(src))?;
    assert!(
        bool::from(result.is_clean()),
        "nested module source must mold cleanly; obligations: {:?}",
        result
            .obligations()
            .iter()
            .map(|obligation| obligation.class)
            .collect::<Vec<_>>()
    );
    assert_eq!(
        result.tree().grammar(),
        pbg.fingerprint(),
        "nested module parse commits against the shared built-in grammar"
    );
    assert_eq!(
        Some(NodeLabel::Wald),
        label_of(result.tree(), result.tree().root())
    );
    Ok(())
}

/// A typed hole written in a pattern slot molds at `Sort::Pattern`, and one
/// written in an expression slot still molds at `Sort::Expression`.
///
/// **Cleanliness alone proves nothing here, which is the whole reason this test
/// asserts the sort.** Before the pattern-position rule existed, every source
/// below already parsed with zero obligations — the melder admitted the
/// *expression* hole into the pattern slot, so the committed tile said
/// `Expression` while the page said pattern. Nothing downstream could tell the
/// difference by looking, and a sort-directed consumer would have read a
/// pattern hole as a stray expression. So the witness is the recorded sort of
/// the `?` tile at each position, never the obligation count.
#[test]
fn holes_mold_at_the_sort_of_the_slot_they_stand_in() -> Result<(), Box<dyn Error>>
{
    let pbg = built();
    // Each case pairs a source with the sorts its `?` tiles must carry, in
    // source order.
    let cases: [(&str, &[Sort]); 6] = [
        ("def f = case c { ? => 0 };", &[Sort::Pattern]),
        ("def f = case c { ?arm => 0 };", &[Sort::Pattern]),
        ("def f = case m { Just(?) => 0 };", &[Sort::Pattern]),
        ("def f = case c { ? | ?other => 0 };", &[
            Sort::Pattern,
            Sort::Pattern,
        ]),
        ("def f = case c { ? as whole => 0 };", &[Sort::Pattern]),
        // The scrutinee's hole is an expression, the arm's is a pattern, and
        // the arm body's is an expression again — one spelling, three slots.
        ("def f = case ? { ? => ?body };", &[
            Sort::Expression,
            Sort::Pattern,
            Sort::Expression,
        ]),
    ];
    for (src, expected) in cases {
        let result = parse(pbg, SourceText::from(src))?;
        assert!(
            bool::from(result.is_clean()),
            "pattern-hole source {src:?} molds clean; obligations: {:?}",
            result
                .obligations()
                .iter()
                .map(|obligation| obligation.class)
                .collect::<Vec<_>>()
        );
        assert_eq!(
            expected,
            hole_tile_sorts(pbg, result.tree())?.as_slice(),
            "the `?` tiles of {src:?} carry the sorts of the slots they stand in"
        );
    }
    Ok(())
}

/// The grammar sort of every `?` tile in a committed tree, in source order.
///
/// # Specification
/// # Errors
/// The grammar's refusal of a mold id the tree carries.
fn hole_tile_sorts(
    pbg: &Pbg,
    tree: &SyntaxTree<'_>,
) -> Result<Vec<Sort>, Box<dyn Error>>
{
    let mut sorts = Vec::new();
    let mut pending = vec![tree.root()];
    while let Some(id) = pending.pop() {
        if let Some(NodeLabel::Tile(mold)) = label_of(tree, id)
            && text(tree, id) == "?"
        {
            sorts.push(pbg.mold(mold)?.sort);
        }
        pending.extend(children(tree, id).into_iter().rev());
    }
    Ok(sorts)
}

/// The opaque ascription `:>` parses cleanly, with an abstract type component
/// beside an ordinary value component.
///
/// This is the parse-gated witness the sealing surface lands first: the form is
/// admitted by the grammar before anything elaborates it, so the syntax and its
/// meaning arrive as separate, separately-reviewable changes.
#[test]
fn an_opaque_module_ascription_parses_cleanly() -> Result<(), Box<dyn Error>>
{
    let pbg = built();
    let src = "module Counter :> #{ type T, zero : T } { def zero = 0; }";
    let result = parse(pbg, SourceText::from(src))?;
    assert!(
        bool::from(result.is_clean()),
        "an opaque ascription with an abstract type component is in the clean grammar"
    );
    Ok(())
}

/// The two ascriptions differ on their **first token** and nothing else, so a
/// transparent signature carrying the same components also parses cleanly.
///
/// The pair is what shows the discrimination is lookahead-free: one tile
/// decides it, at a fixed position, with the same body either way.
#[test]
fn a_transparent_ascription_admits_the_same_signature() -> Result<(), Box<dyn Error>>
{
    let pbg = built();
    let src = "module Counter : #{ type T, zero : T } { def zero = 0; }";
    let result = parse(pbg, SourceText::from(src))?;
    assert!(
        bool::from(result.is_clean()),
        "the same signature is admitted under transparent ascription"
    );
    Ok(())
}

/// Module nesting is **unbounded in the clean grammar**, not merely deeper than
/// it was.
///
/// The distinction is the point of the test and the reason the depths are
/// generated rather than written out. An unrolled grammar admits nesting to
/// whatever depth its unrolling was written to and recovers past it, so *some*
/// finite depth parses dirty; a recursive one has no such depth, because the
/// nested form inhabits the very sort its own body repeats. Sweeping a range
/// that straddles and far exceeds any plausible unrolling separates the two:
/// under an unrolled grammar at least one of these depths reports an
/// obligation.
#[test]
fn module_nesting_is_unbounded_in_the_clean_grammar() -> Result<(), Box<dyn Error>>
{
    let pbg = built();
    for depth in [1_usize, 2, 3, 4, 8, 16, 32] {
        let mut src = String::from("module Outer {");
        for level in 0 .. depth {
            write!(src, " module level{level} {{")?;
        }
        src.push_str(" def innermost = 1;");
        for _level in 0 .. depth {
            src.push_str(" }");
        }
        src.push_str(" }");
        let result = parse(pbg, SourceText::from(src.as_str()))?;
        assert!(
            bool::from(result.is_clean()),
            "nesting depth {depth} must parse clean, with no recovery obligation: {:?}",
            result.obligations()
        );
        assert_eq!(
            Some(NodeLabel::Wald),
            label_of(result.tree(), result.tree().root()),
            "nesting depth {depth} commits a whole tree"
        );
    }
    Ok(())
}
#[test]
fn malformed_module_member_uses_ordinary_recovery() -> Result<(), Box<dyn Error>>
{
    let pbg = built();
    let src = "module M { def bad = 1 ~ 2; def good = 1; }";
    let result = parse(pbg, SourceText::from(src))?;
    assert!(
        !bool::from(result.is_clean()),
        "a malformed module member must flag an ordinary repair obligation"
    );
    assert!(
        result.obligations().iter().any(|o| matches!(
            o.class,
            Oblig::MissingMeld | Oblig::MissingTile | Oblig::UnmoldedTok
        )),
        "module member repair should be an ordinary missing-meld/tile/unmolded obligation; got {:?}",
        result
            .obligations()
            .iter()
            .map(|o| o.class)
            .collect::<Vec<_>>()
    );
    assert!(
        result
            .obligations()
            .iter()
            .all(|o| o.class != Oblig::AmbiguousPrec),
        "malformed module member recovery must not introduce precedence ambiguity"
    );
    assert_eq!(
        Some(NodeLabel::Wald),
        label_of(result.tree(), result.tree().root()),
        "malformed module source still commits"
    );
    Ok(())
}
#[test]
fn trace_left_associates_like_figure_24() -> Result<(), Box<dyn Error>>
{
    // `n + n + n` left-associates to `((n + n) + n)`: the first `+` Reduces
    // when the second (equal, left-associative) `+` arrives.
    let pbg = arith_pbg()?;
    let tiles = stream(&pbg, &[
        TileLabel("n"),
        TileLabel("+"),
        TileLabel("n"),
        TileLabel("+"),
        TileLabel("n"),
    ]);
    let source = assembled(&tiles);
    let tree = commit_stream(&pbg, &tiles, SourceText::from(source.as_str()))?;

    let outer = sole_meld(&tree);
    assert!(bool::from(has_tile(&tree, outer, TileText::from("+"))));
    let outer_children = children(&tree, outer);
    assert_eq!(3, outer_children.len());
    // Left child is the inner `(n + n)` meld; right child is the bare atom.
    let inner = outer_children[0];
    assert!(matches!(label_of(&tree, inner), Some(NodeLabel::Meld(_))));
    assert!(bool::from(has_tile(&tree, inner, TileText::from("+"))));
    assert!(matches!(
        label_of(&tree, outer_children[2]),
        Some(NodeLabel::Tile(_))
    ));
    Ok(())
}
#[test]
fn no_obligations_on_well_formed_fragments() -> Result<(), Box<dyn Error>>
{
    let pbg = arith_pbg()?;
    for labels in [
        vec![TileLabel("n")],
        vec![
            TileLabel("n"),
            TileLabel("+"),
            TileLabel("n"),
            TileLabel("*"),
            TileLabel("n"),
        ],
        vec![
            TileLabel("n"),
            TileLabel("+"),
            TileLabel("n"),
            TileLabel("+"),
            TileLabel("n"),
        ],
        vec![
            TileLabel("("),
            TileLabel("n"),
            TileLabel("+"),
            TileLabel("n"),
            TileLabel(")"),
            TileLabel("*"),
            TileLabel("n"),
        ],
    ] {
        let mut state = MeldState::new(&pbg);
        let tiles = stream(&pbg, &labels);
        for tile in &tiles {
            state.push(tile);
        }
        assert!(
            state.obligations().is_empty(),
            "well-formed fragment {labels:?} melds without obligations"
        );
        let _tree = state.commit(SourceText::from(assembled(&tiles).as_str()))?;
    }
    Ok(())
}

/// The number of nodes reachable from `id`, proving the tree is
/// well-formed.
///
/// # Specification
/// trivial.
fn count_nodes(
    tree: &SyntaxTree<'_>,
    id: NodeIndex,
) -> ReachableNodeCount
{
    let mut total = 0_usize;
    let mut pending = vec![id];
    while let Some(next) = pending.pop() {
        total = total.saturating_add(1);
        pending.extend(children(tree, next).into_iter().rev());
    }
    ReachableNodeCount(total)
}

#[test]
fn trace_brackets_reset_precedence_like_figure_33() -> Result<(), Box<dyn Error>>
{
    // `( n + n ) * n` melds to `((n + n) * n)`: the bracket closes on its
    // matching delimiter (a `≐` step) and resets precedence, so `+` binds
    // inside the parens despite being looser than the enclosing `*`.
    let pbg = arith_pbg()?;
    let tiles = stream(&pbg, &[
        TileLabel("("),
        TileLabel("n"),
        TileLabel("+"),
        TileLabel("n"),
        TileLabel(")"),
        TileLabel("*"),
        TileLabel("n"),
    ]);
    let source = assembled(&tiles);
    let tree = commit_stream(&pbg, &tiles, SourceText::from(source.as_str()))?;

    let mul = sole_meld(&tree);
    assert!(
        bool::from(has_tile(&tree, mul, TileText::from("*"))),
        "the outer meld is the `*` term"
    );
    let mul_children = children(&tree, mul);
    assert_eq!(3, mul_children.len());
    let paren = mul_children[0];
    // The paren meld's direct tiles are `(` and `)`, enclosing the `+` meld.
    assert_eq!(direct_tiles(&tree, paren), vec![
        "(".to_owned(),
        ")".to_owned()
    ]);
    assert!(
        bool::from(has_tile(
            &tree,
            children(&tree, paren)[1],
            TileText::from("+")
        )),
        "the `+` term nests inside the parens"
    );
    Ok(())
}
#[test]
fn trace_precedence_climbs_like_figure_23() -> Result<(), Box<dyn Error>>
{
    // `n + n * n` melds to `(n + (n * n))`: Shift, then Reduce the tighter
    // `*` handle before the looser `+` — no stuck states, no grout. Atoms
    // stay bare tokens, so the `+` meld's children are `[n, +, (n * n)]`.
    let pbg = arith_pbg()?;
    let tiles = stream(&pbg, &[
        TileLabel("n"),
        TileLabel("+"),
        TileLabel("n"),
        TileLabel("*"),
        TileLabel("n"),
    ]);
    let source = assembled(&tiles);
    let tree = commit_stream(&pbg, &tiles, SourceText::from(source.as_str()))?;

    let add = sole_meld(&tree);
    assert!(matches!(label_of(&tree, add), Some(NodeLabel::Meld(_))));
    assert!(
        bool::from(has_tile(&tree, add, TileText::from("+"))),
        "the outer meld is the `+` term"
    );
    assert!(
        !bool::from(has_tile(&tree, add, TileText::from("*"))),
        "`*` binds tighter, one level down"
    );
    let add_children = children(&tree, add);
    assert_eq!(3, add_children.len());
    // The right operand is the `*` meld; the left operand is the bare atom.
    assert!(matches!(
        label_of(&tree, add_children[0]),
        Some(NodeLabel::Tile(_))
    ));
    let mul = add_children[2];
    assert!(matches!(label_of(&tree, mul), Some(NodeLabel::Meld(_))));
    assert!(
        bool::from(has_tile(&tree, mul, TileText::from("*"))),
        "the nested meld is the `*` term"
    );
    Ok(())
}

/// A synthetic arithmetic grammar: atoms, `*` (tight), `+` (loose), parens.
///
/// # Specification
/// # Errors
/// A refusal from the precedence or grammar build, which this fixed grammar
/// never meets.
fn arith_pbg() -> Result<Pbg, Box<dyn Error>>
{
    let mut spec = PrecSpec::new();
    let atom = spec.insert("atom", Assoc::Non)?;
    let mul = spec.insert("mul", Assoc::Left)?;
    let add = spec.insert("add", Assoc::Left)?;
    spec.add_edge(atom, mul)?;
    spec.add_edge(mul, add)?;
    let dag = PrecDag::build(&spec)?;
    let pbg = Pbg::build(dag, vec![
        Rule::new(
            RuleName("num"),
            Sort::Expression,
            atom,
            Regex::tile(TileLabel("n")),
        ),
        Rule::new(
            RuleName("paren"),
            Sort::Expression,
            atom,
            Regex::seq([
                Regex::tile(TileLabel("(")),
                Regex::sort(Sort::Expression),
                Regex::tile(TileLabel(")")),
            ]),
        ),
        Rule::new(
            RuleName("mul"),
            Sort::Expression,
            mul,
            Regex::seq([
                Regex::sort(Sort::Expression),
                Regex::tile(TileLabel("*")),
                Regex::sort(Sort::Expression),
            ]),
        ),
        Rule::new(
            RuleName("add"),
            Sort::Expression,
            add,
            Regex::seq([
                Regex::sort(Sort::Expression),
                Regex::tile(TileLabel("+")),
                Regex::sort(Sort::Expression),
            ]),
        ),
    ])?;
    Ok(pbg)
}
/// Push a whole stream and commit it over `source`, the text its tiles
/// assemble.
///
/// # Specification
/// # Errors
/// The melder's refusal at commit, which an assembled source never meets.
fn commit_stream<'source>(
    pbg: &Pbg,
    tiles: &[MoldedTile],
    source: SourceText<'source>,
) -> Result<SyntaxTree<'source>, Box<dyn Error>>
{
    let mut state = MeldState::new(pbg);
    for tile in tiles {
        state.push(tile);
    }
    let tree = state.commit(source)?;
    Ok(tree)
}

/// The source a stream of tiles assembles: their texts, abutting.
///
/// # Specification
/// trivial.
fn assembled(tiles: &[MoldedTile]) -> String
{
    tiles.iter().map(|tile| <&str>::from(tile.text())).collect()
}

/// Build a molded-tile stream from `(label)` pairs over `pbg`.
///
/// # Specification
/// trivial.
fn stream(
    pbg: &Pbg,
    labels: &[TileLabel],
) -> Vec<MoldedTile>
{
    labels
        .iter()
        .map(|&label| MoldedTile::new(only(pbg, label), TileText::from(label.0)))
        .collect()
}

/// The sole mold id declared for `label`.
///
/// # Specification
/// - panics: when `label` has other than one mold, so a fixture grammar that
///   breaks the premise fails its own test.
fn only(
    pbg: &Pbg,
    label: TileLabel,
) -> MoldId
{
    let molds = pbg.candidates(label);
    assert_eq!(1, molds.len(), "label {} must have one mold", label.0);
    molds[0]
}

/// The single child of the root.
///
/// # Specification
/// - panics: when the root has other than one child.
fn sole_meld(tree: &SyntaxTree<'_>) -> NodeIndex
{
    let top = children(tree, tree.root());
    assert_eq!(1, top.len(), "one top-level term");
    top[0]
}

/// Whether the direct tile children of `id` include `wanted`.
///
/// # Specification
/// trivial.
fn has_tile(
    tree: &SyntaxTree<'_>,
    id: NodeIndex,
    wanted: TileText<'_>,
) -> TilePresence
{
    let wanted = <&str>::from(wanted);
    TilePresence(direct_tiles(tree, id).iter().any(|tile| tile == wanted))
}

/// The texts of a form's direct tile children, left to right.
///
/// # Specification
/// trivial.
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

// Totality / panic-freedom over arbitrary molded-tile streams.

/// A biased tile-index strategy over the real mold table plus out-of-range
/// sentinels (boundary bias: extremes and the out-of-range edge).
///
/// # Specification
/// trivial.
fn tile_index(mold_count: MoldCount) -> impl Strategy<Value = MoldId>
{
    let mold_count = u32::from(mold_count);
    prop_oneof![
        6 => 0_u32 .. mold_count,
        1 => Just(0_u32),
        1 => Just(mold_count.saturating_sub(1)),
        2 => mold_count .. mold_count.saturating_add(8),
    ]
    .prop_map(MoldId::from)
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(256))]

    #[test]
    fn arbitrary_real_mold_streams_parse_totally(
        indices in {
            let count = match u32::try_from(built().mold_count().0) {
                | Ok(count) => count,
                | Err(_error) => u32::MAX,
            };
            prop::collection::vec(tile_index(MoldCount::from(count)), 0 .. 48)
        }
    ) {
        let pbg = built();
        let tiles: Vec<MoldedTile> = indices
            .iter()
            .map(|&mold| {
                let label = pbg.mold(mold).map_or("?", |def| def.label);
                MoldedTile::new(mold, TileText::from(label))
            })
            .collect();

        // Every push is total; finalize is a non-destructive query.
        let mut state = MeldState::new(pbg);
        for tile in &tiles {
            state.push(tile);
            let _completion = state.finalize();
        }

        // Commit yields a well-formed tree recording the grammar fingerprint.
        let obligations = state.obligations().to_vec();
        let source = assembled(&tiles);
        let tree = state
            .commit(SourceText::from(source.as_str()))
            .expect("commit is total on a well-formed slope");
        prop_assert_eq!(tree.grammar(), pbg.fingerprint());
        let reachable = count_nodes(&tree, tree.root());
        prop_assert!(usize::from(reachable) >= 1);

        // Determinism: an identical run yields an identical committed tree.
        let mut replay = MeldState::new(pbg);
        for tile in &tiles {
            replay.push(tile);
        }
        prop_assert_eq!(replay.obligations().to_vec(), obligations);
        let replayed = replay
            .commit(SourceText::from(source.as_str()))
            .expect("replay commits");
        prop_assert_eq!(root_digest(&tree), root_digest(&replayed));
    }

    /// The declaration boundary is a property of the grammar, not of the
    /// whitespace that happens to sit on it: every layout separating the two
    /// declarations must yield the same two items and confine the repair to
    /// the first of them.
    #[test]
    fn declaration_boundary_stays_stable_under_layout(
        separator in prop_oneof![
            Just(" "),
            Just("\n"),
            Just("\n\n"),
            Just(" \n "),
        ]
    ) {
        let source = format!("def bad = ( 1 ;{separator}def good = 2;");
        let boundary = ByteOffset::from(source.find("def good").unwrap_or(source.len()));
        let result = parse(built(), SourceText::from(source.as_str()))
            .expect("total parser commit");
        let significant = significant_children(result.tree(), result.tree().root());
        prop_assert_eq!(significant.len(), 2);
        prop_assert!(!bool::from(result.is_clean()));
        let damaged = span(result.tree(), significant[0]).expect("first item");
        prop_assert!(damaged.end() <= boundary);
        let survivor = span(result.tree(), significant[1]).expect("second item");
        prop_assert_eq!(survivor.start(), boundary);
        prop_assert!(
            result
                .obligations()
                .iter()
                .all(|obligation| obligation.span.end() <= boundary)
        );
    }
}

/// A bracket-heavy vocabulary strategy over the arithmetic grammar.
///
/// # Specification
/// trivial.
fn arith_label() -> impl Strategy<Value = TileLabel>
{
    prop_oneof![
        3 => Just(TileLabel("n")),
        2 => Just(TileLabel("+")),
        2 => Just(TileLabel("*")),
        2 => Just(TileLabel("(")),
        2 => Just(TileLabel(")")),
    ]
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(256))]

    #[test]
    fn arbitrary_bracket_streams_parse_totally(
        labels in prop::collection::vec(arith_label(), 0 .. 32)
    ) {
        let pbg = arith_pbg().expect("arith grammar");
        let tiles: Vec<MoldedTile> = labels
            .iter()
            .map(|&label| MoldedTile::new(only(&pbg, label), TileText::from(label.0)))
            .collect();
        let mut state = MeldState::new(&pbg);
        for tile in &tiles {
            state.push(tile);
        }
        let source = assembled(&tiles);
        let tree = state
            .commit(SourceText::from(source.as_str()))
            .expect("bracket stream commits");
        let reachable = count_nodes(&tree, tree.root());
        prop_assert!(usize::from(reachable) >= 1);
    }
}

// Checkpoint round-trip and resume-equivalence over synthesized streams.

proptest! {
    #![proptest_config(ProptestConfig::with_cases(256))]

    #[test]
    fn checkpoint_resume_equals_uninterrupted(
        labels in prop::collection::vec(arith_label(), 0 .. 24),
        split in 0_usize .. 24
    ) {
        let pbg = arith_pbg().expect("arith grammar");
        let tiles: Vec<MoldedTile> = labels
            .iter()
            .map(|&label| MoldedTile::new(only(&pbg, label), TileText::from(label.0)))
            .collect();
        let cut = split.min(tiles.len());

        // Uninterrupted run.
        let mut plain = MeldState::new(&pbg);
        for tile in &tiles {
            plain.push(tile);
        }
        let plain_obligations = plain.obligations().to_vec();
        let source = assembled(&tiles);
        let plain_tree = plain
            .commit(SourceText::from(source.as_str()))
            .expect("plain commits");

        // Checkpoint at the split, round-trip through bytes, resume.
        let mut prefix = MeldState::new(&pbg);
        for tile in tiles.get(.. cut).unwrap_or(&[]) {
            prefix.push(tile);
        }
        let checkpoint = prefix.checkpoint();
        let bytes = checkpoint.to_bytes();
        let restored = Checkpoint::from_bytes(CheckpointBytesRef::from(&bytes))
            .expect("round-trips");
        prop_assert_eq!(&restored, &checkpoint);

        let mut resumed = MeldState::resume(&pbg, &restored);
        for tile in tiles.get(cut ..).unwrap_or(&[]) {
            resumed.push(tile);
        }
        prop_assert_eq!(resumed.obligations().to_vec(), plain_obligations);
        let resumed_tree = resumed
            .commit(SourceText::from(source.as_str()))
            .expect("resumed commits");
        prop_assert_eq!(root_digest(&resumed_tree), root_digest(&plain_tree));
    }
}
