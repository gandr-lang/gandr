//! Test fixtures: parsed and hand-built molded trees over the built-in
//! grammar, synthetic positions, origins and spans, and the attribute
//! registry's entries.
//!
//! A source the parser accepts is the default fixture, so a witness exercises
//! the lowering over the tree the parser really produces. A hand-built tree is
//! reserved for a shape the parser never emits — a literal whose text is not
//! its lexeme, a tree molded under another grammar, a mold no table holds — and
//! names the grammar rules its tiles belong to, so it fails loudly when the
//! grammar moves.
//!
//! This crate's own tests read the module, and the `fixture` feature opens it
//! to the tests of `gandr-surface-lowering`, whose fixture adds the units it
//! lowers. A fixture panics where the test misread its source. The module
//! is built for a test or for the feature, and in each build it expects the
//! panic lints.
#![expect(
    clippy::expect_used,
    clippy::missing_panics_doc,
    clippy::panic,
    reason = "a fixture refuses loudly a source or a tree the test did not mean, and its specification states each panic"
)]

use alloc::string::String;
use alloc::vec;
use core::fmt::Write as _;

use anodized::spec;
use gandr_core_term::CoreArena;
use gandr_core_term::Value;
use gandr_core_term::ValueId;
use gandr_kernel_term::Literal;
use gandr_surface_grammar::Pbg;
use gandr_surface_grammar::built_in;
use gandr_surface_parser::parse;
use gandr_surface_syntax::BlockOffset;
use gandr_surface_syntax::ByteOffset;
use gandr_surface_syntax::ByteSpan;
use gandr_surface_syntax::GrammarFingerprint;
use gandr_surface_syntax::LayoutBlock;
use gandr_surface_syntax::MoldId;
use gandr_surface_syntax::NodeIndex;
use gandr_surface_syntax::NodeLabel;
use gandr_surface_syntax::SourceText;
use gandr_surface_syntax::StagedId;
use gandr_surface_syntax::SyntaxTree;
use gandr_surface_syntax::TreeBuilder;
use gandr_theory_levitation::THEORY_CONSTRUCTORS;
use quenchant_shape::shape::Maybe;

use crate::attribute::AttributeRegistry;
use crate::attribute::RegisteredAttribute;
use crate::origin::Origin;
use crate::resolve::SurfaceName;

/// A grammar rule, by its unique name.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Rule(pub &'static str);

/// A tile label, as the mold table spells it.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Spelled(pub &'static str);

/// The built-in grammar.
///
/// # Specification
/// trivial.
#[inline]
#[must_use]
pub fn grammar() -> Pbg
{
    built_in().expect("the built-in grammar builds")
}

/// The tree the parser builds for `source`, which it must accept cleanly.
///
/// # Specification
/// - requires: the parser accepts the source without repairs under the grammar.
/// - ensures: the returned tree retains the supplied source and grammar.
/// - provides: a clean parser-produced lowering fixture.
/// - fails: never returns a parser refusal or a repaired tree.
/// - panics: if parsing fails or reports a repair.
///
/// # Adequacy
/// - hypothesis: L3 — a clean source parses to a tree over its source and
///   grammar, and a source the parser repairs panics.
/// - witness: `fixture::tests::a_clean_source_parses_whole_and_a_broken_one_carries_its_repair`
/// - witness: `fixture::tests::a_broken_source_is_no_clean_fixture`
#[spec(
    ensures: |ret| ret.source() == source && ret.grammar() == pbg.fingerprint(),
)]
#[inline]
#[must_use]
pub fn parsed<'source>(
    pbg: &Pbg,
    source: SourceText<'source>,
) -> SyntaxTree<'source>
{
    let result = parse(pbg, source).expect("the parser reads the source");
    assert!(
        bool::from(result.is_clean()),
        "the fixture source is one the parser accepts without repair"
    );

    result.into_tree()
}

/// The tree the parser builds for `source`, which it must have repaired.
///
/// # Specification
/// - requires: parsing succeeds with at least one repair.
/// - ensures: the returned tree retains the supplied source and grammar.
/// - provides: a parser-produced fixture containing the reported repair.
/// - fails: never returns a failed parse or accepts a clean fixture.
/// - panics: if parsing fails or reports no repair.
///
/// # Adequacy
/// - hypothesis: L3 — a source the parser repairs parses to a tree over its
///   source and grammar whose reading holds the repair, and a clean source
///   panics.
/// - witness: `fixture::tests::a_clean_source_parses_whole_and_a_broken_one_carries_its_repair`
/// - witness: `fixture::tests::a_clean_source_is_no_repaired_fixture`
#[spec(
    ensures: |ret| ret.source() == source && ret.grammar() == pbg.fingerprint(),
)]
#[inline]
#[must_use]
pub fn repaired<'source>(
    pbg: &Pbg,
    source: SourceText<'source>,
) -> SyntaxTree<'source>
{
    let result = parse(pbg, source).expect("the parser reads the source");
    assert!(
        !bool::from(result.is_clean()),
        "the fixture source is one the parser had to repair"
    );

    result.into_tree()
}

/// The span from `start` to `end`.
///
/// # Specification
/// - requires: the start does not follow the end.
/// - ensures: the returned span has exactly the supplied endpoints.
/// - provides: an ordered fixture span, including an empty one.
/// - fails: never returns an inverted span.
/// - panics: if the endpoints are inverted.
///
/// # Adequacy
/// - hypothesis: L3 — exact endpoints are checked on every instrumented call.
///   Synthetic-origin fixtures cover the spans at offset zero and at the
///   position ceiling; ordinary malformed-literal fixtures distinguish nonempty
///   source spans.
/// - witness: `fixture::tests::synthetic_origins_span_one_byte_from_their_offset`
#[spec(
    requires: start <= end,
    ensures: |ret| ret.start() == start && ret.end() == end,
)]
#[inline]
#[must_use]
pub fn span(
    start: ByteOffset,
    end: ByteOffset,
) -> ByteSpan
{
    ByteSpan::new(start, end).expect("the fixture span is ordered")
}

/// The registry entry `name` spells, which must be registered.
///
/// # Specification
/// - requires: the attribute registry contains the supplied name.
/// - ensures: the entry's spelling equals the supplied spelling exactly.
/// - provides: a registered name for a lowering expectation.
/// - fails: never substitutes another name for an unknown spelling.
/// - panics: if the name is unregistered.
///
/// # Adequacy
/// - hypothesis: L3 — the spelling predicate is exercised by the four registry
///   entries used in near-miss expectations. A fixed replacement entry fails
///   the other spellings; this does not enumerate every unknown spelling.
/// - witness: `attribute::tests::a_near_misspelling_suggests_its_attribute`
#[spec(
    ensures: |ret| ret.as_ref() == name.as_ref(),
)]
#[inline]
#[must_use]
pub fn registered(name: SurfaceName<'_>) -> RegisteredAttribute
{
    let Maybe::Present((entry, _schema)) = AttributeRegistry::lookup(name)
    else {
        panic!("the fixture names a registered attribute");
    };

    entry
}

/// A synthetic position: offset `offset` of the first layout block.
///
/// # Specification
/// - requires: nothing; every offset is admitted.
/// - ensures: the position in block zero at `offset`, so distinct offsets give
///   distinct positions.
/// - provides: distinct node identities without consulting a syntax tree.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — zero and the offset ceiling each name block zero at their
///   own offset; a shifted block or offset differs.
/// - witness: `fixture::tests::synthetic_origins_span_one_byte_from_their_offset`
#[spec(ensures: |ret| usize::from(ret.block()) == 0_usize && ret.offset() == BlockOffset::from(offset))]
#[inline]
pub fn node<Offset>(offset: Offset) -> NodeIndex
where
    Offset: Copy,
    BlockOffset: From<Offset>,
{
    NodeIndex::at(LayoutBlock::default(), BlockOffset::from(offset))
}

/// A distinct origin naming the node at `position`.
///
/// # Specification
/// - requires: nothing; every node position is admitted.
/// - ensures: a written origin names the position, with a span starting at its
///   offset and ending one byte later.
/// - provides: distinct synthetic metadata without consulting a syntax tree.
/// - fails: never; an offset fits a byte offset with room for its successor.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — zero and the offset ceiling separate a fixed endpoint
///   from the largest offset. The observer checks node identity, both endpoints
///   and written provenance; no association with a real syntax tree is claimed.
/// - witness: `fixture::tests::synthetic_origins_span_one_byte_from_their_offset`
#[spec(
    ensures: |ret| {
        ret.node() == position
            && usize::from(ret.span().start()) == usize::from(position.offset())
            && usize::from(ret.span().end()) == usize::from(position.offset()).saturating_add(1_usize)
            && ret.provenance() == crate::origin::Provenance::Written
    },
)]
#[inline]
#[must_use]
pub fn origin_at(position: NodeIndex) -> Origin
{
    let start = usize::from(position.offset());
    let covered = span(
        ByteOffset::from(start),
        ByteOffset::from(start.saturating_add(1_usize)),
    );

    Origin::new(position, covered)
}

/// A molded tree built node by node, for shapes the parser never emits.
pub struct Handmade<'run, 'source>
{
    /// The grammar the tiles' molds are looked up in.
    pbg: &'run Pbg,
    /// The builder the nodes are staged in.
    builder: TreeBuilder<'source>,
}

impl<'run, 'source> Handmade<'run, 'source>
{
    /// A builder over `source`, molded under `pbg`.
    ///
    /// # Specification
    /// - requires: a fresh builder identity remains available.
    /// - ensures: mold lookup uses the supplied grammar; a finished tree
    ///   records that grammar's fingerprint and the supplied source.
    /// - provides: a fixture builder whose lookup and recorded grammars agree.
    /// - fails: never substitutes a different grammar after construction fails.
    /// - panics: if the builder identity space is exhausted.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a declaration built under the grammar reads as the
    ///   parser's tree of its text, over its source and the grammar's
    ///   fingerprint.
    /// - witness: `fixture::tests::a_handmade_tree_reads_as_the_parser_s_tree_of_its_text`
    #[spec(
        ensures: |ret| ret.pbg.fingerprint() == pbg.fingerprint(),
    )]
    #[inline]
    #[must_use]
    pub fn new(
        pbg: &'run Pbg,
        source: SourceText<'source>,
    ) -> Self
    {
        Self::under(pbg, source, pbg.fingerprint())
    }

    /// A builder over `source` whose tree records `grammar` as the grammar it
    /// was molded under, while its molds are looked up in `pbg`.
    ///
    /// # Specification
    /// - requires: a fresh builder identity remains available.
    /// - ensures: mold lookup uses the supplied grammar, independently of the
    ///   recorded fingerprint; the finished tree retains the supplied source.
    /// - provides: a fixture whose recorded grammar may intentionally differ
    ///   from the grammar used to select its molds.
    /// - fails: never replaces the requested fingerprint with the lookup one.
    /// - panics: if the builder identity space is exhausted.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a tree built under another grammar records that
    ///   grammar's fingerprint.
    /// - witness: `fixture::tests::a_handmade_tree_reads_as_the_parser_s_tree_of_its_text`
    #[spec(
        ensures: |ret| ret.pbg.fingerprint() == pbg.fingerprint(),
    )]
    #[inline]
    #[must_use]
    pub fn under(
        pbg: &'run Pbg,
        source: SourceText<'source>,
        grammar: GrammarFingerprint,
    ) -> Self
    {
        Self {
            pbg,
            builder: TreeBuilder::new(source, grammar).expect("the builder opens"),
        }
    }

    /// The mold of `rule` whose tile is labelled `label`.
    ///
    /// # Specification
    /// - requires: the mold table fits a u32 count and contains the rule-label
    ///   pair requested by the fixture.
    /// - ensures: the returned mold belongs to that rule and has that label.
    /// - provides: a mold selected by both components, not either alone.
    /// - fails: never substitutes a mold for a missing pair.
    /// - panics: if the count does not fit or the pair is missing.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the tiles of a declaration selected by their rule and
    ///   label read as the parser's.
    /// - witness: `fixture::tests::a_handmade_tree_reads_as_the_parser_s_tree_of_its_text`
    #[spec(
        ensures: |ret| {
            self.pbg.rule_of(ret).is_ok_and(|held| held.name == rule.0)
                && self.pbg.mold(ret).is_ok_and(|held| held.label == label.0)
        },
    )]
    #[inline]
    #[must_use]
    pub fn mold(
        &self,
        rule: Rule,
        label: Spelled,
    ) -> MoldId
    {
        let count = u32::try_from(self.pbg.mold_count().0).expect("the mold table is small");
        (0_u32 .. count)
            .map(MoldId::from)
            .find(|&mold| {
                let named = self.pbg.rule_of(mold).map(|held| held.name);
                let spelled = self.pbg.mold(mold).map(|held| held.label);
                named == Ok(rule.0) && spelled == Ok(label.0)
            })
            .expect("the grammar holds the fixture's mold")
    }

    /// Stage a node labelled `label` covering `at` over `children`.
    ///
    /// # Specification
    /// - requires: the span stays inside the source at character boundaries;
    ///   children are distinct, unattached nodes already staged in this
    ///   builder.
    /// - ensures: a fresh parent handle distinct from every supplied child; the
    ///   staged node retains the label, span and ordered children.
    /// - provides: raw fixture staging, including labels unknown to the
    ///   grammar.
    /// - fails: never returns a handle after the builder refuses staging.
    /// - panics: if staging fails; children accepted before a refusal may
    ///   remain attached, so a caught panic does not promise rollback.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a raw layout node keeps its label and its span at the
    ///   root.
    /// - witness: `fixture::tests::a_handmade_tree_reads_as_the_parser_s_tree_of_its_text`
    #[spec(
        ensures: |ret| !children.contains(&ret),
    )]
    #[inline]
    pub fn raw(
        &mut self,
        label: NodeLabel,
        at: ByteSpan,
        children: &[StagedId],
    ) -> StagedId
    {
        self.builder
            .node(label, at, children)
            .expect("the fixture node stages")
    }

    /// Stage a one-tile form: the tile of `rule` labelled `label`.
    ///
    /// # Specification
    /// - requires: the grammar contains the rule-label pair, its mold count
    ///   fits u32, and the span stays inside the source at character
    ///   boundaries.
    /// - ensures: a staged tile with the selected mold and span and no
    ///   children.
    /// - provides: a leaf form selected from the lookup grammar.
    /// - fails: never falls back to another rule or label.
    /// - panics: if mold selection or staging fails.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — each tile of a hand-built declaration reads as the
    ///   parser's tile at its span.
    /// - witness: `fixture::tests::a_handmade_tree_reads_as_the_parser_s_tree_of_its_text`
    #[spec(
        requires: u32::try_from(self.pbg.mold_count().0).is_ok_and(|count| {
            (0_u32 .. count).any(|position| {
                let mold = MoldId::from(position);
                self.pbg.rule_of(mold).is_ok_and(|held| held.name == rule.0)
                    && self.pbg.mold(mold).is_ok_and(|held| held.label == label.0)
            })
        }),
    )]
    #[inline]
    pub fn tile(
        &mut self,
        rule: Rule,
        label: Spelled,
        at: ByteSpan,
    ) -> StagedId
    {
        let mold = self.mold(rule, label);

        self.raw(NodeLabel::Tile(mold), at, &[])
    }

    /// Stage a form of several tiles of `rule`, labelled by its tile `label`.
    ///
    /// # Specification
    /// - requires: mold selection succeeds, the span stays inside the source at
    ///   character boundaries, and children are distinct, unattached nodes
    ///   already staged in this builder.
    /// - ensures: a fresh meld handle distinct from every child, carrying the
    ///   selected mold, span and ordered children.
    /// - provides: a composite fixture form over the supplied children.
    /// - fails: never returns a handle after selection or staging fails.
    /// - panics: if mold selection or staging fails; no rollback is promised.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a declaration melded over five tiles reads as the
    ///   parser's declaration.
    /// - witness: `fixture::tests::a_handmade_tree_reads_as_the_parser_s_tree_of_its_text`
    #[spec(
        ensures: |ret| !children.contains(&ret),
    )]
    #[inline]
    pub fn meld(
        &mut self,
        rule: Rule,
        label: Spelled,
        at: ByteSpan,
        children: &[StagedId],
    ) -> StagedId
    {
        let mold = self.mold(rule, label);

        self.raw(NodeLabel::Meld(mold), at, children)
    }

    /// Finish the tree at a root holding `children`.
    ///
    /// # Specification
    /// - requires: the span stays inside the source at character boundaries;
    ///   children are distinct, unattached nodes already staged in this
    ///   builder.
    /// - ensures: the finished root is a wald with the supplied span and
    ///   exactly the supplied number of ordered children; source and grammar
    ///   are retained.
    /// - provides: a module-shaped tree without reparsing the staged fixtures.
    /// - fails: never returns a partial result after staging or finishing
    ///   fails.
    /// - panics: if staging or finishing fails.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the module closed over a hand-built declaration reads
    ///   it as its first form.
    /// - witness: `fixture::tests::a_handmade_tree_reads_as_the_parser_s_tree_of_its_text`
    #[spec(
        ensures: |ret| {
            ret.node(ret.root()).is_some_and(|root| {
                root.label() == NodeLabel::Wald
                    && root.span() == at
                    && usize::from(root.child_count()) == children.len()
            })
        },
    )]
    #[inline]
    #[must_use]
    pub fn module(
        mut self,
        at: ByteSpan,
        children: &[StagedId],
    ) -> SyntaxTree<'source>
    {
        let root = self.raw(NodeLabel::Wald, at, children);

        self.finish(root)
    }

    /// Finish the tree at `root`.
    ///
    /// # Specification
    /// - requires: the root was minted by this builder.
    /// - ensures: the finished tree is rooted at that staged node, retaining
    ///   the staged source and grammar without imposing a module root; staged
    ///   nodes not reachable from this root are omitted.
    /// - provides: a fixture tree, including roots the lowering must refuse.
    /// - fails: never substitutes a different root after finishing fails.
    /// - panics: if finishing fails.
    /// - executable: none — the builder exposes no staged-node, source or
    ///   grammar observer, and the opaque staged handle cannot be compared to a
    ///   finished node index. Checking that correspondence would consume the
    ///   builder.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a tree finished at a declaration is rooted there and
    ///   reads as that declaration.
    /// - witness: `fixture::tests::a_handmade_tree_reads_as_the_parser_s_tree_of_its_text`
    #[inline]
    #[must_use]
    pub fn finish(
        self,
        root: StagedId,
    ) -> SyntaxTree<'source>
    {
        self.builder
            .finish(root)
            .expect("the fixture tree finishes")
    }
}

/// The constructor tree `value` holds, each constructor by its name in
/// `Theory` and each text quoted: the spelling a test compares a theory's
/// presentation against.
///
/// # Specification
/// - requires: `value` is a presentation the description route minted into
///   `arena`: constructors of `Theory` and texts.
/// - ensures: each constructor's name, then its fields in order between
///   parentheses and separated by `, `; a constructor with no field is its name
///   alone; a text between double quotes.
/// - provides: a presentation compared as one line.
/// - fails: never on a presentation.
/// - panics: at a node that is neither a constructor nor a text.
///
/// # Adequacy
/// - hypothesis: L3 — a theory's sorts, operations and laws spell node for
///   node, so a missing or a reordered field changes the line.
/// - witness: `fixture::tests::a_presentation_spells_each_constructor_and_text`
#[spec(ensures: |ret| !ret.is_empty())]
#[must_use]
#[inline]
pub fn presentation_text(
    arena: &CoreArena,
    value: ValueId,
) -> String
{
    /// One piece of the rendering.
    enum Piece
    {
        /// A value to render.
        Term(ValueId),
        /// Fixed text.
        Text(&'static str),
    }
    let mut out = String::new();
    let mut pending = vec![Piece::Term(value)];
    while let Some(piece) = pending.pop() {
        match piece {
            Piece::Text(text) => out.push_str(text),
            Piece::Term(id) => match arena.value(id) {
                Some(&Value::Constructor {
                    tag, ref fields, ..
                }) => {
                    out.push_str(
                        THEORY_CONSTRUCTORS
                            .get(usize::from(tag))
                            .copied()
                            .unwrap_or("?"),
                    );
                    if fields.is_empty() {
                        continue;
                    }
                    pending.push(Piece::Text(")"));
                    for (at, &field) in fields.iter().enumerate().rev() {
                        pending.push(Piece::Term(field));
                        if at > 0 {
                            pending.push(Piece::Text(", "));
                        }
                    }
                    pending.push(Piece::Text("("));
                },
                Some(&Value::Literal(Literal::Text(ref text))) => {
                    write!(out, "\"{}\"", AsRef::<str>::as_ref(text))
                        .expect("a string takes every write");
                },
                other => panic!("not a presentation node: {other:?}"),
            },
        }
    }
    out
}

#[cfg(test)]
mod tests
{
    use alloc::string::String;
    use alloc::vec;
    use alloc::vec::Vec;

    use gandr_core_term::CoreArena;
    use gandr_kernel_term::ConstantIndex;
    use gandr_kernel_term::ConstructorTag;
    use gandr_kernel_term::Literal;
    use gandr_kernel_term::StringLiteral;
    use gandr_theory_levitation::THEORY_CONSTRUCTORS;

    use super::node;
    use super::origin_at;
    use super::presentation_text;
    use crate::origin::Provenance;

    #[test]
    fn synthetic_origins_span_one_byte_from_their_offset()
    {
        let ceiling = usize::try_from(u32::MAX).unwrap();
        for offset in [0_usize, ceiling] {
            let position = node(offset);
            let start = offset;
            assert_eq!(usize::from(position.block()), 0);
            assert_eq!(usize::from(position.offset()), start);
            let origin = origin_at(position);
            assert_eq!(origin.node(), position);
            assert_eq!(usize::from(origin.span().start()), start);
            assert_eq!(usize::from(origin.span().end()), start.saturating_add(1));
            assert_eq!(origin.provenance(), Provenance::Written);
        }
    }

    #[test]
    fn a_presentation_spells_each_constructor_and_text()
    {
        let mut arena = CoreArena::new();
        let family = ConstantIndex::from(0_usize);
        let tag = |name: &str| {
            ConstructorTag::from(
                THEORY_CONSTRUCTORS
                    .iter()
                    .position(|&held| held == name)
                    .expect("a constructor of `Theory`"),
            )
        };
        let end = arena.value_constructor_of(family, Vec::new(), tag("End"), Vec::new());
        let name = arena.value_literal(Literal::Text(StringLiteral::new(String::from("Nat"))));
        let sort =
            arena.value_constructor_of(family, Vec::new(), tag("Sort"), vec![name, end, end]);
        let presents =
            arena.value_constructor_of(family, Vec::new(), tag("Presents"), vec![sort, end]);
        assert_eq!(
            presentation_text(&arena, presents),
            r#"Presents(Sort("Nat", End, End), End)"#,
            "each field in order between parentheses, a text quoted"
        );
        assert_eq!(
            presentation_text(&arena, end),
            "End",
            "a constructor with no field is its name alone"
        );
    }

    /// A clean source parses to a tree over that source and grammar, and a
    /// broken one to such a tree whose root reads the parser's repair.
    #[test]
    fn a_clean_source_parses_whole_and_a_broken_one_carries_its_repair()
    {
        use gandr_surface_syntax::SourceText;

        use super::grammar;
        use super::parsed;
        use super::repaired;
        use crate::form::Pieces;
        use crate::form::read_pieces;

        let pbg = grammar();
        let clean = SourceText::from("def a = 3;");
        let tree = parsed(&pbg, clean);
        assert_eq!((tree.source(), tree.grammar()), (clean, pbg.fingerprint()));
        let broken = SourceText::from("def x ;");
        let tree = repaired(&pbg, broken);
        assert_eq!((tree.source(), tree.grammar()), (broken, pbg.fingerprint()));
        let mut root = Pieces::new();
        read_pieces(&pbg, &tree, tree.root(), &mut root).unwrap();
        let declaration = root.pieces.first().unwrap().placed();
        let mut read = Pieces::new();
        read_pieces(&pbg, &tree, declaration.node, &mut read).unwrap();
        assert!(
            [root.repair, read.repair]
                .iter()
                .any(|repair| matches!(*repair, quenchant_shape::shape::Maybe::Present(_))),
            "the root or the declaration reads the repair"
        );
    }

    /// A source the parser repairs is no clean fixture.
    #[test]
    #[should_panic(expected = "repair")]
    fn a_broken_source_is_no_clean_fixture()
    {
        let _tree = super::parsed(
            &super::grammar(),
            gandr_surface_syntax::SourceText::from("def x ;"),
        );
    }

    /// A source the parser accepts whole is no repaired fixture.
    #[test]
    #[should_panic(expected = "repair")]
    fn a_clean_source_is_no_repaired_fixture()
    {
        let _tree = super::repaired(
            &super::grammar(),
            gandr_surface_syntax::SourceText::from("def a = 3;"),
        );
    }

    /// A declaration built by hand reads as the one the parser builds for its
    /// text, under the module the builder closes; finished at the declaration
    /// it is rooted there; a builder under another grammar records it, and a
    /// raw node keeps its label.
    #[test]
    fn a_handmade_tree_reads_as_the_parser_s_tree_of_its_text()
    {
        use gandr_surface_syntax::ByteOffset;
        use gandr_surface_syntax::ByteSpan;
        use gandr_surface_syntax::GrammarFingerprint;
        use gandr_surface_syntax::NodeLabel;
        use gandr_surface_syntax::SourceText;
        use gandr_surface_syntax::StagedId;
        use gandr_surface_syntax::SyntaxTree;

        use super::Handmade;
        use super::Rule;
        use super::Spelled;
        use super::grammar;
        use super::parsed;
        use super::span;
        use crate::form::Piece;
        use crate::form::Pieces;
        use crate::form::read_pieces;

        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));
        let pbg = grammar();
        let text = SourceText::from("def a = 3 ;");
        let declaration = |made: &mut Handmade<'_, 'static>| -> StagedId {
            let keyword = made.tile(Rule("def_value"), Spelled("def"), at(0_usize, 3_usize));
            let name = made.tile(
                Rule("def_value"),
                Spelled("identifier"),
                at(4_usize, 5_usize),
            );
            let equals = made.tile(Rule("def_value"), Spelled("="), at(6_usize, 7_usize));
            let body = made.tile(
                Rule("number.expression"),
                Spelled("number"),
                at(8_usize, 9_usize),
            );
            let close = made.tile(Rule("def_value"), Spelled(";"), at(10_usize, 11_usize));
            made.meld(Rule("def_value"), Spelled("def"), at(0_usize, 11_usize), &[
                keyword, name, equals, body, close,
            ])
        };
        let pieces = |tree: &SyntaxTree<'_>, root: bool| -> Vec<(bool, ByteSpan)> {
            let mut held = tree.root();
            if root {
                let mut read = Pieces::new();
                read_pieces(&pbg, tree, held, &mut read).unwrap();
                held = read.pieces.first().unwrap().placed().node;
            }
            let mut read = Pieces::new();
            read_pieces(&pbg, tree, held, &mut read).unwrap();
            read.pieces
                .iter()
                .map(|piece| (matches!(*piece, Piece::Tile { .. }), piece.placed().span))
                .collect()
        };
        let mut made = Handmade::new(&pbg, text);
        let staged = declaration(&mut made);
        let module = made.module(at(0_usize, 11_usize), &[staged]);
        assert_eq!(
            (module.source(), module.grammar()),
            (text, pbg.fingerprint())
        );
        assert_eq!(
            pieces(&module, true),
            pieces(&parsed(&pbg, text), true),
            "the hand-built declaration reads as the parsed one"
        );
        let mut made = Handmade::new(&pbg, text);
        let staged = declaration(&mut made);
        let finished = made.finish(staged);
        assert_eq!(
            pieces(&finished, false),
            pieces(&module, true),
            "finished at the declaration, the tree is rooted there"
        );
        let foreign = GrammarFingerprint::from(0_u64);
        let mut made = Handmade::under(&pbg, SourceText::from("x"), foreign);
        let name = made.tile(
            Rule("identifier.expression"),
            Spelled("identifier"),
            at(0_usize, 1_usize),
        );
        assert_eq!(
            made.module(at(0_usize, 1_usize), &[name]).grammar(),
            foreign
        );
        let mut made = Handmade::new(&pbg, SourceText::from("  "));
        let space = made.raw(NodeLabel::Space, at(0_usize, 2_usize), &[]);
        let tree = made.finish(space);
        assert_eq!(
            tree.node(tree.root())
                .map(|node| (node.label(), node.span())),
            Some((NodeLabel::Space, at(0_usize, 2_usize)))
        );
    }
}
