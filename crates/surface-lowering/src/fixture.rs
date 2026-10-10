//! Test fixtures: parsed and hand-built molded trees over the built-in
//! grammar.
//!
//! A source the parser accepts is the default fixture, so a witness exercises
//! the lowering over the tree the parser really produces. A hand-built tree is
//! reserved for a shape the parser never emits — a literal whose text is not
//! its lexeme, a tree molded under another grammar, a mold no table holds — and
//! names the grammar rules its tiles belong to, so it fails loudly when the
//! grammar moves.

use anodized::spec;
use gandr_surface_grammar::Pbg;
use gandr_surface_grammar::built_in;
use gandr_surface_parser::parse;
use gandr_surface_syntax::ByteOffset;
use gandr_surface_syntax::ByteSpan;
use gandr_surface_syntax::GrammarFingerprint;
use gandr_surface_syntax::MoldId;
use gandr_surface_syntax::NodeDigest;
use gandr_surface_syntax::NodeIndex;
use gandr_surface_syntax::NodeLabel;
use gandr_surface_syntax::SourceText;
use gandr_surface_syntax::StagedId;
use gandr_surface_syntax::SyntaxTree;
use gandr_surface_syntax::TreeBuilder;
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
/// - hypothesis: L3 — the predicate checks source and grammar identity; the
///   body assertion separates a clean fixture from a repaired parse. Exact
///   lowered spans observe the supplied source on finite built-in examples.
/// - witness: `lower::tests::every_minted_node_has_an_origin`
#[spec(
    ensures: |ret| ret.source() == source && ret.grammar() == pbg.fingerprint(),
)]
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
/// - hypothesis: L3 — source and grammar are checked by the predicate; the body
///   assertion requires a repair. The declaration witness observes a postfix
///   grout and its exact empty span, not every repair kind.
/// - witness: `lower::tests::a_repaired_declaration_is_refused`
#[spec(
    ensures: |ret| ret.source() == source && ret.grammar() == pbg.fingerprint(),
)]
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
///   Synthetic-origin fixtures cover zero and the saturation boundary pair;
///   ordinary malformed-literal fixtures distinguish nonempty source spans.
/// - witness: `fixture::tests::synthetic_origins_saturate_only_at_the_position_ceiling`
/// - witness: `lower::tests::a_malformed_integer_literal_is_refused`
#[spec(
    requires: start <= end,
    ensures: |ret| ret.start() == start && ret.end() == end,
)]
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
pub fn registered(name: SurfaceName<'_>) -> RegisteredAttribute
{
    let Maybe::Present((entry, _schema)) = AttributeRegistry::lookup(name)
    else {
        panic!("the fixture names a registered attribute");
    };

    entry
}

/// A distinct origin naming the node at arena position `position`.
///
/// # Specification
/// - requires: nothing; every node position is admitted.
/// - ensures: a written origin names the position, with a span starting there
///   and ending at its saturating successor.
/// - provides: distinct synthetic metadata without consulting a syntax tree.
/// - fails: never; the ceiling position has an empty span.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — zero, the ceiling predecessor and the ceiling separate a
///   fixed endpoint, ordinary increment and saturation. The observer checks
///   node identity, both endpoints and written provenance; no digest identity
///   or association with a real syntax tree is claimed.
/// - witness: `fixture::tests::synthetic_origins_saturate_only_at_the_position_ceiling`
#[spec(
    ensures: |ret| {
        ret.node() == position
            && usize::from(ret.span().start()) == usize::from(position)
            && usize::from(ret.span().end()) == usize::from(position).saturating_add(1_usize)
            && ret.provenance() == crate::origin::Provenance::Written
    },
)]
pub fn origin_at(position: NodeIndex) -> Origin
{
    let start = usize::from(position);
    let covered = span(
        ByteOffset::from(start),
        ByteOffset::from(start.saturating_add(1_usize)),
    );

    Origin::new(position, NodeDigest::from([0_u8; 32_usize]), covered)
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
    /// - hypothesis: L3 — the predicate checks the lookup grammar. Hand-built
    ///   declarations exercise the staged source and molds through an exact
    ///   lowering refusal; process-wide identity exhaustion is outside this
    ///   fixture.
    /// - witness: `lower::tests::a_malformed_integer_literal_is_refused`
    #[spec(
        ensures: |ret| ret.pbg.fingerprint() == pbg.fingerprint(),
    )]
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
    /// - hypothesis: L3 — the predicate checks the lookup grammar; a completed
    ///   foreign-grammar tree observes the independent recorded fingerprint via
    ///   the exact grammar-mismatch refusal. Identity exhaustion is not
    ///   exercised.
    /// - witness: `lower::tests::a_tree_of_another_grammar_is_refused`
    #[spec(
        ensures: |ret| ret.pbg.fingerprint() == pbg.fingerprint(),
    )]
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
    /// - hypothesis: L3 — the returned mold is checked against both table
    ///   fields. Hand-built declarations exercise repeated tile labels across
    ///   named rules and exact malformed-literal refusals; arbitrary custom
    ///   grammars are not enumerated by these built-in-grammar fixtures.
    /// - witness: `lower::tests::a_malformed_integer_literal_is_refused`
    /// - witness: `lower::tests::a_root_that_is_not_a_module_is_refused`
    #[spec(
        ensures: |ret| {
            self.pbg.rule_of(ret).is_ok_and(|held| held.name == rule.0)
                && self.pbg.mold(ret).is_ok_and(|held| held.label == label.0)
        },
    )]
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
    /// - hypothesis: L3 — the predicate separates a new parent from its
    ///   children. A hand-built declaration's malformed literal and exact
    ///   refusal span observe label, span and child placement after finishing;
    ///   this is finite fixture evidence, not a predicate over the opaque
    ///   staged graph.
    /// - witness: `lower::tests::a_malformed_integer_literal_is_refused`
    #[spec(
        ensures: |ret| !children.contains(&ret),
    )]
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
    /// - hypothesis: L3 — the predicate checks the named-pair domain without
    ///   allocating a second tree. Hand-built literal and declaration fixtures
    ///   observe the selected tile through exact lowering refusals. The finite
    ///   fixtures do not enumerate all missing pairs or invalid spans.
    /// - witness: `lower::tests::a_malformed_integer_literal_is_refused`
    /// - witness: `lower::tests::a_root_that_is_not_a_module_is_refused`
    #[spec(
        requires: u32::try_from(self.pbg.mold_count().0).is_ok_and(|count| {
            (0_u32 .. count).any(|position| {
                let mold = MoldId::from(position);
                self.pbg.rule_of(mold).is_ok_and(|held| held.name == rule.0)
                    && self.pbg.mold(mold).is_ok_and(|held| held.label == label.0)
            })
        }),
    )]
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
    /// - hypothesis: L3 — the predicate checks parent-child distinctness. A
    ///   declaration fixture with several differently labelled children
    ///   observes their placement through the malformed literal's exact
    ///   refusal; the opaque staged graph is not inspected by the predicate.
    /// - witness: `lower::tests::a_malformed_integer_literal_is_refused`
    #[spec(
        ensures: |ret| !children.contains(&ret),
    )]
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
    /// - hypothesis: L3 — the root label, span and child count are checked by
    ///   predicate. Malformed-literal and foreign-grammar fixtures observe the
    ///   root's contents and retained grammar through different exact refusals;
    ///   this does not cover every staged graph or finishing failure.
    /// - witness: `lower::tests::a_malformed_integer_literal_is_refused`
    /// - witness: `lower::tests::a_tree_of_another_grammar_is_refused`
    #[spec(
        ensures: |ret| {
            ret.node(ret.root()).is_some_and(|root| {
                root.label() == NodeLabel::Wald
                    && root.span() == at
                    && usize::from(root.child_count()) == children.len()
            })
        },
    )]
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
    /// - hypothesis: L3 — a declaration-rooted tree is refused as the wrong
    ///   module sort at its exact span, while a wald-rooted foreign-grammar
    ///   tree retains its requested fingerprint. These distinguish root
    ///   wrapping and grammar substitution on those fixtures, not arbitrary
    ///   staged graphs.
    /// - witness: `lower::tests::a_root_that_is_not_a_module_is_refused`
    /// - witness: `lower::tests::a_tree_of_another_grammar_is_refused`
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

#[cfg(test)]
mod tests
{
    use gandr_surface_syntax::NodeIndex;

    use super::origin_at;
    use crate::origin::Provenance;

    #[test]
    fn synthetic_origins_saturate_only_at_the_position_ceiling()
    {
        for (position, end) in [
            (0_usize, 1_usize),
            (usize::MAX.saturating_sub(1_usize), usize::MAX),
            (usize::MAX, usize::MAX),
        ] {
            let origin = origin_at(NodeIndex::from(position));
            assert_eq!(origin.node(), NodeIndex::from(position));
            assert_eq!(usize::from(origin.span().start()), position);
            assert_eq!(usize::from(origin.span().end()), end);
            assert_eq!(origin.provenance(), Provenance::Written);
        }
    }
}
