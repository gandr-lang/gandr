//! Test fixtures: parsed and hand-built molded trees over the built-in
//! grammar.
//!
//! A source the parser accepts is the default fixture, so a witness exercises
//! the lowering over the tree the parser really produces. A hand-built tree is
//! reserved for a shape the parser never emits — a literal whose text is not
//! its lexeme, a tree molded under another grammar, a mold no table holds — and
//! names the grammar rules its tiles belong to, so it fails loudly when the
//! grammar moves.

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
/// trivial.
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
/// trivial.
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
/// trivial.
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
/// trivial.
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
/// trivial.
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
    /// trivial.
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
    /// trivial.
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
    /// trivial.
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
    /// trivial.
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
    /// trivial.
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
    /// trivial.
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
    /// trivial.
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
    /// trivial.
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
