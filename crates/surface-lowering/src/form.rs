//! The named-kind dispatch: the forms the lowering reads, how a form's
//! children split into its own tiles and its operands, and the name a
//! diagnostic writes a form as.
//!
//! # A node's kind is the grammar's, read off its mold
//!
//! A molded tree labels every form with the mold of one of its tiles, and the
//! grammar resolves that mold to the named kind its rule realises
//! (`Pbg::named_kind`). The lowering dispatches on that kind and on nothing
//! else: there is no adapter tree and no second vocabulary of node kinds, and a
//! kind the table below does not hold is a form the fragment does not admit.
//!
//! # A form's own tiles are the tiles of its own rule
//!
//! A form of several tiles is one node whose children are its own tiles and
//! the forms standing in its holes, interleaved in source order. A child tile
//! whose mold belongs to the parent's rule is one of the parent's own tiles;
//! every other child is an operand. A variant the grammar folded into another
//! form — the unit `()` and the tuple into the parenthesised expression, the
//! signature into the declaration — is told apart by its own tiles, and a
//! diagnostic names it by the folded form's own kind.

use alloc::vec::Vec;
use core::fmt;

use gandr_surface_grammar::NamedKind;
use gandr_surface_grammar::Pbg;
use gandr_surface_syntax::ByteSpan;
use gandr_surface_syntax::ClosingClass;
use gandr_surface_syntax::GroutShape;
use gandr_surface_syntax::MoldId;
use gandr_surface_syntax::Node;
use gandr_surface_syntax::NodeIndex;
use gandr_surface_syntax::NodeLabel;
use gandr_surface_syntax::SyntaxTree;
use quenchant_shape::shape::Maybe;

use crate::error::LoweringRefusal;
use crate::resolve::OperandCount;

quenchant_shape::reason_enum! {
    /// Why a cursor over a form's pieces yields no tile.
    pub mod cursor {
        /// The next piece is not the tile asked for.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// Every piece has been read.
            Exhausted,
            /// The next piece is an operand, or a tile of another label.
            Elsewhere,
        }
    }
}

quenchant_shape::reason_enum! {
    /// Why a form's children hold no repair.
    pub mod repair {
        /// The parser inserted nothing among the children.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// Every child is a tile, an operand or layout the source wrote.
            Unrepaired,
        }
    }
}

/// The name a diagnostic writes a form as: a named kind of the grammar, or a
/// form the grammar folds into one and records as an adaptation.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct FormName(&'static str);

impl FormName
{
    /// Every form name the lowering spells itself, rather than reading it off
    /// a mold.
    pub const ALL: [Self; 25_usize] = [
        Self::ROOT,
        Self::UNIT,
        Self::TUPLE,
        Self::ANNOTATION,
        Self::SIGNATURE,
        Self::FUNCTION,
        Self::RECURSIVE,
        Self::PARAMETERS,
        Self::PARAMETER,
        Self::TYPE_ABSTRACTION,
        Self::GRADE,
        Self::BLOCK,
        Self::INTERPOLATION,
        Self::ATTRIBUTE,
        Self::DECLARATION,
        Self::BIND_STATEMENT,
        Self::LET_STATEMENT,
        Self::UNPACK_STATEMENT,
        Self::LETA_STATEMENT,
        Self::RECV_STATEMENT,
        Self::ACQUIRE_STATEMENT,
        Self::RELEASE_STATEMENT,
        Self::FORK_STATEMENT,
        Self::FORK_SHARED_STATEMENT,
        Self::EXPRESSION_STATEMENT,
    ];
    /// The statement `acquire …;`, inlined into its block.
    pub const ACQUIRE_STATEMENT: Self = Self("acquire_statement");
    /// An annotation: `(e : T)`, folded into the parenthesised expression, and
    /// `run x : B <- c ;`, inlined with its statement into the block.
    pub const ANNOTATION: Self = Self("annotation_expression");
    /// One attribute `name(payload)`, folded into the attribute block.
    pub const ATTRIBUTE: Self = Self("attribute");
    /// The statement `run x <- c ;`, inlined into its block.
    pub const BIND_STATEMENT: Self = Self("bind_statement");
    /// A block's statements, inlined into the form that opens the block.
    pub const BLOCK: Self = Self("block");
    /// The declaration family `def name …`, whose tail decides its variant.
    pub const DECLARATION: Self = Self("def_value");
    /// The statement `e ;`, inlined into its block.
    pub const EXPRESSION_STATEMENT: Self = Self("expression_statement");
    /// The statement `fork !(…) { … } ;`, inlined into its block.
    pub const FORK_SHARED_STATEMENT: Self = Self("fork_shared_statement");
    /// The statement `fork (…) { … } as x ;`, inlined into its block.
    pub const FORK_STATEMENT: Self = Self("fork_statement");
    /// The function tail `(params) -> T? { … }`, folded into the declaration.
    pub const FUNCTION: Self = Self("def_function");
    /// A grade annotation `[r]`, folded into the thunk and its type.
    pub const GRADE: Self = Self("grade");
    /// An interpolation `${ e }`, folded into the string.
    pub const INTERPOLATION: Self = Self("string_interpolation");
    /// The statement `leta x = e ;`, inlined into its block.
    pub const LETA_STATEMENT: Self = Self("leta_statement");
    /// The statement `val p = e ;`, inlined into its block.
    pub const LET_STATEMENT: Self = Self("let_statement");
    /// One typed parameter `name : T`, folded into its parameter list.
    pub const PARAMETER: Self = Self("parameter");
    /// A parameter list, explicit `( … )` or implicit `@[ … ]`, folded into the
    /// declaration and the lambda.
    pub const PARAMETERS: Self = Self("parameters");
    /// The recursive tail `rec name (params) { … }`, folded into the
    /// declaration.
    pub const RECURSIVE: Self = Self("def_rec");
    /// The statement `recv …;`, inlined into its block.
    pub const RECV_STATEMENT: Self = Self("recv_statement");
    /// The statement `release …;`, inlined into its block.
    pub const RELEASE_STATEMENT: Self = Self("release_statement");
    /// The source root, which holds a module's declarations.
    pub const ROOT: Self = Self("source_file");
    /// The signature tail `: T ;`, folded into the declaration.
    pub const SIGNATURE: Self = Self("def_signature");
    /// The tuple `(a, b)`, folded into the parenthesised expression.
    pub const TUPLE: Self = Self("tuple_expression");
    /// The type abstraction `fn [T] { … }`, folded into the lambda.
    pub const TYPE_ABSTRACTION: Self = Self("type_abstraction");
    /// The empty parentheses `()`, folded into the parenthesised expression.
    pub const UNIT: Self = Self("unit");
    /// The statement `unpack … = e ;`, inlined into its block.
    pub const UNPACK_STATEMENT: Self = Self("unpack_statement");
}

impl From<NamedKind<'static>> for FormName
{
    /// The form a mold's named kind names.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(kind: NamedKind<'static>) -> Self
    {
        Self(kind.0)
    }
}

impl AsRef<str> for FormName
{
    /// The form's kind, as the grammar spells it.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn as_ref(&self) -> &str
    {
        self.0
    }
}

impl fmt::Display for FormName
{
    /// Writes the form's kind between backticks, as a diagnostic quotes it.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        write!(f, "`{}`", self.0)
    }
}

/// The label one tile carries, as its mold spells it.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct TileName(&'static str);

impl TileName
{
    /// The acquire keyword `acquire`, opening a statement.
    pub const ACQUIRE: Self = Self("acquire");
    /// The arrow `->` of a function type and of a function's result.
    pub const ARROW: Self = Self("->");
    /// The alias keyword `as` of an import.
    pub const AS: Self = Self("as");
    /// The attribute-block opener `@[`.
    pub const ATTRIBUTES: Self = Self("@[");
    /// The bang `!` marking a shared fork.
    pub const BANG: Self = Self("!");
    /// The bind arrow `<-` of a `run` statement.
    pub const BIND: Self = Self("<-");
    /// A bracket closer `]`.
    pub const BRACKET_CLOSE: Self = Self("]");
    /// A bracket opener `[`.
    pub const BRACKET_OPEN: Self = Self("[");
    /// A brace closer `}`.
    pub const BRACE_CLOSE: Self = Self("}");
    /// A brace opener `{`.
    pub const BRACE_OPEN: Self = Self("{");
    /// The colon `:` opening a signature tail, an annotation or a typed
    /// parameter.
    pub const COLON: Self = Self(":");
    /// The comma separating list members.
    pub const COMMA: Self = Self(",");
    /// The declaration keyword `def`.
    pub const DEF: Self = Self("def");
    /// The lambda keyword `fn`.
    pub const FN: Self = Self("fn");
    /// The force keyword `force`.
    pub const FORCE: Self = Self("force");
    /// The fork keyword `fork`, opening a statement.
    pub const FORK: Self = Self("fork");
    /// The equals sign `=` opening a definition tail.
    pub const EQUALS: Self = Self("=");
    /// An escape sequence inside a string's own tiles.
    pub const ESCAPE_SEQUENCE: Self = Self("escape_sequence");
    /// An identifier written as one of a form's own tiles.
    pub const IDENTIFIER: Self = Self("identifier");
    /// The import keyword `import`.
    pub const IMPORT: Self = Self("import");
    /// The interpolation opener `${`.
    pub const INTERPOLATION: Self = Self("${");
    /// The keyword `leta`, opening a statement.
    pub const LETA: Self = Self("leta");
    /// A parenthesis closer `)`.
    pub const PAREN_CLOSE: Self = Self(")");
    /// A parenthesis opener `(`.
    pub const PAREN_OPEN: Self = Self("(");
    /// A double quote opening or closing a string written among a form's own
    /// tiles.
    pub const QUOTE: Self = Self("\"");
    /// The recursion keyword `rec`.
    pub const REC: Self = Self("rec");
    /// The receive keyword `recv`, opening a statement.
    pub const RECV: Self = Self("recv");
    /// The release keyword `release`, opening a statement.
    pub const RELEASE: Self = Self("release");
    /// The returner keyword `ret`.
    pub const RET: Self = Self("ret");
    /// The bind keyword `run`, opening a statement.
    pub const RUN: Self = Self("run");
    /// The semicolon `;` closing a declaration or a statement.
    pub const SEMICOLON: Self = Self(";");
    /// A run of plain text inside a string's own tiles.
    pub const STRING_FRAGMENT: Self = Self("string_fragment");
    /// The thunk keyword `thunk`.
    pub const THUNK: Self = Self("thunk");
    /// A type identifier written as one of a form's own tiles.
    pub const TYPE_IDENTIFIER: Self = Self("type_identifier");
    /// A type variable written as one of a form's own tiles.
    pub const TYPE_VARIABLE: Self = Self("type_variable");
    /// The unpack keyword `unpack`, opening a statement.
    pub const UNPACK: Self = Self("unpack");
    /// The keyword `val`, opening a statement.
    pub const VAL: Self = Self("val");

    /// The three tiles that can name a parameter: an identifier, a type
    /// variable and a type identifier, the spellings the parameter list parses.
    pub const BINDERS: [Self; 3] = [Self::IDENTIFIER, Self::TYPE_VARIABLE, Self::TYPE_IDENTIFIER];
}

impl AsRef<str> for TileName
{
    /// The tile's label, as its mold spells it.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn as_ref(&self) -> &str
    {
        self.0
    }
}

/// What the lowering reads one named kind as.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Former
{
    /// An identifier in term position: a variable or an earlier declaration.
    Name,
    /// A number literal.
    Number,
    /// A string literal.
    Text,
    /// The parenthesised expression: the unit, a grouping, the reserved
    /// tuple or an annotation, told apart by its own tiles.
    Parenthesized,
    /// The thunk `thunk { c }`.
    Thunk,
    /// The lambda `fn (x) { c }`.
    Lambda,
    /// The returner `ret v`.
    Return,
    /// The force `force v`.
    Force,
    /// The application `c(v)`.
    Call,
    /// A bare type head: a primitive, a type identifier or a type variable.
    TypeHead,
    /// A type head applied to arguments, `Foo(A)`.
    TypeApplication,
    /// The thunk type `U C`.
    ThunkType,
    /// The returner type `F A`.
    ReturnerType,
    /// The arrow type `A -> C`.
    ArrowType,
    /// The reserved product type `A * B`.
    ProductType,
    /// A parenthesised type.
    ParenthesizedType,
    /// The declaration family `def name …`.
    Declaration,
    /// An attribute block standing on its own, decorating nothing.
    AttributeBlock,
    /// The import `import "URI" as name ;`.
    Import,
    /// Every other kind: a form the fragment does not admit.
    Unadmitted,
}

impl Former
{
    /// Every former, in declaration order.
    pub const ALL: [Self; 20_usize] = [
        Self::Name,
        Self::Number,
        Self::Text,
        Self::Parenthesized,
        Self::Thunk,
        Self::Lambda,
        Self::Return,
        Self::Force,
        Self::Call,
        Self::TypeHead,
        Self::TypeApplication,
        Self::ThunkType,
        Self::ReturnerType,
        Self::ArrowType,
        Self::ProductType,
        Self::ParenthesizedType,
        Self::Declaration,
        Self::AttributeBlock,
        Self::Import,
        Self::Unadmitted,
    ];
}

/// The named kinds the lowering reads, with the former each is read as.
pub const FORMERS: [(&str, Former); 21_usize] = [
    ("identifier", Former::Name),
    ("number", Former::Number),
    ("string", Former::Text),
    ("parenthesized_expression", Former::Parenthesized),
    ("thunk_expression", Former::Thunk),
    ("lambda_expression", Former::Lambda),
    ("ret_expression", Former::Return),
    ("force_expression", Former::Force),
    ("call_expression", Former::Call),
    ("primitive_type", Former::TypeHead),
    ("type_identifier", Former::TypeHead),
    ("type_variable", Former::TypeHead),
    ("type_application", Former::TypeApplication),
    ("u_type", Former::ThunkType),
    ("f_type", Former::ReturnerType),
    ("function_type", Former::ArrowType),
    ("product_type", Former::ProductType),
    ("parenthesized_type", Former::ParenthesizedType),
    ("def_value", Former::Declaration),
    ("attribute_block", Former::AttributeBlock),
    ("import_declaration", Former::Import),
];

/// The former a form of named kind `kind` is read as.
///
/// # Specification
/// - requires: nothing — every kind, one the grammar does not realise included,
///   is admissible input.
/// - ensures: exactly the former the dispatch table pairs with `kind`'s
///   spelling, and [`Former::Unadmitted`] for every kind the table does not
///   hold.
/// - provides: the one dispatch the lowering takes on a form, so a kind outside
///   the fragment is declined by the same rule wherever it stands.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the table is a finite class, enumerated exhaustively with
///   each row's exact former asserted, separated from the miss arm by kinds the
///   grammar realises and the fragment declines, each asserted unadmitted;
///   every row's kind is asserted to be a kind the built-in grammar realises,
///   so a renamed grammar kind breaks the table rather than silently declining
///   the form.
/// - witness: `form::tests::every_dispatched_kind_is_pinned`
/// - witness: `form::tests::a_kind_outside_the_table_is_unadmitted`
/// - witness: `form::tests::every_form_name_is_realised_by_the_grammar`
#[inline]
#[must_use]
pub fn former_of(kind: NamedKind<'_>) -> Former
{
    FORMERS
        .into_iter()
        .find_map(|(entry, former)| (entry == kind.0).then_some(former))
        .unwrap_or(Former::Unadmitted)
}

/// What the parser inserted where the source fell short of the grammar.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Repair
{
    /// Grout standing where the source wrote no term, or over a token no
    /// label molds.
    Grout(GroutShape),
    /// A closing tile of this family that the source never wrote.
    GhostClose(ClosingClass),
}

impl fmt::Display for Repair
{
    /// Writes what the parser inserted.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        match *self {
            | Self::Grout(GroutShape::Convex) => f.write_str("grout for a missing term"),
            | Self::Grout(GroutShape::Prefix | GroutShape::Postfix) => {
                f.write_str("grout for a missing operand")
            },
            | Self::Grout(GroutShape::Infix) => f.write_str("grout for a missing operator"),
            | Self::GhostClose(ClosingClass::Paren) => f.write_str("a `)` the source never wrote"),
            | Self::GhostClose(ClosingClass::Bracket) => {
                f.write_str("a `]` the source never wrote")
            },
            | Self::GhostClose(ClosingClass::Brace) => f.write_str("a `}` the source never wrote"),
        }
    }
}

/// One node of a molded tree, as the dispatch reads it.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Shape
{
    /// The root of a source.
    Root,
    /// A form: the name a diagnostic writes it as and the former it is read
    /// as.
    Form
    {
        /// The form's named kind.
        name: FormName,
        /// What the lowering reads the kind as.
        former: Former,
    },
    /// Material the parser inserted.
    Repair(Repair),
    /// Layout: whitespace, a comment, or a shebang line.
    Layout,
}

/// The shape of `node` under `pbg`.
///
/// # Specification
/// - requires: `node` belongs to a tree molded under `pbg`.
/// - ensures: the root reads as [`Shape::Root`], a form or tile as the form its
///   mold's named kind names, grout and a minted close as the repair they stand
///   for, and layout as [`Shape::Layout`].
/// - provides: the one total reading of a node label every pass dispatches on.
/// - fails: [`LoweringRefusal::UnknownMold`] when a form's mold is not in
///   `pbg`'s table, which only a tree built under another table can carry.
/// - panics: none.
///
/// # Errors
/// [`LoweringRefusal::UnknownMold`] for a mold `pbg` does not hold.
#[inline]
pub fn shape_of<'source>(
    pbg: &Pbg,
    node: &Node,
) -> Result<Shape, LoweringRefusal<'source>>
{
    match node.label() {
        | NodeLabel::Wald => Ok(Shape::Root),
        | NodeLabel::Meld(mold) | NodeLabel::Tile(mold) => {
            let kind = named_kind(pbg, node, mold)?;

            Ok(Shape::Form {
                name: FormName::from(kind),
                former: former_of(kind),
            })
        },
        | NodeLabel::Grout { shape, .. } => Ok(Shape::Repair(Repair::Grout(shape))),
        | NodeLabel::GhostClose { class, .. } => Ok(Shape::Repair(Repair::GhostClose(class))),
        | NodeLabel::Space => Ok(Shape::Layout),
    }
}

/// The named kind `mold` resolves to under `pbg`.
///
/// # Specification
/// - requires: `node` is the node carrying `mold`.
/// - ensures: the kind `pbg` resolves the mold to.
/// - provides: the lookup every dispatch takes.
/// - fails: [`LoweringRefusal::UnknownMold`] for a mold `pbg` does not hold.
/// - panics: none.
///
/// # Errors
/// [`LoweringRefusal::UnknownMold`] for a mold `pbg` does not hold.
fn named_kind<'source>(
    pbg: &Pbg,
    node: &Node,
    mold: MoldId,
) -> Result<NamedKind<'static>, LoweringRefusal<'source>>
{
    pbg.named_kind(mold)
        .map_err(|_unknown| LoweringRefusal::UnknownMold {
            span: node.span(),
            mold,
        })
}

/// The rule name `mold` belongs to under `pbg`.
///
/// # Specification
/// - requires: `node` is the node carrying `mold`.
/// - ensures: the rule `pbg` numbered the mold for, by its unique name.
/// - provides: the test that tells a form's own tiles from its operands.
/// - fails: [`LoweringRefusal::UnknownMold`] for a mold `pbg` does not hold.
/// - panics: none.
///
/// # Errors
/// [`LoweringRefusal::UnknownMold`] for a mold `pbg` does not hold.
fn rule_name<'source>(
    pbg: &Pbg,
    node: &Node,
    mold: MoldId,
) -> Result<RuleIdentity, LoweringRefusal<'source>>
{
    pbg.rule_of(mold)
        .map(|rule| RuleIdentity(rule.name))
        .map_err(|_unknown| LoweringRefusal::UnknownMold {
            span: node.span(),
            mold,
        })
}

/// A rule's identity: its name, unique in its grammar.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct RuleIdentity(&'static str);

/// What holds a node's children: a form of one rule, or the root.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
enum Holder
{
    /// A form, whose own tiles are the tiles of this rule.
    Rule(RuleIdentity),
    /// The root, which has no tiles of its own.
    Root,
}

/// A child of a form, with the bytes it covers.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Placed
{
    /// The child's arena position.
    pub node: NodeIndex,
    /// The bytes the child covers.
    pub span: ByteSpan,
}

impl Placed
{
    /// The child at `node`, covering what `held` covers.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn of(
        node: NodeIndex,
        held: &Node,
    ) -> Self
    {
        Self {
            node,
            span: held.span(),
        }
    }
}

/// One child of a form, read against the form's own rule.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Piece
{
    /// One of the form's own tiles, with the label its mold carries.
    Tile
    {
        /// The tile's label.
        label: TileName,
        /// The tile.
        at: Placed,
    },
    /// A form standing in one of the form's holes.
    Operand(Placed),
}

impl Piece
{
    /// The child this piece reads.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn placed(self) -> Placed
    {
        match self {
            | Self::Tile { at, .. } | Self::Operand(at) => at,
        }
    }
}

/// A repair the parser made among a form's children.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Repaired
{
    /// The bytes the inserted node stands at.
    pub span: ByteSpan,
    /// What was inserted.
    pub repair: Repair,
}

/// A form's children as its rule reads them.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Pieces
{
    /// Every child the source wrote, in source order, layout dropped.
    pub pieces: Vec<Piece>,
    /// The first repair among the children, in child order.
    pub repair: Maybe<Repaired, repair::Absent>,
}

impl Pieces
{
    /// An empty reading, ready to be filled by [`read_pieces`].
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn new() -> Self
    {
        Self {
            pieces: Vec::new(),
            repair: Maybe::Absent(repair::Absent::Unrepaired),
        }
    }
}

impl Default for Pieces
{
    /// An empty reading.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn default() -> Self
    {
        Self::new()
    }
}

/// Read the children of the node at `position` against its own rule, into
/// `read`.
///
/// # Specification
/// - requires: `position` names a node of `tree`, molded under `pbg`.
/// - ensures: `read` is refilled from nothing: a one-tile form reads as itself,
///   its one own tile; a form of several tiles reads each child tile of its own
///   rule as an own tile and every other written child as an operand, in child
///   order; the root reads every written child as an operand; layout is dropped
///   everywhere, and the first grout or minted close among the children is
///   reported beside the pieces rather than read as one.
/// - provides: the one reading of a form's children every reader takes, so the
///   own-tile test is decided in one place, over one buffer reused from form to
///   form.
/// - fails: [`LoweringRefusal::UnknownMold`] when a mold is not in `pbg`'s
///   table.
/// - panics: none.
///
/// # Errors
/// [`LoweringRefusal::UnknownMold`] for a mold `pbg` does not hold.
///
/// # Adequacy
/// - hypothesis: L3 — three decision surfaces (the own-rule test, the repair
///   test, the one-tile case) separated by a parsed form mixing own tiles and
///   operands, a parsed form holding grout, and a one-tile form, each asserted
///   as an exact piece list.
/// - witness: `form::tests::a_form_reads_its_own_tiles_apart_from_its_operands`
/// - witness: `form::tests::a_repair_among_the_children_is_reported_beside_them`
/// - witness: `form::tests::a_one_tile_form_is_its_own_tile`
#[inline]
pub fn read_pieces<'source>(
    pbg: &Pbg,
    tree: &SyntaxTree<'source>,
    position: NodeIndex,
    read: &mut Pieces,
) -> Result<(), LoweringRefusal<'source>>
{
    read.pieces.clear();
    read.repair = Maybe::Absent(repair::Absent::Unrepaired);
    let Some(node) = tree.node(position)
    else {
        return Ok(());
    };
    let own = match node.label() {
        | NodeLabel::Tile(mold) => {
            let label = tile_name(pbg, node, mold)?;
            read.pieces.push(Piece::Tile {
                label,
                at: Placed::of(position, node),
            });
            return Ok(());
        },
        | NodeLabel::Meld(mold) => Holder::Rule(rule_name(pbg, node, mold)?),
        | NodeLabel::Wald => Holder::Root,
        | NodeLabel::Grout { .. } | NodeLabel::GhostClose { .. } | NodeLabel::Space => {
            return Ok(());
        },
    };
    for child in tree.children(position) {
        let Some(held) = tree.node(child)
        else {
            continue;
        };
        let placed = Placed::of(child, held);
        let piece = match held.label() {
            | NodeLabel::Space => continue,
            | NodeLabel::Grout { shape, .. } => {
                note_repair(read, placed, Repair::Grout(shape));
                continue;
            },
            | NodeLabel::GhostClose { class, .. } => {
                note_repair(read, placed, Repair::GhostClose(class));
                continue;
            },
            | NodeLabel::Tile(mold) => own_tile(pbg, held, own, mold, placed)?,
            | NodeLabel::Meld(_) | NodeLabel::Wald => Piece::Operand(placed),
        };
        read.pieces.push(piece);
    }

    Ok(())
}

/// Read one child tile against the rule of the form holding it.
///
/// # Specification
/// - requires: `held` is the child `placed` names, labelled with `mold`; `own`
///   is what holds it.
/// - ensures: an own tile when the tile's mold belongs to `own`, and an operand
///   otherwise, the root's children included.
/// - provides: the own-tile test of [`read_pieces`].
/// - fails: [`LoweringRefusal::UnknownMold`] for a mold `pbg` does not hold.
/// - panics: none.
///
/// # Errors
/// [`LoweringRefusal::UnknownMold`] for a mold `pbg` does not hold.
fn own_tile<'source>(
    pbg: &Pbg,
    held: &Node,
    own: Holder,
    mold: MoldId,
    placed: Placed,
) -> Result<Piece, LoweringRefusal<'source>>
{
    let Holder::Rule(rule) = own
    else {
        return Ok(Piece::Operand(placed));
    };
    if rule != rule_name(pbg, held, mold)? {
        return Ok(Piece::Operand(placed));
    }

    Ok(Piece::Tile {
        label: tile_name(pbg, held, mold)?,
        at: placed,
    })
}

/// Record `repair` at `placed` when it is the first repair among the
/// children.
///
/// # Specification
/// - requires: `placed` is a child of the form `read` describes.
/// - ensures: the first repair offered is kept and every later one is not.
/// - provides: the first-repair rule of [`read_pieces`].
/// - fails: never.
/// - panics: none.
fn note_repair(
    read: &mut Pieces,
    placed: Placed,
    repair: Repair,
)
{
    if let Maybe::Absent(_) = read.repair {
        read.repair = Maybe::Present(Repaired {
            span: placed.span,
            repair,
        });
    }
}

/// The label `mold`'s tile carries under `pbg`.
///
/// # Specification
/// - requires: `node` is the node carrying `mold`.
/// - ensures: the tile label the mold table holds for the mold.
/// - provides: the own-tile label a reader matches on.
/// - fails: [`LoweringRefusal::UnknownMold`] for a mold `pbg` does not hold.
/// - panics: none.
///
/// # Errors
/// [`LoweringRefusal::UnknownMold`] for a mold `pbg` does not hold.
fn tile_name<'source>(
    pbg: &Pbg,
    node: &Node,
    mold: MoldId,
) -> Result<TileName, LoweringRefusal<'source>>
{
    pbg.mold(mold)
        .map(|held| TileName(held.label))
        .map_err(|_unknown| LoweringRefusal::UnknownMold {
            span: node.span(),
            mold,
        })
}

/// The operands standing between two of a form's own tiles.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Run
{
    /// No operand: the hole is empty, at the gap these bytes name.
    Empty(ByteSpan),
    /// Exactly one operand.
    One(Placed),
    /// More than one operand.
    Several
    {
        /// The first operand of the run.
        first: Placed,
        /// The second operand of the run: the first a one-operand hole does
        /// not take.
        extra: Placed,
        /// How many operands the run holds.
        count: OperandCount,
    },
}

/// A reading position in a form's pieces.
#[derive(Clone, Debug)]
pub struct Cursor<'pieces>
{
    /// The pieces not yet read.
    rest: &'pieces [Piece],
    /// The last piece read, or the empty span at the form's start before any:
    /// an empty hole stands at its end.
    edge: ByteSpan,
}

impl<'pieces> Cursor<'pieces>
{
    /// A cursor before the first of `pieces`, a form covering `form`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn new(
        pieces: &'pieces [Piece],
        form: ByteSpan,
    ) -> Self
    {
        Self {
            rest: pieces,
            edge: ByteSpan::new(form.start(), form.start()).unwrap_or(form),
        }
    }

    /// The next piece, unread.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the piece the cursor stands before, or the exhausted absence
    ///   past the last one; the cursor does not move.
    /// - provides: the lookahead every reader branches on.
    /// - fails: never.
    /// - panics: none.
    #[inline]
    pub fn peek(&self) -> Maybe<Piece, cursor::Absent>
    {
        self.rest
            .first()
            .copied()
            .map_or(Maybe::Absent(cursor::Absent::Exhausted), Maybe::Present)
    }

    /// Whether the next piece is an own tile labelled `label`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the tile when the next piece is an own tile of that label,
    ///   and an absence naming why otherwise; the cursor does not move.
    /// - provides: the branch test on a form's discriminating tile.
    /// - fails: never.
    /// - panics: none.
    #[inline]
    pub fn at(
        &self,
        label: TileName,
    ) -> Maybe<Placed, cursor::Absent>
    {
        match self.peek() {
            | Maybe::Present(Piece::Tile { label: held, at }) if held == label => {
                Maybe::Present(at)
            },
            | Maybe::Present(Piece::Tile { .. } | Piece::Operand(_)) => {
                Maybe::Absent(cursor::Absent::Elsewhere)
            },
            | Maybe::Absent(reason) => Maybe::Absent(reason),
        }
    }

    /// Read the next piece when it is an own tile labelled `label`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: on a match, the tile, with the cursor moved past it;
    ///   otherwise the absence [`Cursor::at`] names, with the cursor unmoved.
    /// - provides: the consuming half of every reader's tile match.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the match and the two absences are separated by a
    ///   matching tile, a tile of another label, an operand and an exhausted
    ///   cursor, each asserted with the cursor's position after it.
    /// - witness: `form::tests::a_cursor_reads_a_tile_only_by_its_label`
    #[inline]
    pub fn tile(
        &mut self,
        label: TileName,
    ) -> Maybe<Placed, cursor::Absent>
    {
        let found = self.at(label);
        if let Maybe::Present(placed) = found {
            self.advance(placed);
        }

        found
    }

    /// Read the next piece, whatever it is.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the piece the cursor stood before, with the cursor moved past
    ///   it, or the exhausted absence past the last one.
    /// - provides: the step a reader scanning for a tile takes over the pieces
    ///   it does not read.
    /// - fails: never.
    /// - panics: none.
    #[inline]
    pub fn read(&mut self) -> Maybe<Piece, cursor::Absent>
    {
        let found = self.peek();
        if let Maybe::Present(piece) = found {
            self.advance(piece.placed());
        }

        found
    }

    /// Read the run of operands at the cursor.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: every operand up to the next own tile or the end is read, and
    ///   the run says how many there were: none, with the gap the empty hole
    ///   stands at; exactly one; or several, naming the first two.
    /// - provides: the hole reading every reader takes.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the run's three cases separated by an empty hole
    ///   between two tiles, a single operand and a juxtaposed pair, each
    ///   asserted exactly with the gap's offset for the empty case.
    /// - witness: `form::tests::a_run_counts_the_operands_between_two_tiles`
    #[inline]
    pub fn operands(&mut self) -> Run
    {
        let gap = self.gap();
        let mut first = Maybe::Absent(cursor::Absent::Exhausted);
        let mut extra = Maybe::Absent(cursor::Absent::Exhausted);
        let mut count = 0_usize;
        while let Maybe::Present(Piece::Operand(placed)) = self.peek() {
            self.advance(placed);
            count = count.saturating_add(1_usize);
            if let Maybe::Absent(_) = first {
                first = Maybe::Present(placed);
            }
            else if let Maybe::Absent(_) = extra {
                extra = Maybe::Present(placed);
            }
        }
        match (first, extra) {
            | (Maybe::Present(placed), Maybe::Absent(_)) => Run::One(placed),
            | (Maybe::Present(head), Maybe::Present(placed)) => Run::Several {
                first: head,
                extra: placed,
                count: OperandCount::from(count),
            },
            | (Maybe::Absent(_), _) => Run::Empty(gap),
        }
    }

    /// The bytes the cursor stands at: the next piece's span, or the empty
    /// gap past the last piece read once every piece has been read.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the span of the piece the cursor stands before, and the
    ///   zero-width span at the end of the last piece read when none remains;
    ///   the cursor does not move.
    /// - provides: the position a reader names when a piece is out of place.
    /// - fails: never.
    /// - panics: none.
    #[inline]
    #[must_use]
    pub fn here(&self) -> ByteSpan
    {
        match self.peek() {
            | Maybe::Present(piece) => piece.placed().span,
            | Maybe::Absent(_) => self.gap(),
        }
    }

    /// The zero-width span at the end of the last piece read.
    ///
    /// # Specification
    /// trivial.
    fn gap(&self) -> ByteSpan
    {
        ByteSpan::new(self.edge.end(), self.edge.end()).unwrap_or(self.edge)
    }

    /// Step past the piece `placed`, moving the edge to it.
    ///
    /// # Specification
    /// - requires: `placed` is the piece the cursor stands before.
    /// - ensures: the cursor stands after that piece, and the edge is the
    ///   piece's span.
    /// - provides: the one way a reader advances.
    /// - fails: never.
    /// - panics: none.
    fn advance(
        &mut self,
        placed: Placed,
    )
    {
        if let Some((_read, rest)) = self.rest.split_first() {
            self.rest = rest;
        }
        self.edge = placed.span;
    }
}

#[cfg(test)]
mod tests
{
    use alloc::vec::Vec;

    use gandr_surface_grammar::NamedKind;
    use gandr_surface_grammar::PBG_ONLY_KINDS;
    use gandr_surface_grammar::Pbg;
    use gandr_surface_grammar::TREE_SITTER_NAMED_KINDS;
    use gandr_surface_syntax::ByteOffset;
    use gandr_surface_syntax::ByteSpan;
    use gandr_surface_syntax::GroutShape;
    use gandr_surface_syntax::NodeIndex;
    use gandr_surface_syntax::SourceText;
    use gandr_surface_syntax::SyntaxTree;
    use quenchant_shape::shape::Maybe;

    use super::Cursor;
    use super::FORMERS;
    use super::FormName;
    use super::Former;
    use super::Piece;
    use super::Pieces;
    use super::Placed;
    use super::Repair;
    use super::Repaired;
    use super::Run;
    use super::TileName;
    use super::cursor;
    use super::former_of;
    use super::read_pieces;
    use crate::fixture::grammar;
    use crate::fixture::parsed;
    use crate::fixture::repaired;
    use crate::fixture::span;
    use crate::resolve::OperandCount;

    /// One piece as a test reads it: a tile by its label, or an operand, each
    /// with the bytes it covers.
    #[derive(Clone, Copy, Debug, Eq, PartialEq)]
    enum Sketch
    {
        /// An own tile.
        Tile(TileName, ByteSpan),
        /// An operand.
        Operand(ByteSpan),
    }

    /// The pieces of the first declaration of `tree`.
    ///
    /// # Specification
    /// trivial.
    fn first_declaration(
        pbg: &Pbg,
        tree: &SyntaxTree<'_>,
    ) -> Pieces
    {
        let mut root = Pieces::new();
        read_pieces(pbg, tree, tree.root(), &mut root).unwrap();
        let declaration = root.pieces.first().unwrap().placed();
        let mut read = Pieces::new();
        read_pieces(pbg, tree, declaration.node, &mut read).unwrap();

        read
    }

    /// `pieces` as sketches, node positions dropped.
    ///
    /// # Specification
    /// trivial.
    fn sketch(pieces: &Pieces) -> Vec<Sketch>
    {
        pieces
            .pieces
            .iter()
            .map(|piece| match *piece {
                | Piece::Tile { label, at } => Sketch::Tile(label, at.span),
                | Piece::Operand(at) => Sketch::Operand(at.span),
            })
            .collect()
    }

    #[test]
    fn a_form_reads_its_own_tiles_apart_from_its_operands()
    {
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));
        let pbg = grammar();
        let tree = parsed(&pbg, SourceText::from("def x = 3 ;"));
        let read = first_declaration(&pbg, &tree);

        assert_eq!(
            sketch(&read),
            [
                Sketch::Tile(TileName::DEF, at(0_usize, 3_usize)),
                Sketch::Tile(TileName::IDENTIFIER, at(4_usize, 5_usize)),
                Sketch::Tile(TileName::EQUALS, at(6_usize, 7_usize)),
                Sketch::Operand(at(8_usize, 9_usize)),
                Sketch::Tile(TileName::SEMICOLON, at(10_usize, 11_usize)),
            ],
            "the declaration's own tiles are read by label, the body as its operand, layout dropped"
        );
        assert!(
            matches!(read.repair, Maybe::Absent(_)),
            "a clean form carries no repair"
        );
    }

    #[test]
    fn a_repair_among_the_children_is_reported_beside_them()
    {
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));
        let pbg = grammar();
        let tree = repaired(&pbg, SourceText::from("def x ;"));
        let read = first_declaration(&pbg, &tree);

        assert_eq!(
            read.repair,
            Maybe::Present(Repaired {
                span: at(5_usize, 5_usize),
                repair: Repair::Grout(GroutShape::Postfix),
            }),
            "the grout the parser inserted is reported where it stands"
        );
        assert!(
            read.pieces
                .iter()
                .all(|piece| piece.placed().span != at(5_usize, 5_usize)),
            "the grout is not read as a piece"
        );
    }

    #[test]
    fn a_one_tile_form_is_its_own_tile()
    {
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));
        let pbg = grammar();
        let tree = parsed(&pbg, SourceText::from("def x = 3 ;"));
        let body = first_declaration(&pbg, &tree)
            .pieces
            .into_iter()
            .find_map(|piece| match piece {
                | Piece::Operand(operand) => Some(operand),
                | Piece::Tile { .. } => None,
            })
            .unwrap();
        let mut read = Pieces::new();
        read_pieces(&pbg, &tree, body.node, &mut read).unwrap();

        assert_eq!(
            sketch(&read),
            [Sketch::Tile(TileName("number"), at(8_usize, 9_usize))],
            "a number is one tile, read as its own"
        );
    }

    #[test]
    fn a_cursor_reads_a_tile_only_by_its_label()
    {
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));
        let keyword = Placed {
            node: NodeIndex::from(1_usize),
            span: at(0_usize, 3_usize),
        };
        let operand = Placed {
            node: NodeIndex::from(2_usize),
            span: at(4_usize, 5_usize),
        };
        let pieces = [
            Piece::Tile {
                label: TileName::DEF,
                at: keyword,
            },
            Piece::Operand(operand),
        ];
        let mut reading = Cursor::new(&pieces, at(0_usize, 5_usize));

        assert_eq!(
            reading.tile(TileName::EQUALS),
            Maybe::Absent(cursor::Absent::Elsewhere),
            "a tile of another label is not read"
        );
        assert_eq!(
            reading.here(),
            keyword.span,
            "a miss leaves the cursor where it stood"
        );
        assert_eq!(
            reading.tile(TileName::DEF),
            Maybe::Present(keyword),
            "a tile of the asked label is read"
        );
        assert_eq!(
            reading.tile(TileName::DEF),
            Maybe::Absent(cursor::Absent::Elsewhere),
            "an operand is not a tile"
        );
        assert_eq!(
            reading.here(),
            operand.span,
            "the cursor stands at the operand"
        );
        assert_eq!(
            reading.operands(),
            Run::One(operand),
            "the operand is read as a run"
        );
        assert_eq!(
            reading.tile(TileName::DEF),
            Maybe::Absent(cursor::Absent::Exhausted),
            "nothing is left to read"
        );
        assert_eq!(
            reading.here(),
            at(5_usize, 5_usize),
            "an exhausted cursor stands at the gap past the last piece"
        );
    }

    #[test]
    fn a_run_counts_the_operands_between_two_tiles()
    {
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));
        let placed = |node: usize, start: usize, end: usize| Placed {
            node: NodeIndex::from(node),
            span: at(start, end),
        };
        let empty = [
            Piece::Tile {
                label: TileName::PAREN_OPEN,
                at: placed(1_usize, 0_usize, 1_usize),
            },
            Piece::Tile {
                label: TileName::PAREN_CLOSE,
                at: placed(2_usize, 1_usize, 2_usize),
            },
        ];
        let mut reading = Cursor::new(&empty, at(0_usize, 2_usize));
        let _open = reading.tile(TileName::PAREN_OPEN);
        assert_eq!(
            reading.operands(),
            Run::Empty(at(1_usize, 1_usize)),
            "an empty hole stands at the gap after the tile before it"
        );

        let first = placed(3_usize, 0_usize, 1_usize);
        let second = placed(4_usize, 2_usize, 3_usize);
        let juxtaposed = [
            Piece::Operand(first),
            Piece::Operand(second),
            Piece::Operand(placed(5_usize, 4_usize, 5_usize)),
        ];
        let mut reading = Cursor::new(&juxtaposed, at(0_usize, 5_usize));
        assert_eq!(
            reading.operands(),
            Run::Several {
                first,
                extra: second,
                count: OperandCount::from(3_usize),
            },
            "a juxtaposition names its first two operands and counts them all"
        );
    }

    #[test]
    fn every_dispatched_kind_is_pinned()
    {
        let expected = [
            ("identifier", Former::Name),
            ("number", Former::Number),
            ("string", Former::Text),
            ("parenthesized_expression", Former::Parenthesized),
            ("thunk_expression", Former::Thunk),
            ("lambda_expression", Former::Lambda),
            ("ret_expression", Former::Return),
            ("force_expression", Former::Force),
            ("call_expression", Former::Call),
            ("primitive_type", Former::TypeHead),
            ("type_identifier", Former::TypeHead),
            ("type_variable", Former::TypeHead),
            ("type_application", Former::TypeApplication),
            ("u_type", Former::ThunkType),
            ("f_type", Former::ReturnerType),
            ("function_type", Former::ArrowType),
            ("product_type", Former::ProductType),
            ("parenthesized_type", Former::ParenthesizedType),
            ("def_value", Former::Declaration),
            ("attribute_block", Former::AttributeBlock),
            ("import_declaration", Former::Import),
        ];
        for (kind, former) in expected {
            assert_eq!(
                former_of(NamedKind(kind)),
                former,
                "the kind `{kind}` is read as its pinned former"
            );
        }
        assert_eq!(
            FORMERS.len(),
            expected.len(),
            "the table holds no row beyond the pinned ones"
        );
    }

    #[test]
    fn a_kind_outside_the_table_is_unadmitted()
    {
        for kind in ["and_expression", "acquire_statement", "no_such_kind"] {
            assert_eq!(
                former_of(NamedKind(kind)),
                Former::Unadmitted,
                "the kind `{kind}` is outside the fragment"
            );
        }
    }

    #[test]
    fn every_form_name_is_realised_by_the_grammar()
    {
        let pbg = grammar();
        let realised =
            |kind: &str| TREE_SITTER_NAMED_KINDS.contains(&kind) || PBG_ONLY_KINDS.contains(&kind);
        for name in FormName::ALL {
            let spelled: &str = name.as_ref();
            assert!(
                realised(spelled),
                "the form name `{spelled}` is a named kind of the grammar"
            );
        }
        for (kind, _former) in FORMERS {
            assert!(
                pbg.rules().iter().any(|rule| rule.provenance == kind),
                "the dispatched kind `{kind}` is realised by a rule of the built-in grammar"
            );
        }
    }
}
