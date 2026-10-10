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

use anodized::spec;
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
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: distinct authored form names, each realised by the grammar.
    /// - provides: the diagnostic form-name inventory.
    /// - fails: no claim enumerates names read dynamically from custom molds.
    /// - panics: none.
    /// - executable: none — the specification attribute does not support const
    ///   items; functions consuming the inventory retain predicates.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — pairwise name identity and grammar realisation are
    ///   checked for this finite inventory, without assuming it contains every
    ///   possible custom grammar kind.
    /// - witness: `error::tests::the_form_names_are_pairwise_distinct`
    /// - witness: `form::tests::every_form_name_is_realised_by_the_grammar`
    pub const ALL: [Self; 26_usize] = [
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
        Self::MODULE,
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
    /// The module family `module M …`, its members included.
    pub const MODULE: Self = Self("module_declaration");
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
    /// The static abstraction's lead `\`.
    pub const BACKSLASH: Self = Self("\\");
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
    /// The selection dot `.` of a path.
    pub const DOT: Self = Self(".");
    /// The lambda keyword `fn`.
    pub const FN: Self = Self("fn");
    /// The force keyword `force`.
    pub const FORCE: Self = Self("force");
    /// The fork keyword `fork`, opening a statement.
    pub const FORK: Self = Self("fork");
    /// The equals sign `=` opening a definition tail.
    pub const EQUALS: Self = Self("=");
    /// The value function space's `=>`.
    pub const FAT_ARROW: Self = Self("=>");
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
    /// The sort literal `-` of a universe: the computation types.
    pub const MINUS: Self = Self("-");
    /// The module keyword `module`.
    pub const MODULE: Self = Self("module");
    /// A numeral written as one of a form's own tiles: a universe's level or a
    /// bridge's grade.
    pub const NUMBER: Self = Self("number");
    /// The default grade `ω` of a bridge.
    pub const OMEGA: Self = Self("ω");
    /// A parenthesis closer `)`.
    pub const PAREN_CLOSE: Self = Self(")");
    /// A parenthesis opener `(`.
    pub const PAREN_OPEN: Self = Self("(");
    /// The sort literal `+` of a universe: the value types.
    pub const PLUS: Self = Self("+");
    /// A double quote opening or closing a string written among a form's own
    /// tiles.
    pub const QUOTE: Self = Self("\"");
    /// The recursion keyword `rec`.
    pub const REC: Self = Self("rec");
    /// The record and signature opener `#{`.
    pub const RECORD: Self = Self("#{");
    /// The receive keyword `recv`, opening a statement.
    pub const RECV: Self = Self("recv");
    /// The release keyword `release`, opening a statement.
    pub const RELEASE: Self = Self("release");
    /// The returner keyword `ret`.
    pub const RET: Self = Self("ret");
    /// The bind keyword `run`, opening a statement.
    pub const RUN: Self = Self("run");
    /// The eager product's `*`.
    pub const STAR: Self = Self("*");
    /// The opaque ascription `:>`.
    pub const SEAL: Self = Self(":>");
    /// The semicolon `;` closing a declaration or a statement.
    pub const SEMICOLON: Self = Self(";");
    /// A run of plain text inside a string's own tiles.
    pub const STRING_FRAGMENT: Self = Self("string_fragment");
    /// The thunk keyword `thunk`.
    pub const THUNK: Self = Self("thunk");
    /// The type-component keyword `type` of a module signature.
    pub const TYPE: Self = Self("type");
    /// A type identifier written as one of a form's own tiles.
    pub const TYPE_IDENTIFIER: Self = Self("type_identifier");
    /// A type variable written as one of a form's own tiles.
    pub const TYPE_VARIABLE: Self = Self("type_variable");
    /// The universe keyword `Type`.
    pub const UNIVERSE: Self = Self("Type");
    /// The unpack keyword `unpack`, opening a statement.
    pub const UNPACK: Self = Self("unpack");
    /// The keyword `val`, opening a statement.
    pub const VAL: Self = Self("val");

    /// The three tiles that can name a parameter: an identifier, a type
    /// variable and a type identifier, the spellings the parameter list parses.
    ///
    /// # Specification
    /// - requires: parameter tiles have been read under their own rule.
    /// - ensures: identifier, type-variable and type-identifier labels are
    ///   recognised as binder spellings rather than punctuation.
    /// - provides: the shared binder-label class used by function readers.
    /// - fails: membership alone does not admit a binder to the fragment.
    /// - panics: none.
    /// - executable: none — the specification attribute does not support const
    ///   items; the function readers check admission in context.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — ordinary term parameters lower to a lambda chain,
    ///   while a type-spelled parameter receives the typed unadmitted refusal.
    ///   These witnesses concern binder recognition in function tails, not all
    ///   custom grammar labels or all binder positions.
    /// - witness: `lower::tests::a_function_tail_lowers_to_a_thunked_lambda_chain`
    /// - witness: `lower::tests::forms_outside_the_fragment_are_unadmitted`
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
///
/// # Specification
/// - requires: the named kind and reading position supply the dispatch context.
/// - ensures: each variant names one lowering interpretation; Unadmitted
///   represents kinds outside the dispatch table.
/// - provides: a typed dispatch result.
/// - fails: no variant certifies that the form is valid in its position.
/// - panics: none.
/// - executable: none — the originating named kind is not retained; `former_of`
///   checks the correspondence when producing the tag.
///
/// # Adequacy
/// - hypothesis: L3 — the finite dispatch table and absent kinds distinguish
///   all current interpretations; positional admission is witnessed by the
///   lowering readers rather than certified by this tag.
/// - witness: `form::tests::every_form_name_is_realised_by_the_grammar`
/// - witness: `form::tests::a_kind_outside_the_table_is_unadmitted`
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Former
{
    /// An identifier in term position: a variable or an earlier declaration.
    Name,
    /// A capitalised name in term position: an earlier declaration, or a type
    /// atom or the universe standing where a value is read, which is quoted.
    Constructor,
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
    /// An infix operation in the native vocabulary.
    Binary,
    /// A prefix operation in the native vocabulary.
    Unary,
    /// A selection `e.name`: a static path when its head names a module, and
    /// a record projection the fragment does not admit otherwise.
    Projection,
    /// A bare type head: a primitive, a type identifier or a type variable.
    TypeHead,
    /// The universe `Type[s, l]`, its sort and level each defaulted when left
    /// off.
    Universe,
    /// A type head applied to arguments, `Foo(A)`: a unary type former, or a
    /// static application of a type operator a binder or a declaration names.
    TypeApplication,
    /// The thunk type `+U C`.
    ThunkType,
    /// The returner type `-F A`.
    ReturnerType,
    /// The arrow type `A -> C`, or the static Pi `A -> B` where a value type
    /// is read.
    ArrowType,
    /// The eager product type `A * B`.
    ProductType,
    /// The reserved lazy product type `C & D`.
    LazyProductType,
    /// The value function space `A => B` or `(A, B) => C`, the alias of the
    /// thunked arrow.
    ValueFunctionType,
    /// The static abstraction `\A. T`.
    StaticAbstraction,
    /// A parenthesised type.
    ParenthesizedType,
    /// The declaration family `def name …`.
    Declaration,
    /// An attribute block standing on its own, decorating nothing.
    AttributeBlock,
    /// The import `import "URI" as name ;`.
    Import,
    /// The module family `module M …`: a module declaration, and each member
    /// of its body — a definition or a nested module — which the grammar
    /// files under the same kind.
    Module,
    /// Every other kind: a form the fragment does not admit.
    Unadmitted,
}

impl Former
{
    /// Every former represented by the dispatch vocabulary.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: each dispatch former occurs once, including Unadmitted.
    /// - provides: the complete current dispatch-result inventory.
    /// - fails: never duplicates a classification.
    /// - panics: none.
    /// - executable: none — the specification attribute does not support const
    ///   items; `former_of` checks the dispatch relation.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the inventory is pairwise distinct and equals the set
    ///   of successful table outcomes plus the miss outcome. The evidence is
    ///   bounded to the current closed enum and table.
    /// - witness: `form::tests::every_form_name_is_realised_by_the_grammar`
    pub const ALL: [Self; 29_usize] = [
        Self::Name,
        Self::Constructor,
        Self::Number,
        Self::Text,
        Self::Parenthesized,
        Self::Thunk,
        Self::Lambda,
        Self::Return,
        Self::Force,
        Self::Call,
        Self::Binary,
        Self::Unary,
        Self::Projection,
        Self::TypeHead,
        Self::Universe,
        Self::TypeApplication,
        Self::ThunkType,
        Self::ReturnerType,
        Self::ArrowType,
        Self::ProductType,
        Self::LazyProductType,
        Self::ValueFunctionType,
        Self::StaticAbstraction,
        Self::ParenthesizedType,
        Self::Declaration,
        Self::AttributeBlock,
        Self::Import,
        Self::Module,
        Self::Unadmitted,
    ];
}

/// The named kinds the lowering reads, with the former each is read as.
///
/// # Specification
/// - requires: nothing; named kinds are compared by exact spelling.
/// - ensures: each admitted kind has one former; absent kinds dispatch to
///   Unadmitted through `former_of`.
/// - provides: the grammar-to-lowering dispatch table.
/// - fails: does not certify positional admission of a dispatched form.
/// - panics: none.
/// - executable: none — the specification attribute does not support const
///   items; `former_of` checks its result against this table.
///
/// # Adequacy
/// - hypothesis: L3 — exact kind/former pairs and declined kinds separate the
///   dispatch outcomes; grammar realisation checks that every current table key
///   names a built-in rule.
/// - witness: `lower::tests::a_function_tail_lowers_to_a_thunked_lambda_chain`
/// - witness: `form::tests::a_kind_outside_the_table_is_unadmitted`
/// - witness: `form::tests::every_form_name_is_realised_by_the_grammar`
pub const FORMERS: [(&str, Former); 30_usize] = [
    ("identifier", Former::Name),
    ("constructor", Former::Constructor),
    ("number", Former::Number),
    ("string", Former::Text),
    ("parenthesized_expression", Former::Parenthesized),
    ("thunk_expression", Former::Thunk),
    ("lambda_expression", Former::Lambda),
    ("ret_expression", Former::Return),
    ("force_expression", Former::Force),
    ("call_expression", Former::Call),
    ("binary_expression", Former::Binary),
    ("unary_expression", Former::Unary),
    ("projection_expression", Former::Projection),
    ("primitive_type", Former::TypeHead),
    ("type_identifier", Former::TypeHead),
    ("type_variable", Former::TypeHead),
    ("universe_type", Former::Universe),
    ("type_application", Former::TypeApplication),
    ("u_type", Former::ThunkType),
    ("f_type", Former::ReturnerType),
    ("function_type", Former::ArrowType),
    ("product_type", Former::ProductType),
    ("lazy_product_type", Former::LazyProductType),
    ("value_function_type", Former::ValueFunctionType),
    ("static_abstraction", Former::StaticAbstraction),
    ("parenthesized_type", Former::ParenthesizedType),
    ("def_value", Former::Declaration),
    ("attribute_block", Former::AttributeBlock),
    ("import_declaration", Former::Import),
    ("module_declaration", Former::Module),
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
/// - witness: `lower::tests::a_function_tail_lowers_to_a_thunked_lambda_chain`
/// - witness: `form::tests::a_kind_outside_the_table_is_unadmitted`
/// - witness: `form::tests::every_form_name_is_realised_by_the_grammar`
#[spec(
    ensures: |ret| match ret {
        | Former::Unadmitted => FORMERS.iter().all(|&(entry, _)| entry != kind.0),
        | former => FORMERS
            .iter()
            .any(|&(entry, held)| entry == kind.0 && held == former),
    },
)]
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
///
/// # Specification
/// - requires: the originating parser node supplies the insertion context.
/// - ensures: grout retains its shape and a minted close retains its family.
/// - provides: the repair class independently of its source span.
/// - fails: no variant certifies which node the parser inserted.
/// - panics: none.
/// - executable: none — the parser node is absent; `shape_of` checks its label
///   against the returned repair.
///
/// # Adequacy
/// - hypothesis: L3 — grout and a ghost close retain different exact payloads
///   when their node labels are classified. The evidence covers those labels,
///   not the parser's repair-selection algorithm.
/// - witness: `form::tests::every_label_shape_is_read_and_unknown_molds_are_located`
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
///
/// # Specification
/// - requires: a source node and grammar establish the classification.
/// - ensures: forms pair their named kind with its dispatched former; root,
///   layout and repairs remain distinct classes.
/// - provides: the shape a lowering pass dispatches on.
/// - fails: no shape authenticates its originating grammar.
/// - panics: none.
/// - executable: none — type refinements require the disabled logic feature;
///   `shape_of` checks the name/former relation at construction.
///
/// # Adequacy
/// - hypothesis: L3 — all six label classes and an unknown mold exercise exact
///   shape classification. These observations concern values returned by the
///   reader, not arbitrary manually constructed Shape values.
/// - witness: `form::tests::every_label_shape_is_read_and_unknown_molds_are_located`
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
/// - requires: nothing; the supplied grammar interprets the node's mold.
/// - ensures: the root reads as [`Shape::Root`], a form or tile as the form its
///   mold's named kind names, grout and a minted close as the repair they stand
///   for, and layout as [`Shape::Layout`].
/// - provides: the one total reading of a node label every pass dispatches on.
/// - fails: [`LoweringRefusal::UnknownMold`] when the mold is absent from the
///   supplied table, including malformed hand-built labels. A recorded grammar
///   fingerprint alone does not validate a mold.
/// - panics: none.
///
/// # Errors
/// [`LoweringRefusal::UnknownMold`] for a mold `pbg` does not hold.
///
/// # Adequacy
/// - hypothesis: L3 — all six label classes are observed as exact shapes,
///   including a ghost close and an unknown mold with its exact location.
///   Parsed forms also exercise grammar-relative named-kind dispatch; no claim
///   authenticates which grammar originally produced an arbitrary node.
/// - witness: `form::tests::every_label_shape_is_read_and_unknown_molds_are_located`
/// - witness: `form::tests::a_form_reads_its_own_tiles_apart_from_its_operands`
#[spec(
    ensures: |ret| match node.label() {
        | NodeLabel::Wald => ret == Ok(Shape::Root),
        | NodeLabel::Space => ret == Ok(Shape::Layout),
        | NodeLabel::Grout { shape, .. } => ret == Ok(Shape::Repair(Repair::Grout(shape))),
        | NodeLabel::GhostClose { class, .. } => {
            ret == Ok(Shape::Repair(Repair::GhostClose(class)))
        },
        | NodeLabel::Meld(mold) | NodeLabel::Tile(mold) => pbg.named_kind(mold).map_or_else(
            |_| {
                ret == Err(LoweringRefusal::UnknownMold {
                    span: node.span(),
                    mold,
                })
            },
            |kind| {
                matches!(ret, Ok(Shape::Form { name, former })
    if name.0 == kind.0 && former == former_of(kind))
            },
        ),
    },
)]
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
///
/// # Adequacy
/// - hypothesis: L3 — known molded labels resolve to their exact kind through
///   shape classification; an absent mold reports both its identity and the
///   rejected node span. These cases distinguish lookup success from a
///   fabricated kind.
/// - witness: `form::tests::every_label_shape_is_read_and_unknown_molds_are_located`
#[spec(
    requires: matches!(node.label(), NodeLabel::Meld(held) | NodeLabel::Tile(held) if held == mold),
    ensures: |ret| match ret {
        | Ok(kind) => pbg.named_kind(mold).is_ok_and(|held| held.0 == kind.0),
        | Err(error) => {
            pbg.named_kind(mold).is_err()
                && error
                    == LoweringRefusal::UnknownMold {
                        span: node.span(),
                        mold,
                    }
        },
    },
)]
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
///
/// # Adequacy
/// - hypothesis: L3 — own and foreign rule tiles are separated by parsed
///   declaration pieces. An unknown child mold reports its own span after a
///   valid prefix; unknown parent molds are covered before any child is read.
/// - witness: `form::tests::a_form_reads_its_own_tiles_apart_from_its_operands`
/// - witness: `form::tests::an_unknown_child_mold_retains_only_the_new_prefix`
/// - witness: `form::tests::unknown_root_molds_clear_the_reused_buffer`
#[spec(
    requires: matches!(node.label(), NodeLabel::Meld(held) | NodeLabel::Tile(held) if held == mold),
    ensures: |ret| match ret {
        | Ok(rule) => pbg.rule_of(mold).is_ok_and(|held| held.name == rule.0),
        | Err(error) => {
            pbg.rule_of(mold).is_err()
                && error
                    == LoweringRefusal::UnknownMold {
                        span: node.span(),
                        mold,
                    }
        },
    },
)]
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
///
/// # Specification
/// - requires: the parent node and grammar establish its owning rule.
/// - ensures: Root owns no tiles; Rule compares child rule identities.
/// - provides: the ownership context for reading a child tile.
/// - fails: does not validate child molds by itself.
/// - panics: none.
/// - executable: none — the parent node and grammar are not retained;
///   `own_tile` checks the interpretation while both are available.
///
/// # Adequacy
/// - hypothesis: L3 — a parsed declaration separates own-rule tiles and a
///   foreign number tile; its root reads the declaration as an operand.
/// - witness: `form::tests::a_form_reads_its_own_tiles_apart_from_its_operands`
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
enum Holder
{
    /// A form, whose own tiles are the tiles of this rule.
    Rule(RuleIdentity),
    /// The root, which has no tiles of its own.
    Root,
}

/// A child of a form, with the bytes it covers.
///
/// # Specification
/// - requires: the node index and span refer to the same syntax tree.
/// - ensures: the span records the bytes covered by that node.
/// - provides: a tree-local child location.
/// - fails: does not authenticate ownership of a numeric node index.
/// - panics: none.
/// - executable: none — the syntax tree needed to resolve the index is absent;
///   `read_pieces` checks returned locations against its tree.
///
/// # Adequacy
/// - hypothesis: L3 — exact parsed piece spans and a rejected child's location
///   observe association with one tree. This does not certify foreign indices
///   or manually assembled node/span pairs.
/// - witness: `form::tests::a_form_reads_its_own_tiles_apart_from_its_operands`
/// - witness: `form::tests::an_unknown_child_mold_retains_only_the_new_prefix`
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
///
/// # Specification
/// - requires: the parent rule and grammar determine child ownership.
/// - ensures: Tile carries an own-rule label and location; Operand carries the
///   location of another written form.
/// - provides: the distinction consumed by form cursors.
/// - fails: no piece certifies its ownership without the parent context.
/// - panics: none.
/// - executable: none — the parent rule and mold table are absent; `own_tile`
///   checks their classification before returning a piece.
///
/// # Adequacy
/// - hypothesis: L3 — exact declaration pieces distinguish keyword and
///   punctuation tiles from a numeric operand, while a root supplies only
///   operands.
/// - witness: `form::tests::a_form_reads_its_own_tiles_apart_from_its_operands`
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
///
/// # Specification
/// - requires: a repaired syntax node supplies the span and repair class.
/// - ensures: both fields describe that same inserted node.
/// - provides: the first repair retained beside a written-piece sequence.
/// - fails: does not prove parser provenance from the two fields alone.
/// - panics: none.
/// - executable: none — the originating node is not retained; `read_pieces`
///   checks the first repair against the actual children.
///
/// # Adequacy
/// - hypothesis: L3 — the parser's missing-operand repair has its exact class
///   and empty span; a different later repair cannot replace the first record.
/// - witness: `form::tests::a_repair_among_the_children_is_reported_beside_them`
/// - witness: `form::tests::the_first_repair_survives_later_repairs`
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Repaired
{
    /// The bytes the inserted node stands at.
    pub span: ByteSpan,
    /// What was inserted.
    pub repair: Repair,
}

/// A form's children as its rule reads them.
///
/// # Specification
/// - requires: a reading is interpreted with its syntax tree and parent.
/// - ensures: written pieces follow child order with layout removed; the
///   separate record names the first repair in that order.
/// - provides: a reusable reading buffer whose successful contents are
///   established by `read_pieces`.
/// - fails: a refused reading may retain only its newly read prefix.
/// - panics: none.
/// - executable: none — tree, parent and traversal history are absent;
///   `read_pieces` checks their relation while holding that context.
///
/// # Adequacy
/// - hypothesis: L3 — parsed pieces and repairs establish exact successful
///   contents; buffer reuse and a late unknown mold distinguish replacement,
///   first repair and prefix-preserving refusal. Arbitrary field mutation is
///   not certified.
/// - witness: `form::tests::a_form_reads_its_own_tiles_apart_from_its_operands`
/// - witness: `form::tests::reading_another_form_discards_old_pieces_and_repairs`
/// - witness: `form::tests::an_unknown_child_mold_retains_only_the_new_prefix`
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
/// - requires: `position` names a node of `tree`; `pbg` interprets its molds.
/// - ensures: `read` is refilled from nothing: a one-tile form reads as itself,
///   its one own tile; a form of several tiles reads each child tile of its own
///   rule as an own tile and every other written child as an operand, in child
///   order; the root reads every written child as an operand; layout is dropped
///   everywhere, and the first grout or minted close among the children is
///   reported beside the pieces rather than read as one. Reading layout or a
///   repair node itself leaves both fields empty.
/// - provides: the one reading of a form's children every reader takes, so the
///   own-tile test is decided in one place, over one buffer reused from form to
///   form.
/// - fails: [`LoweringRefusal::UnknownMold`] on a mold lookup absent from
///   `pbg`. Failure retains only the newly read prefix and any repair already
///   encountered; previous buffer contents are always discarded.
/// - panics: none.
///
/// # Errors
/// [`LoweringRefusal::UnknownMold`] for a mold `pbg` does not hold.
///
/// # Adequacy
/// - hypothesis: L3 — parsed own/foreign tiles, root operands, repairs and a
///   single-tile form separate the successful readings. Buffer reuse observes
///   clearing both fields; an unknown child preserves only the new prefix,
///   while an unknown parent or root tile leaves it empty. Layout and repairs
///   read directly produce empty buffers. This does not validate all descendant
///   molds.
/// - witness: `form::tests::a_form_reads_its_own_tiles_apart_from_its_operands`
/// - witness: `form::tests::a_repair_among_the_children_is_reported_beside_them`
/// - witness: `form::tests::a_one_tile_form_is_its_own_tile`
/// - witness: `form::tests::reading_another_form_discards_old_pieces_and_repairs`
/// - witness: `form::tests::an_unknown_child_mold_retains_only_the_new_prefix`
/// - witness: `form::tests::every_label_shape_is_read_and_unknown_molds_are_located`
/// - witness: `form::tests::unknown_root_molds_clear_the_reused_buffer`
#[inline]
#[spec(
    requires: tree.node(position).is_some(),
    ensures: |ret| {
        read.pieces.iter().all(|piece| {
            let at = piece.placed();
            tree.node(at.node)
                .is_some_and(|held| held.span() == at.span)
        }) && match ret {
            | Ok(()) => tree.node(position).is_some_and(|node| match node.label() {
                | NodeLabel::Tile(mold) => {
                    read.repair == Maybe::Absent(repair::Absent::Unrepaired)
                        && matches!(read.pieces.as_slice(), [Piece::Tile { label, at }]
        if *at == Placed::of(position, node)
            && pbg.mold(mold).is_ok_and(|held| held.label == label.0))
                },
                | NodeLabel::Grout { .. } | NodeLabel::GhostClose { .. } | NodeLabel::Space => {
                    read.pieces.is_empty()
                        && read.repair == Maybe::Absent(repair::Absent::Unrepaired)
                },
                | NodeLabel::Wald | NodeLabel::Meld(_) => {
                    let written = tree.children(position).filter_map(|child| {
                        let held = tree.node(child)?;
                        match held.label() {
                            | NodeLabel::Space
                            | NodeLabel::Grout { .. }
                            | NodeLabel::GhostClose { .. } => None,
                            | _ => Some(Placed::of(child, held)),
                        }
                    });
                    let first_repair = tree
                        .children(position)
                        .find_map(|child| {
                            let held = tree.node(child)?;
                            let repair = match held.label() {
                                | NodeLabel::Grout { shape, .. } => Repair::Grout(shape),
                                | NodeLabel::GhostClose { class, .. } => {
                                    Repair::GhostClose(class)
                                },
                                | _ => return None,
                            };
                            Some(Repaired {
                                span: held.span(),
                                repair,
                            })
                        })
                        .map_or(Maybe::Absent(repair::Absent::Unrepaired), Maybe::Present);
                    read.pieces.iter().map(|piece| piece.placed()).eq(written)
                        && read.repair == first_repair
                        && (node.label() != NodeLabel::Wald
                            || read
                                .pieces
                                .iter()
                                .all(|piece| matches!(*piece, Piece::Operand(_))))
                },
            }),
            | Err(LoweringRefusal::UnknownMold { span, mold }) => {
                let rejected = |index| {
                    tree.node(index).is_some_and(|held| {
                        held.span() == span
                            && matches!(held.label(),
        NodeLabel::Tile(found) | NodeLabel::Meld(found) if found == mold)
                    })
                };
                (pbg.mold(mold).is_err() || pbg.rule_of(mold).is_err())
                    && (rejected(position) || tree.children(position).any(rejected))
            },
            | Err(_) => false,
        }
    },
)]
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
///
/// # Adequacy
/// - hypothesis: L3 — a parsed declaration distinguishes its own keyword/name
///   tiles from its numeric operand. Root children remain operands. An unknown
///   child mold under a named rule is refused at its own span after an earlier
///   tile.
/// - witness: `form::tests::a_form_reads_its_own_tiles_apart_from_its_operands`
/// - witness: `form::tests::an_unknown_child_mold_retains_only_the_new_prefix`
#[spec(
    requires: held.label() == NodeLabel::Tile(mold) && placed.span == held.span(),
    ensures: |ret| match ret {
        | Ok(Piece::Operand(at)) => {
            at == placed
                && match own {
                    | Holder::Root => true,
                    | Holder::Rule(rule) => {
                        pbg.rule_of(mold).is_ok_and(|child| child.name != rule.0)
                    },
                }
        },
        | Ok(Piece::Tile { label, at }) => {
            at == placed
                && matches!(own, Holder::Rule(rule)
    if pbg.rule_of(mold).is_ok_and(|child| child.name == rule.0))
                && pbg.mold(mold).is_ok_and(|tile| tile.label == label.0)
        },
        | Err(error) => {
            matches!(own, Holder::Rule(_))
                && (pbg.rule_of(mold).is_err() || pbg.mold(mold).is_err())
                && error
                    == LoweringRefusal::UnknownMold {
                        span: held.span(),
                        mold,
                    }
        },
    },
)]
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
///
/// # Adequacy
/// - hypothesis: L3 — the absent-to-present transition is observed with an
///   exact repair and span; a different later repair leaves the first intact. A
///   written piece remains present across both calls, separating note-taking
///   from clearing.
/// - witness: `form::tests::the_first_repair_survives_later_repairs`
#[spec(
    captures: before = (read.repair, read.pieces.len()),
    ensures: read.pieces.len() == before.1
        && read.repair
            == match before.0 {
                | Maybe::Present(first) => Maybe::Present(first),
                | Maybe::Absent(_) => Maybe::Present(Repaired {
                    span: placed.span,
                    repair,
                }),
            },
)]
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
///
/// # Adequacy
/// - hypothesis: L3 — a one-tile number and declaration punctuation observe
///   exact labels from the grammar. An unknown root tile is refused with its
///   mold and span while clearing the previous reading; no fallback label is
///   admitted.
/// - witness: `form::tests::a_one_tile_form_is_its_own_tile`
/// - witness: `form::tests::a_form_reads_its_own_tiles_apart_from_its_operands`
/// - witness: `form::tests::unknown_root_molds_clear_the_reused_buffer`
#[spec(
    requires: matches!(node.label(), NodeLabel::Meld(held) | NodeLabel::Tile(held) if held == mold),
    ensures: |ret| match ret {
        | Ok(label) => pbg.mold(mold).is_ok_and(|held| held.label == label.0),
        | Err(error) => {
            pbg.mold(mold).is_err()
                && error
                    == LoweringRefusal::UnknownMold {
                        span: node.span(),
                        mold,
                    }
        },
    },
)]
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
///
/// # Specification
/// - requires: a cursor supplies the maximal leading operand sequence.
/// - ensures: Empty names its gap, One names its sole operand, and Several
///   names its first two operands with a count of at least two.
/// - provides: operand cardinality without allocating another sequence.
/// - fails: does not retain the remaining operands for later inspection.
/// - panics: none.
/// - executable: none — type refinements require the disabled logic feature;
///   `Cursor::operands` checks cardinality and payloads together.
///
/// # Adequacy
/// - hypothesis: L3 — zero, one, two and three operands separate every
///   cardinality case. A following tile stops the run despite an operand beyond
///   it.
/// - witness: `form::tests::a_run_counts_the_operands_between_two_tiles`
/// - witness: `form::tests::an_operand_run_stops_at_the_first_tile`
/// - witness: `form::tests::an_empty_cursor_starts_at_the_form_start`
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
///
/// # Specification
/// - requires: the original piece slice and consumption history define the
///   current reading position.
/// - ensures: rest is the unconsumed suffix; edge is the last consumed piece
///   span, initially an empty span at the form start.
/// - provides: lookahead and consumption without copying the slice.
/// - fails: does not authenticate that supplied pieces belong to a tree.
/// - panics: none.
/// - executable: none — the original prefix and history are not retained;
///   cursor operations check each suffix/edge transition with captures.
///
/// # Adequacy
/// - hypothesis: L3 — initially empty and mixed-piece cursors observe both edge
///   sources; tile misses preserve position and maximal runs stop at tiles.
/// - witness: `form::tests::an_empty_cursor_starts_at_the_form_start`
/// - witness: `form::tests::a_cursor_reads_a_tile_only_by_its_label`
/// - witness: `form::tests::an_operand_run_stops_at_the_first_tile`
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
    /// - requires: nothing; the supplied slice is read in its given order.
    /// - ensures: the cursor borrows that slice without consuming a piece and
    ///   starts with an empty edge at the form's start, not its end.
    /// - provides: the initial lookahead and empty-hole position.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a nonzero, nonempty form span with an empty piece
    ///   slice separates start from end. Mixed pieces exercise the retained
    ///   first item; the predicate also checks the borrowed slice identity
    ///   without copying it.
    /// - witness: `form::tests::an_empty_cursor_starts_at_the_form_start`
    /// - witness: `form::tests::a_cursor_reads_a_tile_only_by_its_label`
    #[spec(
        ensures: |ret| {
            core::ptr::eq(&raw const *ret.rest, &raw const *pieces)
                && ret.edge.start() == form.start()
                && ret.edge.end() == form.start()
        },
    )]
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
    ///
    /// # Adequacy
    /// - hypothesis: L3 — mixed tile/operand reads observe the exact next piece
    ///   before consumption, and the final read observes exhausted absence.
    ///   Empty cursors exercise absence without a preceding successful read.
    /// - witness: `form::tests::reading_keeps_piece_order_and_the_terminal_gap`
    /// - witness: `form::tests::an_empty_cursor_starts_at_the_form_start`
    #[spec(
        ensures: |ret| {
            ret == self
                .rest
                .first()
                .copied()
                .map_or(Maybe::Absent(cursor::Absent::Exhausted), Maybe::Present)
        },
    )]
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
    ///
    /// # Adequacy
    /// - hypothesis: L3 — matching tiles, another label, an operand and
    ///   exhaustion separate presence, elsewhere and exhausted outcomes.
    ///   Subsequent reads observe that lookahead did not consume the offered
    ///   piece.
    /// - witness: `form::tests::a_cursor_reads_a_tile_only_by_its_label`
    /// - witness: `form::tests::reading_keeps_piece_order_and_the_terminal_gap`
    #[spec(
        ensures: |ret| match self.rest.first().copied() {
            | Some(Piece::Tile { label: held, at }) if held == label => ret == Maybe::Present(at),
            | Some(_) => ret == Maybe::Absent(cursor::Absent::Elsewhere),
            | None => ret == Maybe::Absent(cursor::Absent::Exhausted),
        },
    )]
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
    #[spec(
        captures: before = (self.rest, self.edge),
        ensures: |ret| match (before.0.split_first(), ret) {
            | (Some((&Piece::Tile { label: held, at }, rest)), Maybe::Present(found)) => {
                (held, found, self.edge) == (label, at, at.span)
                    && core::ptr::eq(&raw const *self.rest, &raw const *rest)
            },
            | (Some((piece, _)), Maybe::Absent(cursor::Absent::Elsewhere)) => {
                !matches!(*piece, Piece::Tile { label: held, .. } if held == label)
                    && self.edge == before.1
                    && core::ptr::eq(&raw const *self.rest, &raw const *before.0)
            },
            | (None, Maybe::Absent(cursor::Absent::Exhausted)) => {
                self.edge == before.1 && core::ptr::eq(&raw const *self.rest, &raw const *before.0)
            },
            | _ => false,
        },
    )]
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
    ///
    /// # Adequacy
    /// - hypothesis: L3 — two different pieces are read in order, with
    ///   lookahead before each and an exact terminal gap. Repeated exhaustion
    ///   keeps that gap rather than inventing a piece or moving the edge.
    /// - witness: `form::tests::reading_keeps_piece_order_and_the_terminal_gap`
    /// - witness: `form::tests::an_empty_cursor_starts_at_the_form_start`
    #[spec(
        captures: before = (self.rest, self.edge),
        ensures: |ret| match (before.0.split_first(), ret) {
            | (Some((&piece, rest)), Maybe::Present(found)) => {
                found == piece
                    && self.edge == piece.placed().span
                    && core::ptr::eq(&raw const *self.rest, &raw const *rest)
            },
            | (None, Maybe::Absent(cursor::Absent::Exhausted)) => {
                self.edge == before.1 && core::ptr::eq(&raw const *self.rest, &raw const *before.0)
            },
            | _ => false,
        },
    )]
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
    /// - hypothesis: L3 — empty, one-, two- and three-operand runs distinguish
    ///   the cardinality boundary and the first/extra payloads. A tile stops a
    ///   two-item run even when another operand follows it; exact gaps and
    ///   subsequent reads observe the retained suffix and the last consumed
    ///   edge.
    /// - witness: `form::tests::a_run_counts_the_operands_between_two_tiles`
    /// - witness: `form::tests::an_operand_run_stops_at_the_first_tile`
    /// - witness: `form::tests::an_empty_cursor_starts_at_the_form_start`
    #[spec(
        captures: before = (self.rest, self.edge),
        ensures: |ret| {
            let count = before
                .0
                .iter()
                .take_while(|&&piece| matches!(piece, Piece::Operand(_)))
                .count();
            before
                .0
                .split_at_checked(count)
                .is_some_and(|(prefix, rest)| {
                    let run_matches =
                        match (prefix.first().copied(), prefix.get(1_usize).copied(), ret) {
                            | (None, None, Run::Empty(span)) => {
                                span.start() == before.1.end() && span.end() == before.1.end()
                            },
                            | (Some(Piece::Operand(first)), None, Run::One(held)) => held == first,
                            | (
                                Some(Piece::Operand(first)),
                                Some(Piece::Operand(extra)),
                                Run::Several {
                                    first: held,
                                    extra: second,
                                    count: offered,
                                },
                            ) => {
                                held == first
                                    && second == extra
                                    && offered == OperandCount::from(count)
                            },
                            | _ => false,
                        };
                    run_matches
                        && core::ptr::eq(&raw const *self.rest, &raw const *rest)
                        && self.edge == prefix.last().map_or(before.1, |piece| piece.placed().span)
                })
        },
    )]
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
    ///
    /// # Adequacy
    /// - hypothesis: L3 — exact next-piece spans are observed before
    ///   consumption; exhaustion and an initially empty cursor instead report
    ///   zero-width gaps at the last edge and form start respectively.
    /// - witness: `form::tests::a_cursor_reads_a_tile_only_by_its_label`
    /// - witness: `form::tests::reading_keeps_piece_order_and_the_terminal_gap`
    /// - witness: `form::tests::an_empty_cursor_starts_at_the_form_start`
    #[spec(
        ensures: |ret| {
            self.rest.first().map_or_else(
                || ret.start() == self.edge.end() && ret.end() == self.edge.end(),
                |piece| ret == piece.placed().span,
            )
        },
    )]
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
    /// - requires: nothing.
    /// - ensures: an empty span at the current edge's end.
    /// - provides: the location of an empty operand run or exhausted cursor.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a nonzero initial form start and a consumed nonempty
    ///   piece separate the two edge sources. Both endpoints are asserted, so
    ///   returning the entire edge or its start is distinguished.
    /// - witness: `form::tests::an_empty_cursor_starts_at_the_form_start`
    /// - witness: `form::tests::a_cursor_reads_a_tile_only_by_its_label`
    #[spec(
        ensures: |ret| ret.start() == self.edge.end() && ret.end() == self.edge.end(),
    )]
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
    ///
    /// # Adequacy
    /// - hypothesis: L3 — tile and operand consumption observe the next item
    ///   and the terminal gap. The predicate requires the offered placement to
    ///   be the current piece and checks the exact borrowed suffix and new
    ///   edge.
    /// - witness: `form::tests::reading_keeps_piece_order_and_the_terminal_gap`
    /// - witness: `form::tests::a_cursor_reads_a_tile_only_by_its_label`
    /// - witness: `form::tests::an_operand_run_stops_at_the_first_tile`
    #[spec(
        requires: self
            .rest
            .first()
            .is_some_and(|piece| piece.placed() == placed),
        captures: before = self.rest,
        ensures: before
            .split_first()
            .is_some_and(|(_, rest)| core::ptr::eq(&raw const *self.rest, &raw const *rest))
            && self.edge == placed.span,
    )]
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

    use anodized::spec;
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
    /// - requires: a module root whose first written child is a readable
    ///   declaration, with all molds needed by that reading present in pbg.
    /// - ensures: returned written pieces belong to the first written child
    ///   rather than a later declaration.
    /// - provides: the declaration reading used by parsed form witnesses.
    /// - fails: never substitutes another declaration when reading fails.
    /// - panics: if the fixture does not meet those requirements.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — two clean declarations with different body spans
    ///   observe first-child selection. A buffer from a separate repaired tree
    ///   is then reused for the second declaration, observing replacement of
    ///   both its written pieces and repair record.
    /// - witness: `form::tests::reading_another_form_discards_old_pieces_and_repairs`
    /// - witness: `form::tests::a_form_reads_its_own_tiles_apart_from_its_operands`
    #[spec(
        ensures: |ret| {
            tree.children(tree.root())
                .find(|&index| {
                    tree.node(index).is_some_and(|node| {
                        !matches!(
                            node.label(),
                            super::NodeLabel::Space
                                | super::NodeLabel::Grout { .. }
                                | super::NodeLabel::GhostClose { .. }
                        )
                    })
                })
                .is_some_and(|declaration| {
                    ret.pieces.iter().all(|piece| {
                        tree.children(declaration)
                            .any(|child| child == piece.placed().node)
                    })
                })
        },
    )]
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
    /// - requires: nothing.
    /// - ensures: one sketch per piece, in order, retaining tile labels and
    ///   every span while omitting node positions.
    /// - provides: exact source-oriented observations of a form reading.
    /// - fails: never filters or reorders pieces.
    /// - panics: allocation failure follows the allocator policy.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — mixed own tiles and operands are asserted against
    ///   source spans, while a one-tile form and a reused reading exercise the
    ///   projection at different cardinalities. No statement compares node
    ///   identities.
    /// - witness: `form::tests::a_form_reads_its_own_tiles_apart_from_its_operands`
    /// - witness: `form::tests::reading_another_form_discards_old_pieces_and_repairs`
    /// - witness: `form::tests::a_one_tile_form_is_its_own_tile`
    #[spec(
        ensures: |ret| {
            ret.len() == pieces.pieces.len()
                && ret
                    .iter()
                    .zip(&pieces.pieces)
                    .all(|(held, piece)| match (*held, *piece) {
                        | (
                            Sketch::Tile(label, span),
                            Piece::Tile {
                                label: expected,
                                at,
                            },
                        ) => label == expected && span == at.span,
                        | (Sketch::Operand(span), Piece::Operand(at)) => span == at.span,
                        | _ => false,
                    })
        },
    )]
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

    #[test]
    fn an_empty_cursor_starts_at_the_form_start()
    {
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));
        let mut reading = Cursor::new(&[], at(4_usize, 9_usize));
        assert_eq!(reading.here(), at(4_usize, 4_usize));
        assert_eq!(reading.gap(), at(4_usize, 4_usize));
        assert_eq!(reading.operands(), Run::Empty(at(4_usize, 4_usize)));
        assert_eq!(reading.read(), Maybe::Absent(cursor::Absent::Exhausted));
        assert_eq!(
            reading.tile(TileName::DEF),
            Maybe::Absent(cursor::Absent::Exhausted)
        );
        assert_eq!(reading.here(), at(4_usize, 4_usize));
    }

    #[test]
    fn reading_keeps_piece_order_and_the_terminal_gap()
    {
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));
        let keyword = Piece::Tile {
            label: TileName::DEF,
            at: Placed {
                node: NodeIndex::from(1_usize),
                span: at(2_usize, 5_usize),
            },
        };
        let operand = Piece::Operand(Placed {
            node: NodeIndex::from(2_usize),
            span: at(6_usize, 9_usize),
        });
        let pieces = [keyword, operand];
        let mut reading = Cursor::new(&pieces, at(2_usize, 12_usize));
        for expected in pieces {
            assert_eq!(reading.peek(), Maybe::Present(expected));
            assert_eq!(reading.here(), expected.placed().span);
            assert_eq!(reading.read(), Maybe::Present(expected));
        }
        assert_eq!(reading.peek(), Maybe::Absent(cursor::Absent::Exhausted));
        assert_eq!(reading.read(), Maybe::Absent(cursor::Absent::Exhausted));
        assert_eq!(reading.here(), at(9_usize, 9_usize));
        assert_eq!(reading.read(), Maybe::Absent(cursor::Absent::Exhausted));
        assert_eq!(reading.here(), at(9_usize, 9_usize));
    }

    #[test]
    fn an_operand_run_stops_at_the_first_tile()
    {
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));
        let placed = |node: usize, start: usize, end: usize| Placed {
            node: NodeIndex::from(node),
            span: at(start, end),
        };
        let first = placed(1_usize, 0_usize, 1_usize);
        let second = placed(2_usize, 2_usize, 3_usize);
        let comma = placed(3_usize, 3_usize, 4_usize);
        let last = placed(4_usize, 5_usize, 6_usize);
        let pieces = [
            Piece::Operand(first),
            Piece::Operand(second),
            Piece::Tile {
                label: TileName::COMMA,
                at: comma,
            },
            Piece::Operand(last),
        ];
        let mut reading = Cursor::new(&pieces, at(0_usize, 6_usize));
        assert_eq!(reading.operands(), Run::Several {
            first,
            extra: second,
            count: OperandCount::from(2_usize),
        });
        assert_eq!(reading.here(), comma.span);
        assert_eq!(reading.operands(), Run::Empty(at(3_usize, 3_usize)));
        assert_eq!(reading.tile(TileName::COMMA), Maybe::Present(comma));
        assert_eq!(reading.operands(), Run::One(last));
        assert_eq!(reading.operands(), Run::Empty(at(6_usize, 6_usize)));
    }

    #[test]
    fn the_first_repair_survives_later_repairs()
    {
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));
        let written = Piece::Operand(Placed {
            node: NodeIndex::from(1_usize),
            span: at(0_usize, 1_usize),
        });
        let first = Placed {
            node: NodeIndex::from(2_usize),
            span: at(1_usize, 1_usize),
        };
        let later = Placed {
            node: NodeIndex::from(3_usize),
            span: at(3_usize, 3_usize),
        };
        let mut read = Pieces::new();
        read.pieces.push(written);
        super::note_repair(&mut read, first, Repair::Grout(GroutShape::Postfix));
        let expected = Maybe::Present(Repaired {
            span: first.span,
            repair: Repair::Grout(GroutShape::Postfix),
        });
        assert_eq!(read.repair, expected);
        super::note_repair(
            &mut read,
            later,
            Repair::GhostClose(gandr_surface_syntax::ClosingClass::Bracket),
        );
        assert_eq!(read.repair, expected);
        assert_eq!(read.pieces, [written]);
    }

    #[test]
    fn reading_another_form_discards_old_pieces_and_repairs()
    {
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));
        let pbg = grammar();
        let tree = repaired(&pbg, SourceText::from("def x ;"));
        let mut read = first_declaration(&pbg, &tree);
        assert_eq!(
            read.repair,
            Maybe::Present(Repaired {
                span: at(5_usize, 5_usize),
                repair: Repair::Grout(GroutShape::Postfix),
            })
        );
        let tree = parsed(&pbg, SourceText::from("def y = 3 ; def z = 4 ;"));
        assert_eq!(sketch(&first_declaration(&pbg, &tree)), [
            Sketch::Tile(TileName::DEF, at(0_usize, 3_usize)),
            Sketch::Tile(TileName::IDENTIFIER, at(4_usize, 5_usize)),
            Sketch::Tile(TileName::EQUALS, at(6_usize, 7_usize)),
            Sketch::Operand(at(8_usize, 9_usize)),
            Sketch::Tile(TileName::SEMICOLON, at(10_usize, 11_usize)),
        ]);
        let mut root = Pieces::new();
        read_pieces(&pbg, &tree, tree.root(), &mut root).unwrap();
        let second = root.pieces[1_usize].placed();
        read_pieces(&pbg, &tree, second.node, &mut read).unwrap();
        assert_eq!(
            read.repair,
            Maybe::Absent(super::repair::Absent::Unrepaired)
        );
        assert_eq!(sketch(&read), [
            Sketch::Tile(TileName::DEF, at(12_usize, 15_usize)),
            Sketch::Tile(TileName::IDENTIFIER, at(16_usize, 17_usize)),
            Sketch::Tile(TileName::EQUALS, at(18_usize, 19_usize)),
            Sketch::Operand(at(20_usize, 21_usize)),
            Sketch::Tile(TileName::SEMICOLON, at(22_usize, 23_usize)),
        ]);
    }

    #[test]
    fn an_unknown_child_mold_retains_only_the_new_prefix()
    {
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));
        let pbg = grammar();
        let mut made = crate::fixture::Handmade::new(&pbg, SourceText::from("def x"));
        let keyword = made.tile(
            crate::fixture::Rule("def_value"),
            crate::fixture::Spelled("def"),
            at(0_usize, 3_usize),
        );
        let mold = gandr_surface_syntax::MoldId::from(u32::MAX);
        let unknown = made.raw(super::NodeLabel::Tile(mold), at(4_usize, 5_usize), &[]);
        let parent = made.meld(
            crate::fixture::Rule("def_value"),
            crate::fixture::Spelled("def"),
            at(0_usize, 5_usize),
            &[keyword, unknown],
        );
        let tree = made.finish(parent);
        let mut read = Pieces::new();
        read.pieces.push(Piece::Operand(Placed {
            node: tree.root(),
            span: at(0_usize, 5_usize),
        }));
        read.repair = Maybe::Present(Repaired {
            span: at(0_usize, 0_usize),
            repair: Repair::Grout(GroutShape::Convex),
        });
        assert_eq!(
            read_pieces(&pbg, &tree, tree.root(), &mut read),
            Err(crate::error::LoweringRefusal::UnknownMold {
                span: at(4_usize, 5_usize),
                mold
            })
        );
        assert_eq!(sketch(&read), [Sketch::Tile(
            TileName::DEF,
            at(0_usize, 3_usize)
        )]);
        assert_eq!(
            read.repair,
            Maybe::Absent(super::repair::Absent::Unrepaired)
        );
    }

    #[test]
    fn unknown_root_molds_clear_the_reused_buffer()
    {
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));
        let pbg = grammar();
        let mold = gandr_surface_syntax::MoldId::from(u32::MAX);
        for label in [super::NodeLabel::Tile(mold), super::NodeLabel::Meld(mold)] {
            let mut made = crate::fixture::Handmade::new(&pbg, SourceText::from("x"));
            let root = made.raw(label, at(0_usize, 1_usize), &[]);
            let tree = made.finish(root);
            let mut read = Pieces::new();
            read.pieces.push(Piece::Operand(Placed {
                node: tree.root(),
                span: at(0_usize, 1_usize),
            }));
            read.repair = Maybe::Present(Repaired {
                span: at(0_usize, 0_usize),
                repair: Repair::Grout(GroutShape::Convex),
            });
            assert_eq!(
                read_pieces(&pbg, &tree, tree.root(), &mut read),
                Err(crate::error::LoweringRefusal::UnknownMold {
                    span: at(0_usize, 1_usize),
                    mold
                })
            );
            assert!(read.pieces.is_empty());
            assert_eq!(
                read.repair,
                Maybe::Absent(super::repair::Absent::Unrepaired)
            );
        }
    }

    #[test]
    fn every_label_shape_is_read_and_unknown_molds_are_located()
    {
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));
        let pbg = grammar();
        let mut made = crate::fixture::Handmade::new(&pbg, SourceText::from("def 1 "));
        let keyword = made.tile(
            crate::fixture::Rule("def_value"),
            crate::fixture::Spelled("def"),
            at(0_usize, 3_usize),
        );
        let declaration = made.meld(
            crate::fixture::Rule("def_value"),
            crate::fixture::Spelled("def"),
            at(0_usize, 3_usize),
            &[keyword],
        );
        let number = made.tile(
            crate::fixture::Rule("number.expression"),
            crate::fixture::Spelled("number"),
            at(4_usize, 5_usize),
        );
        let layout = made.raw(super::NodeLabel::Space, at(5_usize, 6_usize), &[]);
        let grout = made.raw(
            super::NodeLabel::Grout {
                sort: gandr_surface_syntax::GroutSort::from(0_u16),
                shape: GroutShape::Infix,
            },
            at(5_usize, 5_usize),
            &[],
        );
        let ghost = made.raw(
            super::NodeLabel::GhostClose {
                sort: gandr_surface_syntax::GroutSort::from(0_u16),
                class: gandr_surface_syntax::ClosingClass::Bracket,
            },
            at(5_usize, 5_usize),
            &[],
        );
        let mold = gandr_surface_syntax::MoldId::from(u32::MAX);
        let unknown = made.raw(super::NodeLabel::Tile(mold), at(5_usize, 6_usize), &[]);
        let tree = made.module(at(0_usize, 6_usize), &[
            declaration,
            number,
            layout,
            grout,
            ghost,
            unknown,
        ]);
        assert_eq!(
            super::shape_of(&pbg, tree.node(tree.root()).unwrap()),
            Ok(super::Shape::Root)
        );
        let expected = [
            Ok(super::Shape::Form {
                name: FormName::DECLARATION,
                former: Former::Declaration,
            }),
            Ok(super::Shape::Form {
                name: FormName::from(NamedKind("number")),
                former: Former::Number,
            }),
            Ok(super::Shape::Layout),
            Ok(super::Shape::Repair(Repair::Grout(GroutShape::Infix))),
            Ok(super::Shape::Repair(Repair::GhostClose(
                gandr_surface_syntax::ClosingClass::Bracket,
            ))),
            Err(crate::error::LoweringRefusal::UnknownMold {
                span: at(5_usize, 6_usize),
                mold,
            }),
        ];
        for (child, shape) in tree.children(tree.root()).zip(expected) {
            assert_eq!(super::shape_of(&pbg, tree.node(child).unwrap()), shape);
            if matches!(shape, Ok(super::Shape::Layout | super::Shape::Repair(_))) {
                let mut read = Pieces::new();
                read.pieces.push(Piece::Operand(Placed {
                    node: tree.root(),
                    span: at(0_usize, 6_usize),
                }));
                read.repair = Maybe::Present(Repaired {
                    span: at(0_usize, 0_usize),
                    repair: Repair::Grout(GroutShape::Convex),
                });
                read_pieces(&pbg, &tree, child, &mut read).unwrap();
                assert!(read.pieces.is_empty());
                assert_eq!(
                    read.repair,
                    Maybe::Absent(super::repair::Absent::Unrepaired)
                );
            }
        }
    }
}
