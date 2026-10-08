//! The closed lexical vocabulary of the surface fragment: [`TokenKind`], its
//! fixed spellings, and the spanned [`Token`] a lexer emits.
//!
//! The vocabulary lives beside the tree rather than inside the lexer because
//! two consumers read it. The lexer produces the stream; a re-render walks a
//! tree back into one, and the two are compared. A vocabulary owned by the
//! producer would make that comparison a producer agreeing with itself.
//!
//! # No trivia and no end marker
//!
//! Whitespace, and any later comment form, are skipped by the lexer rather than
//! carried as tokens: a tree that does not retain trivia could not re-render a
//! stream containing it, and the round-trip comparison is the reason the
//! vocabulary is shared at all. The stream likewise ends by exhaustion rather
//! than with a marker token, so the tokens of a source are exactly its
//! significant lexemes.
//!
//! # Type heads are identifiers
//!
//! `Unit`, `Integer`, `String`, `U` and `F` are [`TokenKind::Identifier`]
//! tokens, not keywords: a misspelled type head is an unresolved name carrying
//! its span, and a reserved-word list would instead give the same mistake a
//! different class depending on how it was misspelled. The keyword set is
//! therefore only the four forms whose shape the grammar depends on.

use crate::span::ByteSpan;

/// The fixed spelling of a token kind that has exactly one.
///
/// A kind whose text varies — an identifier, a literal — has no spelling, which
/// is the distinction this type's absence carries.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct TokenSpelling(&'static str);

impl From<&'static str> for TokenSpelling
{
    /// Read a static string as a kind's fixed spelling.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(spelling: &'static str) -> Self
    {
        Self(spelling)
    }
}

impl From<TokenSpelling> for &'static str
{
    /// Read the spelling back out as a static string.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(spelling: TokenSpelling) -> Self
    {
        spelling.0
    }
}

impl AsRef<str> for TokenSpelling
{
    /// Borrow the spelling's text.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn as_ref(&self) -> &str
    {
        self.0
    }
}

impl core::fmt::Display for TokenSpelling
{
    /// Write the spelling.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: writes exactly the kind's fixed text, neither escaped nor
    ///   quoted, so a re-render of a spelled token reproduces the lexeme the
    ///   lexer read.
    /// - provides: the half of the round-trip comparison that turns a kind back
    ///   into source.
    /// - fails: propagates the formatter's own write failure unchanged.
    /// - panics: none.
    #[inline]
    fn fmt(
        &self,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result
    {
        f.write_str(self.0)
    }
}

/// Every lexeme class the surface fragment admits.
///
/// The enum is closed: a form the fragment does not admit has no kind here, so
/// widening the surface is a source change that breaks every consumer until
/// each has considered the new form.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum TokenKind
{
    /// The `def` keyword, which leads every declaration.
    Def,
    /// The `thunk` keyword, which leads a suspended computation.
    Thunk,
    /// The `return` keyword, which leads a returner computation.
    Return,
    /// The `force` keyword, which leads a forced thunk.
    Force,

    /// An identifier: a declared name, a binder, or a type head.
    Identifier,
    /// An integer literal.
    IntegerLiteral,
    /// A quoted text literal.
    TextLiteral,

    /// `:`, which separates a declared name from its type.
    Colon,
    /// `;`, which ends a declaration.
    Semicolon,
    /// `=`, which separates a declared name from its definition.
    Equals,
    /// `,`, which separates attributes and the components of a pair.
    Comma,
    /// `.`, which separates a lambda's binder from its body.
    Dot,
    /// `\`, which leads a lambda.
    Backslash,
    /// `->`, the arrow of a computation type.
    Arrow,
    /// `*`, the reserved product former.
    Star,

    /// `(`, which opens a grouping or a pair.
    LeftParen,
    /// `)`, which closes a grouping or a pair.
    RightParen,
    /// `{`, which opens a thunk body.
    LeftBrace,
    /// `}`, which closes a thunk body.
    RightBrace,
    /// `@[`, which opens an attribute block.
    AtBracket,
    /// `]`, which closes an attribute block.
    RightBracket,
}

impl TokenKind
{
    /// Every token kind, in vocabulary order.
    pub const ALL: [Self; 21_usize] = [
        Self::Def,
        Self::Thunk,
        Self::Return,
        Self::Force,
        Self::Identifier,
        Self::IntegerLiteral,
        Self::TextLiteral,
        Self::Colon,
        Self::Semicolon,
        Self::Equals,
        Self::Comma,
        Self::Dot,
        Self::Backslash,
        Self::Arrow,
        Self::Star,
        Self::LeftParen,
        Self::RightParen,
        Self::LeftBrace,
        Self::RightBrace,
        Self::AtBracket,
        Self::RightBracket,
    ];

    /// The one spelling this kind is written with, when it has one.
    ///
    /// # Specification
    /// - requires: nothing; the function is total over the vocabulary.
    /// - ensures: a keyword or punctuation kind yields exactly the characters a
    ///   lexer matches for it and a re-render emits for it; an identifier or a
    ///   literal yields nothing, because its text is drawn from the source.
    /// - provides: the shared spelling table the lexer and the tree-to-stream
    ///   re-render are both written against, so neither can drift from the
    ///   other without the differential noticing. This stays a `const fn`
    ///   without `#[spec]`: the pinned `anodized` expansion calls a non-const
    ///   evaluator (`E0015`).
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the vocabulary is a finite class, enumerated
    ///   exhaustively with each kind's exact spelling asserted, and the three
    ///   text-bearing kinds asserted to have none; a swapped or dropped table
    ///   row changes one asserted pair.
    /// - witness: `token::tests::every_fixed_spelling_is_pinned`
    /// - witness: `token::tests::the_text_bearing_kinds_have_no_fixed_spelling`
    #[inline]
    #[must_use]
    pub const fn spelling(self) -> Option<TokenSpelling>
    {
        let spelling = match self {
            | Self::Def => "def",
            | Self::Thunk => "thunk",
            | Self::Return => "return",
            | Self::Force => "force",
            | Self::Identifier | Self::IntegerLiteral | Self::TextLiteral => return None,
            | Self::Colon => ":",
            | Self::Semicolon => ";",
            | Self::Equals => "=",
            | Self::Comma => ",",
            | Self::Dot => ".",
            | Self::Backslash => "\\",
            | Self::Arrow => "->",
            | Self::Star => "*",
            | Self::LeftParen => "(",
            | Self::RightParen => ")",
            | Self::LeftBrace => "{",
            | Self::RightBrace => "}",
            | Self::AtBracket => "@[",
            | Self::RightBracket => "]",
        };

        Some(TokenSpelling(spelling))
    }
}

/// One lexeme: its kind and the source range it covers.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Token
{
    /// The lexeme's class.
    kind: TokenKind,
    /// The bytes of the source the lexeme covers.
    span: ByteSpan,
}

impl Token
{
    /// The token of `kind` covering `span`.
    ///
    /// # Specification
    /// - requires: `span` was minted against the source the token was read
    ///   from, and covers exactly that lexeme; neither claim is checkable here,
    ///   since a span carries no source provenance.
    /// - ensures: the token carries exactly the kind and span offered.
    /// - provides: the one way to mint a token, so a stream and a re-render are
    ///   comparable term by term.
    /// - fails: never.
    /// - panics: none.
    #[inline]
    #[must_use]
    pub const fn new(
        kind: TokenKind,
        span: ByteSpan,
    ) -> Self
    {
        Self { kind, span }
    }

    /// The lexeme's class.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn kind(self) -> TokenKind
    {
        self.kind
    }

    /// The bytes of the source the lexeme covers.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn span(self) -> ByteSpan
    {
        self.span
    }
}

#[cfg(test)]
mod tests
{
    use super::Token;
    use super::TokenKind;
    use super::TokenSpelling;
    use crate::span::ByteOffset;
    use crate::span::ByteSpan;

    #[test]
    fn every_token_kind_is_listed_once()
    {
        for kind in TokenKind::ALL {
            // Exhaustive by construction: a kind added to the vocabulary does
            // not compile until it is listed here and in `ALL`.
            let ordinal = match kind {
                | TokenKind::Def => 0_usize,
                | TokenKind::Thunk => 1_usize,
                | TokenKind::Return => 2_usize,
                | TokenKind::Force => 3_usize,
                | TokenKind::Identifier => 4_usize,
                | TokenKind::IntegerLiteral => 5_usize,
                | TokenKind::TextLiteral => 6_usize,
                | TokenKind::Colon => 7_usize,
                | TokenKind::Semicolon => 8_usize,
                | TokenKind::Equals => 9_usize,
                | TokenKind::Comma => 10_usize,
                | TokenKind::Dot => 11_usize,
                | TokenKind::Backslash => 12_usize,
                | TokenKind::Arrow => 13_usize,
                | TokenKind::Star => 14_usize,
                | TokenKind::LeftParen => 15_usize,
                | TokenKind::RightParen => 16_usize,
                | TokenKind::LeftBrace => 17_usize,
                | TokenKind::RightBrace => 18_usize,
                | TokenKind::AtBracket => 19_usize,
                | TokenKind::RightBracket => 20_usize,
            };

            assert_eq!(
                TokenKind::ALL[ordinal],
                kind,
                "the vocabulary list holds each kind at its own position"
            );
        }

        assert_eq!(
            TokenKind::ALL.len(),
            21_usize,
            "the vocabulary has twenty-one kinds"
        );
    }

    #[test]
    fn every_fixed_spelling_is_pinned()
    {
        let expected = [
            (TokenKind::Def, "def"),
            (TokenKind::Thunk, "thunk"),
            (TokenKind::Return, "return"),
            (TokenKind::Force, "force"),
            (TokenKind::Colon, ":"),
            (TokenKind::Semicolon, ";"),
            (TokenKind::Equals, "="),
            (TokenKind::Comma, ","),
            (TokenKind::Dot, "."),
            (TokenKind::Backslash, "\\"),
            (TokenKind::Arrow, "->"),
            (TokenKind::Star, "*"),
            (TokenKind::LeftParen, "("),
            (TokenKind::RightParen, ")"),
            (TokenKind::LeftBrace, "{"),
            (TokenKind::RightBrace, "}"),
            (TokenKind::AtBracket, "@["),
            (TokenKind::RightBracket, "]"),
        ];

        for (kind, spelling) in expected {
            assert_eq!(
                kind.spelling(),
                Some(TokenSpelling::from(spelling)),
                "the spelling table is pinned row by row"
            );
        }

        assert_eq!(
            expected.len(),
            18_usize,
            "eighteen of the twenty-one kinds have a fixed spelling"
        );
    }

    #[test]
    fn the_text_bearing_kinds_have_no_fixed_spelling()
    {
        for kind in [
            TokenKind::Identifier,
            TokenKind::IntegerLiteral,
            TokenKind::TextLiteral,
        ] {
            assert_eq!(
                kind.spelling(),
                None,
                "a kind whose text comes from the source has no fixed spelling"
            );
        }
    }

    #[test]
    fn a_token_keeps_its_kind_and_span()
    {
        let span = ByteSpan::new(ByteOffset::from(3_usize), ByteOffset::from(6_usize)).unwrap();
        let token = Token::new(TokenKind::Identifier, span);

        assert_eq!(
            token.kind(),
            TokenKind::Identifier,
            "the kind is the offered kind"
        );
        assert_eq!(token.span(), span, "the span is the offered span");
    }
}
