//! The labeler: a hand-rolled DFA over source bytes into lexical tokens.
//!
//! `label` is the front of the batch pipeline
//! (`labeler ∘ molder ∘ fold(push) ∘ commit`). It is a total scan over `&[u8]`
//! — no `logos`, no `phf`, no proc-macro — that classifies each maximal lexeme
//! into a [`Lexeme`] class and records its exact byte span. The classes mirror
//! the lexical surface of gandr's tree-sitter grammar:
//!
//! * trivia — whitespace, newlines, `//` line comments, nested `/* */` block
//!   comments, and `#!/…` shebangs (the tree-sitter `extras`) — classify as
//!   [`Lexeme::Space`], stored as layout for losslessness and skipped by the
//!   content digest (that invariance holds in `gandr-surface-syntax`);
//! * every non-trivia lexeme is handed to the molder, which resolves the
//!   grammar tile label(s) by dry-run (`crate::mold`);
//! * a byte the grammar has no tile for classifies as [`Lexeme::Unknown`] and
//!   flows the [`crate::Oblig::UnmoldedTok`] path in the molder — never a lexer
//!   error (totality extends to the labeler).
//!
//! Lexical ambiguity (a lowercase word is an `identifier` or a `type_variable`;
//! an uppercase word is a `constructor`, a `type_identifier`, or a keyword like
//! `Type` / `Integer`) is **not** resolved here: the labeler emits the class
//! and the exact text, and the molder enumerates the candidate molds over the
//! text-as-label plus the class's generic labels, picking the obligation
//! minimum (`crate::mold::candidate_labels`).

use alloc::vec::Vec;

use gandr_surface_syntax::SourceFragment;

/// The lexical class of one maximal lexeme.
///
/// The class is the labeler's whole output vocabulary; the molder maps each
/// non-space, non-unknown class plus the lexeme text to grammar tile labels.
///
/// # Specification
/// - requires: none.
/// - ensures: exactly one class is assigned per maximal lexeme.
/// - provides: the closed labeler output vocabulary the molder consumes.
/// - fails: never.
/// - panics: none.
/// - executable: none — this carrier has no entry or return boundary; the
///   labeler and token-text observer carry its executable obligations.
///
/// # Adequacy
/// - hypothesis: L3 — host and shell contexts cover the complete lexical
///   vocabulary with exact class streams and source spans. Wrong modes, missing
///   classes and shifted spans change these observations.
/// - witness: `label::tests::every_lexical_class_has_a_contextual_witness`
/// - witness: `label::tests::labels_a_definition_losslessly`
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Lexeme
{
    /// A lowercase-led word: an `identifier`, a `type_variable`, or a keyword.
    LowerWord,
    /// An uppercase-led word: a `constructor`, a `type_identifier`, a primitive
    /// type name, or an uppercase keyword (`Type`).
    UpperWord,
    /// A numeric literal with no primitive-type suffix.
    Number,
    /// A numeric literal with a mandatory primitive-type suffix.
    TypedNumber,
    /// A single-quoted character literal.
    Character,
    /// A string delimiter `"`.
    Quote,
    /// A run of ordinary string content between escapes and the closing quote.
    StringFragment,
    /// A backslash escape inside a string or character.
    EscapeSequence,
    /// An operator or punctuation tile whose label is its exact text.
    Punct,
    /// A bare word inside a shell block (a `command_name` / `shell_word` /
    /// `argument` run over the shell-word byte class).
    ShellWord,
    /// A command-local environment assignment `NAME=value` inside a shell
    /// block: one whole token, the shape the tree-sitter `token(seq(…))`
    /// `environment_assignment` and the PBG's single-tile atom both expect.
    /// A shell word whose name part is not identifier-shaped
    /// (`--color=auto`) or that has no name (`=`) stays a
    /// [`Lexeme::ShellWord`].
    EnvAssign,
    /// The raw interior of a single-quoted shell string (`'…'`): everything
    /// between the quotes verbatim (the tree-sitter `single_quoted_string`'s
    /// `token.immediate(/[^']*/)`), one opaque `single_quoted_content` tile.
    SingleQuotedContent,
    /// A shell variable name after `$` (`$name`): the `variable_name` tile of a
    /// `variable_expansion` (tree-sitter `variable_expansion`).
    VariableName,
    /// A shell subshell opener `[` (tree-sitter `subshell` = `[ … ]`). A
    /// shell-context bracket, DISTINCT from the host list-literal `[`, so a
    /// subshell never widens the host `[` mold menu.
    SubshellOpen,
    /// A shell subshell closer `]`, the shell-context partner of
    /// [`Lexeme::SubshellOpen`].
    SubshellClose,
    /// A shell redirection file descriptor: a digit run immediately before a
    /// `<` / `>` redirection operator (`2>`, `2>&1`; tree-sitter
    /// `file_descriptor`). A bare digit run NOT before a redirection stays an
    /// ordinary shell word.
    FileDescriptor,
    /// Insignificant layout: whitespace, newlines, comments, or a shebang.
    Space,
    /// A byte the grammar has no tile for (the `UnmoldedTok` path).
    Unknown,
}

/// Borrowed UTF-8 source bytes under the labeler's cursor domain.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
struct SourceBytes<'source>(&'source [u8]);

impl SourceBytes<'_>
{
    /// Return an empty borrowed byte buffer.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    fn empty() -> Self
    {
        Self(&[])
    }

    /// Return the byte length as a lexer cursor offset.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    fn len(self) -> ByteOffset
    {
        ByteOffset::from(self.0.len())
    }

    /// Return the byte at `pos` when it is inside the source buffer.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    fn byte(
        self,
        pos: ByteOffset,
    ) -> Option<SourceByte>
    {
        self.0.get(usize::from(pos)).copied().map(SourceByte::from)
    }

    /// Return the borrowed byte slice covered by `start .. end`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    fn span(
        self,
        start: ByteOffset,
        end: ByteOffset,
    ) -> Option<Self>
    {
        self.0.get(usize::from(start) .. usize::from(end)).map(Self)
    }

    /// Return whether the whole byte slice equals `pattern`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    fn equals(
        self,
        pattern: BytePattern<'_>,
    ) -> BytePredicate
    {
        BytePredicate::from(self.0 == pattern.0)
    }

    /// Return whether the byte slice starts with `pattern`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    fn starts_with(
        self,
        pattern: BytePattern<'_>,
    ) -> BytePredicate
    {
        BytePredicate::from(self.0.starts_with(pattern.0))
    }

    /// Return whether the byte slice ends with `pattern`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    fn ends_with(
        self,
        pattern: BytePattern<'_>,
    ) -> BytePredicate
    {
        BytePredicate::from(self.0.ends_with(pattern.0))
    }

    /// Return whether `start .. end` equals `pattern`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    fn span_matches(
        self,
        start: ByteOffset,
        end: ByteOffset,
        pattern: BytePattern<'_>,
    ) -> BytePredicate
    {
        BytePredicate::from(self.0.get(usize::from(start) .. usize::from(end)) == Some(pattern.0))
    }
}

impl<'source> From<&'source [u8]> for SourceBytes<'source>
{
    /// Borrow a byte slice as the scanner's source bytes.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: &'source [u8]) -> Self
    {
        Self(value)
    }
}

/// Borrowed byte-pattern literal used for lexer lookahead checks.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
struct BytePattern<'pattern>(&'pattern [u8]);

/// Host byte cursor in the labeler's source buffer.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct ByteOffset(usize);

impl ByteOffset
{
    /// Start of a source buffer.
    const ZERO: Self = Self(0);

    /// Advance this cursor by a checked byte width, saturating at host maximum.
    ///
    /// # Specification
    /// - ensures: the cursor advances by the width, saturating at the host
    ///   ceiling.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — zero, ordinary and host-ceiling operands expose exact
    ///   cursors; arithmetic wrap, wrong direction and an off-by-one saturation
    ///   boundary change the observed offsets.
    /// - witness: `label::tests::cursor_arithmetic_saturates_at_both_boundaries`
    #[inline]
    #[must_use]
    #[anodized::spec(ensures: |ret| ret.0 == self.0.saturating_add(width.0))]
    fn advance(
        self,
        width: ByteWidth,
    ) -> Self
    {
        Self(self.0.saturating_add(width.0))
    }

    /// Move this cursor backwards by a byte width, saturating at zero.
    ///
    /// # Specification
    /// - ensures: the cursor moves back by the width, saturating at zero.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — zero, ordinary and host-ceiling operands expose exact
    ///   cursors; arithmetic wrap, wrong direction and an off-by-one saturation
    ///   boundary change the observed offsets.
    /// - witness: `label::tests::cursor_arithmetic_saturates_at_both_boundaries`
    #[inline]
    #[must_use]
    #[anodized::spec(ensures: |ret| ret.0 == self.0.saturating_sub(width.0))]
    fn retreat(
        self,
        width: ByteWidth,
    ) -> Self
    {
        Self(self.0.saturating_sub(width.0))
    }
}

impl From<usize> for ByteOffset
{
    /// Adopt a host offset as a scanner cursor.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: usize) -> Self
    {
        Self(value)
    }
}

impl From<ByteOffset> for usize
{
    /// Read the cursor back as a host offset.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: ByteOffset) -> Self
    {
        value.0
    }
}

/// Width in UTF-8/source bytes.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct ByteWidth(usize);

impl ByteWidth
{
    /// One byte.
    const ONE: Self = Self(1);
    /// Two bytes.
    const TWO: Self = Self(2);
    /// Three bytes.
    const THREE: Self = Self(3);
    /// Four bytes.
    const FOUR: Self = Self(4);
}

impl From<usize> for ByteWidth
{
    /// Adopt a host width as a byte width.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: usize) -> Self
    {
        Self(value)
    }
}

impl From<ByteWidth> for usize
{
    /// Read the width back as a host width.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: ByteWidth) -> Self
    {
        value.0
    }
}

/// One source byte under a lexical byte-class predicate.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
struct SourceByte(u8);

impl SourceByte
{
    /// Return whether this byte is an ASCII digit.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    fn is_ascii_digit(self) -> BytePredicate
    {
        BytePredicate::from(u8::from(self).is_ascii_digit())
    }

    /// Return whether this byte can start a shell variable name (`[A-Za-z_]`).
    ///
    /// # Specification
    /// - ensures: accepts ASCII letters and underscore.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — all 256 byte values are compared with the explicit
    ///   lexical alphabet, including both neighbors of every ASCII class
    ///   boundary. Missing members and accidental additions flip an observed
    ///   classification.
    /// - witness: `label::tests::byte_classes_match_the_complete_byte_domain`
    #[inline]
    #[must_use]
    #[anodized::spec(ensures: |ret| bool::from(ret) == matches!(self.0, b'A' ..= b'Z' | b'a' ..= b'z' | b'_'))]
    fn is_var_name_start(self) -> BytePredicate
    {
        let byte = u8::from(self);
        BytePredicate::from(byte.is_ascii_alphabetic() || byte == b'_')
    }

    /// Return whether this byte continues a word `[A-Za-z0-9_]`.
    ///
    /// # Specification
    /// - ensures: accepts ASCII letters, digits and underscore.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — all 256 byte values are compared with the explicit
    ///   lexical alphabet, including both neighbors of every ASCII class
    ///   boundary. Missing members and accidental additions flip an observed
    ///   classification.
    /// - witness: `label::tests::byte_classes_match_the_complete_byte_domain`
    #[inline]
    #[must_use]
    #[anodized::spec(ensures: |ret| bool::from(ret) == matches!(self.0, b'A' ..= b'Z' | b'a' ..= b'z' | b'0' ..= b'9' | b'_'))]
    fn is_word_continue(self) -> BytePredicate
    {
        let byte = u8::from(self);
        BytePredicate::from(byte.is_ascii_alphanumeric() || byte == b'_')
    }

    /// Return whether this byte continues a shell word.
    ///
    /// # Specification
    /// - ensures: accepts every byte except shell separators and delimiters.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — all 256 byte values are compared with the explicit
    ///   lexical alphabet, including both neighbors of every ASCII class
    ///   boundary. Missing members and accidental additions flip an observed
    ///   classification.
    /// - witness: `label::tests::byte_classes_match_the_complete_byte_domain`
    #[inline]
    #[must_use]
    #[anodized::spec(ensures: |ret| bool::from(ret) != b" \t\r\n\x0c\x0b;|&<>{}[]()`\"'$#".contains(&self.0))]
    fn is_shell_word(self) -> BytePredicate
    {
        BytePredicate::from(!matches!(
            u8::from(self),
            b' ' | b'\t'
                | b'\r'
                | b'\n'
                | 0x0c
                | 0x0b
                | b';'
                | b'|'
                | b'&'
                | b'<'
                | b'>'
                | b'{'
                | b'}'
                | b'['
                | b']'
                | b'('
                | b')'
                | b'`'
                | b'"'
                | b'\''
                | b'$'
                | b'#'
        ))
    }

    /// Return whether this byte can appear in a shell dialect word.
    ///
    /// # Specification
    /// - ensures: accepts ASCII letters, digits, underscore and hyphen.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — all 256 byte values are compared with the explicit
    ///   lexical alphabet, including both neighbors of every ASCII class
    ///   boundary. Missing members and accidental additions flip an observed
    ///   classification.
    /// - witness: `label::tests::byte_classes_match_the_complete_byte_domain`
    #[inline]
    #[must_use]
    #[anodized::spec(ensures: |ret| bool::from(ret) == matches!(self.0, b'A' ..= b'Z' | b'a' ..= b'z' | b'0' ..= b'9' | b'_' | b'-'))]
    fn is_dialect(self) -> BytePredicate
    {
        let byte = u8::from(self);
        BytePredicate::from(byte.is_ascii_alphanumeric() || byte == b'_' || byte == b'-')
    }

    /// Return whether this byte can start a lowercase-led word.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    fn is_lower_start(self) -> BytePredicate
    {
        BytePredicate::from(u8::from(self).is_ascii_lowercase())
    }

    /// Return whether this byte can start an uppercase-led word.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    fn is_upper_start(self) -> BytePredicate
    {
        BytePredicate::from(u8::from(self).is_ascii_uppercase())
    }

    /// Return whether this byte is a single-character operator/punctuation
    /// tile.
    ///
    /// # Specification
    /// - ensures: accepts exactly the single-byte operator vocabulary.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — all 256 byte values are compared with the explicit
    ///   lexical alphabet, including both neighbors of every ASCII class
    ///   boundary. Missing members and accidental additions flip an observed
    ///   classification.
    /// - witness: `label::tests::byte_classes_match_the_complete_byte_domain`
    #[inline]
    #[must_use]
    #[anodized::spec(ensures: |ret| bool::from(ret) == b"!&()*+,-:;<=>?@[]{}|$".contains(&self.0))]
    fn is_single_punct(self) -> BytePredicate
    {
        BytePredicate::from(matches!(
            u8::from(self),
            b'!' | b'&'
                | b'('
                | b')'
                | b'*'
                | b'+'
                | b','
                | b'-'
                | b':'
                | b';'
                | b'<'
                | b'='
                | b'>'
                | b'?'
                | b'@'
                | b'['
                | b']'
                | b'{'
                | b'|'
                | b'}'
                | b'$'
        ))
    }
}

impl From<u8> for SourceByte
{
    /// Wrap a raw source byte.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: u8) -> Self
    {
        Self(value)
    }
}

impl From<SourceByte> for u8
{
    /// Read the raw byte back.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: SourceByte) -> Self
    {
        value.0
    }
}

/// Boolean result of a lexical byte predicate.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
struct BytePredicate(bool);

impl From<bool> for BytePredicate
{
    /// Wrap a predicate's answer.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: bool) -> Self
    {
        Self(value)
    }
}

impl From<BytePredicate> for bool
{
    /// Read the predicate's answer back.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: BytePredicate) -> Self
    {
        value.0
    }
}

/// One scanner step: the lexeme class and the next byte cursor.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
struct ScanResult
{
    /// Class assigned to the scanned lexeme.
    lexeme: Lexeme,
    /// Cursor immediately after the lexeme.
    next: ByteOffset,
}

impl ScanResult
{
    /// Build a scanner step from its semantic parts.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    fn new(
        lexeme: Lexeme,
        next: ByteOffset,
    ) -> Self
    {
        Self { lexeme, next }
    }
}

/// One labeled lexeme: its class and exact byte span.
///
/// The token borrows nothing; the source text is recovered from the `start ..
/// end` span against the original buffer. A [`Lexeme::Space`] token is layout;
/// every other token, unknown bytes included, is handed to the molder.
///
/// # Specification
/// - requires: `start <= end` and both index the labeled source buffer.
/// - ensures: preserves the class and span exactly.
/// - provides: the unit of the labeler's output stream and the molder's input.
/// - fails: never.
/// - panics: none.
/// - executable: none — this carrier has no entry or return boundary; the
///   labeler and token-text observer carry its executable obligations.
///
/// # Adequacy
/// - hypothesis: L3 — host and shell contexts cover the complete lexical
///   vocabulary with exact class streams and source spans. Wrong modes, missing
///   classes and shifted spans change these observations.
/// - witness: `label::tests::every_lexical_class_has_a_contextual_witness`
/// - witness: `label::tests::labels_a_definition_losslessly`
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct Token
{
    /// The lexical class of the lexeme.
    pub lexeme: Lexeme,
    /// Inclusive source start byte.
    pub start: u32,
    /// Exclusive source end byte.
    pub end: u32,
}

impl Token
{
    /// Return the token's source text against the labeled buffer.
    ///
    /// # Specification
    /// - requires: `src` is the exact buffer the token was labeled from.
    /// - ensures: returns the `start .. end` slice, or `""` if the span escapes
    ///   `src` (never on the labeler's own output).
    /// - provides: zero-copy token text for the molder and tests.
    /// - fails: never; an out-of-range span yields `""`.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — whole multibyte text, a tail token, empty ranges,
    ///   inverted bounds, split characters and one-past-source ends expose
    ///   exact fragments; clamping or partial UTF-8 changes those answers.
    /// - witness: `label::tests::token_text_checks_ranges_and_character_boundaries`
    #[inline]
    #[must_use]
    #[anodized::spec(ensures: |ret| ret.as_ref() == src.as_ref().get(usize::try_from(self.start).unwrap_or(usize::MAX) .. usize::try_from(self.end).unwrap_or(usize::MAX)).unwrap_or(""))]
    pub fn text<'src>(
        &self,
        src: &'src SourceFragment<'src>,
    ) -> SourceFragment<'src>
    {
        let source = AsRef::<str>::as_ref(src);
        let start = usize::try_from(self.start).unwrap_or(usize::MAX);
        let end = usize::try_from(self.end).unwrap_or(usize::MAX);
        SourceFragment::from(source.get(start .. end).unwrap_or(""))
    }
}

/// The multi-byte operator and punctuation tiles, longest first for maximal
/// munch.
///
/// The single-byte operators are handled by [`punct_len`] directly. `#`, `$`,
/// `/`, `"`, and `'` lead mode-shifting lexemes (comments, shebang, shell
/// starts, strings, characters) and are dispatched before this table. `~>` is
/// the **retired** rewrite-face arrow: `==>` is the face former at every
/// position, and `~>` stays in this table only so a stale spelling munches as
/// one tile and earns the elaborator's migration decline instead of
/// splintering into a parse repair that names bytes rather than the
/// respelling. A lone `~` remains an [`Lexeme::Unknown`] stray byte, so `~~>`
/// — a directed former on types the grammar does not declare yet — still
/// scans as a stray `~` followed by `~>`; declaring it adds one table entry
/// ahead of `~>`.
///
/// The four leading entries are the circuit-cell **arrow grid** of the block
/// form: the shaft carries the kind-class and the head carries
/// directedness, so `-->` / `<->` are the circuit 1-cell formers and `==>` /
/// `<=>` the rewrite faces at every dimension. Each is a strict extension of a
/// live shorter tile, so all four sit ahead of their prefixes and the maximal
/// munch is the grid glyph:
///
/// | grid glyph | shorter tile it extends | live use of the shorter tile      |
/// | ---------- | ----------------------- | --------------------------------- |
/// | `-->`      | `->`                    | the term-language function arrow  |
/// | `<->`      | `<-`                    | the `run PAT <- E ;` bind arrow   |
/// | `==>`      | `==`                    | the equality operator             |
/// | `<=>`      | `<=`                    | the less-or-equal operator        |
///
/// `=>` (the case arm) is unaffected: it is not a prefix of `==>` and `==>` is
/// not a prefix of it, so the two never compete. The `--` inside `-->` is not
/// a comment lead in this language — the repo comments with `//` and `/* … */`
/// — so no comment convention is disturbed.
///
/// **`:>` is the opaque-ascription tile**: `module M :> #{ …
/// }` against transparent `module M : #{ … }`, the ML-family spelling. It
/// extends the live single tile `:`, so it sits in this table for the maximal
/// munch, and the two forms differ on their **first token** — which is what
/// keeps the discrimination lookahead-free. Nothing already written can change
/// meaning: `:` is only ever followed by a type or a signature, and neither can
/// begin with `>`, so no existing byte sequence re-munches.
const MULTI_PUNCT: &[&str] = &[
    "-->", "<->", "==>", "<=>", "/\\", "~>", "->", "<-", "=>", "==", "!=", "<=", ">=", "++", "&&",
    "||", "|&", "<>", "<&", ">&", ">>", "@[", ":>",
];

/// UTF-8 bytes for U+00A0 NO-BREAK SPACE.
const NO_BREAK_SPACE_UTF8: [u8; 2] = [0xc2, 0xa0];
/// UTF-8 continuation bytes after E2 for U+200B ZERO WIDTH SPACE.
const ZERO_WIDTH_SPACE_TAIL: (u8, u8) = (0x80, 0x8b);
/// UTF-8 continuation bytes after E2 for U+2060 WORD JOINER.
const WORD_JOINER_TAIL: (u8, u8) = (0x81, 0xa0);
/// Shared first byte for U+200B and U+2060 layout blanks.
const THREE_BYTE_LAYOUT_PREFIX: u8 = 0xe2;
/// UTF-8 bytes for U+FEFF ZERO WIDTH NO-BREAK SPACE.
const BYTE_ORDER_MARK_UTF8: [u8; 3] = [0xef, 0xbb, 0xbf];
/// UTF-8 bytes for `ω` (U+03C9), gandr's grade punctuation.
const OMEGA_GRADE_UTF8: [u8; 2] = [0xcf, 0x89];
/// UTF-8 bytes for `′` (U+2032 PRIME), a word-continuing byte run.
const PRIME_UTF8: [u8; 3] = [0xe2, 0x80, 0xb2];

/// Label a UTF-8 source buffer into a total stream of lexemes.
///
/// The scan is left to right and total: every byte is covered by exactly one
/// token, trivia and unknown bytes included, so the concatenated token spans
/// reconstruct the source (losslessness). The molder consumes the non-space
/// tokens; space tokens are recorded into the tree verbatim.
///
/// # Specification
/// - requires: `src` is valid UTF-8 (the caller's source buffer).
/// - ensures: returns tokens whose spans tile `0 .. src.len()` with no gaps or
///   overlaps; trivia classify as [`Lexeme::Space`]; the scan never panics on
///   any input.
/// - provides: the labeler stage of the batch pipeline.
/// - fails: never; ungrammatical bytes classify as [`Lexeme::Unknown`], not an
///   error.
/// - panics: none.
/// - intension: multi-byte operators match longest-first; words, numbers,
///   strings, and comments are maximal-munch runs; a lone stray byte is one
///   `Unknown` token.
///
/// # Adequacy
/// - hypothesis: L2/L3 — exact token classes and spans for every lexical mode
///   distinguish wrong dispatch, premature consumption, overconsumption and
///   lost layout; sampled sources additionally observe full reconstruction. The
///   green witnesses do not cover a dangling shell-assignment escape or a
///   non-ASCII braced shell name, whose spans violate the intended boundary
///   contract. Source sizes above the wire ceiling are not exercised.
/// - witness: `label::tests::labels_a_definition_losslessly`
/// - witness: `label::tests::span_tiling_is_total_and_gapless`
/// - witness: `label::tests::scanner_decisions_preserve_class_and_end`
/// - witness: `parse::tests::arbitrary_source_parses_totally`
#[inline]
#[must_use]
#[anodized::spec(ensures: |ret| ret.first().map_or_else(|| src.as_ref().is_empty(), |first| first.start == 0)
    && ret.last().is_none_or(|last| usize::try_from(last.end).ok() == Some(src.as_ref().len()))
    && ret.iter().all(|token| token.start < token.end && usize::try_from(token.start).ok().zip(usize::try_from(token.end).ok()).is_some_and(|(start, end)| src.as_ref().get(start .. end).is_some()))
    && ret.iter().zip(ret.iter().skip(1)).all(|(left, right)| left.end == right.start))]
pub fn label(src: SourceFragment<'_>) -> Vec<Token>
{
    let source = AsRef::<str>::as_ref(&src);
    let source_bytes = SourceBytes::from(source.as_bytes());
    let mut tokens = Vec::new();
    let mut pos = ByteOffset::ZERO;
    let len = source_bytes.len();
    // Track whether the cursor sits between a `"` and its closing `"`, so string
    // content lexes as fragments/escapes (the tree-sitter string sub-grammar).
    let mut in_string = false;
    // Track `#!{` / `$!{` shell-block nesting so the interior lexes in the shell
    // word class (context-aware lexing, tree-sitter `_shell_block_start`).
    let mut shell_depth = 0_u32;
    // Track whether the cursor sits between a shell `'` and its closing `'`, so
    // the single-quoted interior lexes as one opaque `single_quoted_content` run
    // (tree-sitter `single_quoted_string`), never split on interior spaces.
    let mut shell_single = false;
    // A one-shot flag: the token immediately after a shell `$` (that a name
    // follows) is the `variable_name` of a `variable_expansion`, not a shell
    // word (tree-sitter `variable_expansion` = `$` `variable_name`).
    let mut shell_var = false;
    // Track whether the cursor sits inside a shell braced parameter expansion
    // `${name}`: the interior lexes as a `variable_name`
    // parameter and the matching `}` closes the brace WITHOUT touching
    // `shell_depth` (it is not the shell block's closer). This is a shell-native
    // brace, DISTINCT from the string-interpolation `${ E }` (`interp_stack`):
    // a shell parameter name is not a host expression, so the interior stays a
    // `variable_name`, not host-expression tokens. A `bool` (not a depth stack)
    // suffices for `${name}`, whose interior has no nested braces (the
    // `${name:-word}` / `${#name}` operator forms are not scanned yet).
    let mut shell_brace = false;
    // Track whether the cursor sits inside a shell double-quoted string
    // `"…"`: the interior lexes as `double_string_fragment`
    // runs, `\.` escapes, and `$name` / `${name}` expansions (tree-sitter
    // `double_quoted_string`), so a quoted argument with interior spaces is ONE
    // string rather than juxtaposed shell words. The `$` / `${` dispatch rides
    // the existing shell-depth conditions below (this mode is entered only at
    // `shell_depth > 0`), and a `'` inside is an ordinary fragment byte, not a
    // single-quote opener. Distinct from the host string mode (`in_string`),
    // which never lexes shell expansions.
    let mut shell_double = false;
    // String-interpolation frames: each `"… ${` opens an interpolation whose
    // interior lexes as ordinary host-expression tokens (the string-segment
    // mode). The stack entry is that interpolation's `{`-brace depth (the
    // opening `${` counts as one); a `}` that returns the depth to zero closes
    // the interpolation and resumes the containing string. A stack (not a
    // counter) so a nested string inside an interpolation — `"${ f("${x}") }"`
    // — is handled to arbitrary depth. Only `{`-suffixed openers at this mode
    // level (`{`, `#{`) push depth; `#!{` / `$!{` switch to shell mode, which
    // owns its own `}` accounting.
    let mut interp_stack: Vec<u32> = Vec::new();
    while pos < len {
        let start = pos;
        let scan = if in_string {
            scan_string_interior(source_bytes, pos)
        }
        else if shell_single {
            scan_single_quoted_interior(source_bytes, pos)
        }
        else if shell_var {
            scan_variable_name(source_bytes, pos)
        }
        else if shell_brace {
            scan_braced_shell_interior(source_bytes, pos)
        }
        else if shell_double {
            scan_shell_double_interior(source_bytes, pos)
        }
        else if shell_depth > 0 {
            scan_shell_interior(source_bytes, pos)
        }
        else {
            scan_one(source_bytes, pos)
        };
        let lexeme = scan.lexeme;
        // The variable-name state lasts exactly one token after its `$`.
        shell_var = false;
        // Defensive: scanning always advances; never emit a zero-width token.
        let next = if scan.next > start {
            scan.next
        }
        else {
            start.advance(ByteWidth::ONE)
        };
        if matches!(lexeme, Lexeme::Quote) {
            in_string = !in_string;
        }
        else if matches!(lexeme, Lexeme::Punct) {
            // Track shell-block depth by the opener/closer punctuation.
            let text = source_bytes
                .span(start, next)
                .unwrap_or_else(SourceBytes::empty);
            if bool::from(text.equals(BytePattern(b"${"))) && in_string {
                // A `"… ${` opens a string interpolation: leave string mode and
                // lex the interior as ordinary host-expression tokens until the
                // matching `}`. The opening brace counts, so the frame depth is 1.
                in_string = false;
                interp_stack.push(1);
            }
            else if bool::from(text.equals(BytePattern(b"${"))) && shell_depth > 0 {
                // A shell `${` opens a braced parameter expansion: the interior
                // lexes as a `variable_name` parameter and the matching `}`
                // closes the brace (not the shell block). DISTINCT from the
                // string-interpolation `${` above — the shell interior is a
                // shell parameter name, never a host expression.
                shell_brace = true;
            }
            else if bool::from(text.equals(BytePattern(b"}"))) && shell_brace {
                // The braced parameter expansion's closer: end the brace mode
                // and resume shell lexing WITHOUT decrementing `shell_depth`
                // (this `}` is the parameter's, not the shell block's).
                shell_brace = false;
            }
            else if bool::from(text.equals(BytePattern(b"\""))) && shell_depth > 0 {
                // A shell `"` opens or closes a double-quoted string: the
                // interior lexes as fragments / escapes / expansions (never a
                // nested block or the shell block's closer).
                shell_double = !shell_double;
            }
            else if bool::from(text.equals(BytePattern(b"'"))) && shell_depth > 0 {
                // A shell `'` opens or closes a single-quoted string; the
                // interior between them is lexed opaquely, so it cannot start a
                // nested block or close the shell block.
                shell_single = !shell_single;
            }
            else if bool::from(text.equals(BytePattern(b"$")))
                && shell_depth > 0
                && source_bytes
                    .byte(next)
                    .is_some_and(|byte| bool::from(byte.is_var_name_start()))
            {
                // A bare shell `$name`: the following word is the variable name
                // (`$( … )` host escapes and `$!{ … }` substitutions do not set
                // this — their next byte is not a name start).
                shell_var = true;
            }
            else if bool::from(is_shell_open(text)) {
                shell_depth = shell_depth.saturating_add(1);
            }
            else if bool::from(text.equals(BytePattern(b"}"))) && shell_depth > 0 {
                shell_depth = shell_depth.saturating_sub(1);
            }
            else if shell_depth == 0
                && let Some(depth) = interp_stack.last_mut()
            {
                // Inside an interpolation's host-expression interior (shell mode
                // owns its own brace accounting, so it is excluded). A `{`- or
                // `#{`-opened form deepens this frame; a `}` that empties it
                // closes the interpolation and resumes the containing string.
                if bool::from(text.equals(BytePattern(b"{")))
                    || bool::from(text.equals(BytePattern(b"#{")))
                {
                    *depth = depth.saturating_add(1);
                }
                else if bool::from(text.equals(BytePattern(b"}"))) {
                    *depth = depth.saturating_sub(1);
                    if *depth == 0 {
                        interp_stack.pop();
                        in_string = true;
                    }
                }
            }
        }
        tokens.push(Token {
            lexeme,
            start: u32::try_from(usize::from(start)).unwrap_or(u32::MAX),
            end: u32::try_from(usize::from(next)).unwrap_or(u32::MAX),
        });
        pos = next;
    }
    tokens
}
/// Scan one lexeme of string interior: a closing quote, an escape, an
/// interpolation opener `${`, or a fragment run up to the next `"` / `\` /
/// `${`.
///
/// # Specification
/// - requires: the cursor identifies a byte in this scanner's lexical domain.
/// - ensures: scanning advances; string mode distinguishes quotes, escapes,
///   interpolation and raw fragments.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — quotes, escapes, interpolation openers and raw fragments
///   at zero and nonzero offsets expose exact class and end positions. A
///   mode-insensitive classifier or premature stop changes the token stream.
/// - witness: `label::tests::scanner_decisions_preserve_class_and_end`
/// - witness: `label::tests::every_lexical_class_has_a_contextual_witness`
#[anodized::spec(requires: pos < bytes.len(), ensures: |ret| ret.next > pos && (matches!(ret.lexeme, Lexeme::Quote | Lexeme::EscapeSequence | Lexeme::Punct | Lexeme::StringFragment | Lexeme::Unknown)))]
fn scan_string_interior(
    bytes: SourceBytes<'_>,
    pos: ByteOffset,
) -> ScanResult
{
    match bytes.byte(pos).map(u8::from) {
        | Some(b'"') => ScanResult::new(Lexeme::Quote, pos.advance(ByteWidth::ONE)),
        | Some(b'\\') => scan_escape(bytes, pos),
        // `${` opens a string interpolation; the caller leaves string mode.
        | Some(b'$') if bytes.byte(pos.advance(ByteWidth::ONE)) == Some(SourceByte::from(b'{')) => {
            ScanResult::new(Lexeme::Punct, pos.advance(ByteWidth::TWO))
        },
        | Some(_) => {
            let mut cursor = pos;
            while let Some(byte) = bytes.byte(cursor) {
                if u8::from(byte) == b'"'
                    || u8::from(byte) == b'\\'
                    || (u8::from(byte) == b'$'
                        && bytes.byte(cursor.advance(ByteWidth::ONE))
                            == Some(SourceByte::from(b'{')))
                {
                    break;
                }
                cursor = cursor.advance(ByteWidth::ONE);
            }
            ScanResult::new(Lexeme::StringFragment, cursor)
        },
        | None => ScanResult::new(Lexeme::Unknown, pos.advance(ByteWidth::ONE)),
    }
}
/// Scan one lexeme of single-quoted shell interior: the closing `'`, or the
/// raw content run up to it (tree-sitter `single_quoted_string` is `'`
/// `token.immediate(/[^']*/)` `'` — the interior is verbatim, no escapes).
///
/// # Specification
/// - requires: the cursor identifies a byte in this scanner's lexical domain.
/// - ensures: scanning advances; a closing quote is punctuation; all interior
///   bytes remain verbatim.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — closing quotes and verbatim runs containing
///   escape-looking bytes expose exact class and end positions at two offsets.
///   Interpreting an escape or swallowing the closing quote changes shell text.
/// - witness: `label::tests::scanner_decisions_preserve_class_and_end`
/// - witness: `label::tests::every_lexical_class_has_a_contextual_witness`
#[anodized::spec(requires: pos < bytes.len(), ensures: |ret| ret.next > pos && (matches!(ret.lexeme, Lexeme::Punct | Lexeme::SingleQuotedContent)))]
fn scan_single_quoted_interior(
    bytes: SourceBytes<'_>,
    pos: ByteOffset,
) -> ScanResult
{
    if bytes.byte(pos) == Some(SourceByte::from(b'\'')) {
        return ScanResult::new(Lexeme::Punct, pos.advance(ByteWidth::ONE));
    }
    let mut cursor = pos;
    while bytes
        .byte(cursor)
        .is_some_and(|byte| u8::from(byte) != b'\'')
    {
        cursor = cursor.advance(ByteWidth::ONE);
    }
    ScanResult::new(Lexeme::SingleQuotedContent, cursor)
}
/// Scan a shell variable name after `$` (`[A-Za-z_][A-Za-z0-9_]*`, tree-sitter
/// `variable_name`).
///
/// # Specification
/// - requires: the cursor identifies a byte in this scanner's lexical domain.
/// - ensures: scanning advances; a nonempty word-byte run is a variable name;
///   other starts advance as unknown.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — names, digit continuations and non-name starts at two
///   offsets expose exact variable width and unknown fallback. Accepting
///   punctuation into a name or failing to advance changes the shell token
///   stream.
/// - witness: `label::tests::scanner_decisions_preserve_class_and_end`
/// - witness: `label::tests::every_lexical_class_has_a_contextual_witness`
#[anodized::spec(requires: pos < bytes.len(), ensures: |ret| ret.next > pos && (matches!(ret.lexeme, Lexeme::VariableName | Lexeme::Unknown)))]
fn scan_variable_name(
    bytes: SourceBytes<'_>,
    pos: ByteOffset,
) -> ScanResult
{
    let mut cursor = pos;
    while bytes
        .byte(cursor)
        .is_some_and(|byte| bool::from(byte.is_word_continue()))
    {
        cursor = cursor.advance(ByteWidth::ONE);
    }
    if cursor > pos {
        ScanResult::new(Lexeme::VariableName, cursor)
    }
    else {
        // Defensive: the caller only sets the flag when a name start follows.
        ScanResult::new(Lexeme::Unknown, pos.advance(ByteWidth::ONE))
    }
}
/// Scan one lexeme of shell braced-parameter interior (`${…}`): the
/// closing `}`, or the parameter's `variable_name` run.
///
/// The interior is a bare parameter name `[A-Za-z0-9_]+` (tree-sitter
/// `variable_name`); the `${name:-word}` / `${#name}` operator forms are not
/// scanned yet. A stray non-name, non-`}` byte advances one as a shell
/// word so the scan stays total on malformed input.
///
/// # Specification
/// - requires: the cursor identifies a byte in this scanner's lexical domain.
/// - ensures: scanning advances; the closing brace is punctuation, names are
///   variable runs and stray bytes are shell words.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — closing braces, parameter-name runs and stray ASCII bytes
///   at two offsets expose exact class and width. Treating a closer as content
///   or stopping a name early changes the parameter subtree; multibyte stray
///   content is outside this witness matrix.
/// - witness: `label::tests::scanner_decisions_preserve_class_and_end`
/// - witness: `label::tests::every_lexical_class_has_a_contextual_witness`
#[anodized::spec(requires: pos < bytes.len(), ensures: |ret| ret.next > pos && (matches!(ret.lexeme, Lexeme::Punct | Lexeme::VariableName | Lexeme::ShellWord)))]
fn scan_braced_shell_interior(
    bytes: SourceBytes<'_>,
    pos: ByteOffset,
) -> ScanResult
{
    if bytes.byte(pos) == Some(SourceByte::from(b'}')) {
        return ScanResult::new(Lexeme::Punct, pos.advance(ByteWidth::ONE));
    }
    let mut cursor = pos;
    while bytes
        .byte(cursor)
        .is_some_and(|byte| bool::from(byte.is_word_continue()))
    {
        cursor = cursor.advance(ByteWidth::ONE);
    }
    if cursor > pos {
        ScanResult::new(Lexeme::VariableName, cursor)
    }
    else {
        // A stray byte inside the braces (not a name char, not `}`): emit one
        // shell-word byte and stay in brace mode, keeping the scan total.
        ScanResult::new(Lexeme::ShellWord, pos.advance(ByteWidth::ONE))
    }
}

/// Scan one lexeme of shell double-quoted interior (`"…"`): the closing
/// `"`, a `\.` escape, a `$`-led expansion, or a `double_string_fragment` run
/// up to the next `"` / `\` / `$` (tree-sitter `double_quoted_string`).
///
/// The `$`-led forms (`$name`, `${name}`, and the `$!{…}` command-substitution
/// start) are dispatched by [`scan_dollar`]; the caller's shell-depth
/// conditions then set the variable / brace state, so an expansion inside a
/// double-quoted string lexes exactly as it does bare. A fragment run keeps
/// interior spaces, so a quoted argument is one string.
///
/// # Specification
/// - requires: the cursor identifies a byte in this scanner's lexical domain.
/// - ensures: scanning advances; double-quoted shell mode preserves spaces and
///   recognizes escapes and dollar expansions.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — valid scanner leads at zero and a nonzero offset,
///   complete tokens, adjacent delimiters and truncated tails are compared with
///   exact class/end pairs. Wrong mode, premature consumption, overconsumption
///   and failure to advance change a row; double-quoted shell mode preserves
///   spaces and recognizes escapes and dollar expansions.
/// - witness: `label::tests::scanner_decisions_preserve_class_and_end`
#[anodized::spec(requires: pos < bytes.len(), ensures: |ret| ret.next > pos && (matches!(ret.lexeme, Lexeme::Punct | Lexeme::EscapeSequence | Lexeme::Unknown | Lexeme::StringFragment)))]
fn scan_shell_double_interior(
    bytes: SourceBytes<'_>,
    pos: ByteOffset,
) -> ScanResult
{
    match bytes.byte(pos).map(u8::from) {
        | Some(b'"') => ScanResult::new(Lexeme::Punct, pos.advance(ByteWidth::ONE)),
        | Some(b'\\') => scan_escape(bytes, pos),
        | Some(b'$') => scan_dollar(bytes, pos),
        | Some(_) => {
            let mut cursor = pos;
            while let Some(byte) = bytes.byte(cursor) {
                if matches!(u8::from(byte), b'"' | b'\\' | b'$') {
                    break;
                }
                cursor = cursor.advance(ByteWidth::ONE);
            }
            ScanResult::new(Lexeme::StringFragment, cursor)
        },
        | None => ScanResult::new(Lexeme::Unknown, pos.advance(ByteWidth::ONE)),
    }
}
/// Scan one lexeme of shell-block interior: separators and operators as
/// punctuation, quoted strings, and otherwise a run of shell-word bytes.
///
/// # Specification
/// - requires: the cursor identifies a byte in this scanner's lexical domain.
/// - ensures: scanning advances; shell brackets are subshell delimiters, not
///   host punctuation.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — valid scanner leads at zero and a nonzero offset,
///   complete tokens, adjacent delimiters and truncated tails are compared with
///   exact class/end pairs. Wrong mode, premature consumption, overconsumption
///   and failure to advance change a row; shell brackets are subshell
///   delimiters, not host punctuation.
/// - witness: `label::tests::scanner_decisions_preserve_class_and_end`
#[anodized::spec(requires: pos < bytes.len(), ensures: |ret| ret.next > pos && (match bytes.0.get(pos.0).copied() { Some(b'[') => ret.lexeme == Lexeme::SubshellOpen, Some(b']') => ret.lexeme == Lexeme::SubshellClose, _ => true }))]
fn scan_shell_interior(
    bytes: SourceBytes<'_>,
    pos: ByteOffset,
) -> ScanResult
{
    let Some(byte) = bytes.byte(pos)
    else {
        return ScanResult::new(Lexeme::Unknown, pos.advance(ByteWidth::ONE));
    };
    match u8::from(byte) {
        // Whitespace and newlines are layout inside shell blocks too (the
        // grammar's `list_operator` newline is approximated as layout; the
        // explicit `;` / `&` separators carry the list structure the corpus
        // uses).
        | b' ' | b'\t' | 0x0c | 0x0b => {
            ScanResult::new(Lexeme::Space, scan_horizontal_space(bytes, pos))
        },
        | b'\r' | b'\n' => ScanResult::new(Lexeme::Space, scan_newlines(bytes, pos)),
        // `#!{` / `$!{` open a nested shell block; the brace / bracket / paren
        // punctuation is structural.
        | b'#' => scan_hash(bytes, pos),
        | b'$' => scan_dollar(bytes, pos),
        // A shell `[` / `]` is a subshell bracket (tree-sitter `subshell`),
        // classified DISTINCTLY from the host list-literal `[` so a subshell
        // never widens the host `[` mold menu.
        | b'[' => ScanResult::new(Lexeme::SubshellOpen, pos.advance(ByteWidth::ONE)),
        | b']' => ScanResult::new(Lexeme::SubshellClose, pos.advance(ByteWidth::ONE)),
        // Brace / paren / quote punctuation is structural. `=` is NOT: it is a
        // shell-word byte, so `NAME=value` munches into one `environment_assignment`
        // token and a bare `=` stays an ordinary word — no shell rule
        // declares a `=` tile, so a split `=` could only ever be an `UnmoldedTok`.
        | b'}' | b'{' | b'(' | b')' | b'\'' | b'"' => {
            ScanResult::new(Lexeme::Punct, pos.advance(ByteWidth::ONE))
        },
        // Shell list / pipe / logical operators.
        | b';' | b'&' | b'|' => scan_shell_operator(bytes, pos),
        // Redirections.
        | b'<' | b'>' => scan_shell_redirection(bytes, pos),
        // A digit run immediately before a redirection is a file descriptor
        // (`2>`); otherwise it is an ordinary shell word.
        | b'0' ..= b'9' => scan_shell_fd_or_word(bytes, pos),
        // A run of shell-word bytes (`pattern_shell_word`).
        | _ => scan_shell_word(bytes, pos),
    }
}
/// Scan one lexeme starting at `pos`, returning its class and the next cursor.
///
/// # Specification
/// - requires: the cursor identifies a byte in this scanner's lexical domain.
/// - ensures: scanning advances; host word classification preserves the case of
///   its leading letter.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — valid scanner leads at zero and a nonzero offset,
///   complete tokens, adjacent delimiters and truncated tails are compared with
///   exact class/end pairs. Wrong mode, premature consumption, overconsumption
///   and failure to advance change a row; host word classification preserves
///   the case of its leading letter.
/// - witness: `label::tests::scanner_decisions_preserve_class_and_end`
#[anodized::spec(requires: pos < bytes.len(), ensures: |ret| ret.next > pos && (match bytes.0.get(pos.0).copied() { Some(b'a' ..= b'z') => ret.lexeme == Lexeme::LowerWord, Some(b'A' ..= b'Z') => ret.lexeme == Lexeme::UpperWord, _ => true }))]
fn scan_one(
    bytes: SourceBytes<'_>,
    pos: ByteOffset,
) -> ScanResult
{
    let Some(byte) = bytes.byte(pos)
    else {
        return ScanResult::new(Lexeme::Unknown, pos.advance(ByteWidth::ONE));
    };
    match u8::from(byte) {
        | b' ' | b'\t' | 0x0c | 0x0b => {
            ScanResult::new(Lexeme::Space, scan_horizontal_space(bytes, pos))
        },
        | b'\r' | b'\n' => ScanResult::new(Lexeme::Space, scan_newlines(bytes, pos)),
        | b'/' => scan_slash(bytes, pos),
        | b'#' => scan_hash(bytes, pos),
        | b'"' => ScanResult::new(Lexeme::Quote, pos.advance(ByteWidth::ONE)),
        | b'\'' => scan_character(bytes, pos),
        // In code a backslash is the static abstraction's lead `\A. T`, one
        // tile; escape sequences belong to strings and characters, whose
        // scanners read them.
        | b'\\' => ScanResult::new(Lexeme::Punct, pos.advance(ByteWidth::ONE)),
        | b'0' ..= b'9' => scan_number(bytes, pos),
        | b'.' => scan_dot(bytes, pos),
        | b'_' => scan_word_or_underscore(bytes, pos),
        | _ if bool::from(byte.is_lower_start()) => {
            ScanResult::new(Lexeme::LowerWord, scan_word(bytes, pos))
        },
        | _ if bool::from(byte.is_upper_start()) => {
            ScanResult::new(Lexeme::UpperWord, scan_word(bytes, pos))
        },
        | _ => scan_punct_or_unknown(bytes, pos),
    }
}
/// Return whether a punctuation token text opens a shell block (`#!…{` /
/// `$!…{`).
///
/// # Specification
/// - ensures: recognizes exactly hash-bang or dollar-bang prefixes whose final
///   byte is an opening brace.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — empty, truncated, complete and wrong-sigil forms expose
///   the decision; dropping either the prefix or final-brace condition accepts
///   a negative neighbor.
/// - witness: `label::tests::prefix_recognizers_respect_truncation_and_word_boundaries`
#[anodized::spec(ensures: |ret| bool::from(ret) == ((text.0.starts_with(b"#!") || text.0.starts_with(b"$!")) && text.0.ends_with(b"{")))]
fn is_shell_open(text: SourceBytes<'_>) -> BytePredicate
{
    BytePredicate::from(
        (bool::from(text.starts_with(BytePattern(b"#!")))
            || bool::from(text.starts_with(BytePattern(b"$!"))))
            && bool::from(text.ends_with(BytePattern(b"{"))),
    )
}

/// Scan a run of non-newline horizontal whitespace, including the Unicode
/// blank code points the grammar treats as layout.
///
/// # Specification
/// - requires: the cursor is a character boundary within the UTF-8 source or at
///   its end.
/// - ensures: consumes exactly the maximal ASCII or Unicode horizontal-blank
///   run, never a newline.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — empty and nonblank input, every admitted Unicode blank, a
///   mixed run and an immediately following newline expose the exact endpoint.
///   Adding newlines, dropping a Unicode blank or splitting its bytes changes
///   it.
/// - witness: `label::tests::run_scanners_stop_at_the_first_excluded_byte`
#[anodized::spec(requires: pos <= bytes.len(), ensures: |ret| ret >= pos && ret <= bytes.len() && bytes.0.get(pos.0 .. ret.0).is_some_and(|run| core::str::from_utf8(run).is_ok_and(|text| text.chars().all(|ch| matches!(ch, ' ' | '\t' | '\u{c}' | '\u{b}' | '\u{a0}' | '\u{200b}' | '\u{2060}' | '\u{feff}')))))]
fn scan_horizontal_space(
    bytes: SourceBytes<'_>,
    pos: ByteOffset,
) -> ByteOffset
{
    let mut cursor = pos;
    while cursor < bytes.len() {
        // ASCII blanks advance one byte; the Unicode layout blanks
        // (U+00A0, U+200B, U+2060, U+FEFF) are handled as UTF-8 sequences.
        if let Some(byte) = bytes.byte(cursor)
            && matches!(u8::from(byte), b' ' | b'\t' | 0x0c | 0x0b)
        {
            cursor = cursor.advance(ByteWidth::ONE);
            continue;
        }
        match unicode_blank_len(bytes, cursor) {
            | Some(width) => cursor = cursor.advance(width),
            | None => break,
        }
    }
    cursor
}

/// Scan a run of `\r` / `\n` newlines as one layout token (tree-sitter
/// `_newline`).
///
/// # Specification
/// - requires: the cursor is within the source or at its end.
/// - ensures: returns the maximal run of carriage returns and line feeds,
///   including an empty run.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — empty input, an immediate delimiter, a mixed run, end of
///   input and a nonzero origin expose the first excluded byte. Skipping a
///   delimiter, accepting the neighboring class or consuming too little changes
///   the pinned end offset.
/// - witness: `label::tests::run_scanners_stop_at_the_first_excluded_byte`
#[anodized::spec(requires: pos <= bytes.len(), ensures: |ret| ret >= pos && ret <= bytes.len() && bytes.0.get(pos.0 .. ret.0).is_some_and(|run| run.iter().copied().all(|byte| matches!(byte, b'\r' | b'\n'))) && bytes.0.get(ret.0).copied().is_none_or(|byte| !(matches!(byte, b'\r' | b'\n'))))]
fn scan_newlines(
    bytes: SourceBytes<'_>,
    pos: ByteOffset,
) -> ByteOffset
{
    let mut cursor = pos;
    while let Some(byte) = bytes.byte(cursor) {
        if matches!(u8::from(byte), b'\r' | b'\n') {
            cursor = cursor.advance(ByteWidth::ONE);
        }
        else {
            break;
        }
    }
    cursor
}

/// Return the UTF-8 width of a Unicode layout blank at `pos`, if any.
///
/// # Specification
/// - ensures: returns the complete width of one of the four admitted Unicode
///   blanks, otherwise none.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — every admitted blank, each incomplete byte prefix, an
///   ordinary space and a neighboring nonblank scalar expose the optional
///   width. Prefix-only matching or a shifted Unicode code point changes it.
/// - witness: `label::tests::prefix_recognizers_respect_truncation_and_word_boundaries`
#[anodized::spec(ensures: |ret| ret.map(usize::from) == bytes.0.get(pos.0 ..).and_then(|tail| ["\u{a0}", "\u{200b}", "\u{2060}", "\u{feff}"].into_iter().find(|blank| tail.starts_with(blank.as_bytes())).map(str::len)))]
fn unicode_blank_len(
    bytes: SourceBytes<'_>,
    pos: ByteOffset,
) -> Option<ByteWidth>
{
    let b0 = bytes.byte(pos)?;
    // U+00A0 NO-BREAK SPACE = C2 A0.
    if b0 == SourceByte::from(NO_BREAK_SPACE_UTF8[0])
        && bytes.byte(pos.advance(ByteWidth::ONE)) == Some(SourceByte::from(NO_BREAK_SPACE_UTF8[1]))
    {
        return Some(ByteWidth::TWO);
    }
    // U+200B ZERO WIDTH SPACE = E2 80 8B; U+2060 WORD JOINER = E2 81 A0.
    if b0 == SourceByte::from(THREE_BYTE_LAYOUT_PREFIX) {
        let b1 = bytes.byte(pos.advance(ByteWidth::ONE))?;
        let b2 = bytes.byte(pos.advance(ByteWidth::TWO))?;
        let tail = (u8::from(b1), u8::from(b2));
        if tail == ZERO_WIDTH_SPACE_TAIL || tail == WORD_JOINER_TAIL {
            return Some(ByteWidth::THREE);
        }
    }
    // U+FEFF ZERO WIDTH NO-BREAK SPACE (BOM) = EF BB BF.
    if b0 == SourceByte::from(BYTE_ORDER_MARK_UTF8[0])
        && bytes.byte(pos.advance(ByteWidth::ONE))
            == Some(SourceByte::from(BYTE_ORDER_MARK_UTF8[1]))
        && bytes.byte(pos.advance(ByteWidth::TWO))
            == Some(SourceByte::from(BYTE_ORDER_MARK_UTF8[2]))
    {
        return Some(ByteWidth::THREE);
    }
    None
}

/// Scan a lexeme led by `/`: `//` line comment, `/* */` block comment, or the
/// `/\` intersection operator.
///
/// # Specification
/// - requires: the cursor identifies a byte in this scanner's lexical domain.
/// - ensures: scanning advances; line and nested block comments are layout;
///   intersection is punctuation and a lone slash is unknown.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — valid scanner leads at zero and a nonzero offset,
///   complete tokens, adjacent delimiters and truncated tails are compared with
///   exact class/end pairs. Wrong mode, premature consumption, overconsumption
///   and failure to advance change a row; line and nested block comments are
///   layout; intersection is punctuation and a lone slash is unknown.
/// - witness: `label::tests::scanner_decisions_preserve_class_and_end`
#[anodized::spec(requires: bytes.0.get(pos.0) == Some(&b'/'), ensures: |ret| ret.next > pos && (matches!(ret.lexeme, Lexeme::Space | Lexeme::Punct | Lexeme::Unknown)))]
fn scan_slash(
    bytes: SourceBytes<'_>,
    pos: ByteOffset,
) -> ScanResult
{
    match bytes.byte(pos.advance(ByteWidth::ONE)).map(u8::from) {
        | Some(b'/') => ScanResult::new(
            Lexeme::Space,
            scan_line_comment_from(bytes, pos.advance(ByteWidth::TWO)),
        ),
        | Some(b'*') => ScanResult::new(Lexeme::Space, scan_block_comment(bytes, pos)),
        | Some(b'\\') => ScanResult::new(Lexeme::Punct, pos.advance(ByteWidth::TWO)),
        | _ => ScanResult::new(Lexeme::Unknown, pos.advance(ByteWidth::ONE)),
    }
}
/// Scan a lexeme led by `#`: shebang, shell/record start, or a stray byte.
///
/// # Specification
/// - requires: the cursor identifies a byte in this scanner's lexical domain.
/// - ensures: scanning advances; shebangs are layout, record and valid shell
///   openers are punctuation, other hashes are unknown.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — valid scanner leads at zero and a nonzero offset,
///   complete tokens, adjacent delimiters and truncated tails are compared with
///   exact class/end pairs. Wrong mode, premature consumption, overconsumption
///   and failure to advance change a row; shebangs are layout, record and valid
///   shell openers are punctuation, other hashes are unknown.
/// - witness: `label::tests::scanner_decisions_preserve_class_and_end`
#[anodized::spec(requires: bytes.0.get(pos.0) == Some(&b'#'), ensures: |ret| ret.next > pos && (matches!(ret.lexeme, Lexeme::Space | Lexeme::Punct | Lexeme::Unknown)))]
fn scan_hash(
    bytes: SourceBytes<'_>,
    pos: ByteOffset,
) -> ScanResult
{
    match bytes.byte(pos.advance(ByteWidth::ONE)).map(u8::from) {
        | Some(b'!') => match bytes.byte(pos.advance(ByteWidth::TWO)).map(u8::from) {
            // `#!/…` first-line shebang (trivia).
            | Some(b'/') => ScanResult::new(
                Lexeme::Space,
                scan_line_comment_from(bytes, pos.advance(ByteWidth::TWO)),
            ),
            // `#!{` or `#!dialect{` shell-block start.
            | _ => scan_shell_start(bytes, pos, SourceByte::from(b'{')),
        },
        // `#{` record / record-type / record-pattern open.
        | Some(b'{') => ScanResult::new(Lexeme::Punct, pos.advance(ByteWidth::TWO)),
        | _ => ScanResult::new(Lexeme::Unknown, pos.advance(ByteWidth::ONE)),
    }
}

/// Scan to end of line from `from` (line comments and shebangs).
///
/// # Specification
/// - requires: the cursor is within the source or at its end.
/// - ensures: returns the maximal run of bytes before the next carriage return
///   or line feed, including an empty run.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — empty input, an immediate delimiter, a mixed run, end of
///   input and a nonzero origin expose the first excluded byte. Skipping a
///   delimiter, accepting the neighboring class or consuming too little changes
///   the pinned end offset.
/// - witness: `label::tests::run_scanners_stop_at_the_first_excluded_byte`
#[anodized::spec(requires: from <= bytes.len(), ensures: |ret| ret >= from && ret <= bytes.len() && bytes.0.get(from.0 .. ret.0).is_some_and(|run| run.iter().copied().all(|byte| !matches!(byte, b'\r' | b'\n'))) && bytes.0.get(ret.0).copied().is_none_or(|byte| matches!(byte, b'\r' | b'\n')))]
fn scan_line_comment_from(
    bytes: SourceBytes<'_>,
    from: ByteOffset,
) -> ByteOffset
{
    let mut cursor = from;
    while let Some(byte) = bytes.byte(cursor) {
        if matches!(u8::from(byte), b'\r' | b'\n') {
            break;
        }
        cursor = cursor.advance(ByteWidth::ONE);
    }
    cursor
}

/// Scan a nested `/* … */` block comment.
///
/// # Specification
/// - requires: the cursor points to an opening block-comment pair.
/// - ensures: stops just after the matching outer close, or at the source end
///   if unclosed.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — nested and unterminated comments plus following live
///   source expose the consumed endpoint. Ignoring depth, swallowing following
///   source or failing to consume the opener changes the boundary.
/// - witness: `label::tests::scanner_decisions_preserve_class_and_end`
#[anodized::spec(requires: bytes.0.get(pos.0 ..).is_some_and(|tail| tail.starts_with(b"/*")), ensures: |ret| ret.0 >= pos.0.saturating_add(2) && ret <= bytes.len() && (ret == bytes.len() || bytes.0.get(ret.0.saturating_sub(2) .. ret.0) == Some(b"*/")))]
fn scan_block_comment(
    bytes: SourceBytes<'_>,
    pos: ByteOffset,
) -> ByteOffset
{
    let mut cursor = pos.advance(ByteWidth::TWO);
    let mut depth = 1_u32;
    while depth > 0 && cursor < bytes.len() {
        match (
            bytes.byte(cursor).map(u8::from),
            bytes.byte(cursor.advance(ByteWidth::ONE)).map(u8::from),
        ) {
            | (Some(b'/'), Some(b'*')) => {
                depth = depth.saturating_add(1);
                cursor = cursor.advance(ByteWidth::TWO);
            },
            | (Some(b'*'), Some(b'/')) => {
                depth = depth.saturating_sub(1);
                cursor = cursor.advance(ByteWidth::TWO);
            },
            | (Some(_), _) => cursor = cursor.advance(ByteWidth::ONE),
            | (None, _) => break,
        }
    }
    cursor
}

/// Scan a `'…'` character literal (`'\.'` or `'[^'\]'`), tolerating an
/// unterminated tail as a stray quote.
///
/// # Specification
/// - requires: the cursor identifies a byte in this scanner's lexical domain.
/// - ensures: scanning advances; a complete character consumes both quotes;
///   empty and truncated literals leave a punctuation quote.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — valid scanner leads at zero and a nonzero offset,
///   complete tokens, adjacent delimiters and truncated tails are compared with
///   exact class/end pairs. Wrong mode, premature consumption, overconsumption
///   and failure to advance change a row; a complete character consumes both
///   quotes; empty and truncated literals leave a punctuation quote.
/// - witness: `label::tests::scanner_decisions_preserve_class_and_end`
#[anodized::spec(requires: bytes.0.get(pos.0) == Some(&b'\''), ensures: |ret| ret.next > pos && (matches!(ret.lexeme, Lexeme::Character | Lexeme::Punct)))]
fn scan_character(
    bytes: SourceBytes<'_>,
    pos: ByteOffset,
) -> ScanResult
{
    let inner = pos.advance(ByteWidth::ONE);
    match bytes.byte(inner).map(u8::from) {
        | Some(b'\\') => {
            // `'\x'`: backslash, one escaped byte, closing quote.
            let escaped = inner.advance(ByteWidth::TWO);
            if bytes.byte(escaped) == Some(SourceByte::from(b'\'')) {
                ScanResult::new(Lexeme::Character, escaped.advance(ByteWidth::ONE))
            }
            else {
                ScanResult::new(Lexeme::Punct, pos.advance(ByteWidth::ONE))
            }
        },
        | Some(byte) if byte != b'\'' => {
            // `'x'`: one non-quote byte (or UTF-8 lead) and a closing quote.
            let width = utf8_width(SourceByte::from(byte));
            let close = inner.advance(width);
            if bytes.byte(close) == Some(SourceByte::from(b'\'')) {
                ScanResult::new(Lexeme::Character, close.advance(ByteWidth::ONE))
            }
            else {
                ScanResult::new(Lexeme::Punct, pos.advance(ByteWidth::ONE))
            }
        },
        // A bare `'` or empty `''`: treat the quote as a stray punctuation tile.
        | _ => ScanResult::new(Lexeme::Punct, pos.advance(ByteWidth::ONE)),
    }
}
/// Scan a `\x` escape sequence (backslash and one following byte).
///
/// # Specification
/// - requires: the cursor identifies a byte in this scanner's lexical domain.
/// - ensures: scanning advances; an escape consumes its following scalar; a
///   terminal backslash remains unknown.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — valid scanner leads at zero and a nonzero offset,
///   complete tokens, adjacent delimiters and truncated tails are compared with
///   exact class/end pairs. Wrong mode, premature consumption, overconsumption
///   and failure to advance change a row; an escape consumes its following
///   scalar; a terminal backslash remains unknown.
/// - witness: `label::tests::scanner_decisions_preserve_class_and_end`
#[anodized::spec(requires: bytes.0.get(pos.0) == Some(&b'\\'), ensures: |ret| ret.next > pos && (matches!(ret.lexeme, Lexeme::EscapeSequence | Lexeme::Unknown)))]
fn scan_escape(
    bytes: SourceBytes<'_>,
    pos: ByteOffset,
) -> ScanResult
{
    match bytes.byte(pos.advance(ByteWidth::ONE)) {
        | Some(byte) => ScanResult::new(
            Lexeme::EscapeSequence,
            pos.advance(ByteWidth::ONE).advance(utf8_width(byte)),
        ),
        | None => ScanResult::new(Lexeme::Unknown, pos.advance(ByteWidth::ONE)),
    }
}
/// Scan a `$`-led shell lexeme (`$!{` command substitution, `${` braced
/// parameter expansion, `$(` host escape, `$name` variable, or a bare `$`).
///
/// # Specification
/// - requires: the cursor identifies a byte in this scanner's lexical domain.
/// - ensures: scanning advances; a braced parameter or valid command opener is
///   punctuation; an incomplete command start is unknown.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — valid scanner leads at zero and a nonzero offset,
///   complete tokens, adjacent delimiters and truncated tails are compared with
///   exact class/end pairs. Wrong mode, premature consumption, overconsumption
///   and failure to advance change a row; a braced parameter or valid command
///   opener is punctuation; an incomplete command start is unknown.
/// - witness: `label::tests::scanner_decisions_preserve_class_and_end`
#[anodized::spec(requires: bytes.0.get(pos.0) == Some(&b'$'), ensures: |ret| ret.next > pos && matches!(ret.lexeme, Lexeme::Punct | Lexeme::Unknown))]
fn scan_dollar(
    bytes: SourceBytes<'_>,
    pos: ByteOffset,
) -> ScanResult
{
    match bytes.byte(pos.advance(ByteWidth::ONE)).map(u8::from) {
        | Some(b'!') => scan_shell_start(bytes, pos, SourceByte::from(b'{')),
        // `${` opens a braced parameter expansion (`${name}`); the two-byte
        // opener is one lexeme, and the caller sets the brace mode so the
        // interior lexes as a `variable_name` and the matching `}` does not
        // close the shell block.
        | Some(b'{') => ScanResult::new(Lexeme::Punct, pos.advance(ByteWidth::TWO)),
        | _ => ScanResult::new(Lexeme::Punct, pos.advance(ByteWidth::ONE)),
    }
}
/// Scan a shell list/pipe/logical operator (`;`, `&`, `&&`, `|`, `||`, `|&`).
///
/// # Specification
/// - requires: the cursor identifies a byte in this scanner's lexical domain.
/// - ensures: scanning advances; shell logical and pipe pairs take precedence
///   over their single-byte prefixes.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — valid scanner leads at zero and a nonzero offset,
///   complete tokens, adjacent delimiters and truncated tails are compared with
///   exact class/end pairs. Wrong mode, premature consumption, overconsumption
///   and failure to advance change a row; shell logical and pipe pairs take
///   precedence over their single-byte prefixes.
/// - witness: `label::tests::scanner_decisions_preserve_class_and_end`
#[anodized::spec(requires: bytes.0.get(pos.0).is_some_and(|byte| b";&|".contains(byte)), ensures: |ret| ret.next > pos && (ret.lexeme == Lexeme::Punct && ret.next.0 == pos.0.saturating_add(if bytes.0.get(pos.0 ..).is_some_and(|tail| [b"&&", b"||", b"|&"].iter().any(|op| tail.starts_with(*op))) { 2 } else { 1 })))]
fn scan_shell_operator(
    bytes: SourceBytes<'_>,
    pos: ByteOffset,
) -> ScanResult
{
    let two = pos.advance(ByteWidth::TWO);
    if bool::from(bytes.span_matches(pos, two, BytePattern(b"&&")))
        || bool::from(bytes.span_matches(pos, two, BytePattern(b"||")))
        || bool::from(bytes.span_matches(pos, two, BytePattern(b"|&")))
    {
        ScanResult::new(Lexeme::Punct, two)
    }
    else {
        ScanResult::new(Lexeme::Punct, pos.advance(ByteWidth::ONE))
    }
}
/// Scan a shell redirection operator (`<`, `>`, `<>`, `<&`, `>&`, `>>`).
///
/// # Specification
/// - requires: the cursor identifies a byte in this scanner's lexical domain.
/// - ensures: scanning advances; redirection pairs consume two bytes; other
///   redirection prefixes consume one.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — valid scanner leads at zero and a nonzero offset,
///   complete tokens, adjacent delimiters and truncated tails are compared with
///   exact class/end pairs. Wrong mode, premature consumption, overconsumption
///   and failure to advance change a row; redirection pairs consume two bytes;
///   other redirection prefixes consume one.
/// - witness: `label::tests::scanner_decisions_preserve_class_and_end`
#[anodized::spec(requires: bytes.0.get(pos.0).is_some_and(|byte| b"<>".contains(byte)), ensures: |ret| ret.next > pos && (ret.lexeme == Lexeme::Punct && ret.next.0 == pos.0.saturating_add(if bytes.0.get(pos.0 ..).is_some_and(|tail| [b"<>", b"<&", b">&", b">>"].iter().any(|op| tail.starts_with(*op))) { 2 } else { 1 })))]
fn scan_shell_redirection(
    bytes: SourceBytes<'_>,
    pos: ByteOffset,
) -> ScanResult
{
    let two = pos.advance(ByteWidth::TWO);
    if bool::from(bytes.span_matches(pos, two, BytePattern(b"<>")))
        || bool::from(bytes.span_matches(pos, two, BytePattern(b"<&")))
        || bool::from(bytes.span_matches(pos, two, BytePattern(b">&")))
        || bool::from(bytes.span_matches(pos, two, BytePattern(b">>")))
    {
        ScanResult::new(Lexeme::Punct, two)
    }
    else {
        ScanResult::new(Lexeme::Punct, pos.advance(ByteWidth::ONE))
    }
}

/// Scan a shell digit run as a redirection file descriptor when it abuts a
/// `<` / `>` operator (`2>`, `2>&1`), else as an ordinary shell word.
///
/// The lookahead is exactly one byte past the digit run, so a bare numeric
/// word (`echo 2`) and a digit-led word (`2nd`) stay shell words; only the
/// `2>` / `2>>` / `2>&1` redirection-prefix shape classifies as a
/// `file_descriptor` (tree-sitter `file_descriptor`).
///
/// # Specification
/// - requires: the cursor identifies a byte in this scanner's lexical domain.
/// - ensures: scanning advances; only a digit run immediately followed by
///   redirection is a file descriptor.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — valid scanner leads at zero and a nonzero offset,
///   complete tokens, adjacent delimiters and truncated tails are compared with
///   exact class/end pairs. Wrong mode, premature consumption, overconsumption
///   and failure to advance change a row; only a digit run immediately followed
///   by redirection is a file descriptor.
/// - witness: `label::tests::scanner_decisions_preserve_class_and_end`
#[anodized::spec(requires: bytes.0.get(pos.0).is_some_and(u8::is_ascii_digit), ensures: |ret| ret.next > pos && (matches!(ret.lexeme, Lexeme::FileDescriptor | Lexeme::ShellWord)))]
fn scan_shell_fd_or_word(
    bytes: SourceBytes<'_>,
    pos: ByteOffset,
) -> ScanResult
{
    let digits_end = scan_digits(bytes, pos);
    if bytes
        .byte(digits_end)
        .is_some_and(|byte| matches!(u8::from(byte), b'<' | b'>'))
    {
        ScanResult::new(Lexeme::FileDescriptor, digits_end)
    }
    else {
        scan_shell_word(bytes, pos)
    }
}

/// Scan a `#!` / `$!` shell start with an optional dialect run up to `open`.
///
/// The whole `#!dialect{` (or `$!dialect{`) spelling is one lexeme; its label
/// is resolved by the molder from the opener text.
///
/// # Specification
/// - requires: the cursor points to a hash-bang or dollar-bang prefix.
/// - ensures: a complete optional dialect and opener is punctuation; otherwise
///   only the leading byte is unknown.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — empty and named dialects, absent openers and trailing
///   source expose the exact class/end pair. Accepting a missing brace or
///   keeping the dialect after a rejected prefix changes the observation.
/// - witness: `label::tests::scanner_decisions_preserve_class_and_end`
/// - witness: `label::tests::prefix_recognizers_respect_truncation_and_word_boundaries`
#[anodized::spec(requires: bytes.0.get(pos.0 ..).is_some_and(|tail| tail.starts_with(b"#!") || tail.starts_with(b"$!")), ensures: |ret| match ret.lexeme { Lexeme::Punct => ret.next.0 >= pos.0.saturating_add(3) && ret.next <= bytes.len() && bytes.0.get(ret.next.0.saturating_sub(1)) == Some(&open.0), Lexeme::Unknown => ret.next.0 == pos.0.saturating_add(1), _ => false })]
fn scan_shell_start(
    bytes: SourceBytes<'_>,
    pos: ByteOffset,
    open: SourceByte,
) -> ScanResult
{
    // Skip the two-byte `#!` / `$!` lead, then an optional dialect word.
    let mut cursor = pos.advance(ByteWidth::TWO);
    while let Some(byte) = bytes.byte(cursor) {
        if bool::from(byte.is_dialect()) {
            cursor = cursor.advance(ByteWidth::ONE);
        }
        else {
            break;
        }
    }
    if bytes.byte(cursor) == Some(open) {
        ScanResult::new(Lexeme::Punct, cursor.advance(ByteWidth::ONE))
    }
    else {
        // No opening brace: not a shell start; fall back to a stray byte.
        ScanResult::new(Lexeme::Unknown, pos.advance(ByteWidth::ONE))
    }
}

/// Scan a numeric literal, classifying a trailing primitive suffix as
/// `typed_number`.
///
/// # Specification
/// - requires: the cursor identifies a byte in this scanner's lexical domain.
/// - ensures: scanning advances; a number commits fractions and exponents only
///   with a digit and promotes only a bounded primitive suffix.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — valid scanner leads at zero and a nonzero offset,
///   complete tokens, adjacent delimiters and truncated tails are compared with
///   exact class/end pairs. Wrong mode, premature consumption, overconsumption
///   and failure to advance change a row; a number commits fractions and
///   exponents only with a digit and promotes only a bounded primitive suffix.
/// - witness: `label::tests::scanner_decisions_preserve_class_and_end`
#[anodized::spec(requires: bytes.0.get(pos.0).is_some_and(u8::is_ascii_digit) || (bytes.0.get(pos.0) == Some(&b'.') && bytes.0.get(pos.0.saturating_add(1)).is_some_and(u8::is_ascii_digit)), ensures: |ret| ret.next > pos && (matches!(ret.lexeme, Lexeme::Number | Lexeme::TypedNumber)))]
fn scan_number(
    bytes: SourceBytes<'_>,
    pos: ByteOffset,
) -> ScanResult
{
    let mut cursor = scan_digits(bytes, pos);
    // Optional fractional part `.[0-9]+` (a lone `.` after digits is a
    // projection, so only consume the dot when a digit follows).
    if bytes.byte(cursor) == Some(SourceByte::from(b'.'))
        && bytes
            .byte(cursor.advance(ByteWidth::ONE))
            .is_some_and(|byte| bool::from(byte.is_ascii_digit()))
    {
        cursor = scan_digits(bytes, cursor.advance(ByteWidth::ONE));
    }
    // Optional exponent `[eE][+-]?[0-9]+`.
    if let Some(byte) = bytes.byte(cursor)
        && matches!(u8::from(byte), b'e' | b'E')
    {
        let mut probe = cursor.advance(ByteWidth::ONE);
        if matches!(bytes.byte(probe).map(u8::from), Some(b'+' | b'-')) {
            probe = probe.advance(ByteWidth::ONE);
        }
        if bytes
            .byte(probe)
            .is_some_and(|digit| bool::from(digit.is_ascii_digit()))
        {
            cursor = scan_digits(bytes, probe);
        }
    }
    // Optional primitive-type suffix promotes the literal to `typed_number`.
    suffix_len(bytes, cursor).map_or_else(
        || ScanResult::new(Lexeme::Number, cursor),
        |width| ScanResult::new(Lexeme::TypedNumber, cursor.advance(width)),
    )
}

/// Advance over a run of ASCII digits.
///
/// # Specification
/// - requires: the cursor is within the source or at its end.
/// - ensures: returns the maximal run of ASCII decimal digits, including an
///   empty run.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — empty input, an immediate delimiter, a mixed run, end of
///   input and a nonzero origin expose the first excluded byte. Skipping a
///   delimiter, accepting the neighboring class or consuming too little changes
///   the pinned end offset.
/// - witness: `label::tests::run_scanners_stop_at_the_first_excluded_byte`
#[anodized::spec(requires: pos <= bytes.len(), ensures: |ret| ret >= pos && ret <= bytes.len() && bytes.0.get(pos.0 .. ret.0).is_some_and(|run| run.iter().copied().all(|byte| byte.is_ascii_digit())) && bytes.0.get(ret.0).copied().is_none_or(|byte| !byte.is_ascii_digit()))]
fn scan_digits(
    bytes: SourceBytes<'_>,
    pos: ByteOffset,
) -> ByteOffset
{
    let mut cursor = pos;
    while bytes
        .byte(cursor)
        .is_some_and(|byte| bool::from(byte.is_ascii_digit()))
    {
        cursor = cursor.advance(ByteWidth::ONE);
    }
    cursor
}
/// Scan a run of shell-word bytes, classifying a `NAME=…` run as an
/// environment assignment.
///
/// The `=` is a shell-word byte, so the run is a maximal munch across it and a
/// `NAME=value` assignment arrives as ONE token — the whole-token shape both
/// tree-sitter grammar (`environment_assignment` is a `token(seq(…))`, not a
/// composite rule) and the PBG (a single-tile Expression atom) already expect.
/// Splitting it into `NAME` / `=` / `value` left the `=` with no admissible
/// shell mold at all — no shell rule declares a `=` tile — so it could only
/// ever raise an `UnmoldedTok`, and the assignment mold could never fire.
///
/// A `"`-quoted value binds into the same token when the run ends at the `=`
/// (the tree-sitter `choice(pattern_shell_word, /"([^"\\]|\\.)*"/)` value), so
/// `FOO="a b"` is one assignment rather than an assignment plus a string.
///
/// # Specification
/// - requires: the cursor identifies an existing byte.
/// - ensures: advances over a shell word, whole assignment or one unknown byte.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — valid scanner leads at zero and a nonzero offset,
///   complete tokens, adjacent delimiters and truncated tails are compared with
///   exact class/end pairs. Wrong mode, premature consumption, overconsumption
///   and failure to advance change a row; identifier-led assignment prefixes
///   stay whole, while flags containing equals remain ordinary words.
/// - witness: `label::tests::scanner_decisions_preserve_class_and_end`
#[anodized::spec(requires: pos < bytes.len(), ensures: |ret| ret.next > pos && (matches!(ret.lexeme, Lexeme::ShellWord | Lexeme::EnvAssign | Lexeme::Unknown)))]
fn scan_shell_word(
    bytes: SourceBytes<'_>,
    pos: ByteOffset,
) -> ScanResult
{
    let mut cursor = pos;
    while bytes
        .byte(cursor)
        .is_some_and(|byte| bool::from(byte.is_shell_word()))
    {
        cursor = cursor.advance(ByteWidth::ONE);
    }
    if cursor <= pos {
        // Not a shell-word byte and unmatched above: advance one to stay total.
        return ScanResult::new(Lexeme::Unknown, pos.advance(ByteWidth::ONE));
    }
    if !bool::from(is_env_assign_run(bytes, pos, cursor)) {
        return ScanResult::new(Lexeme::ShellWord, cursor);
    }
    // `NAME=` immediately before a `"` takes the quoted string as its value.
    let end = if bytes.byte(cursor.retreat(ByteWidth::ONE)) == Some(SourceByte::from(b'='))
        && bytes.byte(cursor) == Some(SourceByte::from(b'"'))
    {
        scan_shell_quoted_value(bytes, cursor)
    }
    else {
        cursor
    };
    ScanResult::new(Lexeme::EnvAssign, end)
}

/// Return whether the shell-word run `bytes[start .. end]` is an environment
/// assignment: an identifier-shaped `NAME` followed by `=` (tree-sitter
/// `environment_assignment`'s `/[A-Za-z_][A-Za-z0-9_]*/ "="` prefix).
///
/// A run whose name part is not identifier-shaped is an ordinary shell word,
/// so `--color=auto` and a bare `=` (a `[ "$a" = "$b" ]` test operator) stay
/// words rather than assignments.
///
/// # Specification
/// - requires: start and end bound a source run.
/// - ensures: recognizes a nonempty ASCII variable name immediately followed by
///   equals, irrespective of its value.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — empty runs, empty values, digit-led names and flags
///   containing equals are compared with assignment classification. Moving the
///   name-start boundary or accepting a separator inside the name changes it.
/// - witness: `label::tests::prefix_recognizers_respect_truncation_and_word_boundaries`
#[anodized::spec(requires: start <= end && end <= bytes.len(), ensures: |ret| bool::from(ret) == bytes.0.get(start.0 .. end.0).is_some_and(|run| run.iter().position(|byte| *byte == b'=').is_some_and(|equal| equal > 0 && run.first().is_some_and(|byte| byte.is_ascii_alphabetic() || *byte == b'_') && run.get(1 .. equal).is_some_and(|name| name.iter().all(|byte| byte.is_ascii_alphanumeric() || *byte == b'_')))))]
fn is_env_assign_run(
    bytes: SourceBytes<'_>,
    start: ByteOffset,
    end: ByteOffset,
) -> BytePredicate
{
    let mut cursor = start;
    if !bytes
        .byte(cursor)
        .is_some_and(|byte| bool::from(byte.is_var_name_start()))
    {
        return BytePredicate::from(false);
    }
    cursor = cursor.advance(ByteWidth::ONE);
    while cursor < end
        && bytes
            .byte(cursor)
            .is_some_and(|byte| bool::from(byte.is_word_continue()))
    {
        cursor = cursor.advance(ByteWidth::ONE);
    }
    BytePredicate::from(cursor < end && bytes.byte(cursor) == Some(SourceByte::from(b'=')))
}

/// Scan a `"`-quoted environment-assignment value from its opening quote to the
/// byte past its closing quote, honoring `\.` escapes. An unterminated string
/// runs to end of input (the scan stays total; the melder raises the
/// obligation).
///
/// # Specification
/// - requires: the cursor points to a double quote.
/// - ensures: an unescaped closing quote ends the value; otherwise scanning
///   continues through the tail.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — empty, spaced and escaped-quote values, with a following
///   delimiter or an ordinary unclosed tail, expose the end offset. Stopping at
///   an escaped quote or consuming past a real closing quote changes it.
/// - witness: `label::tests::quoted_values_stop_only_at_an_unescaped_quote`
#[anodized::spec(requires: bytes.0.get(pos.0) == Some(&b'"'), ensures: |ret| ret > pos && ret <= bytes.len() && (ret == bytes.len() || bytes.0.get(ret.0.saturating_sub(1)) == Some(&b'"')))]
fn scan_shell_quoted_value(
    bytes: SourceBytes<'_>,
    pos: ByteOffset,
) -> ByteOffset
{
    let mut cursor = pos.advance(ByteWidth::ONE);
    while let Some(byte) = bytes.byte(cursor) {
        match u8::from(byte) {
            | b'\\' => cursor = cursor.advance(ByteWidth::TWO),
            | b'"' => return cursor.advance(ByteWidth::ONE),
            | _ => cursor = cursor.advance(ByteWidth::ONE),
        }
    }
    cursor
}

/// Return the width of a primitive-numeric suffix at `pos` (`u32`, `f64`, …).
///
/// # Specification
/// - ensures: returns three bytes exactly for a primitive numeric suffix not
///   followed by a word byte; otherwise none.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — all six suffixes at end and before punctuation, every
///   truncated prefix and an added word byte expose the optional width.
///   Omitting a suffix, accepting a partial suffix or ignoring the word
///   boundary changes that width.
/// - witness: `label::tests::prefix_recognizers_respect_truncation_and_word_boundaries`
#[anodized::spec(ensures: |ret| ret.map(usize::from) == (bytes.0.get(pos.0 .. pos.0.saturating_add(3)).is_some_and(|word| [b"u32".as_slice(), b"u64".as_slice(), b"i32".as_slice(), b"i64".as_slice(), b"f32".as_slice(), b"f64".as_slice()].contains(&word)) && bytes.0.get(pos.0.saturating_add(3)).is_none_or(|byte| !byte.is_ascii_alphanumeric() && *byte != b'_')).then_some(3))]
fn suffix_len(
    bytes: SourceBytes<'_>,
    pos: ByteOffset,
) -> Option<ByteWidth>
{
    for suffix in [
        b"u32".as_slice(),
        b"u64".as_slice(),
        b"i32".as_slice(),
        b"i64".as_slice(),
        b"f32".as_slice(),
        b"f64".as_slice(),
    ] {
        let width = ByteWidth::from(suffix.len());
        let end = pos.advance(width);
        if bool::from(bytes.span_matches(pos, end, BytePattern(suffix))) {
            // A suffix must not run into a longer word (`1u32x` is not typed).
            if bytes
                .byte(end)
                .is_some_and(|byte| bool::from(byte.is_word_continue()))
            {
                continue;
            }
            return Some(width);
        }
    }
    None
}

/// Scan a lexeme led by `.`: a fractional number, the `..` rest token, or a
/// bare `.` projection.
///
/// # Specification
/// - requires: the cursor identifies a byte in this scanner's lexical domain.
/// - ensures: scanning advances; a dot before a digit starts a fraction; a pair
///   is rest punctuation and other dots stand alone.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — valid scanner leads at zero and a nonzero offset,
///   complete tokens, adjacent delimiters and truncated tails are compared with
///   exact class/end pairs. Wrong mode, premature consumption, overconsumption
///   and failure to advance change a row; a dot before a digit starts a
///   fraction; a pair is rest punctuation and other dots stand alone.
/// - witness: `label::tests::scanner_decisions_preserve_class_and_end`
#[anodized::spec(requires: bytes.0.get(pos.0) == Some(&b'.'), ensures: |ret| ret.next > pos && (matches!(ret.lexeme, Lexeme::Punct | Lexeme::Number | Lexeme::TypedNumber)))]
fn scan_dot(
    bytes: SourceBytes<'_>,
    pos: ByteOffset,
) -> ScanResult
{
    // A leading `.[0-9]` is a fractional number (`.5`); `..` is the rest token.
    if bytes
        .byte(pos.advance(ByteWidth::ONE))
        .is_some_and(|byte| bool::from(byte.is_ascii_digit()))
    {
        return scan_number(bytes, pos);
    }
    if bytes.byte(pos.advance(ByteWidth::ONE)) == Some(SourceByte::from(b'.')) {
        ScanResult::new(Lexeme::Punct, pos.advance(ByteWidth::TWO))
    }
    else {
        ScanResult::new(Lexeme::Punct, pos.advance(ByteWidth::ONE))
    }
}

/// Scan `_` as the wildcard tile or the head of a `_`-led identifier.
///
/// # Specification
/// - requires: the cursor identifies a byte in this scanner's lexical domain.
/// - ensures: scanning advances; a lone underscore is wildcard punctuation; a
///   continued underscore begins a lower word.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — valid scanner leads at zero and a nonzero offset,
///   complete tokens, adjacent delimiters and truncated tails are compared with
///   exact class/end pairs. Wrong mode, premature consumption, overconsumption
///   and failure to advance change a row; a lone underscore is wildcard
///   punctuation; a continued underscore begins a lower word.
/// - witness: `label::tests::scanner_decisions_preserve_class_and_end`
#[anodized::spec(requires: bytes.0.get(pos.0) == Some(&b'_'), ensures: |ret| ret.next > pos && (ret.lexeme == if ret.next.0 == pos.0.saturating_add(1) { Lexeme::Punct } else { Lexeme::LowerWord }))]
fn scan_word_or_underscore(
    bytes: SourceBytes<'_>,
    pos: ByteOffset,
) -> ScanResult
{
    let next = scan_word(bytes, pos);
    if next == pos.advance(ByteWidth::ONE) {
        // A lone `_` is the wildcard punctuation tile.
        ScanResult::new(Lexeme::Punct, next)
    }
    else {
        ScanResult::new(Lexeme::LowerWord, next)
    }
}

/// Advance over an identifier/constructor word from its lead, over
/// `[A-Za-z0-9_]` and the prime `′`.
///
/// The prime is a **continuation** — it never starts a word, so a stray `′`
/// stays an [`Lexeme::Unknown`] byte and `x′` is one word rather than a word
/// plus a stray. It is not restricted to the tail: `x′y` and `x′1` are single
/// words, exactly as an underscore in the same position would be, because a
/// prime that ended the word would make `x′y` two adjacent operands with no
/// operator between them. The primed variable is the circuit block form's own
/// spelling for a rewrite's target endpoint (`node : p(x) ==> (x′)`), and it
/// is the mathematical convention the rest of the corpus writes
/// in prose. ASCII `'` is deliberately **not** a word byte: it opens a shell
/// single-quoted run, and a word-continuing apostrophe would make `'…'` depend
/// on whether a word precedes it.
///
/// # Specification
/// - requires: the cursor starts an ASCII letter or underscore.
/// - ensures: consumes the maximal word-byte and Unicode-prime continuation,
///   leaving punctuation untouched.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — single-letter words, repeated and interior primes, a lone
///   prime and a following ASCII quote expose word boundaries. Treating prime
///   as a separator or a valid word start changes the class/text stream.
/// - witness: `label::tests::a_primed_word_is_one_word_and_a_lone_prime_is_not`
/// - witness: `label::tests::scanner_decisions_preserve_class_and_end`
#[anodized::spec(requires: bytes.0.get(pos.0).is_some_and(|byte| byte.is_ascii_alphabetic() || *byte == b'_'), ensures: |ret| ret > pos && ret <= bytes.len() && bytes.0.get(ret.0).is_none_or(|byte| !byte.is_ascii_alphanumeric() && *byte != b'_') && bytes.0.get(ret.0 ..).is_none_or(|tail| !tail.starts_with("′".as_bytes())))]
fn scan_word(
    bytes: SourceBytes<'_>,
    pos: ByteOffset,
) -> ByteOffset
{
    let mut cursor = pos.advance(ByteWidth::ONE);
    loop {
        if bytes
            .byte(cursor)
            .is_some_and(|byte| bool::from(byte.is_word_continue()))
        {
            cursor = cursor.advance(ByteWidth::ONE);
            continue;
        }
        let prime_end = cursor.advance(ByteWidth::THREE);
        if bool::from(bytes.span_matches(cursor, prime_end, BytePattern(&PRIME_UTF8))) {
            cursor = prime_end;
            continue;
        }
        return cursor;
    }
}

/// Scan an operator/punctuation tile, or a stray byte as `Unknown`.
///
/// # Specification
/// - requires: the cursor identifies a byte in this scanner's lexical domain.
/// - ensures: scanning advances; maximal operators, grade omega and bounded
///   bridges are punctuation; a stray scalar is unknown.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — valid scanner leads at zero and a nonzero offset,
///   complete tokens, adjacent delimiters and truncated tails are compared with
///   exact class/end pairs. Wrong mode, premature consumption, overconsumption
///   and failure to advance change a row; maximal operators, grade omega and
///   bounded bridges are punctuation; a stray scalar is unknown.
/// - witness: `label::tests::scanner_decisions_preserve_class_and_end`
#[anodized::spec(requires: pos < bytes.len(), ensures: |ret| ret.next > pos && (matches!(ret.lexeme, Lexeme::Punct | Lexeme::Unknown)))]
fn scan_punct_or_unknown(
    bytes: SourceBytes<'_>,
    pos: ByteOffset,
) -> ScanResult
{
    // `ω` (U+03C9, grade) = CF 89.
    if bytes.byte(pos) == Some(SourceByte::from(OMEGA_GRADE_UTF8[0]))
        && bytes.byte(pos.advance(ByteWidth::ONE)) == Some(SourceByte::from(OMEGA_GRADE_UTF8[1]))
    {
        return ScanResult::new(Lexeme::Punct, pos.advance(ByteWidth::TWO));
    }
    if let Some(end) = bridge_end(bytes, pos) {
        return ScanResult::new(Lexeme::Punct, end);
    }
    punct_len(bytes, pos).map_or_else(
        || {
            // A single stray byte (advance by its UTF-8 width to stay total).
            let width = bytes.byte(pos).map_or(ByteWidth::ONE, utf8_width);
            ScanResult::new(Lexeme::Unknown, pos.advance(width))
        },
        |width| ScanResult::new(Lexeme::Punct, pos.advance(width)),
    )
}

/// The compound bridge tiles: the sign that names the row a bridge produces,
/// and the bridge's letter, as one tile.
///
/// `+U` is the suspension, a positive type from a negative one, and `-F` the
/// returner, a negative type from a positive one. The pair is one tile only
/// when the letter ends there: `+Unit` is the sign `+` before the word `Unit`,
/// so the sum `A +Unit` and the difference `a -Foo` lex as they did before the
/// bridges took the sign. A type has no unary sign, so `+U` never stands for
/// `+` applied to a name `U`, and `A + B` is the sum whatever its spacing; `A
/// +U B` is the bridge after an operand, which the lowering refuses as an
/// operand its form does not take.
const BRIDGES: [&[u8]; 2] = [b"+U", b"-F"];

/// The end of the compound bridge tile at `pos`, if one starts there.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the offset two bytes past `pos` when the bytes there spell `+U`
///   or `-F` and the byte after neither continues a word nor opens a prime;
///   none otherwise.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — each bridge, a bridge letter continuing into a word or a
///   prime, the sum and difference signs before a name, a spaced sign, and a
///   bridge before punctuation and at the end of input separate the decision.
/// - witness: `label::tests::bridge_tiles_end_where_their_letter_does`
#[anodized::spec(ensures: |ret| ret.map(usize::from) == (bytes.0.get(pos.0 ..).is_some_and(|tail| tail.starts_with(b"+U") || tail.starts_with(b"-F")) && bytes.0.get(pos.0.saturating_add(2)).is_none_or(|byte| !byte.is_ascii_alphanumeric() && *byte != b'_') && bytes.0.get(pos.0.saturating_add(2) ..).is_none_or(|tail| !tail.starts_with("′".as_bytes()))).then_some(pos.0.saturating_add(2)))]
fn bridge_end(
    bytes: SourceBytes<'_>,
    pos: ByteOffset,
) -> Option<ByteOffset>
{
    let end = pos.advance(ByteWidth::TWO);
    let spelled = BRIDGES
        .iter()
        .any(|bridge| bool::from(bytes.span_matches(pos, end, BytePattern(bridge))));
    let continues = bytes
        .byte(end)
        .is_some_and(|byte| bool::from(byte.is_word_continue()))
        || bool::from(bytes.span_matches(
            end,
            end.advance(ByteWidth::THREE),
            BytePattern(&PRIME_UTF8),
        ));
    (spelled && !continues).then_some(end)
}

/// Return the byte length of an operator/punctuation tile at `pos`, if any.
///
/// # Specification
/// - ensures: returns the longest supported operator width, or one for single
///   punctuation, or none.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — every multi-byte spelling and every strict prefix, plus a
///   stray scalar and absent input, expose the maximal width. A shorter
///   operator shadowing a longer one or an overlong match changes the result.
/// - witness: `label::tests::prefix_recognizers_respect_truncation_and_word_boundaries`
#[anodized::spec(ensures: |ret| ret.map(usize::from) == bytes.0.get(pos.0 ..).and_then(|tail| MULTI_PUNCT.iter().filter(|operator| tail.starts_with(operator.as_bytes())).map(|operator| operator.len()).max().or_else(|| tail.first().filter(|byte| b"!&()*+,-:;<=>?@[]{}|$".contains(byte)).map(|_| 1))))]
fn punct_len(
    bytes: SourceBytes<'_>,
    pos: ByteOffset,
) -> Option<ByteWidth>
{
    for op in MULTI_PUNCT {
        let width = ByteWidth::from(op.len());
        let end = pos.advance(width);
        if bool::from(bytes.span_matches(pos, end, BytePattern(op.as_bytes()))) {
            return Some(width);
        }
    }
    let byte = bytes.byte(pos)?;
    bool::from(byte.is_single_punct()).then_some(ByteWidth::ONE)
}

/// Return the UTF-8 byte width implied by a leading byte (1 on ASCII).
///
/// # Specification
/// - ensures: C0–DF lead a two-byte step, E0–EF three bytes, F0–F7 four; every
///   other byte advances one, including continuation and invalid leads.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the entire byte domain is partitioned into pinned width
///   intervals; every boundary and its neighbor distinguishes shifted
///   thresholds, wrong widths and nonprogress on invalid leading bytes.
/// - witness: `label::tests::utf8_step_widths_cover_every_leading_byte`
#[anodized::spec(ensures: |ret| ret.0 == match lead.0 { 0xc0 ..= 0xdf => 2, 0xe0 ..= 0xef => 3, 0xf0 ..= 0xf7 => 4, _ => 1 })]
fn utf8_width(lead: SourceByte) -> ByteWidth
{
    match u8::from(lead) {
        | 0xc0 ..= 0xdf => ByteWidth::TWO,
        | 0xe0 ..= 0xef => ByteWidth::THREE,
        | 0xf0 ..= 0xf7 => ByteWidth::FOUR,
        // ASCII (`0x00..=0x7f`) and any continuation or invalid lead advance one
        // byte, keeping the scan total.
        | _ => ByteWidth::ONE,
    }
}

#[cfg(test)]
mod tests
{
    use alloc::borrow::ToOwned as _;
    use alloc::string::String;
    use alloc::vec;
    use alloc::vec::Vec;

    use gandr_surface_syntax::SourceFragment;

    use super::Lexeme;
    use super::Token;
    use super::label;

    #[test]
    fn token_observers_preserve_supplied_order()
    {
        let source = SourceFragment::from("a b");
        let tokens = [
            Token {
                lexeme: Lexeme::LowerWord,
                start: 2,
                end: 3,
            },
            Token {
                lexeme: Lexeme::Space,
                start: 1,
                end: 2,
            },
            Token {
                lexeme: Lexeme::LowerWord,
                start: 0,
                end: 1,
            },
            Token {
                lexeme: Lexeme::Unknown,
                start: 3,
                end: 3,
            },
        ];
        assert_eq!(tiles(source, &tokens), vec![
            (Lexeme::LowerWord, "b".to_owned()),
            (Lexeme::LowerWord, "a".to_owned()),
            (Lexeme::Unknown, String::new())
        ]);
        assert_eq!(reconstruct(source, &tokens), "b a");
    }

    #[test]
    fn run_scanners_stop_at_the_first_excluded_byte()
    {
        type Run =
            for<'source> fn(super::SourceBytes<'source>, super::ByteOffset) -> super::ByteOffset;
        type Row<'source> = (&'source str, usize);
        let cases: &[(Run, &[Row<'_>])] = &[
            (super::scan_digits, &[
                ("", 0),
                ("x", 0),
                ("123x", 3),
                ("123", 3),
            ]),
            (super::scan_newlines, &[
                ("", 0),
                ("x", 0),
                ("\r\n\nx", 3),
                ("\r\n", 2),
            ]),
            (super::scan_line_comment_from, &[
                ("", 0),
                ("\n", 0),
                ("éx\r\n", 3),
                ("éx", 3),
            ]),
            (super::scan_horizontal_space, &[
                ("", 0),
                ("\n", 0),
                ("x", 0),
                (" \t\u{c}\u{b}\u{a0}\u{200b}\u{2060}\u{feff}\nx", 15),
            ]),
        ];
        for &(scan, rows) in cases {
            for &(source, end) in rows {
                for prefix in ["", "?"] {
                    let input = alloc::format!("{prefix}{source}");
                    assert_eq!(
                        usize::from(scan(
                            super::SourceBytes::from(input.as_bytes()),
                            super::ByteOffset::from(prefix.len())
                        )),
                        prefix.len().saturating_add(end),
                        "{input:?}"
                    );
                }
            }
        }
    }

    #[test]
    fn quoted_values_stop_only_at_an_unescaped_quote()
    {
        for (source, end) in [
            ("\"\";", 2_usize),
            ("\"a b\";", 5),
            ("\"a\\\"b\";", 6),
            ("\"tail", 5),
        ] {
            assert_eq!(
                usize::from(super::scan_shell_quoted_value(
                    super::SourceBytes::from(source.as_bytes()),
                    super::ByteOffset::from(0_usize)
                )),
                end
            );
        }
    }

    #[test]
    fn prefix_recognizers_respect_truncation_and_word_boundaries()
    {
        let zero = super::ByteOffset::from(0_usize);
        for (source, expected) in [
            ("", false),
            ("#!", false),
            ("#!{", true),
            ("$!sh{", true),
            ("#sh{", false),
            ("#!sh}", false),
        ] {
            assert_eq!(
                bool::from(super::is_shell_open(super::SourceBytes::from(
                    source.as_bytes()
                ))),
                expected,
                "{source}"
            );
        }
        for (source, expected) in [
            ("", false),
            ("A=", true),
            ("_a9=x", true),
            ("9a=x", false),
            ("--x=y", false),
            ("a-b=x", false),
            ("=x", false),
        ] {
            assert_eq!(
                bool::from(super::is_env_assign_run(
                    super::SourceBytes::from(source.as_bytes()),
                    zero,
                    super::ByteOffset::from(source.len())
                )),
                expected,
                "{source}"
            );
        }
        for suffix in ["u32", "u64", "i32", "i64", "f32", "f64"] {
            for (tail, expected) in [
                ("", Some(3_usize)),
                ("!", Some(3)),
                ("x", None),
                ("_", None),
                ("9", None),
            ] {
                let source = alloc::format!("{suffix}{tail}");
                assert_eq!(
                    super::suffix_len(super::SourceBytes::from(source.as_bytes()), zero)
                        .map(usize::from),
                    expected,
                    "{source}"
                );
            }
            for length in 0 .. suffix.len() {
                let source = suffix.as_bytes().get(.. length).unwrap();
                assert_eq!(
                    super::suffix_len(super::SourceBytes::from(source), zero),
                    None
                );
            }
        }
        for blank in ["\u{a0}", "\u{200b}", "\u{2060}", "\u{feff}"] {
            assert_eq!(
                super::unicode_blank_len(super::SourceBytes::from(blank.as_bytes()), zero)
                    .map(usize::from),
                Some(blank.len())
            );
            for length in 0 .. blank.len() {
                assert_eq!(
                    super::unicode_blank_len(
                        super::SourceBytes::from(blank.as_bytes().get(.. length).unwrap()),
                        zero
                    ),
                    None
                );
            }
        }
        for source in [" ", "é", "\u{200a}"] {
            assert_eq!(
                super::unicode_blank_len(super::SourceBytes::from(source.as_bytes()), zero),
                None
            );
        }
        for operator in [
            "-->", "<->", "==>", "<=>", "/\\", "~>", "->", "<-", "=>", "==", "!=", "<=", ">=",
            "++", "&&", "||", "|&", "<>", "<&", ">&", ">>", "@[", ":>",
        ] {
            assert_eq!(
                super::punct_len(super::SourceBytes::from(operator.as_bytes()), zero)
                    .map(usize::from),
                Some(operator.len()),
                "{operator}"
            );
        }
        for (source, expected) in [
            ("", None),
            ("~", None),
            ("/", None),
            ("é", None),
            ("-", Some(1_usize)),
            ("--", Some(1)),
            ("<", Some(1)),
            ("<=", Some(2)),
            ("==", Some(2)),
        ] {
            assert_eq!(
                super::punct_len(super::SourceBytes::from(source.as_bytes()), zero)
                    .map(usize::from),
                expected,
                "{source}"
            );
        }
        for source in ["#!{", "$!{"] {
            let result = super::scan_shell_start(
                super::SourceBytes::from(source.as_bytes()),
                zero,
                super::SourceByte::from(b'{'),
            );
            assert_eq!(result.lexeme, Lexeme::Punct);
            assert_eq!(usize::from(result.next), 3);
        }
    }

    #[test]
    fn scanner_decisions_preserve_class_and_end()
    {
        type Scanner =
            for<'source> fn(super::SourceBytes<'source>, super::ByteOffset) -> super::ScanResult;
        type Row<'source> = (&'source str, Lexeme, usize);
        let cases: &[(Scanner, &[Row<'_>])] = &[
            (super::scan_string_interior, &[
                ("\"x", Lexeme::Quote, 1),
                ("\\n", Lexeme::EscapeSequence, 2),
                ("\\", Lexeme::Unknown, 1),
                ("${x", Lexeme::Punct, 2),
                ("a$b\"", Lexeme::StringFragment, 3),
            ]),
            (super::scan_single_quoted_interior, &[
                ("'x", Lexeme::Punct, 1),
                ("a\\n'", Lexeme::SingleQuotedContent, 3),
                ("a\"b", Lexeme::SingleQuotedContent, 3),
            ]),
            (super::scan_variable_name, &[
                ("_a9!", Lexeme::VariableName, 3),
                ("9x", Lexeme::VariableName, 2),
                ("!", Lexeme::Unknown, 1),
            ]),
            (super::scan_braced_shell_interior, &[
                ("}x", Lexeme::Punct, 1),
                ("a9_}", Lexeme::VariableName, 3),
                (":x", Lexeme::ShellWord, 1),
            ]),
            (super::scan_shell_double_interior, &[
                ("\"x", Lexeme::Punct, 1),
                ("\\n", Lexeme::EscapeSequence, 2),
                ("\\", Lexeme::Unknown, 1),
                ("${x", Lexeme::Punct, 2),
                ("a b$", Lexeme::StringFragment, 3),
            ]),
            (super::scan_shell_interior, &[
                ("[x", Lexeme::SubshellOpen, 1),
                ("]x", Lexeme::SubshellClose, 1),
                ("word=ok;", Lexeme::EnvAssign, 7),
                (" \t", Lexeme::Space, 2),
                ("2>x", Lexeme::FileDescriptor, 1),
            ]),
            (super::scan_one, &[
                ("a9;", Lexeme::LowerWord, 2),
                ("A9;", Lexeme::UpperWord, 2),
                ("[", Lexeme::Punct, 1),
                ("é", Lexeme::Unknown, 2),
                ("\r\nx", Lexeme::Space, 2),
            ]),
            (super::scan_slash, &[
                ("//a\nx", Lexeme::Space, 3),
                ("/*a/*b*/c*/x", Lexeme::Space, 11),
                ("/*", Lexeme::Space, 2),
                ("/\\x", Lexeme::Punct, 2),
                ("/", Lexeme::Unknown, 1),
            ]),
            (super::scan_hash, &[
                ("#!/x\n", Lexeme::Space, 4),
                ("#!sh{x", Lexeme::Punct, 5),
                ("#{x", Lexeme::Punct, 2),
                ("#!bad", Lexeme::Unknown, 1),
                ("#", Lexeme::Unknown, 1),
            ]),
            (super::scan_character, &[
                ("'é'x", Lexeme::Character, 4),
                ("'\\n'x", Lexeme::Character, 4),
                ("''", Lexeme::Punct, 1),
                ("'a", Lexeme::Punct, 1),
                ("'", Lexeme::Punct, 1),
            ]),
            (super::scan_escape, &[
                ("\\éx", Lexeme::EscapeSequence, 3),
                ("\\n", Lexeme::EscapeSequence, 2),
                ("\\", Lexeme::Unknown, 1),
            ]),
            (super::scan_dollar, &[
                ("${x", Lexeme::Punct, 2),
                ("$!sh{x", Lexeme::Punct, 5),
                ("$!bad", Lexeme::Unknown, 1),
                ("$x", Lexeme::Punct, 1),
                ("$", Lexeme::Punct, 1),
            ]),
            (super::scan_shell_operator, &[
                ("&&x", Lexeme::Punct, 2),
                ("||x", Lexeme::Punct, 2),
                ("|&x", Lexeme::Punct, 2),
                ("&|", Lexeme::Punct, 1),
                (";", Lexeme::Punct, 1),
            ]),
            (super::scan_shell_redirection, &[
                ("<>x", Lexeme::Punct, 2),
                ("<&x", Lexeme::Punct, 2),
                (">&x", Lexeme::Punct, 2),
                (">>x", Lexeme::Punct, 2),
                ("><", Lexeme::Punct, 1),
                (">", Lexeme::Punct, 1),
            ]),
            (super::scan_shell_fd_or_word, &[
                ("12>x", Lexeme::FileDescriptor, 2),
                ("12nd", Lexeme::ShellWord, 4),
                ("12 ", Lexeme::ShellWord, 2),
                ("2", Lexeme::ShellWord, 1),
            ]),
            (super::scan_number, &[
                ("1", Lexeme::Number, 1),
                ("1.", Lexeme::Number, 1),
                ("1.5e-2!", Lexeme::Number, 6),
                ("1e+", Lexeme::Number, 1),
                (".5u32!", Lexeme::TypedNumber, 5),
                ("1u32x", Lexeme::Number, 1),
            ]),
            (super::scan_shell_word, &[
                ("a=b;", Lexeme::EnvAssign, 3),
                ("A=\"a b\";", Lexeme::EnvAssign, 7),
                ("--x=y;", Lexeme::ShellWord, 5),
                ("=", Lexeme::ShellWord, 1),
                (";", Lexeme::Unknown, 1),
            ]),
            (super::scan_dot, &[
                (".5!", Lexeme::Number, 2),
                (".5f64", Lexeme::TypedNumber, 5),
                ("..x", Lexeme::Punct, 2),
                (".x", Lexeme::Punct, 1),
                (".", Lexeme::Punct, 1),
            ]),
            (super::scan_word_or_underscore, &[
                ("_", Lexeme::Punct, 1),
                ("_a!", Lexeme::LowerWord, 2),
                ("_′!", Lexeme::LowerWord, 4),
            ]),
            (super::scan_punct_or_unknown, &[
                ("ωx", Lexeme::Punct, 2),
                ("+U!", Lexeme::Punct, 2),
                ("+Unit", Lexeme::Punct, 1),
                ("<=>x", Lexeme::Punct, 3),
                ("éx", Lexeme::Unknown, 2),
                ("~", Lexeme::Unknown, 1),
            ]),
        ];
        for &(scan, rows) in cases {
            for &(source, class, end) in rows {
                for prefix in ["", "?"] {
                    let input = alloc::format!("{prefix}{source}");
                    let result = scan(
                        super::SourceBytes::from(input.as_bytes()),
                        super::ByteOffset::from(prefix.len()),
                    );
                    assert_eq!(result.lexeme, class, "{input:?}");
                    assert_eq!(
                        usize::from(result.next),
                        prefix.len().saturating_add(end),
                        "{input:?}"
                    );
                }
            }
        }
    }

    #[test]
    fn cursor_arithmetic_saturates_at_both_boundaries()
    {
        for (start, width, forward, backward) in [
            (0_usize, 0_usize, 0_usize, 0_usize),
            (1, 2, 3, 0),
            (0, usize::MAX, usize::MAX, 0),
            (usize::MAX, 1, usize::MAX, usize::MAX.saturating_sub(1)),
            (
                usize::MAX.saturating_sub(1),
                1,
                usize::MAX,
                usize::MAX.saturating_sub(2),
            ),
        ] {
            let start = super::ByteOffset::from(start);
            let width = super::ByteWidth::from(width);
            assert_eq!(usize::from(start.advance(width)), forward);
            assert_eq!(usize::from(start.retreat(width)), backward);
        }
    }

    #[test]
    fn byte_classes_match_the_complete_byte_domain()
    {
        for value in u8::MIN ..= u8::MAX {
            let byte = super::SourceByte::from(value);
            let letter = b"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz".contains(&value);
            let digit = b"0123456789".contains(&value);
            assert_eq!(
                bool::from(byte.is_var_name_start()),
                letter || value == b'_'
            );
            assert_eq!(
                bool::from(byte.is_word_continue()),
                letter || digit || value == b'_'
            );
            assert_eq!(
                bool::from(byte.is_dialect()),
                letter || digit || b"_-".contains(&value)
            );
            assert_eq!(
                bool::from(byte.is_shell_word()),
                !b" \t\r\n\x0c\x0b;|&<>{}[]()`\"'$#".contains(&value)
            );
            assert_eq!(
                bool::from(byte.is_single_punct()),
                b"!&()*+,-:;<=>?@[]{}|$".contains(&value)
            );
        }
    }

    #[test]
    fn utf8_step_widths_cover_every_leading_byte()
    {
        for (first, last, width) in [
            (0_u8, 0xbf_u8, 1_usize),
            (0xc0, 0xdf, 2),
            (0xe0, 0xef, 3),
            (0xf0, 0xf7, 4),
            (0xf8, 0xff, 1),
        ] {
            for byte in first ..= last {
                assert_eq!(
                    usize::from(super::utf8_width(super::SourceByte::from(byte))),
                    width
                );
            }
        }
    }

    #[test]
    fn token_text_checks_ranges_and_character_boundaries()
    {
        let source = SourceFragment::from("éx");
        for (start, end, expected) in [
            (0_u32, 2_u32, "é"),
            (2, 3, "x"),
            (3, 3, ""),
            (0, 0, ""),
            (1, 2, ""),
            (2, 1, ""),
            (0, 4, ""),
        ] {
            let token = Token {
                lexeme: Lexeme::Unknown,
                start,
                end,
            };
            assert_eq!(token.text(&source).as_ref(), expected);
        }
    }

    #[test]
    fn every_lexical_class_has_a_contextual_witness()
    {
        use Lexeme::*;
        let cases: &[(&str, &[Lexeme])] = &[
            ("a", &[LowerWord]),
            ("A", &[UpperWord]),
            ("1", &[Number]),
            ("1u32", &[TypedNumber]),
            ("'a'", &[Character]),
            ("\"a\"", &[Quote, StringFragment, Quote]),
            ("\"\\n\"", &[Quote, EscapeSequence, Quote]),
            ("+", &[Punct]),
            ("#!{hi}", &[Punct, ShellWord, Punct]),
            ("#!{A=b}", &[Punct, EnvAssign, Punct]),
            ("#!{'hi'}", &[
                Punct,
                Punct,
                SingleQuotedContent,
                Punct,
                Punct,
            ]),
            ("#!{$A}", &[Punct, Punct, VariableName, Punct]),
            ("#!{[]}", &[Punct, SubshellOpen, SubshellClose, Punct]),
            ("#!{2>f}", &[Punct, FileDescriptor, Punct, ShellWord, Punct]),
            (" ", &[Space]),
            ("~", &[Unknown]),
        ];
        for &(source, expected) in cases {
            let tokens = label(SourceFragment::from(source));
            assert!(
                tokens
                    .iter()
                    .map(|token| token.lexeme)
                    .eq(expected.iter().copied()),
                "{source:?}: {tokens:?}"
            );
            assert_eq!(reconstruct(SourceFragment::from(source), &tokens), source);
        }
    }

    #[test]
    fn span_tiling_is_total_and_gapless()
    {
        for src in [
            "",
            "   ",
            "def f() -> -F Integer { ret (x * x) }",
            "// comment\n/* nested /* block */ */\n#!/usr/bin/env gandr\nx",
            "1u32 + 2.5f64 - .5e-3 * 42",
            "@[doc(\"d\")] def x = #{ a = 1 };",
            "case v { Inl(x) => x, Inr(y) => y }",
            "\u{feff}def a = 1;",
        ] {
            let tokens = label(SourceFragment::from(src));
            // Spans tile 0..len with no gap or overlap.
            let mut cursor = 0_u32;
            for token in &tokens {
                assert_eq!(token.start, cursor, "no gap before {token:?} in {src:?}");
                assert!(token.end > token.start || src.is_empty());
                cursor = token.end;
            }
            assert_eq!(
                usize::try_from(cursor).unwrap(),
                src.len(),
                "covers {src:?}"
            );
            assert_eq!(reconstruct(SourceFragment::from(src), &tokens), src);
        }
    }
    #[test]
    fn stray_bytes_are_unknown_never_a_panic()
    {
        // Byte soup never panics and always tiles the source.
        for src in ["\u{0}\u{1}\u{2}", "```", "€¥£", "def \\ = ;"] {
            let tokens = label(SourceFragment::from(src));
            assert_eq!(reconstruct(SourceFragment::from(src), &tokens), src);
        }
        let tokens = label(SourceFragment::from("~"));
        assert_eq!(1, tokens.len());
        assert_eq!(Some(Lexeme::Unknown), tokens.first().map(|t| t.lexeme));
    }
    #[test]
    fn string_interpolation_nests_braces_and_strings()
    {
        // A record inside an interpolation keeps its own `#{ … }` braces, and a
        // nested string with its own interpolation re-enters string mode — the
        // brace-depth stack resolves both to the correct closing `}`.
        let record = "\"v=${ #{ a = 1 } }\"";
        assert_eq!(
            tiles(
                SourceFragment::from(record),
                &label(SourceFragment::from(record))
            ),
            vec![
                (Lexeme::Quote, "\"".to_owned()),
                (Lexeme::StringFragment, "v=".to_owned()),
                (Lexeme::Punct, "${".to_owned()),
                (Lexeme::Punct, "#{".to_owned()),
                (Lexeme::LowerWord, "a".to_owned()),
                (Lexeme::Punct, "=".to_owned()),
                (Lexeme::Number, "1".to_owned()),
                (Lexeme::Punct, "}".to_owned()),
                (Lexeme::Punct, "}".to_owned()),
                (Lexeme::Quote, "\"".to_owned()),
            ]
        );
        let nested = "\"${ f(\"${x}\") }\"";
        // Losslessness holds through the nested-string re-entry.
        assert_eq!(
            reconstruct(
                SourceFragment::from(nested),
                &label(SourceFragment::from(nested))
            ),
            nested
        );
        // A bare `$` not followed by `{` stays ordinary string content.
        let dollar = "\"$5.00\"";
        assert_eq!(
            tiles(
                SourceFragment::from(dollar),
                &label(SourceFragment::from(dollar))
            ),
            vec![
                (Lexeme::Quote, "\"".to_owned()),
                (Lexeme::StringFragment, "$5.00".to_owned()),
                (Lexeme::Quote, "\"".to_owned()),
            ]
        );
    }
    #[test]
    fn shell_braced_parameter_lexes_distinctly_from_interpolation()
    {
        // `#!{ echo ${HOME}; }`: the shell `${` opens a braced parameter whose
        // interior is a `variable_name` (VariableName), and the matching `}`
        // closes the brace WITHOUT closing the shell block — the shell block's
        // own `}` still follows. This is the shell-brace mode, distinct from
        // the string-interpolation `${ E }` (whose interior is host tokens).
        let src = "#!{ echo ${HOME}; }";
        let tokens = label(SourceFragment::from(src));
        assert_eq!(
            reconstruct(SourceFragment::from(src), &tokens),
            src,
            "braced param is lossless"
        );
        assert_eq!(tiles(SourceFragment::from(src), &tokens), vec![
            (Lexeme::Punct, "#!{".to_owned()),
            (Lexeme::ShellWord, "echo".to_owned()),
            (Lexeme::Punct, "${".to_owned()),
            (Lexeme::VariableName, "HOME".to_owned()),
            (Lexeme::Punct, "}".to_owned()),
            (Lexeme::Punct, ";".to_owned()),
            (Lexeme::Punct, "}".to_owned()),
        ]);
    }
    #[test]
    fn shell_file_descriptor_is_a_digit_run_before_a_redirection()
    {
        // A digit run immediately before `<` / `>` is a FileDescriptor (`2>`),
        // while a bare digit word and a digit-led word stay ShellWords.
        let src = "#!{ make 2>&1; }";
        assert_eq!(
            reconstruct(SourceFragment::from(src), &label(SourceFragment::from(src))),
            src,
            "fd is lossless"
        );
        assert_eq!(
            tiles(SourceFragment::from(src), &label(SourceFragment::from(src))),
            vec![
                (Lexeme::Punct, "#!{".to_owned()),
                (Lexeme::ShellWord, "make".to_owned()),
                (Lexeme::FileDescriptor, "2".to_owned()),
                (Lexeme::Punct, ">&".to_owned()),
                (Lexeme::ShellWord, "1".to_owned()),
                (Lexeme::Punct, ";".to_owned()),
                (Lexeme::Punct, "}".to_owned()),
            ]
        );
        // A bare digit word (`echo 2 things`) and a digit-led word (`2nd`) are
        // NOT file descriptors — the lookahead requires an abutting redirection.
        assert_eq!(
            tiles(
                SourceFragment::from("#!{ echo 2 2nd; }"),
                &label(SourceFragment::from("#!{ echo 2 2nd; }"))
            ),
            vec![
                (Lexeme::Punct, "#!{".to_owned()),
                (Lexeme::ShellWord, "echo".to_owned()),
                (Lexeme::ShellWord, "2".to_owned()),
                (Lexeme::ShellWord, "2nd".to_owned()),
                (Lexeme::Punct, ";".to_owned()),
                (Lexeme::Punct, "}".to_owned()),
            ]
        );
    }
    #[test]
    fn shell_subshell_brackets_are_distinct_from_host_brackets()
    {
        // A shell `[` / `]` classifies as SubshellOpen / SubshellClose (a
        // shell-context bracket), while a host list literal keeps the ordinary
        // `[` / `]` punctuation — the two never share a lexeme class, so the
        // host `[` mold menu is untouched.
        let shell = "#!{ [ echo a ]; }";
        assert_eq!(
            reconstruct(
                SourceFragment::from(shell),
                &label(SourceFragment::from(shell))
            ),
            shell,
            "subshell lossless"
        );
        assert_eq!(
            tiles(
                SourceFragment::from(shell),
                &label(SourceFragment::from(shell))
            ),
            vec![
                (Lexeme::Punct, "#!{".to_owned()),
                (Lexeme::SubshellOpen, "[".to_owned()),
                (Lexeme::ShellWord, "echo".to_owned()),
                (Lexeme::ShellWord, "a".to_owned()),
                (Lexeme::SubshellClose, "]".to_owned()),
                (Lexeme::Punct, ";".to_owned()),
                (Lexeme::Punct, "}".to_owned()),
            ]
        );
        // A host list literal keeps the plain `[` / `]` punctuation.
        assert_eq!(
            tiles(
                SourceFragment::from("[1, 2]"),
                &label(SourceFragment::from("[1, 2]"))
            ),
            vec![
                (Lexeme::Punct, "[".to_owned()),
                (Lexeme::Number, "1".to_owned()),
                (Lexeme::Punct, ",".to_owned()),
                (Lexeme::Number, "2".to_owned()),
                (Lexeme::Punct, "]".to_owned()),
            ]
        );
    }
    #[test]
    fn shell_single_and_double_quotes_do_not_cross()
    {
        // A `"` inside single quotes is verbatim content, and a `'` inside
        // double quotes is a literal fragment byte — the two quote modes never
        // toggle each other, and neither closes the shell block.
        let src = "#!{ echo 'a \"b' \"c 'd\"; }";
        let tokens = label(SourceFragment::from(src));
        assert_eq!(
            reconstruct(SourceFragment::from(src), &tokens),
            src,
            "mixed quotes are lossless"
        );
        assert_eq!(tiles(SourceFragment::from(src), &tokens), vec![
            (Lexeme::Punct, "#!{".to_owned()),
            (Lexeme::ShellWord, "echo".to_owned()),
            (Lexeme::Punct, "'".to_owned()),
            (Lexeme::SingleQuotedContent, "a \"b".to_owned()),
            (Lexeme::Punct, "'".to_owned()),
            (Lexeme::Punct, "\"".to_owned()),
            (Lexeme::StringFragment, "c 'd".to_owned()),
            (Lexeme::Punct, "\"".to_owned()),
            (Lexeme::Punct, ";".to_owned()),
            (Lexeme::Punct, "}".to_owned()),
        ]);
    }

    #[test]
    fn labels_a_definition_losslessly()
    {
        let src = "def greeting = \"hi\";\nret greeting\n";
        let tokens = label(SourceFragment::from(src));
        assert_eq!(
            reconstruct(SourceFragment::from(src), &tokens),
            src,
            "spans reconstruct the source"
        );
        let non_space = tiles(SourceFragment::from(src), &tokens);
        assert_eq!(non_space, vec![
            (Lexeme::LowerWord, "def".to_owned()),
            (Lexeme::LowerWord, "greeting".to_owned()),
            (Lexeme::Punct, "=".to_owned()),
            (Lexeme::Quote, "\"".to_owned()),
            (Lexeme::StringFragment, "hi".to_owned()),
            (Lexeme::Quote, "\"".to_owned()),
            (Lexeme::Punct, ";".to_owned()),
            (Lexeme::LowerWord, "ret".to_owned()),
            (Lexeme::LowerWord, "greeting".to_owned()),
        ]);
    }
    #[test]
    fn remolding_hinges_on_spacing()
    {
        // `x -y` vs `x - y`: spacing changes trivia but not the `-` lexeme — the
        // prefix/infix distinction is the molder's, over the same non-space
        // token shape (paper Fig. 5).
        let spaced = tiles(
            SourceFragment::from("x - y"),
            &label(SourceFragment::from("x - y")),
        );
        let tight = tiles(
            SourceFragment::from("x -y"),
            &label(SourceFragment::from("x -y")),
        );
        assert_eq!(spaced, vec![
            (Lexeme::LowerWord, "x".to_owned()),
            (Lexeme::Punct, "-".to_owned()),
            (Lexeme::LowerWord, "y".to_owned()),
        ]);
        assert_eq!(tight, vec![
            (Lexeme::LowerWord, "x".to_owned()),
            (Lexeme::Punct, "-".to_owned()),
            (Lexeme::LowerWord, "y".to_owned()),
        ]);
    }
    #[test]
    fn shell_env_assignment_is_one_token()
    {
        // `NAME=value` munches across the `=` into ONE token — the whole-token
        // shape the tree-sitter `token(seq(…))` and the PBG's single-tile atom both
        // expect. Splitting it left the `=` with no admissible
        // shell mold at all.
        let src = "#!{ FOO=1 echo }";
        assert_eq!(
            tiles(SourceFragment::from(src), &label(SourceFragment::from(src))),
            vec![
                (Lexeme::Punct, "#!{".to_owned()),
                (Lexeme::EnvAssign, "FOO=1".to_owned()),
                (Lexeme::ShellWord, "echo".to_owned()),
                (Lexeme::Punct, "}".to_owned()),
            ]
        );
    }
    #[test]
    fn shell_env_assignment_takes_a_quoted_value()
    {
        // A `"`-quoted value binds into the same token (the tree-sitter
        // `choice(pattern_shell_word, /"([^"\\]|\\.)*"/)` value), so an
        // assignment with an interior space is still ONE assignment.
        let src = "#!{ FOO=\"a b\" echo }";
        assert_eq!(
            tiles(SourceFragment::from(src), &label(SourceFragment::from(src))),
            vec![
                (Lexeme::Punct, "#!{".to_owned()),
                (Lexeme::EnvAssign, "FOO=\"a b\"".to_owned()),
                (Lexeme::ShellWord, "echo".to_owned()),
                (Lexeme::Punct, "}".to_owned()),
            ]
        );
    }
    #[test]
    fn shell_words_containing_eq_are_not_assignments()
    {
        // The name part must be identifier-shaped, so a flag with an `=` is ONE
        // ordinary shell word (it was three tiles, with an unmoldable `=`, before
        // the environment-assignment munch) and a bare `=` — the `[ "$a" = "$b" ]` test
        // operator — is a plain word rather than an `UnmoldedTok`.
        let flag = "#!{ ls --color=auto }";
        assert_eq!(
            tiles(
                SourceFragment::from(flag),
                &label(SourceFragment::from(flag))
            ),
            vec![
                (Lexeme::Punct, "#!{".to_owned()),
                (Lexeme::ShellWord, "ls".to_owned()),
                (Lexeme::ShellWord, "--color=auto".to_owned()),
                (Lexeme::Punct, "}".to_owned()),
            ]
        );
        let bare = "#!{ test a = b }";
        assert_eq!(
            tiles(
                SourceFragment::from(bare),
                &label(SourceFragment::from(bare))
            ),
            vec![
                (Lexeme::Punct, "#!{".to_owned()),
                (Lexeme::ShellWord, "test".to_owned()),
                (Lexeme::ShellWord, "a".to_owned()),
                (Lexeme::ShellWord, "=".to_owned()),
                (Lexeme::ShellWord, "b".to_owned()),
                (Lexeme::Punct, "}".to_owned()),
            ]
        );
    }
    #[test]
    fn typed_numbers_and_suffix_boundaries()
    {
        assert_eq!(
            tiles(
                SourceFragment::from("1u32"),
                &label(SourceFragment::from("1u32"))
            ),
            vec![(Lexeme::TypedNumber, "1u32".to_owned())]
        );
        // A suffix that runs into a longer word is a bare number then a word.
        assert_eq!(
            tiles(
                SourceFragment::from("1u32x"),
                &label(SourceFragment::from("1u32x"))
            ),
            vec![
                (Lexeme::Number, "1".to_owned()),
                (Lexeme::LowerWord, "u32x".to_owned()),
            ]
        );
        assert_eq!(
            tiles(
                SourceFragment::from("2.5f64"),
                &label(SourceFragment::from("2.5f64"))
            ),
            vec![(Lexeme::TypedNumber, "2.5f64".to_owned())]
        );
    }
    #[test]
    fn projection_dot_is_not_a_number()
    {
        // `r.field`: the `.` after a word is a projection tile, not a fraction.
        assert_eq!(
            tiles(
                SourceFragment::from("r.field"),
                &label(SourceFragment::from("r.field"))
            ),
            vec![
                (Lexeme::LowerWord, "r".to_owned()),
                (Lexeme::Punct, ".".to_owned()),
                (Lexeme::LowerWord, "field".to_owned()),
            ]
        );
    }
    #[test]
    fn multi_byte_operators_munch_maximally()
    {
        assert_eq!(
            tiles(
                SourceFragment::from("->"),
                &label(SourceFragment::from("->"))
            ),
            vec![(Lexeme::Punct, "->".to_owned())]
        );
        assert_eq!(
            tiles(
                SourceFragment::from("<-"),
                &label(SourceFragment::from("<-"))
            ),
            vec![(Lexeme::Punct, "<-".to_owned())]
        );
        assert_eq!(
            tiles(
                SourceFragment::from("<="),
                &label(SourceFragment::from("<="))
            ),
            vec![(Lexeme::Punct, "<=".to_owned())]
        );
        assert_eq!(
            tiles(
                SourceFragment::from("/\\"),
                &label(SourceFragment::from("/\\"))
            ),
            vec![(Lexeme::Punct, "/\\".to_owned())]
        );
        assert_eq!(
            tiles(
                SourceFragment::from("#{"),
                &label(SourceFragment::from("#{"))
            ),
            vec![(Lexeme::Punct, "#{".to_owned())]
        );
        // `<-` must not split into `<` then `-`.
        assert_eq!(
            tiles(
                SourceFragment::from("a<-b"),
                &label(SourceFragment::from("a<-b"))
            ),
            vec![
                (Lexeme::LowerWord, "a".to_owned()),
                (Lexeme::Punct, "<-".to_owned()),
                (Lexeme::LowerWord, "b".to_owned()),
            ]
        );
        // `~>` (the retired rewrite-face arrow) munches as one tile; a lone `~`
        // stays an unknown stray byte.
        assert_eq!(
            tiles(
                SourceFragment::from("a~>b"),
                &label(SourceFragment::from("a~>b"))
            ),
            vec![
                (Lexeme::LowerWord, "a".to_owned()),
                (Lexeme::Punct, "~>".to_owned()),
                (Lexeme::LowerWord, "b".to_owned()),
            ]
        );
        assert_eq!(
            tiles(SourceFragment::from("~"), &label(SourceFragment::from("~"))),
            vec![(Lexeme::Unknown, "~".to_owned())]
        );
    }

    #[test]
    fn bridge_tiles_end_where_their_letter_does()
    {
        let lexed = |src: &str| tiles(SourceFragment::from(src), &label(SourceFragment::from(src)));
        let punct = |text: &str| (Lexeme::Punct, text.to_owned());
        let upper = |text: &str| (Lexeme::UpperWord, text.to_owned());
        let lower = |text: &str| (Lexeme::LowerWord, text.to_owned());
        assert_eq!(
            lexed("+U[ω] (A -> -F B)"),
            vec![
                punct("+U"),
                punct("["),
                punct("ω"),
                punct("]"),
                punct("("),
                upper("A"),
                punct("->"),
                punct("-F"),
                upper("B"),
                punct(")"),
            ],
            "each bridge is one tile, before a bracket or a space"
        );
        assert_eq!(
            lexed("-F(+U)"),
            vec![punct("-F"), punct("("), punct("+U"), punct(")")],
            "a bridge ends before punctuation and at the end of input"
        );
        assert_eq!(
            lexed("A +Unit"),
            vec![upper("A"), punct("+"), upper("Unit")],
            "a sign before a word beginning with the letter is the sum"
        );
        assert_eq!(
            lexed("a -Foo"),
            vec![lower("a"), punct("-"), upper("Foo")],
            "and the difference"
        );
        assert_eq!(
            lexed("A + U"),
            vec![upper("A"), punct("+"), upper("U")],
            "a spaced sign is its own tile, and the letter a word"
        );
        assert_eq!(
            lexed("U′ F_"),
            vec![upper("U′"), upper("F_")],
            "a letter continued by a word byte or a prime is a word"
        );
        assert_eq!(
            lexed("+U′"),
            vec![punct("+"), upper("U′")],
            "and the sign before it is the sum"
        );
    }
    #[test]
    fn a_backslash_in_code_is_one_tile_and_an_escape_in_a_string()
    {
        let lexed = |src: &str| tiles(SourceFragment::from(src), &label(SourceFragment::from(src)));
        let punct = |text: &str| (Lexeme::Punct, text.to_owned());
        let upper = |text: &str| (Lexeme::UpperWord, text.to_owned());
        assert_eq!(
            lexed(r"\T.\A. T"),
            vec![
                punct("\\"),
                upper("T"),
                punct("."),
                punct("\\"),
                upper("A"),
                punct("."),
                upper("T"),
            ],
            "the abstraction's lead stands apart from the binder it introduces"
        );
        assert_eq!(
            lexed(r#""\T""#),
            vec![
                (Lexeme::Quote, "\"".to_owned()),
                (Lexeme::EscapeSequence, "\\T".to_owned()),
                (Lexeme::Quote, "\"".to_owned()),
            ],
            "inside a string the backslash still begins an escape"
        );
    }
    #[test]
    fn circuit_arrows_munch_past_the_shorter_tiles_they_extend()
    {
        // The arrow grid. Each glyph strictly extends a live shorter
        // tile, so this is the lexical check the grid owes: the
        // grid glyph wins the munch and the shorter tile keeps its own reading
        // one character away.
        for (src, arrow) in [
            ("a-->b", "-->"),
            ("a<->b", "<->"),
            ("a==>b", "==>"),
            ("a<=>b", "<=>"),
        ] {
            assert_eq!(
                tiles(SourceFragment::from(src), &label(SourceFragment::from(src))),
                vec![
                    (Lexeme::LowerWord, "a".to_owned()),
                    (Lexeme::Punct, arrow.to_owned()),
                    (Lexeme::LowerWord, "b".to_owned()),
                ],
                "{src:?} munches {arrow:?} as one tile"
            );
        }
        // The shorter tiles are untouched: the term arrow, the bind arrow, the
        // case arm, and the two comparison operators each still lex alone.
        for (src, shorter) in [
            ("a->b", "->"),
            ("a<-b", "<-"),
            ("a=>b", "=>"),
            ("a==b", "=="),
            ("a<=b", "<="),
        ] {
            assert_eq!(
                tiles(SourceFragment::from(src), &label(SourceFragment::from(src))),
                vec![
                    (Lexeme::LowerWord, "a".to_owned()),
                    (Lexeme::Punct, shorter.to_owned()),
                    (Lexeme::LowerWord, "b".to_owned()),
                ],
                "{src:?} still lexes {shorter:?}"
            );
        }
        // `--` is not a comment lead in this language (the repo comments with
        // `//`), so a doubled dash outside `-->` is two ordinary operators and
        // the rest of the line is live source.
        assert_eq!(
            tiles(
                SourceFragment::from("a--b"),
                &label(SourceFragment::from("a--b"))
            ),
            vec![
                (Lexeme::LowerWord, "a".to_owned()),
                (Lexeme::Punct, "-".to_owned()),
                (Lexeme::Punct, "-".to_owned()),
                (Lexeme::LowerWord, "b".to_owned()),
            ]
        );
    }
    #[test]
    fn the_face_migration_leaves_the_directed_type_former_run_alone()
    {
        // `~~>` is the directed former on types, not yet in this table.
        // Retiring `~>` as the rewrite-face former must not disturb how
        // that byte run scans, because the two are one glyph apart and the
        // point of the retirement was to dissolve that near-collision rather
        // than manage it. The run still scans as a stray `~` followed by `~>`,
        // so landing `~~>` remains the single entry inserted ahead of `~>` —
        // the migration foreclosed nothing.
        assert_eq!(
            tiles(
                SourceFragment::from("A ~~> B"),
                &label(SourceFragment::from("A ~~> B"))
            ),
            vec![
                (Lexeme::UpperWord, "A".to_owned()),
                (Lexeme::Unknown, "~".to_owned()),
                (Lexeme::Punct, "~>".to_owned()),
                (Lexeme::UpperWord, "B".to_owned()),
            ]
        );
        // And the face arrow does not reach into it: `==>` beside `~~>`
        // in one source keeps both readings.
        assert_eq!(
            tiles(
                SourceFragment::from("a ==> b ~~> c"),
                &label(SourceFragment::from("a ==> b ~~> c"))
            ),
            vec![
                (Lexeme::LowerWord, "a".to_owned()),
                (Lexeme::Punct, "==>".to_owned()),
                (Lexeme::LowerWord, "b".to_owned()),
                (Lexeme::Unknown, "~".to_owned()),
                (Lexeme::Punct, "~>".to_owned()),
                (Lexeme::LowerWord, "c".to_owned()),
            ]
        );
    }

    #[test]
    fn a_primed_word_is_one_word_and_a_lone_prime_is_not()
    {
        // `x′` is the circuit block form's spelling for a rewrite's target
        // endpoint: one word, not a word plus a stray byte.
        assert_eq!(
            tiles(
                SourceFragment::from("x′"),
                &label(SourceFragment::from("x′"))
            ),
            vec![(Lexeme::LowerWord, "x′".to_owned())]
        );
        // Primes accumulate, and an uppercase-led word takes them too.
        assert_eq!(
            tiles(
                SourceFragment::from("Nat′′"),
                &label(SourceFragment::from("Nat′′"))
            ),
            vec![(Lexeme::UpperWord, "Nat′′".to_owned())]
        );
        // A prime never *starts* a word.
        assert_eq!(
            tiles(SourceFragment::from("′"), &label(SourceFragment::from("′"))),
            vec![(Lexeme::Unknown, "′".to_owned())]
        );
        // ASCII `'` stays the shell single-quote opener rather than a word
        // byte, so a trailing apostrophe still ends the word.
        assert_eq!(
            tiles(
                SourceFragment::from("x'"),
                &label(SourceFragment::from("x'"))
            ),
            vec![
                (Lexeme::LowerWord, "x".to_owned()),
                (Lexeme::Punct, "'".to_owned()),
            ]
        );
        // The prime continues a word rather than ending it, so an interior
        // prime keeps one word — the alternative would make `x′y` two adjacent
        // operands with no operator between them.
        assert_eq!(
            tiles(
                SourceFragment::from("x′y"),
                &label(SourceFragment::from("x′y"))
            ),
            vec![(Lexeme::LowerWord, "x′y".to_owned())]
        );
        // The prime reaches only the word scanner: strings, comments, and shell
        // words all run their own scanners and are untouched.
        assert_eq!(
            tiles(
                SourceFragment::from("\"a ′ b\""),
                &label(SourceFragment::from("\"a ′ b\""))
            ),
            vec![
                (Lexeme::Quote, "\"".to_owned()),
                (Lexeme::StringFragment, "a ′ b".to_owned()),
                (Lexeme::Quote, "\"".to_owned()),
            ]
        );
    }
    #[test]
    fn string_interpolation_segments_the_string()
    {
        // `"a ${ x } b"` lexes as an open fragment, the `${` opener, the host
        // expression `x`, the `}` closer, and the closing fragment — the
        // string-segment mode. The interior `x` is an ordinary LowerWord, not
        // string content.
        let src = "\"a ${ x } b\"";
        let tokens = label(SourceFragment::from(src));
        assert_eq!(
            reconstruct(SourceFragment::from(src), &tokens),
            src,
            "interpolation is lossless"
        );
        assert_eq!(tiles(SourceFragment::from(src), &tokens), vec![
            (Lexeme::Quote, "\"".to_owned()),
            (Lexeme::StringFragment, "a ".to_owned()),
            (Lexeme::Punct, "${".to_owned()),
            (Lexeme::LowerWord, "x".to_owned()),
            (Lexeme::Punct, "}".to_owned()),
            (Lexeme::StringFragment, " b".to_owned()),
            (Lexeme::Quote, "\"".to_owned()),
        ]);
    }
    #[test]
    fn shell_braced_parameters_nest_and_juxtapose()
    {
        // Adjacent and word-embedded braced parameters keep their own `}` and
        // never leak into the shell block's brace accounting.
        let adjacent = "#!{ echo ${x}${y}; }";
        assert_eq!(
            reconstruct(
                SourceFragment::from(adjacent),
                &label(SourceFragment::from(adjacent))
            ),
            adjacent
        );
        assert_eq!(
            tiles(
                SourceFragment::from(adjacent),
                &label(SourceFragment::from(adjacent))
            ),
            vec![
                (Lexeme::Punct, "#!{".to_owned()),
                (Lexeme::ShellWord, "echo".to_owned()),
                (Lexeme::Punct, "${".to_owned()),
                (Lexeme::VariableName, "x".to_owned()),
                (Lexeme::Punct, "}".to_owned()),
                (Lexeme::Punct, "${".to_owned()),
                (Lexeme::VariableName, "y".to_owned()),
                (Lexeme::Punct, "}".to_owned()),
                (Lexeme::Punct, ";".to_owned()),
                (Lexeme::Punct, "}".to_owned()),
            ]
        );
        // A word-embedded parameter `pre${x}post` splits into three shell atoms.
        let embedded = "#!{ echo pre${x}post; }";
        assert_eq!(
            reconstruct(
                SourceFragment::from(embedded),
                &label(SourceFragment::from(embedded))
            ),
            embedded
        );
        assert_eq!(
            tiles(
                SourceFragment::from(embedded),
                &label(SourceFragment::from(embedded))
            ),
            vec![
                (Lexeme::Punct, "#!{".to_owned()),
                (Lexeme::ShellWord, "echo".to_owned()),
                (Lexeme::ShellWord, "pre".to_owned()),
                (Lexeme::Punct, "${".to_owned()),
                (Lexeme::VariableName, "x".to_owned()),
                (Lexeme::Punct, "}".to_owned()),
                (Lexeme::ShellWord, "post".to_owned()),
                (Lexeme::Punct, ";".to_owned()),
                (Lexeme::Punct, "}".to_owned()),
            ]
        );
    }
    #[test]
    fn shell_double_quote_lexes_fragments_escapes_and_expansions()
    {
        // A shell double-quoted string keeps interior spaces as ONE
        // `double_string_fragment` run, lexes `\.` escapes, and expands
        // `$name` / `${name}` — never juxtaposed shell words. The interior `}`
        // and space stay literal fragment content.
        let src = "#!{ echo \"a $x ${y}\\tb\"; }";
        let tokens = label(SourceFragment::from(src));
        assert_eq!(
            reconstruct(SourceFragment::from(src), &tokens),
            src,
            "shell dquote is lossless"
        );
        assert_eq!(tiles(SourceFragment::from(src), &tokens), vec![
            (Lexeme::Punct, "#!{".to_owned()),
            (Lexeme::ShellWord, "echo".to_owned()),
            (Lexeme::Punct, "\"".to_owned()),
            (Lexeme::StringFragment, "a ".to_owned()),
            (Lexeme::Punct, "$".to_owned()),
            (Lexeme::VariableName, "x".to_owned()),
            (Lexeme::StringFragment, " ".to_owned()),
            (Lexeme::Punct, "${".to_owned()),
            (Lexeme::VariableName, "y".to_owned()),
            (Lexeme::Punct, "}".to_owned()),
            (Lexeme::EscapeSequence, "\\t".to_owned()),
            (Lexeme::StringFragment, "b".to_owned()),
            (Lexeme::Punct, "\"".to_owned()),
            (Lexeme::Punct, ";".to_owned()),
            (Lexeme::Punct, "}".to_owned()),
        ]);
    }
    /// The non-space classes and their texts, in order.
    ///
    /// # Specification
    /// - ensures: returns each non-space token and its text in input order,
    ///   including unknown and empty fragments.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — reversed spans, a space token and an empty unknown
    ///   fragment expose filtering and order independently of the labeler.
    ///   Sorting by source offset, dropping unknowns or retaining spaces
    ///   changes the sequence.
    /// - witness: `label::tests::token_observers_preserve_supplied_order`
    #[anodized::spec(ensures: |ret| ret.len() == tokens.iter().filter(|token| token.lexeme != Lexeme::Space).count() && ret.iter().zip(tokens.iter().filter(|token| token.lexeme != Lexeme::Space)).all(|(observed, token)| observed.0 == token.lexeme && observed.1.as_str() == token.text(&src).as_ref()))]
    fn tiles(
        src: SourceFragment<'_>,
        tokens: &[Token],
    ) -> Vec<(Lexeme, String)>
    {
        let source = src;
        tokens
            .iter()
            .filter(|token| token.lexeme != Lexeme::Space)
            .map(|token| {
                (
                    token.lexeme,
                    AsRef::<str>::as_ref(&token.text(&source)).to_owned(),
                )
            })
            .collect()
    }
    /// Reconstruct the source from the token spans (the losslessness check).
    ///
    /// # Specification
    /// - ensures: concatenates the text of every supplied token in supplied
    ///   order, retaining spaces.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — reversed spans, a space and an empty fragment expose
    ///   ordered reconstruction independently of tokenization. Reordering,
    ///   omitting space or copying the whole source instead changes the
    ///   reconstructed text.
    /// - witness: `label::tests::token_observers_preserve_supplied_order`
    #[anodized::spec(ensures: |ret| tokens.iter().try_fold(ret.as_str(), |remaining, token| remaining.strip_prefix(token.text(&src).as_ref())) == Some(""))]
    fn reconstruct(
        src: SourceFragment<'_>,
        tokens: &[Token],
    ) -> String
    {
        let mut out = String::new();
        let source = src;
        for token in tokens {
            out.push_str(AsRef::<str>::as_ref(&token.text(&source)));
        }
        out
    }
}
