//! The batch parser: `labeler ∘ molder ∘ fold(push) ∘ commit(finalize)`.
//!
//! [`parse`](fn@crate::parse) is the whole front-end composed:
//! it labels the source, molds each
//! token to its obligation-minimizing [`gandr_surface_syntax::MoldId`], folds
//! the molded stream through the melder's `push`, records trivia for
//! losslessness, and commits the molded [`SyntaxTree`]. The result carries the
//! buffered obligations beside the tree so the obligation surface is never
//! lost — a total function: any [`SourceText`] yields a well-formed
//! [`ParseResult`], never a panic.

use alloc::vec::Vec;

use gandr_surface_grammar::Pbg;
use gandr_surface_syntax::ClosingClass;
use gandr_surface_syntax::NodeIndex;
use gandr_surface_syntax::NodeLabel;
use gandr_surface_syntax::SourceFragment;
use gandr_surface_syntax::SourceText;
use gandr_surface_syntax::SyntaxTree;

use crate::MeldError;
use crate::MeldState;
use crate::Molder;
use crate::label::label;
use crate::oblig::ObligationInstance;

/// Whether a batch parse produced no obligations.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct ParseCleanStatus(bool);

impl From<bool> for ParseCleanStatus
{
    /// Wraps the flag.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(is_clean: bool) -> Self
    {
        Self(is_clean)
    }
}

impl From<ParseCleanStatus> for bool
{
    /// Reads the flag back out.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(is_clean: ParseCleanStatus) -> Self
    {
        is_clean.0
    }
}

/// The result of a batch parse: the committed tree and its completion
/// obligations.
///
/// The obligations are the melder's buffer at commit — every convex, ghost or
/// incomparable repair the parse made — severity-ordered by
/// [`obligations`](ParseResult::obligations) so consumers render the most
/// serious first. A clean parse has an empty obligation slice.
///
/// # Specification
/// - requires: constructed by [`parse`](fn@crate::parse).
/// - ensures: preserves the committed [`SyntaxTree`] and the parse's
///   obligations exactly; [`obligations`](ParseResult::obligations) is
///   severity-ordered (highest first) then by span.
/// - provides: the batch parse's carrier so obligations are not lost.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a clean parse and an obligation-bearing parse distinguish
///   the empty and non-empty obligation slice.
/// - witness: `tests::acceptance::core_forms_are_clean`
/// - witness: `tests::acceptance::malformed_programs_repair_predictably`
#[derive(Clone, Debug)]
pub struct ParseResult<'source>
{
    /// The committed concrete syntax tree.
    tree: SyntaxTree<'source>,
    /// The parse's obligations, severity-ordered (highest first) then by span.
    obligations: Vec<ObligationInstance>,
}

impl<'source> ParseResult<'source>
{
    /// Return the committed concrete syntax tree.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn tree(&self) -> &SyntaxTree<'source>
    {
        &self.tree
    }

    /// Return the parse's obligations, severity-ordered (highest first).
    ///
    /// # Specification
    /// - requires: none.
    /// - ensures: returns the buffered obligations sorted by descending
    ///   [`crate::Oblig`] severity, then ascending span.
    /// - provides: the batch obligation surface.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a mixed-severity parse observes the descending order.
    /// - witness: `tests::acceptance::mixed_set_precedence_requires_obligation_and_commits`
    #[inline]
    #[must_use]
    pub fn obligations(&self) -> &[ObligationInstance]
    {
        &self.obligations
    }

    /// Return whether the parse produced no obligations (a clean parse).
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn is_clean(&self) -> ParseCleanStatus
    {
        ParseCleanStatus::from(self.obligations.is_empty())
    }

    /// Return the class of every minted close in the whole tree, in tree
    /// order.
    ///
    /// A ghost's class is **carried**, never reconstructed: the melder records
    /// it when it mints the ghost, from the form-level closing class the
    /// grammar derives, and a ghost whose form has no single such class carries
    /// none. Reading the sequence back is what distinguishes *no ghost was
    /// minted* from *a ghost was minted and carried no class* — which a repair
    /// witness must tell apart, because only the second says the grammar could
    /// not name the closer.
    ///
    /// # Specification
    /// - requires: none.
    /// - ensures: returns one entry per [`NodeLabel::GhostClose`] leaf, in tree
    ///   order; unclassed ghosts contribute nothing.
    /// - provides: the minted-close surface a witness reads directly.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a two-class repair, an unclassed repair, and a clean
    ///   parse distinguish the sequence.
    /// - witness: `tests::acceptance::an_unclosed_delimiter_yields_to_every_declaration_family`
    #[inline]
    #[must_use]
    pub fn minted_close_classes(&self) -> Vec<ClosingClass>
    {
        let mut classes = Vec::new();
        let mut pending: Vec<NodeIndex> = Vec::from([self.tree.root()]);
        let mut children: Vec<NodeIndex> = Vec::new();
        while let Some(next) = pending.pop() {
            let Some(node) = self.tree.node(next)
            else {
                continue;
            };
            if let NodeLabel::GhostClose { class, .. } = node.label() {
                classes.push(class);
            }
            children.clear();
            children.extend(self.tree.children(next));
            pending.extend(children.iter().rev().copied());
        }
        classes
    }

    /// Consume the result and return the committed tree.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn into_tree(self) -> SyntaxTree<'source>
    {
        self.tree
    }
}

/// Batch-parse `source` over the checked grammar `pbg`.
///
/// The whole front-end, composed: label → mold → fold(push) → commit. Trivia
/// are recorded for losslessness (the committed tree reconstructs the source),
/// and the obligations ride the result.
///
/// ```
/// use gandr_surface_grammar::built_in;
/// use gandr_surface_parser::Oblig;
/// use gandr_surface_parser::parse;
/// use gandr_surface_syntax::SourceText;
///
/// let pbg = built_in()?;
///
/// let whole = parse(&pbg, SourceText::from("def answer = 42;"))?;
/// assert!(bool::from(whole.is_clean()));
///
/// // An unclosed group still yields a tree; the missing `)` is an obligation.
/// let partial = parse(&pbg, SourceText::from("def answer = ( 42 ;"))?;
/// assert!(
///     partial
///         .obligations()
///         .iter()
///         .any(|obligation| obligation.class == Oblig::MissingTile)
/// );
/// # Ok::<(), Box<dyn core::error::Error>>(())
/// ```
///
/// # Specification
/// - requires: `pbg` is a checked grammar; `source` is any UTF-8 text.
/// - ensures: returns a well-formed [`SyntaxTree`] over `source` recording
///   `pbg`'s fingerprint plus the parse's severity-ordered obligations; the
///   committed tree's leaf spans, ordered by offset, reconstruct `source`
///   (losslessness — trivia are recorded as [`NodeLabel::Space`] leaves,
///   digest-skipped but byte-preserving); total over every input.
/// - provides: the batch parse entry point.
/// - fails: returns [`MeldError`] only for an arena-construction failure at
///   commit (arena size or coordinate overflow), never for ungrammatical input.
/// - panics: none.
/// - intension: labels are folded in source order; each non-space token is
///   molded by the obligation-minimizing [`Molder`]; space tokens are recorded
///   verbatim.
///
/// # Errors
/// Returns [`MeldError::Build`] when the flat arena cannot be assembled.
///
/// # Adequacy
/// - hypothesis: L3 — the corpus sources (zero obligations), arbitrary byte
///   soup (totality), incomplete input (statement-local obligations), and
///   losslessness each exercise a distinct property.
/// - witness: `parse::tests::corpus_parses_totally`
/// - witness: `parse::tests::parse_is_lossless_and_hash_stable`
/// - witness: `parse::tests::arbitrary_source_parses_totally`
#[inline]
pub fn parse<'source>(
    pbg: &Pbg,
    source: SourceText<'source>,
) -> Result<ParseResult<'source>, MeldError>
{
    let mut molder = Molder::new(pbg);
    let mut state = MeldState::new(pbg);
    let tokens = label(SourceFragment::from(<&str>::from(source)));
    molder.mold_stream(&mut state, &tokens, source);
    // `commit_with_obligations` captures the completion's repairs (force-close
    // and missing-operand obligations flagged while closing the input), which a
    // bare `commit` would drop.
    let (tree, mut obligations) = state.commit_with_obligations(source)?;
    // Severity-ordered (highest first) then by span, so consumers render the
    // most serious repair first.
    obligations.sort_by(|left, right| {
        right
            .class
            .cmp(&left.class)
            .then_with(|| left.span.start().cmp(&right.span.start()))
            .then_with(|| left.span.end().cmp(&right.span.end()))
    });
    Ok(ParseResult { tree, obligations })
}

#[cfg(test)]
mod tests
{
    use alloc::borrow::ToOwned as _;
    use alloc::boxed::Box;
    use alloc::string::String;
    use alloc::vec;
    use alloc::vec::Vec;
    use core::error::Error;
    use core::fmt;
    use std::path::Path;
    use std::path::PathBuf;

    use gandr_surface_grammar::Pbg;
    use gandr_surface_grammar::built_in;
    use gandr_surface_syntax::SourceText;
    use proptest::prelude::*;

    use super::parse;
    use crate::testing::reconstruct;
    use crate::testing::root_digest;

    /// File-read failure with the example path preserved.
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
        /// trivial.
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
    fn corpus_parses_totally() -> Result<(), Box<dyn Error>>
    {
        // Every corpus source parses totally — no panic, a well-formed tree
        // recording the grammar fingerprint, and its leaves reconstruct the
        // source. The stronger zero-obligation gate is
        // `acceptance::corpus_molds_to_zero_obligations`; this is the floor.
        let pbg = built_in()?;
        let files = gandr_files(&corpus_root());
        assert!(!files.is_empty(), "the corpus sources are present");

        for path in &files {
            let src = read_source(path)?;
            let result = parse(&pbg, SourceText::from(src.as_str()))?;
            assert_eq!(result.tree().grammar(), pbg.fingerprint());
            assert_eq!(
                reconstruct(result.tree()),
                src,
                "{:?} reconstructs losslessly",
                path.file_name()
            );
        }
        Ok(())
    }

    /// Every `.gandr` file under `dir`, sorted.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a walk of `dir` and its subdirectories, unreadable entries
    ///   skipped, the paths sorted so a run is deterministic.
    /// - panics: none.
    fn gandr_files(dir: &Path) -> Vec<PathBuf>
    {
        let mut out = Vec::new();
        let mut pending = vec![dir.to_path_buf()];
        while let Some(next_dir) = pending.pop() {
            if let Ok(entries) = std::fs::read_dir(next_dir) {
                for entry in entries.flatten() {
                    let path = entry.path();
                    if path.is_dir() {
                        pending.push(path);
                    }
                    else if path.extension().is_some_and(|ext| ext == "gandr") {
                        out.push(path);
                    }
                }
            }
        }
        out.sort();
        out
    }

    /// The language's source corpus, which the corpus crate owns.
    ///
    /// # Specification
    /// trivial.
    fn corpus_root() -> PathBuf
    {
        Path::new(env!("CARGO_MANIFEST_DIR")).join("../surface-corpus")
    }

    /// Read a source file while retaining path context in the error.
    ///
    /// # Specification
    /// # Errors
    /// The read failure, carrying `path`.
    fn read_source(path: &Path) -> Result<String, ReadSourceError>
    {
        std::fs::read_to_string(path).map_err(|source| ReadSourceError {
            path: path.to_path_buf(),
            source,
        })
    }

    #[test]
    fn parse_is_lossless_and_hash_stable() -> Result<(), Box<dyn Error>>
    {
        // Losslessness: the committed tree's tile and layout leaves
        // reconstruct the exact source, including interleaved comments.
        let pbg = built_in()?;
        let src = r#"// a comment
def greeting = "hi";

ret greeting
"#;
        let result = parse(&pbg, SourceText::from(src))?;
        assert_eq!(
            reconstruct(result.tree()),
            src,
            "the committed tree reconstructs the source"
        );

        // Determinism: a second parse digests identically.
        let again = parse(&pbg, SourceText::from(src))?;
        assert_eq!(root_digest(result.tree()), root_digest(again.tree()));
        Ok(())
    }

    #[test]
    fn declaration_prefix_round_trips_and_snapshots_model_state() -> Result<(), Box<dyn Error>>
    {
        let pbg = built_in()?;
        let src = r#"def nth @[A : Type, i : Fin(length(xs))] (xs : List(A)) -> A {
  ret xs
}
"#;
        let result = parse(&pbg, SourceText::from(src))?;
        assert!(
            result.obligations().is_empty(),
            "the declaration prefix needs no completion: {:?}",
            result.obligations()
        );
        assert_eq!(
            result.tree().grammar(),
            pbg.fingerprint(),
            "the tree records the grammar that produced it"
        );
        assert_eq!(
            reconstruct(result.tree()),
            src,
            "the tree round-trips the raw multiline source"
        );

        let again = parse(&pbg, SourceText::from(src))?;
        assert_eq!(
            root_digest(result.tree()),
            root_digest(again.tree()),
            "the declaration-prefix parse is deterministic"
        );
        Ok(())
    }

    /// A biased strategy: byte soup, fragment mutations, and truncations.
    ///
    /// # Specification
    /// trivial.
    fn hostile_source() -> impl Strategy<Value = String>
    {
        // A pool of gandr fragments to mutate and truncate.
        let fragments = vec![
            "def x = 1;",
            "fn(a) { ret a }",
            "case v { Inl(x) => x, Inr(y) => y }",
            "if c { ret 1 } else { ret 2 }",
            "#{ a = 1, b = \"s\" }",
            "[1, 2, 3] ++ [4]",
            "#!{ echo hi; }",
            "@[doc(\"d\")] def y = 2;",
        ];
        prop_oneof![
            // Byte soup.
            prop::collection::vec(any::<u8>(), 0 .. 64)
                .prop_map(|bytes| String::from_utf8_lossy(&bytes).into_owned()),
            // A fragment, possibly truncated.
            (prop::sample::select(fragments), 0_usize .. 40).prop_map(|(frag, cut)| {
                let end = cut.min(frag.len());
                frag.get(.. end).unwrap_or(frag).to_owned()
            }),
        ]
    }

    proptest! {
        #![proptest_config(ProptestConfig::with_cases(400))]

        #[test]
        fn arbitrary_source_parses_totally(src in hostile_source()) {
            use std::sync::OnceLock;
            static PBG: OnceLock<Pbg> = OnceLock::new();
            let pbg = PBG.get_or_init(|| built_in().expect("built-in grammar"));

            // Parse never panics and always yields a well-formed tree.
            let parse_result = parse(pbg, SourceText::from(src.as_str())).expect("commit is total");
            prop_assert_eq!(parse_result.tree().grammar(), pbg.fingerprint());

            // Losslessness holds over arbitrary input.
            prop_assert_eq!(reconstruct(parse_result.tree()), src);
        }
    }
}
