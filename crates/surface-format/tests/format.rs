//! The formatter through its public surface: the whole corpus kept and
//! formatted once at three page widths, and each layout rule pinned by a
//! golden at the narrow page (40 columns) and the wide page (100 columns).
//!
//! Regenerate the goldens with `UPDATE_EXPECT=1` and review the diff.

#[cfg(test)]
mod tests
{
    use std::path::Path;
    use std::path::PathBuf;

    use expect_test::expect_file;
    use gandr_surface_format::FormatOptions;
    use gandr_surface_format::Formatted;
    use gandr_surface_format::Layout;
    use gandr_surface_format::PageWidth;
    use gandr_surface_format::format;
    use gandr_surface_grammar::Pbg;
    use gandr_surface_grammar::built_in;
    use gandr_surface_parser::parse;
    use gandr_surface_syntax::SourceText;

    /// The narrow page.
    const NARROW: u32 = 40;

    /// The wide page.
    const WIDE: u32 = 100;

    /// The built-in grammar.
    ///
    /// # Specification
    /// trivial.
    fn grammar() -> Pbg
    {
        built_in().expect("the built-in grammar builds")
    }

    /// `source` formatted at a page of `width` columns.
    ///
    /// # Specification
    /// trivial.
    fn formatted<'text>(
        grammar: &Pbg,
        source: impl Into<SourceText<'text>>,
        width: impl Into<PageWidth>,
    ) -> Formatted
    {
        let parsed = parse(grammar, source.into()).expect("every source parses");
        format(grammar, &parsed, FormatOptions { page: width.into() }).expect("the source formats")
    }

    /// The text of `source` formatted at a page of `width` columns.
    ///
    /// # Specification
    /// trivial.
    fn text<'text>(
        grammar: &Pbg,
        source: impl Into<SourceText<'text>>,
        width: impl Into<PageWidth>,
    ) -> String
    {
        String::from(<&str>::from(formatted(grammar, source, width).text()))
    }

    /// Every `.gandr` file under `dir`, sorted.
    ///
    /// # Specification
    /// trivial.
    fn sources(dir: &Path) -> Vec<PathBuf>
    {
        let mut found = Vec::new();
        let mut pending = vec![dir.to_path_buf()];
        while let Some(next) = pending.pop() {
            for entry in std::fs::read_dir(next)
                .expect("the corpus is readable")
                .flatten()
            {
                let path = entry.path();
                if path.is_dir() {
                    pending.push(path);
                }
                else if path
                    .extension()
                    .is_some_and(|extension| extension == "gandr")
                {
                    found.push(path);
                }
            }
        }
        found.sort();
        found
    }

    /// The fixture `name`, and its goldens at both pages.
    ///
    /// # Specification
    /// trivial.
    fn golden(name: &Path)
    {
        let grammar = grammar();
        let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests");
        let source =
            std::fs::read_to_string(root.join("fixtures").join(name).with_extension("gandr"))
                .expect("the fixture is readable");
        for (width, page) in [(NARROW, "narrow"), (WIDE, "wide")] {
            let laid = text(&grammar, source.as_str(), width);
            assert_eq!(
                text(&grammar, laid.as_str(), width),
                laid,
                "{} formats once at {width}",
                name.display()
            );
            expect_file![
                root.join("golden")
                    .join(format!("{}.{page}.txt", name.display()))
            ]
            .assert_eq(&laid);
        }
    }

    #[test]
    fn every_source_keeps_its_meaning_and_formats_once()
    {
        let grammar = grammar();
        let corpus = Path::new(env!("CARGO_MANIFEST_DIR")).join("../surface-corpus");
        let paths = sources(&corpus);
        assert!(
            paths.len() > 100,
            "the whole corpus is read: {}",
            paths.len()
        );
        for path in paths {
            let source = std::fs::read_to_string(&path).expect("a corpus source is readable");
            for width in [NARROW, 80, WIDE] {
                // The formatter itself refuses a text whose digest, tokens
                // or comments differ from the source's.
                let once = text(&grammar, source.as_str(), width);
                assert_eq!(
                    text(&grammar, once.as_str(), width),
                    once,
                    "{} formats once at {width}",
                    path.display()
                );
            }
        }
    }

    #[test]
    fn a_long_declaration_breaks_its_parameters_before_its_type()
    {
        golden(Path::new("declarations"));
    }

    #[test]
    fn a_block_breaks_one_item_per_line_when_it_does_not_fit()
    {
        golden(Path::new("blocks"));
    }

    #[test]
    fn attributes_and_documentation_keep_their_lines()
    {
        golden(Path::new("attributes"));
    }

    #[test]
    fn the_arity_shaped_formers_keep_their_written_spelling()
    {
        golden(Path::new("arity"));
    }

    #[test]
    fn top_level_forms_and_comments_keep_their_lines()
    {
        let grammar = grammar();
        let source = "#!/usr/bin/env gandr\n\n\n// leading\ndef a = 1 ; def b = 2 ; // trailing\n\n\n\n/* own */\nf(a)   ;\ng(b);";
        assert_eq!(
            text(&grammar, source, WIDE),
            "#!/usr/bin/env gandr\n\n// leading\ndef a = 1 ;\ndef b = 2 ; // trailing\n\n/* own */\nf(a) ;\ng(b);\n",
            "forms take a line each, a trailing comment stays, a blank line is kept once, and a statement keeps its separator"
        );
        assert_eq!(text(&grammar, "", WIDE), "", "an empty source stays empty");
    }

    #[test]
    fn a_continuation_line_indents_under_its_statement()
    {
        let grammar = grammar();
        let source = "def f(x : Integer) -> -F Integer {\nrun y <- inc(x)\n      ;\n         run z <- inc(y);\n  return z\n}\n";
        assert_eq!(
            text(&grammar, source, WIDE),
            "def f(x : Integer) -> -F Integer {\n  run y <- inc(x)\n    ;\n  run z <- inc(y);\n  return z\n}\n",
            "a line indented past its statement continues it; one after a separator starts a statement"
        );
    }

    #[test]
    fn strings_shell_blocks_and_holes_are_copied_as_written()
    {
        let grammar = grammar();
        let source = "def s = \"a  ${  b }\tc\" ;\ndef h = #!{\n    printf 'hi'\n} ;\ndef k = (  ?hole  ) ;\n";
        assert_eq!(
            text(&grammar, source, NARROW),
            "def s = \"a  ${  b }\tc\" ;\ndef h = #!{\n    printf 'hi'\n} ;\ndef k = ( ?hole ) ;\n",
            "a string's, a shell block's and a hole's bytes are their own"
        );
    }

    #[test]
    fn a_repaired_form_is_copied_as_written()
    {
        let grammar = grammar();
        let source = "def   a = (1 ;\ndef   b = 2 ;\n";
        let formatted = formatted(&grammar, source, WIDE);
        assert_eq!(
            <&str>::from(formatted.text()),
            "def   a = (1 ;\ndef b = 2 ;\n",
            "the repaired form keeps its bytes and its neighbour is laid out"
        );
        let layouts: Vec<Layout> = formatted
            .pieces()
            .iter()
            .map(|piece| piece.layout)
            .collect();
        assert_eq!(layouts, [Layout::Repaired, Layout::Formatted]);
    }

    #[test]
    fn the_source_line_ending_is_kept()
    {
        let grammar = grammar();
        let source = "def f() -> -F Integer {\r\n\r\n  return 1\r\n}\r\n";
        assert_eq!(
            text(&grammar, source, NARROW),
            "def f() -> -F Integer {\r\n  return 1\r\n}\r\n",
            "carriage returns stay with their line feeds"
        );
    }

    #[test]
    fn pieces_place_each_top_level_form()
    {
        let grammar = grammar();
        let source = "def  a = 1 ;  // note\ndef b = 2 ;\n";
        let formatted = formatted(&grammar, source, WIDE);
        let text = <&str>::from(formatted.text());
        let spans: Vec<(&str, &str)> = formatted
            .pieces()
            .iter()
            .map(|piece| {
                let source_span =
                    usize::from(piece.source.start()) .. usize::from(piece.source.end());
                let formatted_span =
                    usize::from(piece.formatted.start()) .. usize::from(piece.formatted.end());
                (
                    source.get(source_span).unwrap_or_default(),
                    text.get(formatted_span).unwrap_or_default(),
                )
            })
            .collect();
        assert_eq!(
            spans,
            [
                ("def  a = 1 ;  // note", "def a = 1 ; // note"),
                ("def b = 2 ;", "def b = 2 ;")
            ],
            "a form's piece runs from its first token to its trailing comment"
        );
    }
}
