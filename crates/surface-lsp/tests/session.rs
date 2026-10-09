//! Whole sessions over in-memory streams, and the corpus read through them.
//!
//! Each case writes its client frames into one buffer, serves it, and reads
//! back every frame the server wrote. The corpus cases hold the server to the
//! pipeline's own faces: every report the dispatcher's walk renders for a
//! corpus source is published where the walk renders it, and every token
//! covers exactly the bytes the grammar's highlighter classifies.

extern crate alloc;

/// The cases, in a `cfg(test)` module so the crate's lint wall reads them as
/// test code rather than as shipping code.
#[cfg(test)]
mod session
{
    use alloc::collections::BTreeMap;
    use std::path::Path;
    use std::path::PathBuf;

    use gandr_surface_diagnostics::Entry;
    use gandr_surface_diagnostics::Report;
    use gandr_surface_diagnostics::entries;
    use gandr_surface_dispatcher::Goals;
    use gandr_surface_dispatcher::Step;
    use gandr_surface_dispatcher::Verb;
    use gandr_surface_dispatcher::Walk;
    use gandr_surface_grammar::RoleTable;
    use gandr_surface_grammar::built_in;
    use gandr_surface_lsp::Body;
    use gandr_surface_lsp::Capabilities;
    use gandr_surface_lsp::Served;
    use gandr_surface_lsp::TransportFault;
    use gandr_surface_lsp::read_frame;
    use gandr_surface_lsp::serve;
    use gandr_surface_lsp::write_frame;
    use gandr_surface_render_remote::ByteOffset;
    use gandr_surface_render_remote::HlRole;
    use gandr_surface_render_remote::LineIndex;
    use gandr_surface_render_remote::PositionRow;
    use gandr_surface_render_remote::Utf16Column;
    use gandr_surface_render_remote::Utf16Pos;
    use percent_encoding::AsciiSet;
    use percent_encoding::NON_ALPHANUMERIC;
    use percent_encoding::utf8_percent_encode;
    use quenchant_shape::shape::Maybe;
    use serde_json::Value;
    use serde_json::json;

    /// The bytes a `file` URI's path keeps unescaped: RFC 3986's unreserved
    /// characters and the separator.
    const PATH: &AsciiSet = &NON_ALPHANUMERIC
        .remove(b'-')
        .remove(b'.')
        .remove(b'_')
        .remove(b'~')
        .remove(b'/');

    /// A fresh scratch directory, removed when dropped.
    #[repr(transparent)]
    struct Scratch(PathBuf);

    impl Scratch
    {
        /// An empty directory named for `test` and this process.
        ///
        /// # Specification
        /// trivial.
        fn new(test: &Path) -> Self
        {
            let root = std::env::temp_dir().join(format!(
                "gandr-lsp-{}-{}",
                test.display(),
                std::process::id()
            ));
            if root.exists() {
                std::fs::remove_dir_all(&root).expect("a stale scratch directory is removed");
            }
            std::fs::create_dir_all(&root).expect("the scratch directory is created");
            Self(root)
        }
    }

    impl Drop for Scratch
    {
        /// Remove the directory and everything under it.
        ///
        /// # Specification
        /// trivial.
        fn drop(&mut self)
        {
            let removed = std::fs::remove_dir_all(&self.0);
            assert!(removed.is_ok(), "the scratch directory is removed");
        }
    }

    /// One corpus source as a client opens it.
    struct Source
    {
        /// Its `file` URI.
        uri: String,
        /// Its text.
        text: String,
    }

    /// The `file` URI of `path`, escaped as a client escapes it.
    ///
    /// # Specification
    /// trivial.
    fn uri(path: &Path) -> String
    {
        let path = path.to_str().expect("a test path is UTF-8");
        format!("file://{}", utf8_percent_encode(path, PATH))
    }

    /// One input stream carrying `messages` as frames, in order.
    ///
    /// # Specification
    /// trivial.
    fn frames(messages: &[Value]) -> Body
    {
        let mut input = Vec::new();
        for message in messages {
            let body = Body::from(serde_json::to_vec(message).expect("a test message encodes"));
            write_frame(&mut input, &body).expect("a vector takes every write");
        }
        Body::from(input)
    }

    /// Every frame in `output`, each as JSON.
    ///
    /// # Specification
    /// trivial.
    fn written(output: &Body) -> Vec<Value>
    {
        let mut stream = output.as_ref();
        let mut messages = Vec::new();
        while let Maybe::Present(body) = read_frame(&mut stream).expect("the server writes frames")
        {
            messages.push(serde_json::from_slice(body.as_ref()).expect("each frame is JSON"));
        }
        messages
    }

    /// Serve `messages` to the end and return how the session ended and what
    /// the server wrote.
    ///
    /// # Specification
    /// trivial.
    fn session(messages: &[Value]) -> (Served, Vec<Value>)
    {
        let input = frames(messages);
        let mut stream = input.as_ref();
        let mut output = Vec::new();
        let served = serve(&mut stream, &mut output).expect("the streams carry the session");
        (served, written(&Body::from(output)))
    }

    /// The messages opening a session.
    ///
    /// # Specification
    /// trivial.
    fn opening() -> Vec<Value>
    {
        vec![
            json!({"jsonrpc": "2.0", "id": 0_i32, "method": "initialize", "params": {"capabilities": {}}}),
            json!({"jsonrpc": "2.0", "method": "initialized", "params": {}}),
        ]
    }

    /// The messages closing a session.
    ///
    /// # Specification
    /// trivial.
    fn closing() -> [Value; 2]
    {
        [
            json!({"jsonrpc": "2.0", "id": "end", "method": "shutdown"}),
            json!({"jsonrpc": "2.0", "method": "exit"}),
        ]
    }

    /// The `didOpen` notification of `source`.
    ///
    /// # Specification
    /// trivial.
    fn open(source: &Source) -> Value
    {
        json!({"jsonrpc": "2.0", "method": "textDocument/didOpen", "params": {"textDocument": {
            "uri": source.uri, "languageId": "gandr", "version": 1_i32, "text": source.text,
        }}})
    }

    /// The position `byte` projects to in the text `index` was built from,
    /// as the wire carries it.
    ///
    /// # Specification
    /// trivial.
    fn position(
        index: &LineIndex<'_>,
        byte: gandr_surface_syntax::ByteOffset,
    ) -> Value
    {
        let pos = index
            .utf16_pos_of_byte(ByteOffset::from(usize::from(byte)))
            .expect("a renderer span lies on character boundaries");
        json!({"line": usize::from(pos.row), "character": usize::from(pos.col)})
    }

    /// The range, code and message a renderer report reads as, each projected
    /// independently of the server: the wire's own view of `report`.
    ///
    /// # Specification
    /// trivial.
    fn rendered(
        report: &Report<'_>,
        index: &LineIndex<'_>,
    ) -> Value
    {
        let origin = json!({"line": 0_i32, "character": 0_i32});
        let range = match report.span() {
            | Maybe::Present(span) => {
                json!({"start": position(index, span.start()), "end": position(index, span.end())})
            },
            | Maybe::Absent(_) => json!({"start": origin, "end": origin}),
        };
        let code = match report.identifier() {
            | Maybe::Present(spelling) => json!(spelling.to_string()),
            | Maybe::Absent(_) => Value::Null,
        };
        json!({"range": range, "code": code, "message": report.title().to_string()})
    }

    /// The range, code and message of each diagnostic a publication carries.
    ///
    /// # Specification
    /// trivial.
    fn published(publication: &Value) -> Vec<Value>
    {
        publication
            .pointer("/params/diagnostics")
            .and_then(Value::as_array)
            .expect("a publication carries diagnostics")
            .iter()
            .map(|diagnostic| {
                json!({
                    "range": diagnostic["range"],
                    "code": diagnostic.get("code").cloned().unwrap_or(Value::Null),
                    "message": diagnostic["message"],
                })
            })
            .collect()
    }

    /// The corpus root, canonical so its paths classify as the walk's do.
    ///
    /// # Specification
    /// trivial.
    fn corpus() -> PathBuf
    {
        Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../surface-corpus")
            .canonicalize()
            .expect("the corpus is checked out beside this crate")
    }

    /// Every `.gandr` source under the corpus's strict and fixture roots, in
    /// path order.
    ///
    /// # Specification
    /// trivial.
    fn corpus_sources() -> Vec<Source>
    {
        let root = corpus();
        let mut pending = vec![root.join("strict"), root.join("fixture")];
        let mut paths = Vec::new();
        while let Some(directory) = pending.pop() {
            for entry in std::fs::read_dir(&directory).expect("a corpus directory lists") {
                let path = entry.expect("a corpus entry reads").path();
                if path.is_dir() {
                    pending.push(path);
                }
                else if path
                    .extension()
                    .is_some_and(|extension| extension == "gandr")
                {
                    paths.push(path);
                }
            }
        }
        paths.sort();
        paths
            .into_iter()
            .map(|path| Source {
                uri: uri(&path),
                text: std::fs::read_to_string(&path).expect("a corpus source reads"),
            })
            .collect()
    }

    #[test]
    fn a_session_round_trips_over_in_memory_streams()
    {
        let source = Source {
            uri: "file:///tmp/round-trip.gandr".to_owned(),
            text: "def answer = 42 ;\ndef broken = missing ;\n".to_owned(),
        };
        let mut messages = opening();
        messages.push(open(&source));
        messages.push(json!({
            "jsonrpc": "2.0", "id": 1_i32, "method": "textDocument/semanticTokens/full",
            "params": {"textDocument": {"uri": source.uri}},
        }));
        messages.extend(closing());
        let (served, written) = session(&messages);
        assert_eq!(
            served,
            Served::Clean,
            "exit after shutdown ends the session cleanly"
        );
        let capabilities: Value =
            serde_json::from_str(&Capabilities.to_string()).expect("the capabilities are JSON");
        assert_eq!(
            written,
            vec![
                json!({"jsonrpc": "2.0", "id": 0_i32, "result": capabilities}),
                json!({
                    "jsonrpc": "2.0",
                    "method": "textDocument/publishDiagnostics",
                    "params": {
                        "uri": source.uri,
                        "version": 1_i32,
                        "diagnostics": [{
                            "range": {
                                "start": {"line": 1_i32, "character": 13_i32},
                                "end": {"line": 1_i32, "character": 20_i32},
                            },
                            "severity": 1_i32,
                            "code": "UnresolvedName",
                            "source": "gandr",
                            "message": "no declaration or binder answers `missing` at 31..38",
                        }],
                    },
                }),
                json!({
                    "jsonrpc": "2.0",
                    "id": 1_i32,
                    "result": {"data": [
                        0_u32, 0_u32, 3_u32, 0_u32, 0_u32, 0_u32, 4_u32, 6_u32, 2_u32, 1_u32,
                        0_u32, 9_u32, 2_u32, 9_u32, 0_u32, 1_u32, 0_u32, 3_u32, 0_u32, 0_u32,
                        0_u32, 4_u32, 6_u32, 2_u32, 1_u32, 0_u32, 9_u32, 7_u32, 3_u32, 0_u32,
                    ]},
                }),
                json!({"jsonrpc": "2.0", "id": "end", "result": null}),
            ],
            "every answer and the publication, in order, each frame whole"
        );
    }

    #[test]
    fn a_stream_closed_without_exit_ends_abruptly()
    {
        let (served, written) = session(&opening());
        assert_eq!(
            served,
            Served::Abrupt,
            "a stream closed before shutdown is abrupt"
        );
        assert_eq!(written.len(), 1_usize, "initialize alone was answered");

        let mut shutdown = opening();
        shutdown.push(closing()[0].clone());
        let (served, _) = session(&shutdown);
        assert_eq!(
            served,
            Served::Clean,
            "a stream closed after shutdown is clean"
        );

        let mut cut: &[u8] = b"Content-Length: 40\r\n\r\n{\"jsonrpc\"";
        let mut output = Vec::new();
        assert!(
            matches!(serve(&mut cut, &mut output), Err(TransportFault::Truncated)),
            "a stream breaking inside a frame is a transport fault"
        );
    }

    #[test]
    fn a_refusal_is_published_where_the_renderer_renders_it()
    {
        let scratch = Scratch::new(Path::new("refusal"));
        let path = scratch.0.join("broken.gandr");
        let text = "def answer = 42 ;\ndef broken = missing ;\n";
        std::fs::write(&path, text).expect("the source is written");

        let mut walk = Walk::new(vec![path.clone()]);
        let Maybe::Present(step) = walk.step()
        else {
            panic!("the walk reaches the source");
        };
        let renderings = entries(&step, Verb::Check(Goals::Reported))
            .map(|entry| match entry {
                | Entry::Report(report) => report
                    .render(gandr_surface_diagnostics::RenderStyle::Plain)
                    .to_string(),
                | Entry::Line(line) => line.to_string(),
            })
            .collect::<Vec<_>>();
        assert_eq!(renderings.len(), 1_usize, "one refusal, one rendering");
        let rendering = &renderings[0];
        let heading = rendering
            .lines()
            .next()
            .expect("a rendering has a first line");
        let code = heading
            .strip_prefix("error[")
            .and_then(|rest| rest.split_once(']'))
            .map(|(code, _)| code)
            .expect("a refusal's heading names its code");
        let located = rendering
            .lines()
            .find_map(|line| line.split_once(&format!("{}:", path.display())))
            .map(|(_, at)| at.trim().to_owned())
            .expect("a located report names its line and column");
        let (line, column) = located.split_once(':').expect("line:column");
        let line: u64 = line.parse().expect("a line number");
        let column: u64 = column.parse().expect("a column number");

        let source = Source {
            uri: uri(&path),
            text: text.to_owned(),
        };
        let mut messages = opening();
        messages.push(open(&source));
        messages.extend(closing());
        let (_, written) = session(&messages);
        let diagnostics = written[1]
            .pointer("/params/diagnostics")
            .and_then(Value::as_array)
            .expect("the opening publishes diagnostics");
        assert_eq!(diagnostics.len(), 1_usize, "one refusal, one diagnostic");
        assert_eq!(
            diagnostics[0]["code"],
            json!(code),
            "the diagnostic's code is the rendering's identifier"
        );
        assert_eq!(
            diagnostics[0]["range"]["start"],
            json!({"line": line - 1, "character": column - 1}),
            "the diagnostic starts at the rendering's one-based line and column"
        );
        assert_eq!(
            diagnostics[0]["range"]["end"],
            json!({"line": line - 1, "character": column - 1 + 7}),
            "and ends after the refused name"
        );
    }

    #[test]
    fn every_corpus_report_is_published_where_the_walk_renders_it()
    {
        let root = corpus();
        let mut walk = Walk::new(vec![root.join("strict"), root.join("fixture")]);
        let mut expected = BTreeMap::new();
        let mut sources = Vec::new();
        while let Maybe::Present(step) = walk.step() {
            let Step::Source { path, text, .. } = step
            else {
                panic!("every corpus path is carried through the pipeline");
            };
            let index = LineIndex::new(text.as_ref().into());
            let reports = entries(&step, Verb::Check(Goals::Reported))
                .map(|entry| match entry {
                    | Entry::Report(report) => rendered(&report, &index),
                    | Entry::Line(line) => json!({
                        "range": {
                            "start": {"line": 0_i32, "character": 0_i32},
                            "end": {"line": 0_i32, "character": 0_i32},
                        },
                        "code": null,
                        "message": line.to_string(),
                    }),
                })
                .collect::<Vec<_>>();
            let source = Source {
                uri: uri(path),
                text: text.as_ref().to_owned(),
            };
            let _prior = expected.insert(source.uri.clone(), reports);
            sources.push(source);
        }
        assert!(
            sources.len() > 100_usize,
            "the corpus is walked whole: {} sources",
            sources.len()
        );
        let mut messages = opening();
        messages.extend(sources.iter().map(open));
        messages.extend(closing());
        let (served, written) = session(&messages);
        assert_eq!(served, Served::Clean, "the session ends cleanly");
        let mut publications = BTreeMap::new();
        for message in &written {
            if let Some(uri) = message.pointer("/params/uri").and_then(Value::as_str) {
                let _prior = publications.insert(uri.to_owned(), published(message));
            }
        }
        assert_eq!(
            publications, expected,
            "each source publishes the walk's reports, at the walk's spans and codes"
        );
    }

    #[test]
    fn corpus_tokens_cover_the_highlighted_bytes()
    {
        let grammar = built_in().expect("the built-in grammar builds");
        let roles = RoleTable::build(&grammar).expect("the role table builds");
        let sources = corpus_sources();
        let mut messages = opening();
        for (id, source) in sources.iter().enumerate() {
            messages.push(open(source));
            messages.push(json!({
                "jsonrpc": "2.0", "id": id, "method": "textDocument/semanticTokens/full",
                "params": {"textDocument": {"uri": source.uri}},
            }));
        }
        messages.extend(closing());
        let (_, written) = session(&messages);
        let streams = written
            .iter()
            .filter_map(|message| {
                let id = message.get("id").and_then(Value::as_u64)?;
                let data = message.pointer("/result/data").and_then(Value::as_array)?;
                Some((
                    id,
                    data.iter()
                        .map(|integer| integer.as_u64().expect("an integer"))
                        .collect::<Vec<_>>(),
                ))
            })
            .collect::<BTreeMap<_, _>>();
        for (id, source) in sources.iter().enumerate() {
            let text = source.text.as_str();
            let tree = gandr_surface_parser::parse(&grammar, text.into())
                .expect("a corpus source parses")
                .into_tree();
            let spans = roles.highlight(&tree).expect("a corpus source highlights");
            let mut expected = Vec::new();
            for span in spans.iter().filter(|span| span.role != HlRole::Other) {
                let (start, end) = (
                    usize::from(span.range.start()),
                    usize::from(span.range.end()),
                );
                let mut piece = start;
                let covered = text
                    .get(start .. end)
                    .expect("a span lies on character boundaries");
                for (offset, character) in covered.char_indices() {
                    if character == '\n' || character == '\r' {
                        if piece < start + offset {
                            expected.push((piece, start + offset));
                        }
                        piece = start + offset + 1;
                    }
                }
                if piece < end {
                    expected.push((piece, end));
                }
            }
            let index = LineIndex::new(text.into());
            let byte = |row: u64, col: u64| {
                usize::from(index.byte_of_utf16_pos(Utf16Pos {
                    row: PositionRow::from(usize::try_from(row).expect("a row fits")),
                    col: Utf16Column::from(usize::try_from(col).expect("a column fits")),
                }))
            };
            let stream = &streams[&u64::try_from(id).expect("an id fits")];
            assert_eq!(stream.len() % 5, 0_usize, "five integers per token");
            let (mut row, mut col) = (0_u64, 0_u64);
            let mut decoded = Vec::new();
            for token in stream.chunks_exact(5) {
                let &[line_delta, start_delta, length, _, _] = token
                else {
                    panic!("a chunk of five holds five integers");
                };
                if line_delta == 0 {
                    col += start_delta;
                }
                else {
                    row += line_delta;
                    col = start_delta;
                }
                decoded.push((byte(row, col), byte(row, col + length)));
            }
            assert_eq!(
                decoded, expected,
                "{}: the tokens cover exactly the highlighted bytes, line by line",
                source.uri
            );
        }
    }
}
