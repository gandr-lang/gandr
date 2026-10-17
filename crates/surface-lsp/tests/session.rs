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

    use anodized::spec;
    use gandr_surface_diagnostics::AnnotationKind;
    use gandr_surface_diagnostics::Diagnostic;
    use gandr_surface_diagnostics::Severity;
    use gandr_surface_dispatcher::Goals;
    use gandr_surface_dispatcher::Step;
    use gandr_surface_dispatcher::Verb;
    use gandr_surface_dispatcher::Walk;
    use gandr_surface_dispatcher::entries;
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
        /// - requires: test is one normal path component, unique among active
        ///   tests. The temporary directory is writable and no other actor owns
        ///   this path.
        /// - ensures: the owned directory exists and is empty, replacing stale
        ///   content.
        /// - provides: an isolated source root for a protocol/renderer
        ///   comparison.
        /// - fails: never when filesystem operations succeed.
        /// - panics: a stale directory cannot be removed or a new one cannot be
        ///   created.
        ///
        /// # Adequacy
        /// - hypothesis: L3 — the refusal session creates and writes its
        ///   isolated source; instrumented postconditions observe the directory
        ///   and emptiness, distinguishing skipped creation or retained stale
        ///   contents.
        /// - witness: `session::session::a_refusal_is_published_where_the_model_locates_it`
        #[spec(requires: test.components().count() == 1
            && matches!(test.components().next(), Some(std::path::Component::Normal(_))),
            ensures: |ret| ret.0.is_dir() && std::fs::read_dir(&ret.0).is_ok_and(|mut entries| entries.next().is_none()))]
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
        /// - requires: the directory remains exclusively owned and present.
        /// - ensures: the owned directory and its children no longer exist.
        /// - provides: cleanup after the filesystem-backed session.
        /// - fails: never when removal succeeds.
        /// - panics: the filesystem refuses removal.
        ///
        /// # Adequacy
        /// - hypothesis: L3 — the refusal session drops a root containing its
        ///   source; the instrumented absence check detects skipped or
        ///   incomplete removal.
        /// - witness: `session::session::a_refusal_is_published_where_the_model_locates_it`
        #[spec(requires: self.0.is_dir(), ensures: !self.0.exists())]
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
    /// - requires: path is absolute UTF-8.
    /// - ensures: a file URI decodes to the exact path bytes, escaping
    ///   characters outside RFC 3986 unreserved characters and the path
    ///   separator.
    /// - provides: client-spelled document identifiers for fixtures.
    /// - fails: never in the valid domain.
    /// - panics: a non-UTF-8 path violates the requirement.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — a path containing a space and non-ASCII character has
    ///   a pinned URI; corpus sessions link each published URI to its source.
    /// - witness: `session::session::wire_helpers_preserve_escaped_paths_and_unicode_payloads`
    /// - witness: `session::session::every_corpus_diagnostic_is_published_as_the_model_builds_it`
    #[spec(requires: path.is_absolute() && path.to_str().is_some(),
        ensures: |ret| ret.strip_prefix("file://").is_some_and(|encoded|
            percent_encoding::percent_decode_str(encoded).eq(path.as_os_str().as_encoded_bytes().iter().copied())))]
    fn uri(path: &Path) -> String
    {
        let path = path.to_str().expect("a test path is UTF-8");
        format!("file://{}", utf8_percent_encode(path, PATH))
    }

    /// One input stream carrying `messages` as frames, in order.
    ///
    /// # Specification
    /// - requires: every JSON value is serializable and fits the reader
    ///   ceiling.
    /// - ensures: one compact JSON frame per input value, in input order.
    /// - provides: the session input byte stream.
    /// - fails: never for serializable values and the vector writer.
    /// - panics: a message cannot encode or its vector write fails.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — a pinned two-frame UTF-8/nullable stream
    ///   distinguishes wrong byte lengths, missing frames and reordered values;
    ///   full sessions observe each protocol response and publication.
    /// - witness: `session::session::wire_helpers_preserve_escaped_paths_and_unicode_payloads`
    /// - witness: `session::session::a_session_round_trips_over_in_memory_streams`
    #[spec(ensures: |ret| ret.as_ref().windows(4)
        .filter(|window| *window == b"\r\n\r\n").count() == messages.len())]
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
    /// - requires: output contains complete frames with compact JSON bodies.
    /// - ensures: all frame values are decoded in order.
    /// - provides: a semantic observation independent of frame boundaries.
    /// - fails: never in the valid domain.
    /// - panics: framing or JSON decoding rejects the stream.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — a pinned Unicode and null stream distinguishes
    ///   missing, reordered or truncated values; session goldens check protocol
    ///   meaning.
    /// - witness: `session::session::wire_helpers_preserve_escaped_paths_and_unicode_payloads`
    /// - witness: `session::session::a_session_round_trips_over_in_memory_streams`
    #[spec(ensures: |ret| ret.len() == output.as_ref().windows(4)
        .filter(|window| *window == b"\r\n\r\n").count())]
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

    /// Serve `messages` to the end and return how the session ended, what the
    /// server wrote, and the lines it logged.
    ///
    /// # Specification
    /// - requires: messages serialize into frames within the reader ceiling.
    /// - ensures: the session stops at exit or EOF, returning its lifecycle
    ///   ending, every emitted JSON-RPC message in order, and every log line in
    ///   order.
    /// - provides: an in-memory client observation of the public service loop.
    /// - fails: never for the admitted in-memory streams.
    /// - panics: transport or output decoding rejects a fixture stream.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an editor-shaped edit reads one log line per
    ///   synchronisation, at the versions it sent.
    /// - witness: `session::session::an_edit_to_a_large_document_rechecks_its_forms`
    #[spec(ensures: |ret| ret.1.len() <= messages.len() && ret.2.len() <= messages.len()
        && ret.1.iter().all(|message| message.get("jsonrpc").and_then(Value::as_str) == Some("2.0")))]
    fn logged(messages: &[Value]) -> (Served, Vec<Value>, Vec<String>)
    {
        let input = frames(messages);
        let mut stream = input.as_ref();
        let mut output = Vec::new();
        let mut log = Vec::new();
        let served =
            serve(&mut stream, &mut output, &mut log).expect("the streams carry the session");
        let log = String::from_utf8(log).expect("the log is UTF-8");
        (
            served,
            written(&Body::from(output)),
            log.lines().map(str::to_owned).collect(),
        )
    }

    /// Serve `messages` to the end and return how the session ended and what
    /// the server wrote.
    ///
    /// # Specification
    /// - requires: messages serialize into frames within the reader ceiling.
    /// - ensures: the session stops at exit or EOF, returning its lifecycle
    ///   ending and every emitted JSON-RPC message in order.
    /// - provides: an in-memory client observation of the public service loop.
    /// - fails: never for the admitted in-memory streams.
    /// - panics: transport or output decoding rejects a fixture stream.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — a full session has pinned responses and tokens. L3 —
    ///   EOF before/after shutdown and a truncated frame distinguish lifecycle
    ///   ending and lost transport faults.
    /// - witness: `session::session::a_session_round_trips_over_in_memory_streams`
    /// - witness: `session::session::a_stream_closed_without_exit_ends_abruptly`
    #[spec(ensures: |ret| ret.1.len() <= messages.len()
        && ret.1.iter().all(|message| message.get("jsonrpc").and_then(Value::as_str) == Some("2.0")))]
    fn session(messages: &[Value]) -> (Served, Vec<Value>)
    {
        let (served, written, _log) = logged(messages);
        (served, written)
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
    /// - requires: byte lies on a character boundary or beyond the source end.
    /// - ensures: the JSON line and character equal the renderer UTF-16
    ///   projection.
    /// - provides: a wire position independent of the LSP adapter.
    /// - fails: never in the valid domain.
    /// - panics: an interior character byte violates the requirement.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — every located corpus report agrees with the server;
    ///   L3 — the pinned refusal location distinguishes byte/UTF-16 coordinate
    ///   shifts.
    /// - witness: `session::session::every_corpus_diagnostic_is_published_as_the_model_builds_it`
    /// - witness: `session::session::a_refusal_is_published_where_the_model_locates_it`
    #[spec(
        requires: index.utf16_pos_of_byte(ByteOffset::from(usize::from(byte))).is_ok(),
        ensures: |ret| index.utf16_pos_of_byte(ByteOffset::from(usize::from(byte))).is_ok_and(|position|
            ret.get("line").and_then(Value::as_u64) == u64::try_from(usize::from(position.row)).ok()
                && ret.get("character").and_then(Value::as_u64) == u64::try_from(usize::from(position.col)).ok()),
    )]
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

    /// The range, code, message and related information a model diagnostic
    /// reads as, each projected independently of the server: the wire's own
    /// view of `diagnostic`.
    ///
    /// # Specification
    /// - requires: index describes the diagnostic's source; located spans
    ///   project.
    /// - ensures: the primary range, optional code, message (the message, then
    ///   the primary label, each unlocated context and the note on lines of
    ///   their own when present) and related ranges and labels — every context
    ///   annotation, then every located context — are represented in the
    ///   comparison object, in order; a ledger line is its line at the origin.
    /// - provides: an independent model-stage observation of editor
    ///   diagnostics.
    /// - fails: never for valid spans.
    /// - panics: a located span lies inside a character.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — every corpus diagnostic, including absent locations
    ///   and causal contexts, is compared against the actual wire publication;
    ///   exact ranges, codes and labels distinguish lost or misprojected
    ///   fields.
    /// - witness: `session::session::every_corpus_diagnostic_is_published_as_the_model_builds_it`
    #[spec(ensures: |ret|
        ret.get("code").is_some_and(|code| code.is_null() == matches!(diagnostic.identifier, Maybe::Absent(_)))
            && ret.get("message").is_some_and(Value::is_string)
            && ret.get("related").and_then(Value::as_array).is_some_and(|related|
                related.len() == diagnostic.annotations.iter().filter(|annotation| annotation.kind == AnnotationKind::Context).count()
                    .saturating_add(diagnostic.contexts.iter().filter(|context| matches!(context.locus, Maybe::Present(_))).count())))]
    fn rendered(
        diagnostic: &Diagnostic,
        index: &LineIndex<'_>,
    ) -> Value
    {
        let origin = json!({"line": 0_i32, "character": 0_i32});
        let at_origin = json!({"start": origin, "end": origin});
        if diagnostic.severity == Severity::Ledger {
            return json!({
                "range": at_origin,
                "code": null,
                "message": format!("{}: {}", diagnostic.path.display(), diagnostic.message.text),
                "related": [],
            });
        }
        let range = |span: gandr_surface_syntax::ByteSpan| json!({"start": position(index, span.start()), "end": position(index, span.end())});
        let code = match diagnostic.identifier {
            Maybe::Present(ref spelling) => json!(spelling.to_string()),
            Maybe::Absent(_) => Value::Null,
        };
        let mut related: Vec<_> = diagnostic
            .annotations
            .iter()
            .filter(|annotation| annotation.kind == AnnotationKind::Context)
            .map(|annotation| json!({"range": range(annotation.locus.span), "message": annotation.label}))
            .collect();
        let mut message = diagnostic.message.text.clone();
        let lead = match diagnostic.primary() {
            Maybe::Present(primary) => {
                message.push('\n');
                message.push_str(&primary.label);
                range(primary.locus.span)
            },
            Maybe::Absent(_) => at_origin,
        };
        for context in &diagnostic.contexts {
            match context.locus {
                Maybe::Present(locus) => {
                    related.push(json!({"range": range(locus.span), "message": context.label()}));
                },
                Maybe::Absent(_) => {
                    message.push('\n');
                    message.push_str(&context.note());
                },
            }
        }
        if let Maybe::Present(ref note) = diagnostic.note {
            message.push_str("\nnote: ");
            message.push_str(note);
        }
        json!({"range": lead, "code": code, "message": message, "related": related})
    }

    /// The range, code and message of each diagnostic a publication carries.
    ///
    /// # Specification
    /// - requires: publication carries a diagnostic array.
    /// - ensures: each diagnostic preserves its range, code, message and
    ///   related ranges/labels; an absent code is observed as null and absent
    ///   context as an empty array, without changing diagnostic or context
    ///   order.
    /// - provides: the wire projection compared with renderer-stage reports.
    /// - fails: never in the valid domain.
    /// - panics: the diagnostic array is missing.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — every corpus publication is compared with independent
    ///   renderer-stage observations, distinguishing dropped or reordered
    ///   diagnostics and missing codes, titles or causal labels.
    /// - witness: `session::session::every_corpus_diagnostic_is_published_as_the_model_builds_it`
    #[spec(requires: publication.pointer("/params/diagnostics").is_some_and(Value::is_array),
        ensures: |ret| publication.pointer("/params/diagnostics").and_then(Value::as_array).is_some_and(|diagnostics|
            ret.len() == diagnostics.len() && ret.iter().zip(diagnostics).all(|(projected, original)|
                projected.get("range") == original.get("range")
                    && projected.get("message") == original.get("message")
                    && projected.get("code") == Some(original.get("code").unwrap_or(&Value::Null))
                    && projected.get("related").and_then(Value::as_array).is_some_and(|related|
                        related.len() == original.get("relatedInformation").and_then(Value::as_array).map_or(0, Vec::len))))) ]
    fn published(publication: &Value) -> Vec<Value>
    {
        publication
            .pointer("/params/diagnostics")
            .and_then(Value::as_array)
            .expect("a publication carries diagnostics")
            .iter()
            .map(|diagnostic| {
                let related: Vec<_> = diagnostic.get("relatedInformation").and_then(Value::as_array)
                    .into_iter().flatten().map(|annotation| json!({
                        "range": annotation.pointer("/location/range"), "message": annotation.get("message"),
                    })).collect();
                json!({
                    "range": diagnostic["range"],
                    "code": diagnostic.get("code").cloned().unwrap_or(Value::Null),
                    "message": diagnostic["message"],
                    "related": related,
                })
            })
            .collect()
    }

    /// The corpus root, canonical so its paths classify as the walk's do.
    ///
    /// # Specification
    /// - requires: the neighboring corpus checkout is present and readable.
    /// - ensures: the returned root is an absolute directory with the corpus
    ///   name.
    /// - provides: a canonical filesystem root for independent corpus evidence.
    /// - fails: never when canonicalization succeeds.
    /// - panics: the expected corpus directory cannot be canonicalized.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — full corpus report/token comparisons read both strict
    ///   and fixture roots, distinguishing a wrong or unavailable corpus root.
    /// - witness: `session::session::every_corpus_diagnostic_is_published_as_the_model_builds_it`
    /// - witness: `session::session::sweeps::corpus_tokens_cover_the_highlighted_bytes`
    #[spec(ensures: |ret| ret.is_absolute() && ret.is_dir() && ret.ends_with("surface-corpus"))]
    fn corpus() -> PathBuf
    {
        Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../surface-corpus")
            .canonicalize()
            .expect("the corpus is checked out beside this crate")
    }

    /// `sources` as a client opens them: each one's URI and complete text, in
    /// the order given.
    ///
    /// # Specification
    /// - requires: each source is readable UTF-8 text at a UTF-8 path.
    /// - ensures: one source per one given, in order, with its URI and complete
    ///   source text.
    /// - provides: client inputs for the independent token-coverage comparison.
    /// - fails: never in the valid filesystem domain.
    /// - panics: a source cannot be read or a path is not UTF-8.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — source membership agrees with the independent
    ///   dispatcher walk; each source token stream covers its
    ///   grammar-classified bytes. Runtime checks distinguish URI shape.
    /// - witness: `session::session::sweeps::corpus_tokens_cover_the_highlighted_bytes`
    #[spec(ensures: |ret| ret.len() == sources.len()
        && ret.iter().all(|source| source.uri.starts_with("file://")
            && Path::new(&source.uri).extension().is_some_and(|extension| extension == "gandr")))]
    fn opened(sources: &[gandr_workflow_sweep::Source]) -> Vec<Source>
    {
        sources
            .iter()
            .map(|source| Source {
                uri: uri(&source.path),
                text: std::fs::read_to_string(&source.path).expect("a corpus source reads"),
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
        let (served, mut written) = session(&messages);
        written
            .get_mut(1)
            .and_then(|message| message.pointer_mut("/params/diagnostics/0"))
            .and_then(Value::as_object_mut)
            .expect("the refusal diagnostic")
            .remove("message");
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
            matches!(
                serve(&mut cut, &mut output, &mut Vec::new()),
                Err(TransportFault::Truncated)
            ),
            "a stream breaking inside a frame is a transport fault"
        );
    }

    /// A client's stream that, once its frames are read, stays open for a
    /// while before it closes, as an editor sits idle.
    struct Lingering
    {
        /// The frames, back to back.
        frames: Vec<u8>,
        /// How many bytes were read.
        read: usize,
        /// How long the stream stays open after its last frame.
        linger: core::time::Duration,
    }

    impl std::io::Read for Lingering
    {
        /// Copy what is left, as [`std::io::BufRead::fill_buf`] offers it.
        ///
        /// # Specification
        /// trivial.
        fn read(
            &mut self,
            buf: &mut [u8],
        ) -> std::io::Result<usize>
        {
            let copied = {
                let available = std::io::BufRead::fill_buf(self)?;
                let copied = available.len().min(buf.len());
                buf.get_mut(.. copied)
                    .expect("a copy fits its destination")
                    .copy_from_slice(available.get(.. copied).expect("a copy fits its source"));
                copied
            };
            std::io::BufRead::consume(self, copied);
            Ok(copied)
        }
    }

    impl std::io::BufRead for Lingering
    {
        /// What is left of the frames; once none is, wait out the linger
        /// once, then close.
        ///
        /// # Specification
        /// trivial.
        fn fill_buf(&mut self) -> std::io::Result<&[u8]>
        {
            if self.read == self.frames.len() && !self.linger.is_zero() {
                std::thread::sleep(self.linger);
                self.linger = core::time::Duration::ZERO;
            }
            Ok(self.frames.get(self.read ..).unwrap_or_default())
        }

        /// Mark `amount` bytes read.
        ///
        /// # Specification
        /// trivial.
        fn consume(
            &mut self,
            amount: usize,
        )
        {
            self.read = self.read.saturating_add(amount).min(self.frames.len());
        }
    }

    /// What a session writes when the client, its quiet interval the setting
    /// `quiet`, opens a document, types an unfinished declaration into it and
    /// then sits idle for a second: each message's `id`, and each
    /// publication's version and codes.
    ///
    /// # Specification
    /// trivial.
    fn idled(quiet: &Value) -> Vec<Value>
    {
        let uri = "file:///strict/idle.gandr";
        let messages = [
            json!({"jsonrpc": "2.0", "id": 0_i32, "method": "initialize", "params": {
                "capabilities": {}, "initializationOptions": {"diagnostics": {"quiet": quiet}},
            }}),
            json!({"jsonrpc": "2.0", "method": "initialized", "params": {}}),
            json!({"jsonrpc": "2.0", "method": "textDocument/didOpen", "params": {"textDocument": {
                "uri": uri, "languageId": "gandr", "version": 1_i32, "text": "def a = 1 ;\n",
            }}}),
            json!({"jsonrpc": "2.0", "method": "textDocument/didChange", "params": {
                "textDocument": {"uri": uri, "version": 2_i32},
                "contentChanges": [{
                    "range": {
                        "start": {"line": 1_i32, "character": 0_i32},
                        "end": {"line": 1_i32, "character": 0_i32},
                    },
                    "text": "def b =",
                }],
            }}),
        ];
        let mut input = Lingering {
            frames: frames(&messages).as_ref().to_vec(),
            read: 0_usize,
            linger: core::time::Duration::from_secs(1),
        };
        let mut output = Vec::new();
        let served =
            serve(&mut input, &mut output, &mut Vec::new()).expect("the streams carry the session");
        assert_eq!(served, Served::Abrupt, "the stream closes without shutdown");
        written(&Body::from(output))
            .iter()
            .map(|message| {
                message.get("method").map_or_else(
                    || json!(message.get("id")),
                    |method| {
                        json!([
                            method,
                            message.pointer("/params/version"),
                            message
                                .pointer("/params/diagnostics")
                                .and_then(Value::as_array)
                                .map(|diagnostics| diagnostics
                                    .iter()
                                    .map(|diagnostic| diagnostic.get("code"))
                                    .collect::<Vec<_>>()),
                        ])
                    },
                )
            })
            .collect()
    }

    #[test]
    fn a_held_diagnostic_publishes_once_the_document_is_quiet()
    {
        let publication = |version: i32, codes: &[&str]| {
            json!(["textDocument/publishDiagnostics", version, codes])
        };
        assert_eq!(
            idled(&json!(0.05_f64)),
            [
                json!(0_i32),
                publication(1_i32, &[]),
                publication(2_i32, &[]),
                publication(2_i32, &["MalformedForm"]),
            ],
            "the declaration under the caret is held at its change, and published once the \
             document is quiet, with no frame arriving"
        );
        assert_eq!(
            idled(&json!(0_i32)),
            [
                json!(0_i32),
                publication(1_i32, &[]),
                publication(2_i32, &["MalformedForm"]),
            ],
            "a zero interval publishes it with its change, and nothing after"
        );
    }

    #[test]
    fn a_refusal_is_published_where_the_model_locates_it()
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
        let found = entries(&step, Verb::Check(Goals::Reported)).collect::<Vec<_>>();
        assert_eq!(found.len(), 1_usize, "one refusal, one diagnostic");
        let Maybe::Present(ref code) = found[0].identifier
        else {
            panic!("a refusal names its code");
        };
        let Maybe::Present(primary) = found[0].primary()
        else {
            panic!("the refusal is located");
        };
        let line = u64::try_from(primary.locus.line).expect("a line number");
        let column = u64::try_from(primary.locus.column).expect("a column number");

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
            json!(code.to_string()),
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
    fn every_corpus_diagnostic_is_published_as_the_model_builds_it()
    {
        let root = corpus();
        let mut walk = Walk::new(vec![root.join("strict"), root.join("fixture")]);
        let mut expected = BTreeMap::new();
        let mut sources = Vec::new();
        while let Maybe::Present(step) = walk.step() {
            let Step::Source {
                path, text, base, ..
            } = step
            else {
                panic!("every corpus path is carried through the pipeline");
            };
            // An importer's text is its closure's; the editor holds its own.
            let own = <&str>::from(text)
                .get(usize::from(base) ..)
                .expect("a source's own text starts inside its unit's");
            let index = LineIndex::new(own.into());
            let reports = entries(&step, Verb::Check(Goals::Reported))
                .map(|diagnostic| rendered(&diagnostic, &index))
                .collect::<Vec<_>>();
            let source = Source {
                uri: uri(path),
                text: own.to_owned(),
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

    /// One line of the server log.
    #[repr(transparent)]
    #[derive(Clone, Copy)]
    struct Line<'text>(&'text str);

    /// What one timing line counts.
    #[derive(Debug, Eq, PartialEq)]
    struct Census
    {
        /// The version the line names.
        version: i32,
        /// The forms molded.
        molded: usize,
        /// The revision's forms.
        forms: usize,
    }

    /// The census `line`, one timing line of the server log, carries: the
    /// version it names, the forms molded, and the revision's forms.
    ///
    /// # Specification
    /// - requires: `line` is a timing line the server logged.
    /// - ensures: the three counts the line spells.
    /// - provides: the log's census as numbers a transcript compares.
    /// - fails: never in the valid domain.
    /// - panics: a line not in the logged shape violates the requirement.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the transcript's open molds every form and its edit a
    ///   handful; a misread count breaks one of the two.
    /// - witness: `session::session::an_edit_to_a_large_document_rechecks_its_forms`
    #[spec(ensures: |ret| ret.molded <= ret.forms)]
    fn census(Line(line): Line<'_>) -> Census
    {
        let (_, after) = line
            .split_once(" at version ")
            .expect("the line names a version");
        let (version, timing) = after.split_once(": ").expect("the line carries a timing");
        let (forms, _) = timing
            .split_once(" forms molded")
            .expect("the line counts forms");
        let (molded, forms) = forms.split_once('/').expect("molded of forms");
        Census {
            version: version.parse().expect("a version"),
            molded: molded.parse().expect("a molded count"),
            forms: forms.parse().expect("a form count"),
        }
    }

    #[test]
    fn an_edit_to_a_large_document_rechecks_its_forms()
    {
        use core::fmt::Write as _;

        let mut text = String::new();
        for i in 0 .. 1_000_usize {
            if i.is_multiple_of(2) {
                writeln!(text, "def v{i} : Integer ;\ndef v{i} = {i} ;")
            }
            else {
                writeln!(
                    text,
                    "def p{i} : +U (Integer -> Integer -> -F Integer) ;\n\
                     def p{i} = thunk {{ fn (x) {{ fn (y) {{ return x }} }} }} ;"
                )
            }
            .expect("a string takes text");
        }
        let uri = "file:///tmp/large.gandr".to_owned();
        let edited = text.replacen("def v500 = 500 ;", "def v500 = \"text\" ;", 1);
        // The edit writes a complete but wrong value inside the declaration
        // under the caret, which the quiet publication holds; this session
        // reads the recheck, so it holds nothing.
        let mut messages = opening();
        if let Some(params) = messages
            .first_mut()
            .and_then(|initialize| initialize.get_mut("params"))
        {
            params["initializationOptions"] = json!({"diagnostics": {"quiet": 0_i32}});
        }
        messages.push(open(&Source {
            uri: uri.clone(),
            text,
        }));
        messages.push(
            json!({"jsonrpc": "2.0", "method": "textDocument/didChange", "params": {
                "textDocument": {"uri": uri, "version": 2_i32},
                "contentChanges": [{
                    "range": {
                        "start": {"line": 1_001_i32, "character": 11_i32},
                        "end": {"line": 1_001_i32, "character": 14_i32},
                    },
                    "text": "\"text\"",
                }],
            }}),
        );
        messages.extend(closing());
        let (served, written, log) = logged(&messages);
        assert_eq!(served, Served::Clean);

        let mut whole = opening();
        whole.push(open(&Source {
            uri: uri.clone(),
            text: edited,
        }));
        whole.extend(closing());
        let (_, rechecked) = session(&whole);
        let diagnostics = |messages: &[Value], at: usize| {
            messages
                .get(at)
                .and_then(|message| message.pointer("/params/diagnostics"))
                .cloned()
                .expect("a publication")
        };
        assert_eq!(
            written
                .get(2)
                .and_then(|message| message.pointer("/params/version")),
            Some(&json!(2_i32)),
            "the edit is published at the version it brought"
        );
        assert_eq!(
            diagnostics(&written, 2),
            diagnostics(&rechecked, 1),
            "the edit publishes what opening the edited text publishes"
        );
        assert_eq!(
            diagnostics(&written, 2).pointer("/0/code"),
            Some(&json!("TypeMismatch")),
            "the edit is a type mismatch"
        );

        let [ref opened, ref changed] = *log.as_slice()
        else {
            panic!("one timing line per synchronisation: {log:?}");
        };
        assert!(opened.starts_with(&uri), "{opened}");
        assert_eq!(
            census(Line(opened)),
            Census {
                version: 1,
                molded: 2_000,
                forms: 2_000
            },
            "opening molds every form: {opened}"
        );
        let changed_census = census(Line(changed));
        assert_eq!(
            (changed_census.version, changed_census.forms),
            (2_i32, 2_000_usize),
            "{changed}"
        );
        assert!(
            (1_usize ..= 8_usize).contains(&changed_census.molded),
            "the edit molds the form it changed and the forms reading it: {changed}"
        );
        assert!(
            [opened, changed]
                .iter()
                .all(|line| line.contains(" ms, admitted in ")),
            "each synchronisation logs its recheck's wall, then its admission's: {log:?}"
        );
    }

    #[test]
    fn wire_helpers_preserve_escaped_paths_and_unicode_payloads()
    {
        assert_eq!(uri(Path::new("/a b/é.gandr")), "file:///a%20b/%C3%A9.gandr");
        let messages = [json!({"text":"é😀"}), Value::Null];
        let stream = frames(&messages);
        assert_eq!(
            stream.as_ref(),
            "Content-Length: 17\r\n\r\n{\"text\":\"é😀\"}Content-Length: 4\r\n\r\nnull".as_bytes()
        );
        assert_eq!(written(&stream), messages);
    }

    /// The token sweep: each corpus source's semantic tokens against its
    /// highlighted bytes.
    mod sweeps
    {
        use gandr_workflow_sweep::Sample;
        use gandr_workflow_sweep::SampleName;
        use gandr_workflow_sweep::SampleSize;
        use gandr_workflow_sweep::Sweep;

        use super::*;

        /// The sample: sixty-four sources, ranked by their BLAKE3 digest under
        /// this name, at least one of each corpus class — `strict` and each
        /// directory below `fixture` — and every source the change adds or
        /// modifies (`gandr-workflow-sweep`). The `sweeps` profile reads every
        /// source. Every run holds the whole corpus's membership to the
        /// dispatcher's walk.
        const SAMPLE: Sample = Sample {
            name: SampleName("corpus_tokens_cover_the_highlighted_bytes"),
            size: SampleSize(64),
        };

        #[test]
        fn corpus_tokens_cover_the_highlighted_bytes()
        {
            let grammar = built_in().expect("the built-in grammar builds");
            let roles = RoleTable::build(&grammar).expect("the role table builds");
            let all = gandr_workflow_sweep::corpus::sources().expect("the corpus reads");
            let root = corpus();
            let mut walk = Walk::new(vec![root.join("strict"), root.join("fixture")]);
            let mut expected_uris = alloc::collections::BTreeSet::new();
            while let Maybe::Present(step) = walk.step() {
                let Step::Source { path, .. } = step
                else {
                    panic!("a readable corpus source");
                };
                let _inserted = expected_uris.insert(uri(path));
            }
            assert_eq!(
                all.iter()
                    .map(|source| uri(&source.path))
                    .collect::<alloc::collections::BTreeSet<_>>(),
                expected_uris
            );
            let sweep = Sweep::asked().expect("the run's sweep resolves");
            let sources = opened(&sweep.visit(SAMPLE, &all));
            assert!(
                sources.len() >= SAMPLE.size.0,
                "the sample is drawn: {}",
                sources.len()
            );
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
}
