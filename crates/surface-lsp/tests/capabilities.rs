//! The capabilities line, read as a client reads it.

/// The case, in a `cfg(test)` module so the crate's lint wall reads it as
/// test code rather than as shipping code.
#[cfg(test)]
mod capabilities
{
    use gandr_surface_lsp::Capabilities;
    use gandr_surface_lsp::TOKEN_MODIFIERS;
    use gandr_surface_lsp::TOKEN_TYPES;
    use serde_json::Value;
    use serde_json::json;

    #[test]
    fn advertised_capabilities_name_the_token_legend()
    {
        let line = Capabilities.to_string();
        assert_eq!(line.lines().count(), 1_usize, "one line: {line}");
        let advertised: Value = serde_json::from_str(&line).expect("the line is JSON");
        assert_eq!(
            advertised,
            json!({
                "capabilities": {
                    "positionEncoding": "utf-16",
                    "textDocumentSync": {"openClose": true, "change": 1_i32},
                    "semanticTokensProvider": {
                        "legend": {"tokenTypes": TOKEN_TYPES, "tokenModifiers": TOKEN_MODIFIERS},
                        "full": true,
                        "range": true,
                    },
                },
                "serverInfo": {"name": "gandr", "version": env!("CARGO_PKG_VERSION")},
            }),
            "the legend the crate exports, and nothing unserved: no hover, no completion"
        );
    }
}
