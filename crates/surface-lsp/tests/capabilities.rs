//! The capabilities line, read as a client reads it.
//!
//! The case, in a `cfg(test)` module so the crate's lint wall reads it as
//! test code rather than as shipping code.

use anodized::spec;
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
                "textDocumentSync": {"openClose": true, "change": 2_i32},
                "semanticTokensProvider": {
                    "legend": {"tokenTypes": TOKEN_TYPES, "tokenModifiers": TOKEN_MODIFIERS},
                    "full": true,
                    "range": true,
                },
                "completionProvider": {"resolveProvider": false},
                "inlineCompletionProvider": true,
                "documentSymbolProvider": true,
                "foldingRangeProvider": true,
                "selectionRangeProvider": true,
                "hoverProvider": true,
                "signatureHelpProvider": {"triggerCharacters": ["(", ","], "retriggerCharacters": [")"]},
                "definitionProvider": true,
                "typeDefinitionProvider": true,
                "documentFormattingProvider": true,
                "documentRangeFormattingProvider": true,
                "codeLensProvider": {"resolveProvider": false},
                "codeActionProvider": true,
            },
            "serverInfo": {"name": "gandr", "version": env!("CARGO_PKG_VERSION")},
        }),
        "the legend the crate exports, and every request served"
    );
}
/// A formatter sink refusing every write.
struct Refuses;

impl core::fmt::Write for Refuses
{
    /// Refuse the formatted bytes.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: no write succeeds.
    /// - provides: an observable formatting failure.
    /// - fails: returns the formatter's error.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns `core::fmt::Error` on every call.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — rendering the capability object into a refusing sink
    ///   exposes swallowed errors through the exact failed result.
    /// - witness: `tests::capabilities::a_refused_capabilities_write_is_propagated`
    #[spec(ensures: |ret| ret.is_err())]
    fn write_str(
        &mut self,
        _s: &str,
    ) -> core::fmt::Result
    {
        Err(core::fmt::Error)
    }
}

#[test]
fn a_refused_capabilities_write_is_propagated()
{
    assert_eq!(
        core::fmt::write(&mut Refuses, format_args!("{Capabilities}")),
        Err(core::fmt::Error)
    );
}
