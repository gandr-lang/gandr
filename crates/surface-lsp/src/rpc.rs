//! JSON-RPC 2.0 as the protocol carries it: one message per frame, classified
//! by its envelope into a request, a notification or a response, and the
//! envelopes the server writes back.
//!
//! The protocol sends no batches, so an array body is an invalid request
//! rather than a batch to unpack. An outgoing message is a typed value until
//! the transport encodes it, so the one fallible encoding sits at the stream.

use anodized::spec;
use serde::Serialize;
use serde_json::Value;

use crate::protocol::Answer;
use crate::protocol::PublishParams;
use crate::transport::Body;

/// The version every envelope names.
const VERSION: &str = "2.0";

/// The method diagnostics are published under.
const PUBLISH_DIAGNOSTICS: &str = "textDocument/publishDiagnostics";

/// A request's identifier, echoed in its response: a number, a string, or
/// null for a message whose identifier could not be read.
#[repr(transparent)]
#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
#[serde(transparent)]
pub struct RequestId(Value);

impl RequestId
{
    /// The identifier of a response to a message whose own identifier could
    /// not be read.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn unread() -> Self
    {
        Self(Value::Null)
    }
}

impl From<Value> for RequestId
{
    /// Read the value as an identifier.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(id: Value) -> Self
    {
        Self(id)
    }
}

/// A method name.
#[repr(transparent)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Method(String);

impl From<&str> for Method
{
    /// Read the name as a method.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(name: &str) -> Self
    {
        Self(name.to_owned())
    }
}

impl AsRef<str> for Method
{
    /// The method's name.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn as_ref(&self) -> &str
    {
        &self.0
    }
}

/// A JSON-RPC error code.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq, Serialize)]
#[serde(transparent)]
pub struct ErrorCode(i64);

impl ErrorCode
{
    /// The method exists, but its parameters are not the shape it reads.
    pub const INVALID_PARAMS: Self = Self(-32_602);
    /// The message is JSON but not a request, a notification or a response,
    /// or a request the server's lifecycle does not admit.
    pub const INVALID_REQUEST: Self = Self(-32_600);
    /// No method of that name is served.
    pub const METHOD_NOT_FOUND: Self = Self(-32_601);
    /// The body is not JSON.
    pub const PARSE_ERROR: Self = Self(-32_700);
    /// A request arrived before `initialize` was answered.
    pub const SERVER_NOT_INITIALIZED: Self = Self(-32_002);
}

/// One message read off the stream, classified by its envelope.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Incoming
{
    /// A call the server answers.
    Request
    {
        /// The identifier its response echoes.
        id: RequestId,
        /// The method called.
        method: Method,
        /// Its parameters; `null` when the message carries none.
        params: Value,
    },
    /// A call the server never answers.
    Notification
    {
        /// The method called.
        method: Method,
        /// Its parameters; `null` when the message carries none.
        params: Value,
    },
    /// The client's answer to a request of the server's; the server sends
    /// none, so it is read and dropped.
    Response,
}

/// Why a body is not a message.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Malformed
{
    /// The JSON decoder rejected the body, including its resource limits.
    Parse,
    /// The body is JSON, but no request, notification or response: a batch,
    /// a value other than an object, a version other than `2.0`, an
    /// identifier other than a number or a string, or parameters other than
    /// an object, an array or null.
    Invalid(RequestId),
}

impl Malformed
{
    /// The error response the client is sent.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a parse failure is [`ErrorCode::PARSE_ERROR`] under a null
    ///   identifier; an invalid message is [`ErrorCode::INVALID_REQUEST`] under
    ///   its supplied identifier. [`classify()`] supplies null when the input
    ///   identifier could not be read.
    /// - provides: the answer the protocol owes a body the server cannot read.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — parse and invalid-message failures, with null,
    ///   numeric and string identifiers, distinguish wrong codes or lost
    ///   identifiers through their exact response envelope.
    /// - witness: `rpc::tests::a_batch_is_rejected`
    #[spec(
        captures: code = match self { Self::Parse => ErrorCode::PARSE_ERROR, Self::Invalid(_) => ErrorCode::INVALID_REQUEST },
        ensures: |ret| matches!(ret, Outgoing::Failure { jsonrpc: VERSION, ref id, ref error }
            if error.code == code && (code != ErrorCode::PARSE_ERROR || id.0.is_null())),
    )]
    #[inline]
    #[must_use]
    pub fn response(self) -> Outgoing
    {
        match self {
            | Self::Parse => failure(
                RequestId::unread(),
                ErrorCode::PARSE_ERROR,
                "the body is not JSON".to_owned(),
            ),
            | Self::Invalid(id) => failure(
                id,
                ErrorCode::INVALID_REQUEST,
                "the message is not a JSON-RPC 2.0 request, notification or response".to_owned(),
            ),
        }
    }
}

/// One message the server writes.
#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
#[serde(untagged)]
pub enum Outgoing
{
    /// A response carrying a request's result.
    Success
    {
        /// Always `2.0`.
        jsonrpc: &'static str,
        /// The request's identifier.
        id: RequestId,
        /// The result.
        result: Answer,
    },
    /// A response refusing a request.
    Failure
    {
        /// Always `2.0`.
        jsonrpc: &'static str,
        /// The request's identifier, or null when it could not be read.
        id: RequestId,
        /// The refusal.
        error: Refusal,
    },
    /// A notification of the server's.
    Notification
    {
        /// Always `2.0`.
        jsonrpc: &'static str,
        /// The method notified.
        method: &'static str,
        /// Its parameters.
        params: PublishParams,
    },
}

/// The error object of a refusing response.
#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
pub struct Refusal
{
    /// The error code.
    pub code: ErrorCode,
    /// What was refused, and why.
    pub message: String,
}

/// Classify `body` by its envelope.
///
/// # Specification
/// - requires: nothing; any body is admissible input.
/// - ensures: within the JSON decoder's supported fragment, an object naming
///   version `2.0` and a string `method` is a request when it carries an `id`
///   and a notification when it does not; an object naming version `2.0`, an
///   `id` and a `result` or an `error` is a response. A request's `id` is a
///   number or a string, and `params`, when present, an object or an array; an
///   explicit `null`, which some clients send for a method without parameters,
///   reads as absent.
/// - provides: the one reader of a body's envelope; nothing past it reads the
///   raw body.
/// - fails: [`Malformed::Parse`] when JSON decoding rejects the body, including
///   invalid UTF-8, malformed syntax or unsupported nesting/numbers;
///   [`Malformed::Invalid`] for every other body, carrying the message's `id`
///   when it is a number or a string.
/// - panics: none.
///
/// # Errors
/// [`Malformed`], as above.
///
/// # Adequacy
/// - hypothesis: L3 — the decision surfaces are a request, a notification, a
///   response, a body that is not JSON, a batch, a scalar, a wrong version, an
///   object identifier, scalar parameters and a method that is not a string;
///   each separated by its exact classification. Decoder rejection is sampled
///   with invalid UTF-8, an unrepresentable number and 512 nested arrays.
/// - witness: `rpc::tests::a_request_is_classified`
/// - witness: `rpc::tests::a_batch_is_rejected`
/// - witness: `rpc::tests::decoder_rejections_keep_the_parse_error_class`
#[spec(ensures: |ret| match ret {
    Ok(Incoming::Request { ref id, ref params, .. }) =>
        (id.0.is_number() || id.0.is_string())
            && (params.is_null() || params.is_object() || params.is_array()),
    Ok(Incoming::Notification { ref params, .. }) =>
        params.is_null() || params.is_object() || params.is_array(),
    Err(Malformed::Invalid(ref id)) => id.0.is_null() || id.0.is_number() || id.0.is_string(),
    Ok(Incoming::Response) | Err(Malformed::Parse) => true,
})]
#[inline]
pub fn classify(body: &Body) -> Result<Incoming, Malformed>
{
    let value: Value =
        serde_json::from_slice(body.as_ref()).map_err(|_not_json| Malformed::Parse)?;
    let Value::Object(mut object) = value
    else {
        return Err(Malformed::Invalid(RequestId::unread()));
    };
    let id = match object.remove("id") {
        | None => None,
        | Some(id @ (Value::Number(_) | Value::String(_))) => Some(RequestId(id)),
        | Some(_) => return Err(Malformed::Invalid(RequestId::unread())),
    };
    let invalid = || Malformed::Invalid(id.clone().unwrap_or_else(RequestId::unread));
    if object.get("jsonrpc").and_then(Value::as_str) != Some(VERSION) {
        return Err(invalid());
    }
    let params = match object.remove("params") {
        | None | Some(Value::Null) => Value::Null,
        | Some(params @ (Value::Object(_) | Value::Array(_))) => params,
        | Some(_) => return Err(invalid()),
    };
    match (object.remove("method"), id.clone()) {
        | (Some(Value::String(method)), Some(id)) => Ok(Incoming::Request {
            id,
            method: Method(method),
            params,
        }),
        | (Some(Value::String(method)), None) => Ok(Incoming::Notification {
            method: Method(method),
            params,
        }),
        | (None, Some(_)) if object.contains_key("result") || object.contains_key("error") => {
            Ok(Incoming::Response)
        },
        | (Some(_) | None, _) => Err(invalid()),
    }
}

/// The response answering `id` with `result`.
///
/// # Specification
/// trivial.
#[inline]
#[must_use]
pub const fn success(
    id: RequestId,
    result: Answer,
) -> Outgoing
{
    Outgoing::Success {
        jsonrpc: VERSION,
        id,
        result,
    }
}

/// The response refusing `id` with `code` and `message`.
///
/// # Specification
/// trivial.
#[inline]
#[must_use]
pub const fn failure(
    id: RequestId,
    code: ErrorCode,
    message: String,
) -> Outgoing
{
    Outgoing::Failure {
        jsonrpc: VERSION,
        id,
        error: Refusal { code, message },
    }
}

/// The notification publishing `params`.
///
/// # Specification
/// trivial.
#[inline]
#[must_use]
pub const fn publish(params: PublishParams) -> Outgoing
{
    Outgoing::Notification {
        jsonrpc: VERSION,
        method: PUBLISH_DIAGNOSTICS,
        params,
    }
}

#[cfg(test)]
mod tests
{
    use serde_json::Value;
    use serde_json::json;

    use super::Incoming;
    use super::Malformed;
    use super::Method;
    use super::RequestId;
    use super::classify;
    use crate::transport::Body;

    /// A message body, spelled as JSON text.
    #[repr(transparent)]
    struct Json(&'static str);

    /// The classification of a body.
    ///
    /// # Specification
    /// trivial.
    fn classified(Json(text): Json) -> Result<Incoming, Malformed>
    {
        classify(&Body::from(text.as_bytes().to_vec()))
    }

    #[test]
    fn a_request_is_classified()
    {
        assert_eq!(
            classified(Json(r#"{"jsonrpc":"2.0","id":7,"method":"shutdown"}"#)),
            Ok(Incoming::Request {
                id: RequestId(json!(7_i32)),
                method: Method::from("shutdown"),
                params: Value::Null,
            }),
            "an id and a method make a request, its absent params null"
        );
        assert_eq!(
            classified(Json(
                r#"{"jsonrpc":"2.0","method":"initialized","params":{}}"#
            )),
            Ok(Incoming::Notification {
                method: Method::from("initialized"),
                params: json!({}),
            }),
            "a method without an id is a notification"
        );
        assert_eq!(
            classified(Json(r#"{"jsonrpc":"2.0","id":"x","result":null}"#)),
            Ok(Incoming::Response),
            "an id with a result is the client's response"
        );
        assert_eq!(
            classified(Json(
                r#"{"jsonrpc":"2.0","id":8,"method":"shutdown","params":null}"#
            )),
            Ok(Incoming::Request {
                id: RequestId(json!(8_i32)),
                method: Method::from("shutdown"),
                params: Value::Null,
            }),
            "explicit null parameters read as absent"
        );
        let refusals = [
            (
                Json(r#"{"jsonrpc":"2.0","id":1,"method":"m""#),
                Malformed::Parse,
            ),
            (Json("3"), Malformed::Invalid(RequestId::unread())),
            (
                Json(r#"{"jsonrpc":"1.0","id":4,"method":"m"}"#),
                Malformed::Invalid(RequestId(json!(4_i32))),
            ),
            (
                Json(r#"{"jsonrpc":"2.0","id":{},"method":"m"}"#),
                Malformed::Invalid(RequestId::unread()),
            ),
            (
                Json(r#"{"jsonrpc":"2.0","id":"p","method":"m","params":3}"#),
                Malformed::Invalid(RequestId(json!("p"))),
            ),
            (
                Json(r#"{"jsonrpc":"2.0","id":5,"method":6}"#),
                Malformed::Invalid(RequestId(json!(5_i32))),
            ),
        ];
        for (json, refusal) in refusals {
            let text = json.0;
            assert_eq!(classified(json), Err(refusal), "{text} is refused");
        }
    }

    #[test]
    fn a_batch_is_rejected()
    {
        let batch = classified(Json(r#"[{"jsonrpc":"2.0","id":1,"method":"shutdown"}]"#));
        assert_eq!(
            batch,
            Err(Malformed::Invalid(RequestId::unread())),
            "the protocol sends no batches"
        );
        for (malformed, expected_id, expected_code) in [
            (Malformed::Parse, Value::Null, super::ErrorCode::PARSE_ERROR),
            (
                Malformed::Invalid(RequestId::unread()),
                Value::Null,
                super::ErrorCode::INVALID_REQUEST,
            ),
            (
                Malformed::Invalid(RequestId(json!(17_i32))),
                json!(17_i32),
                super::ErrorCode::INVALID_REQUEST,
            ),
            (
                Malformed::Invalid(RequestId(json!("correlation"))),
                json!("correlation"),
                super::ErrorCode::INVALID_REQUEST,
            ),
        ] {
            let super::Outgoing::Failure { jsonrpc, id, error } = malformed.response()
            else {
                panic!("malformed messages require an error envelope");
            };
            assert_eq!(jsonrpc, "2.0");
            assert_eq!(id.0, expected_id);
            assert_eq!(error.code, expected_code);
        }
    }
    #[test]
    fn decoder_rejections_keep_the_parse_error_class()
    {
        for bytes in [b"\xff".as_slice(), b"1e9999".as_slice()] {
            assert_eq!(classify(&Body::from(bytes.to_vec())), Err(Malformed::Parse));
        }
        let nested = format!("{}0{}", "[".repeat(512), "]".repeat(512));
        assert_eq!(
            classify(&Body::from(nested.into_bytes())),
            Err(Malformed::Parse)
        );
        assert_eq!(
            classified(Json("[0]")),
            Err(Malformed::Invalid(RequestId::unread()))
        );
    }
}
