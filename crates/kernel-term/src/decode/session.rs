//! Session inline framing; allocations grow only after bytes are consumed.

use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use alloc::string::String;
use alloc::vec::Vec;

use anodized::spec;

use super::ByteReader;
use crate::DecodeError;
use crate::MalformedSite;
use crate::session::Evidence;
use crate::session::Graph;
use crate::session::Label;
use crate::session::Node;
use crate::session::PayloadSlot;
use crate::session::State;
use crate::session::StatePair;

/// Read one graph position without narrowing silently.
///
/// # Specification
/// - ensures: the position fits the host index type and consumes a varint.
/// - fails: malformed or truncated varints retain their decoder error.
/// - panics: none.
///
/// # Errors
/// Byte-reader failures.
///
/// # Adequacy
/// - hypothesis: L3 truncated framing refuses rather than inventing positions.
/// - witness: `session::tests::session_words_preserve_graph_and_relation`
#[spec(captures: start = reader.position.0, ensures: |ret| ret.is_err() || reader.position.0 > start)]
fn state(reader: &mut ByteReader<'_>) -> Result<State, DecodeError>
{
    let word = reader.read_usize()?;
    Ok(State(usize::from(word)))
}

/// Read raw finite syntax, leaving semantic formation to the kernel.
///
/// # Specification
/// - ensures: every tag, label, edge and payload slot is retained exactly;
///   success consumes the root, count and at least one byte per node.
/// - fails: unknown node tags, invalid UTF-8, duplicate labels and truncated
///   framing refuse as malformed session data or byte-reader failures.
/// - panics: none.
///
/// # Errors
/// Malformed session data or a byte-reader error.
///
/// # Adequacy
/// - hypothesis: L3 all constructors round-trip; truncation and malformed
///   labels cannot yield a graph.
/// - witness: `session::tests::session_words_preserve_graph_and_relation`
/// - witness: `session::tests::session_wire_goldens_and_malformed_fields_are_distinct`
#[spec(captures: start = reader.position.0, ensures: |ret| match ret {
    Ok(ref graph) => reader.position.0.saturating_sub(start) >= graph.nodes.len().saturating_add(2),
    Err(_) => true,
})]
pub fn graph(reader: &mut ByteReader<'_>) -> Result<Graph, DecodeError>
{
    let root = state(reader)?;
    let count = reader.read_uvarint()?;
    let mut nodes = Vec::new();
    for _ in 0 .. u64::from(count) {
        let tag = reader.read_uvarint()?;
        let node = match crate::session::Word(u64::from(tag)) {
            | crate::session::SEND | crate::session::RECEIVE => {
                let slot = state(reader)?;
                let next = state(reader)?;
                if crate::session::Word(u64::from(tag)) == crate::session::SEND {
                    Node::Send(PayloadSlot(slot.0), next)
                }
                else {
                    Node::Receive(PayloadSlot(slot.0), next)
                }
            },
            | crate::session::SELECT | crate::session::OFFER => {
                let count = reader.read_uvarint()?;
                let mut branches = BTreeMap::new();
                for _ in 0 .. u64::from(count) {
                    let count = reader.read_uvarint()?;
                    let mut bytes = Vec::new();
                    for _ in 0 .. u64::from(count) {
                        let word = reader.read_uvarint()?;
                        let byte = u8::try_from(u64::from(word)).map_err(|_invalid| malformed())?;
                        bytes.push(byte);
                    }
                    let label = String::from_utf8(bytes).map_err(|_invalid| malformed())?;
                    let next = state(reader)?;
                    if branches.insert(Label(label), next).is_some() {
                        return Err(malformed());
                    }
                }
                if crate::session::Word(u64::from(tag)) == crate::session::SELECT {
                    Node::Select(branches)
                }
                else {
                    Node::Offer(branches)
                }
            },
            | crate::session::END => Node::End,
            | crate::session::MU => {
                let body = state(reader)?;
                Node::Mu(body)
            },
            | crate::session::VAR => {
                let binder = state(reader)?;
                Node::Var(binder)
            },
            | _ => return Err(malformed()),
        };
        nodes.push(node);
    }
    Ok(Graph { nodes, root })
}

/// Read a finite relation and its ordered payload-proof slots.
///
/// # Specification
/// - ensures: retains all pairs and ordered payload obligations; success
///   consumes both counts and at least two bytes per pair or obligation.
/// - fails: duplicate relation pairs, truncation and unrepresentable indices
///   refuse. Graph bounds and semantic obligations are checked by the kernel.
/// - panics: none.
///
/// # Errors
/// Malformed session data or byte-reader failures.
///
/// # Adequacy
/// - hypothesis: L3 relation and payload framing round-trip independently.
/// - witness: `session::tests::session_words_preserve_graph_and_relation`
/// - witness: `session::tests::session_wire_goldens_and_malformed_fields_are_distinct`
#[spec(captures: start = reader.position.0, ensures: |ret| match ret {
    Ok(ref evidence) => reader.position.0.saturating_sub(start) >= evidence.pairs.len().saturating_add(evidence.payloads.len()).saturating_mul(2).saturating_add(2),
    Err(_) => true,
})]
pub fn evidence(reader: &mut ByteReader<'_>) -> Result<Evidence, DecodeError>
{
    let count = reader.read_uvarint()?;
    let mut pairs = BTreeSet::new();
    for _ in 0 .. u64::from(count) {
        let source = state(reader)?;
        let target = state(reader)?;
        if !pairs.insert(StatePair { source, target }) {
            return Err(malformed());
        }
    }
    let count = reader.read_uvarint()?;
    let mut payloads = Vec::new();
    for _ in 0 .. u64::from(count) {
        let source = state(reader)?;
        let target = state(reader)?;
        payloads.push((PayloadSlot(source.0), PayloadSlot(target.0)));
    }
    Ok(Evidence { pairs, payloads })
}

/// The session inline framing refusal.
///
/// # Specification
/// trivial.
fn malformed() -> DecodeError
{
    DecodeError::Malformed {
        site: MalformedSite::Session,
    }
}
