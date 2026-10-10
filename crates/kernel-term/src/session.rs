//! Finite session-code graphs and untrusted coinductive relation data.
//!
//! Structural edges form a tree; only `Var` edges point back to a `Mu`.
//! Payload slots select fields of a right-associated product ending in Unit.
//! That product is one ordinary native type child, so payload codes retain
//! canonical sharing, content identity and universe formation.

use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use alloc::string::String;
use alloc::vec::Vec;

/// A position in a finite session graph.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct State(pub usize);

/// A zero-based payload-code position in the code's product telescope.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct PayloadSlot(pub usize);

/// An exact UTF-8 branch label.
#[repr(transparent)]
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Label(pub String);

/// One finite syntax occurrence; recursive ownership is absent.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum Node
{
    /// Send the indexed payload, then continue.
    Send(PayloadSlot, State),
    /// Receive the indexed payload, then continue.
    Receive(PayloadSlot, State),
    /// Choose one label.
    Select(BTreeMap<Label, State>),
    /// Accept the peer's chosen label.
    Offer(BTreeMap<Label, State>),
    /// Close the endpoint.
    End,
    /// Bind recursion over a guarded body.
    Mu(State),
    /// Refer to an enclosing binder by graph position.
    Var(State),
}

/// Raw finite syntax; formation, not construction, checks binding and guards.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct Graph
{
    /// Finite syntax occurrences in stable wire order.
    pub nodes: Vec<Node>,
    /// Root syntax occurrence.
    pub root: State,
}

/// A supplied coinductive hypothesis in source-to-target order.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct StatePair
{
    /// Source state.
    pub source: State,
    /// Target state.
    pub target: State,
}

/// Raw finite relation and the payload equalities its consumer must check.
///
/// # Specification
/// - provides: a relation containing the observable root pair and every
///   required continuation pair. `payloads` indexes an accompanying native
///   value tuple of `Path_U` witnesses, in this exact order.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 wire round trips retain relation pairs and payload-proof
///   order; malformed framing refuses before admission.
/// - witness: `session::tests::session_words_preserve_graph_and_relation`
#[derive(Clone, Debug, Default, Eq, Hash, PartialEq)]
pub struct Evidence
{
    /// Every supplied pair is checked, including unreachable extra pairs.
    pub pairs: BTreeSet<StatePair>,
    /// Source and target payload slots for each accompanying `Path_U` value.
    pub payloads: Vec<(PayloadSlot, PayloadSlot)>,
}

/// One unsigned word in the canonical session inline payload.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Word(pub u64);

impl From<usize> for Word
{
    /// Widen a host position through the format's supported-platform
    /// conversion.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: usize) -> Self
    {
        Self(u64::from(crate::wire::WireU64::from(
            crate::wire::WireUsize::from(value),
        )))
    }
}

/// Send opcode inside the finite graph payload.
pub(crate) const SEND: Word = Word(0x53);
/// Receive opcode inside the finite graph payload.
pub(crate) const RECEIVE: Word = Word(0x54);
/// Selection opcode inside the finite graph payload.
pub(crate) const SELECT: Word = Word(0x55);
/// Offer opcode inside the finite graph payload.
pub(crate) const OFFER: Word = Word(0x56);
/// End opcode inside the finite graph payload.
pub(crate) const END: Word = Word(0x57);
/// Binder opcode inside the finite graph payload.
pub(crate) const MU: Word = Word(0x58);
/// Variable opcode inside the finite graph payload.
pub(crate) const VAR: Word = Word(0x59);

impl Graph
{
    /// Emit finite graph framing without allocating a serialization buffer.
    ///
    /// # Specification
    /// - ensures: emits root, node count, then each node's tag and fields;
    ///   labels use byte length followed by exact UTF-8 bytes.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 every constructor and a non-ASCII label round-trip.
    /// - witness: `session::tests::session_words_preserve_graph_and_relation`
    #[inline]
    pub fn write<Emit>(
        &self,
        mut emit: Emit,
    ) where
        Emit: FnMut(Word),
    {
        emit(Word::from(self.root.0));
        emit(Word::from(self.nodes.len()));
        for node in &self.nodes {
            match node {
                | &Node::Send(slot, next) | &Node::Receive(slot, next) => {
                    emit(if matches!(*node, Node::Send(..)) {
                        SEND
                    }
                    else {
                        RECEIVE
                    });
                    emit(Word::from(slot.0));
                    emit(Word::from(next.0));
                },
                | &Node::Select(ref branches) | &Node::Offer(ref branches) => {
                    emit(if matches!(*node, Node::Select(_)) {
                        SELECT
                    }
                    else {
                        OFFER
                    });
                    emit(Word::from(branches.len()));
                    for (label, next) in branches {
                        emit(Word::from(label.0.len()));
                        for byte in label.0.bytes() {
                            emit(Word(u64::from(byte)));
                        }
                        emit(Word::from(next.0));
                    }
                },
                | &Node::End => emit(END),
                | &Node::Mu(body) => {
                    emit(MU);
                    emit(Word::from(body.0));
                },
                | &Node::Var(binder) => {
                    emit(VAR);
                    emit(Word::from(binder.0));
                },
            }
        }
    }
}

impl Evidence
{
    /// Emit ordered relation framing without a temporary buffer.
    ///
    /// # Specification
    /// - ensures: emits pair count and ordered pairs, then payload obligation
    ///   count and slot pairs in supplied order.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 relation and payload-pair framing remain distinct.
    /// - witness: `session::tests::session_words_preserve_graph_and_relation`
    #[inline]
    pub fn write<Emit>(
        &self,
        mut emit: Emit,
    ) where
        Emit: FnMut(Word),
    {
        emit(Word::from(self.pairs.len()));
        for pair in &self.pairs {
            emit(Word::from(pair.source.0));
            emit(Word::from(pair.target.0));
        }
        emit(Word::from(self.payloads.len()));
        for &(source, target) in &self.payloads {
            emit(Word::from(source.0));
            emit(Word::from(target.0));
        }
    }
}

#[cfg(test)]
mod tests;
