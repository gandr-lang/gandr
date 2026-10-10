//! Finite wire framing and truncation boundaries.

use alloc::collections::BTreeSet;
use alloc::string::String;
use alloc::vec;

use super::Evidence;
use super::Graph;
use super::Label;
use super::Node;
use super::PayloadSlot;
use super::State;
use super::StatePair;
use crate::ArtifactImage;
use crate::EncodedArtifact;
use crate::decode::ByteReader;
use crate::wire::WireU64;

#[test]
fn session_artifact_retains_graph_payloads_and_evidence()
{
    let mut arena = crate::TermArena::new();
    let unit = arena.value_type_unit();
    let payload = arena.value_type_base(crate::BaseType::String);
    let payloads = arena.value_type_product(payload, unit);
    let graph = alloc::sync::Arc::new(Graph {
        root: State(0),
        nodes: vec![
            Node::Mu(State(1)),
            Node::Send(PayloadSlot(0), State(2)),
            Node::Var(State(0)),
        ],
    });
    let evidence = alloc::sync::Arc::new(Evidence {
        pairs: [StatePair {
            source: State(1),
            target: State(1),
        }]
        .into(),
        payloads: vec![(PayloadSlot(0), PayloadSlot(0))],
    });
    let session = arena.value_type_session(alloc::sync::Arc::clone(&graph), payloads);
    let code = arena.value_quote(session);
    let classifier = arena.value_type_path_universe(code, code);
    let payload_code = arena.value_quote(payload);
    let proof = arena.value_path_refl(payload_code);
    let end = arena.value_unit();
    let proofs = arena.value_pair(proof, end);
    let value = arena.value_session_path(classifier, alloc::sync::Arc::clone(&evidence), proofs);
    let declaration = crate::DeclarationBuilder::new(&mut arena).def(
        crate::LevelSignature::monomorphic(),
        classifier,
        value,
    );
    let declarations = [crate::MarkedDeclaration::new(
        crate::AdmissionMark::Checked,
        declaration,
    )];
    let bytes = crate::encode(&arena, &declarations);
    let decoded = crate::decode(bytes.as_image()).expect("native session artifact");
    assert_eq!(
        bytes,
        crate::encode(decoded.arena(), decoded.declarations())
    );
    let crate::DeclarationContent::Def { body, .. } =
        *decoded.declarations()[0].declaration().content()
    else {
        panic!("definition retained")
    };
    let crate::Value::SessionPath {
        path_type,
        evidence: ref actual,
        payload_paths,
    } = *decoded.arena().value(body).expect("body")
    else {
        panic!("session evidence retained")
    };
    assert_eq!(actual, &evidence);
    let crate::ValueType::PathUniverse(source, target) =
        *decoded.arena().value_type(path_type).expect("classifier")
    else {
        panic!("path classifier retained")
    };
    assert_eq!(source, target);
    let crate::Value::Quote(ty) = *decoded.arena().value(source).expect("source code")
    else {
        panic!("quote retained")
    };
    let crate::ValueType::Session {
        graph: ref actual,
        payloads,
    } = *decoded.arena().value_type(ty).expect("session type")
    else {
        panic!("session code retained")
    };
    assert_eq!(actual, &graph);
    let crate::ValueType::Product(payload, _) = *decoded
        .arena()
        .value_type(payloads)
        .expect("payload telescope")
    else {
        panic!("payload code retained")
    };
    assert_eq!(
        decoded.arena().value_type(payload),
        Some(&crate::ValueType::Base(crate::BaseType::String))
    );
    let crate::Value::Pair(proof, _) = *decoded
        .arena()
        .value(payload_paths)
        .expect("payload proofs")
    else {
        panic!("proof tuple retained")
    };
    let crate::Value::PathRefl(code) = *decoded.arena().value(proof).expect("payload proof")
    else {
        panic!("payload path retained")
    };
    assert_eq!(
        decoded.arena().value(code),
        Some(&crate::Value::Quote(payload))
    );
}

#[test]
fn session_words_preserve_graph_and_relation()
{
    let graph = Graph {
        root: State(0),
        nodes: vec![
            Node::Mu(State(1)),
            Node::Select(
                [
                    (Label(String::from("report")), State(2)),
                    (Label(String::from("λ")), State(6)),
                ]
                .into(),
            ),
            Node::Send(PayloadSlot(0), State(3)),
            Node::Receive(PayloadSlot(1), State(4)),
            Node::Offer([(Label(String::from("again")), State(5))].into()),
            Node::Var(State(0)),
            Node::End,
        ],
    };
    let evidence = Evidence {
        pairs: BTreeSet::from([
            StatePair {
                source: State(1),
                target: State(2),
            },
            StatePair {
                source: State(3),
                target: State(4),
            },
        ]),
        payloads: vec![
            (PayloadSlot(0), PayloadSlot(2)),
            (PayloadSlot(1), PayloadSlot(1)),
        ],
    };
    let mut bytes = EncodedArtifact::new();
    graph.write(|word| bytes.put_uvarint(WireU64::from(word.0)));
    let image = bytes.as_image();
    let mut reader = ByteReader::new(image);
    assert_eq!(crate::decode::session::graph(&mut reader), Ok(graph));
    let raw: &[u8] = image.as_ref();
    for end in 0 .. raw.len() {
        let prefix = raw.get(.. end).expect("prefix");
        let mut reader = ByteReader::new(ArtifactImage::from(prefix));
        assert_eq!(
            crate::decode::session::graph(&mut reader),
            Err(crate::DecodeError::Truncated)
        );
    }
    let mut bytes = EncodedArtifact::new();
    evidence.write(|word| bytes.put_uvarint(WireU64::from(word.0)));
    let mut reader = ByteReader::new(bytes.as_image());
    assert_eq!(crate::decode::session::evidence(&mut reader), Ok(evidence));
    let mut invalid = EncodedArtifact::new();
    for word in [0_u64, 1, 0x5a] {
        invalid.put_uvarint(WireU64::from(word));
    }
    let mut reader = ByteReader::new(invalid.as_image());
    assert_eq!(
        crate::decode::session::graph(&mut reader),
        Err(crate::DecodeError::Malformed {
            site: crate::MalformedSite::Session
        })
    );
}
