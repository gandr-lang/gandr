//! A peer's names: a secret proves its key, a key reads back from its
//! printing, and a peer's spelling is its key and its addresses.

use core::net::SocketAddr;
use core::str::FromStr as _;

use gandr_runtime_net::NodeId;
use gandr_runtime_net::Peer;
use gandr_runtime_net::PeerError;
use gandr_runtime_net::Secret;

/// A secret fixed by its bytes, `0x01` 32 times.
const SECRET: &str = "0101010101010101010101010101010101010101010101010101010101010101";

#[test]
fn a_secret_spelled_in_hex_proves_its_key()
{
    let secret = Secret::from_str(SECRET).expect("64 hex digits are a secret");
    let again = Secret::from_str(&SECRET.to_uppercase()).expect("case does not matter");
    assert_eq!(secret.node_id(), again.node_id(), "one secret, one key");
    assert_ne!(
        secret.node_id(),
        Secret::generate().node_id(),
        "a fresh secret proves another key"
    );
    for refused in [
        "",
        "01",
        "zz01010101010101010101010101010101010101010101010101010101010101",
    ] {
        assert!(
            matches!(Secret::from_str(refused), Err(PeerError::Key { .. })),
            "`{refused}` is no secret"
        );
    }
}

#[test]
fn a_key_reads_back_from_its_spelling()
{
    let id = Secret::from_str(SECRET).expect("a secret").node_id();
    let spelled = id.to_string();
    assert_eq!(spelled.len(), 64, "32 bytes in hex");
    assert!(
        spelled
            .bytes()
            .all(|byte| byte.is_ascii_digit() || (b'a' ..= b'f').contains(&byte)),
        "lowercase hex: {spelled}"
    );
    assert_eq!(
        NodeId::from_str(&spelled),
        Ok(id),
        "the printing reads back"
    );
    assert_eq!(
        NodeId::from_str(&spelled.to_uppercase()),
        Ok(id),
        "uppercase reads as the same key"
    );
    let short = spelled.get(.. 62).expect("64 digits hold 62");
    for refused in ["", "00", short] {
        assert!(
            matches!(NodeId::from_str(refused), Err(PeerError::Key { .. })),
            "`{refused}` is no key"
        );
    }
}

#[test]
fn a_peer_reads_back_from_its_spelling()
{
    let id = Secret::from_str(SECRET).expect("a secret").node_id();
    let bare = Peer::from_str(&id.to_string()).expect("a bare key is a peer");
    assert_eq!(bare.id(), id);
    assert!(bare.addresses().is_empty(), "a bare key names no address");

    let v4 = SocketAddr::from(([127, 0, 0, 1], 4000));
    let v6 = SocketAddr::from(([0, 0, 0, 0, 0, 0, 0, 1], 4001));
    let spelled = format!("{id}@127.0.0.1:4000@[::1]:4001");
    let peer = Peer::from_str(&spelled).expect("a key and two addresses");
    assert_eq!(peer.id(), id);
    assert_eq!(peer.addresses(), [v4, v6], "both addresses, in order");
    assert_eq!(
        peer.to_string(),
        spelled,
        "the peer prints as it was spelled"
    );
    assert_eq!(
        Peer::new(id).at(v4).at(v6).to_string(),
        spelled,
        "a peer built prints as one spelled"
    );

    for refused in [format!("{id}@"), format!("{id}@127.0.0.1")] {
        assert!(
            matches!(Peer::from_str(&refused), Err(PeerError::Address { .. })),
            "`{refused}` names no address"
        );
    }
    assert!(
        matches!(
            Peer::from_str("@127.0.0.1:4000"),
            Err(PeerError::Key { .. })
        ),
        "an address alone names no peer"
    );
}
