//! A peer's names: the [`Secret`] a host proves its identity with, the
//! [`NodeId`] its peers know it by, and the [`Peer`] a dialer names, a key
//! with the socket addresses it may try. The key is the identity: an address
//! is where a dialer looks for a key, and never part of whom it reaches.

use core::error::Error;
use core::fmt;
use core::net::SocketAddr;
use core::str::FromStr;

use anodized::spec;

/// The secret key an endpoint proves its [`NodeId`] with.
///
/// No formatting shows the key: `Debug` prints `Secret(SecretKey(..))`.
#[derive(Clone, Debug)]
#[repr(transparent)]
pub struct Secret(iroh::SecretKey);

impl Secret
{
    /// A fresh secret drawn from the operating system's randomness.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn generate() -> Self
    {
        Self(iroh::SecretKey::generate())
    }

    /// The key this secret proves.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn node_id(&self) -> NodeId
    {
        NodeId(self.0.public())
    }

    /// The secret as iroh holds it.
    ///
    /// # Specification
    /// trivial.
    pub(crate) fn key(&self) -> iroh::SecretKey
    {
        self.0.clone()
    }
}

impl FromStr for Secret
{
    type Err = PeerError;

    /// The secret spelled as 64 hex digits, or as base32, in either case.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the secret whose 32 bytes `text` spells.
    /// - fails: [`PeerError::Key`] for text spelling no 32 bytes.
    /// - panics: none.
    /// - executable: none — a secret has no observable but its public key,
    ///   which the witness compares.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a secret spelled in hex proves the key a fixed secret
    ///   proves, and short and non-hex spellings are refused.
    /// - witness: `tests::peer::a_secret_spelled_in_hex_proves_its_key`
    #[inline]
    fn from_str(text: &str) -> Result<Self, PeerError>
    {
        iroh::SecretKey::from_str(&text.to_ascii_lowercase())
            .map(Self)
            .map_err(|refused| PeerError::Key {
                text: String::from(text),
                reason: refused.to_string(),
            })
    }
}

/// The public key a peer is known by: its identity on the network.
///
/// It prints as 64 lowercase hex digits.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[repr(transparent)]
pub struct NodeId(iroh::PublicKey);

impl NodeId
{
    /// The key as iroh holds it.
    ///
    /// # Specification
    /// trivial.
    pub(crate) const fn key(self) -> iroh::PublicKey
    {
        self.0
    }
}

impl From<iroh::PublicKey> for NodeId
{
    /// The identity a connection's remote key names.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(key: iroh::PublicKey) -> Self
    {
        Self(key)
    }
}

impl fmt::Display for NodeId
{
    /// The key as 64 lowercase hex digits.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        fmt::Display::fmt(&self.0, f)
    }
}

impl FromStr for NodeId
{
    type Err = PeerError;

    /// The key spelled as 64 hex digits, or as base32, in either case.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the key whose 32 bytes `text` spells, which prints as `text`
    ///   lowercased when `text` is hex.
    /// - fails: [`PeerError::Key`] for text spelling no 32 bytes, or bytes
    ///   naming no point of the curve.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a key printed and read back is the same key, an
    ///   uppercase spelling reads as its lowercase one, and short and non-hex
    ///   spellings are refused.
    /// - witness: `tests::peer::a_key_reads_back_from_its_spelling`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |id| !text.bytes().all(|byte| byte.is_ascii_hexdigit()) || id.to_string().eq_ignore_ascii_case(text)))]
    #[inline]
    fn from_str(text: &str) -> Result<Self, PeerError>
    {
        iroh::PublicKey::from_str(&text.to_ascii_lowercase())
            .map(Self)
            .map_err(|refused| PeerError::Key {
                text: String::from(text),
                reason: refused.to_string(),
            })
    }
}

/// A peer as a dialer names it: the key it must prove, and the socket
/// addresses the dialer may try for it, in order.
///
/// It is spelled `<key>` followed by `@<address>` for each address, as
/// `1f…e0@127.0.0.1:4000@[::1]:4000`.
#[derive(Clone, Debug)]
pub struct Peer
{
    /// The key the peer must prove.
    id: NodeId,
    /// Where the dialer may look for it.
    addresses: Vec<SocketAddr>,
}

impl Peer
{
    /// The peer `id`, at no address yet.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn new(id: NodeId) -> Self
    {
        Self {
            id,
            addresses: Vec::new(),
        }
    }

    /// The peer, also looked for at `address`, after the addresses it has.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn at(
        mut self,
        address: SocketAddr,
    ) -> Self
    {
        self.addresses.push(address);
        self
    }

    /// The key the peer must prove.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn id(&self) -> NodeId
    {
        self.id
    }

    /// The addresses a dialer may try, in order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn addresses(&self) -> &[SocketAddr]
    {
        &self.addresses
    }

    /// The peer as iroh dials it.
    ///
    /// # Specification
    /// trivial.
    pub(crate) fn endpoint_addr(&self) -> iroh::EndpointAddr
    {
        self.addresses.iter().fold(
            iroh::EndpointAddr::new(self.id.key()),
            |dialed, &address| dialed.with_ip_addr(address),
        )
    }
}

impl fmt::Display for Peer
{
    /// The key, then `@` and each address in order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        write!(f, "{}", self.id)?;
        for address in &self.addresses {
            write!(f, "@{address}")?;
        }
        Ok(())
    }
}

impl FromStr for Peer
{
    type Err = PeerError;

    /// The peer `<key>@<address>…` spells.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the key before the first `@`, and one address after each `@`,
    ///   in order.
    /// - fails: [`PeerError::Key`] for a key [`NodeId`] does not read, and
    ///   [`PeerError::Address`] for an address that is no `ip:port`.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a bare key, a key with an IPv4 and an IPv6 address
    ///   read back from their printing, an empty address and an address with no
    ///   port.
    /// - witness: `tests::peer::a_peer_reads_back_from_its_spelling`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |peer| peer.addresses.len() == text.matches('@').count()))]
    #[inline]
    fn from_str(text: &str) -> Result<Self, PeerError>
    {
        let mut parts = text.split('@');
        let id = NodeId::from_str(parts.next().unwrap_or_default())?;
        let addresses = parts
            .map(|part| {
                SocketAddr::from_str(part).map_err(|refused| PeerError::Address {
                    text: String::from(part),
                    reason: refused.to_string(),
                })
            })
            .collect::<Result<Vec<_>, _>>()?;
        Ok(Self { id, addresses })
    }
}

/// Why a key or a peer's spelling does not read.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum PeerError
{
    /// The text spells no key.
    Key
    {
        /// The text read.
        text: String,
        /// Why it is no key.
        reason: String,
    },
    /// The text after an `@` is no socket address.
    Address
    {
        /// The text read.
        text: String,
        /// Why it is no address.
        reason: String,
    },
}

impl fmt::Display for PeerError
{
    /// The text refused and why.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        match *self {
            Self::Key {
                ref text,
                ref reason,
            } => write!(f, "`{text}` is no key: {reason}"),
            Self::Address {
                ref text,
                ref reason,
            } => write!(f, "`{text}` is no socket address: {reason}"),
        }
    }
}

impl Error for PeerError
{
}
