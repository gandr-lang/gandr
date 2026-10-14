//! The store manifest: what names a committed store, as a byte image and a
//! root.
//!
//! # The image
//!
//! ```text
//! image := "gandr:storage-schema:store:v1"
//!       || u16le manifest version
//!       || 32-byte schema identity
//!       || u64le commitment length || boundary commitment
//!       || u64le table count
//!       || table*                       one per object, in ordinal order
//! table := u64le next key || u64le record count || 32-byte root node identity
//! root  := BLAKE3(image)
//! ```
//!
//! **Choice.** One root per store: the manifest binds the schema identity,
//! the record plane's boundary commitment and, per table, the counter, the
//! record count and the root node identity, and the store's root is BLAKE3 of
//! that image. A proof carries the manifest beside the record plane's proof,
//! so a verifier holding only the root authenticates both. The counter is
//! committed so a store reopened from its manifest never mints a key it
//! minted before. The layout follows the artifact and value manifests:
//! domain inside the hashed bytes, fixed-width little-endian integers, the
//! boundary commitment carried opaque.
//!
//! **Alternatives.** One record tree for the whole store, with the table in
//! every key, would make the tree's own root the store's root and drop the
//! manifest from proofs; it would also rebuild every table's leaves on any
//! edit to one, and lose the per-table root a reader can open alone. Binding
//! each table's `TreeRoot` digest instead of its root node identity would
//! leave a reader nothing to load the table by. **Reversal.** A record plane
//! with incremental edits and multi-level trees makes the single tree's
//! rebuild cost local, and with it the one-tree layout the simpler choice.

use alloc::boxed::Box;
use alloc::vec::Vec;
use core::fmt;

use anodized::spec;
use gandr_storage_records::NodeHash;
use gandr_storage_records::ProfileCommitment;
use gandr_storage_records::RecordCount;
use gandr_storage_records::RecordTree;
use gandr_storage_records::TreeParams;
use gandr_storage_records::TreeRoot;

use crate::error::ManifestFault;
use crate::error::StoreError;
use crate::parts::PartKey;
use crate::schema::ObjectId;
use crate::schema::Schema;
use crate::schema::SchemaIdentity;

/// The domain every store manifest image opens with, inside the hashed
/// preimage.
pub const MANIFEST_DOMAIN: &[u8] = b"gandr:storage-schema:store:v1";

/// The manifest layout this crate writes and reads.
const MANIFEST_VERSION: u16 = 1_u16;

/// The byte length of a [`StoreRoot`]: one BLAKE3 output.
pub const STORE_ROOT_LEN: usize = 0x20_usize;

/// The root of a committed store: BLAKE3 of its manifest image.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct StoreRoot([u8; STORE_ROOT_LEN]);

impl From<[u8; STORE_ROOT_LEN]> for StoreRoot
{
    /// Wraps digest bytes; nothing checks that they hash a manifest.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(bytes: [u8; STORE_ROOT_LEN]) -> Self
    {
        Self(bytes)
    }
}

impl AsRef<[u8]> for StoreRoot
{
    /// Borrows the digest bytes.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn as_ref(&self) -> &[u8]
    {
        self.0.as_slice()
    }
}

impl fmt::Display for StoreRoot
{
    /// Writes the root as lowercase hexadecimal.
    ///
    /// # Specification
    /// - ensures: writes two lowercase hexadecimal digits per byte, in byte
    ///   order, and nothing else.
    /// - fails: propagates the formatter's write failure unchanged.
    /// - panics: none.
    /// - executable: none — the formatter exposes no readable output buffer.
    ///
    /// # Errors
    /// Propagates the formatter's write failure.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a root-mismatch refusal renders both roots in full.
    /// - witness: `tests::proofs::a_proof_against_another_root_is_refused`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        for byte in self.0 {
            write!(f, "{byte:02x}")?;
        }

        Ok(())
    }
}

/// One table's committed tree, as the manifest binds it.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct TableRoot
{
    /// The next key the table's counter mints.
    next: PartKey,
    /// How many records the table's tree holds.
    records: RecordCount,
    /// The identity of the tree's root node.
    root_node: NodeHash,
}

impl TableRoot
{
    /// The next key the table's counter mints.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn next(&self) -> PartKey
    {
        self.next
    }

    /// How many records the table's tree holds.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn records(&self) -> RecordCount
    {
        self.records
    }

    /// The identity of the table tree's root node.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn root_node(&self) -> NodeHash
    {
        self.root_node
    }
}

/// A store manifest image, borrowed.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ManifestImage<'image>(&'image [u8]);

impl<'image> From<&'image [u8]> for ManifestImage<'image>
{
    /// Reads bytes as a candidate image; [`StoreManifest::decode`] decides.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(bytes: &'image [u8]) -> Self
    {
        Self(bytes)
    }
}

impl AsRef<[u8]> for ManifestImage<'_>
{
    /// Borrows the image bytes.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn as_ref(&self) -> &[u8]
    {
        self.0
    }
}

/// A store manifest image, owned.
#[repr(transparent)]
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ManifestImageBuf(Box<[u8]>);

impl AsRef<[u8]> for ManifestImageBuf
{
    /// Borrows the image bytes.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn as_ref(&self) -> &[u8]
    {
        &self.0
    }
}

/// What names a committed store.
///
/// # Specification
/// - requires: construction by a commit or [`StoreManifest::decode`].
/// - ensures: the root is BLAKE3 of the image; the image is the layout the
///   module documentation states.
/// - provides: the root, each table's tree root, and the reader's checks.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L2/L3 — a hand-built golden image pins the layout and its
///   BLAKE3; it round-trips through decode; each malformed field is refused by
///   name; a change to any field changes the root.
/// - witness: `manifest::tests::the_image_is_golden_and_round_trips`
/// - witness: `manifest::tests::a_malformed_manifest_is_refused_by_field`
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct StoreManifest
{
    /// The schema the store is of.
    schema: SchemaIdentity,
    /// The record plane's boundary commitment every table was built under.
    commitment: ProfileCommitment,
    /// Each table, in object order.
    tables: Box<[TableRoot]>,
    /// BLAKE3 of the image.
    root: StoreRoot,
}

impl StoreManifest
{
    /// The manifest over one tree per table.
    ///
    /// # Specification
    /// - requires: `tables` yields one counter and tree per object of `schema`,
    ///   in object order, built under `params`.
    /// - ensures: on success the manifest binds the schema, the boundary
    ///   commitment and each table's counter, record count and root node.
    /// - fails: never in practice; the signature carries the record plane's
    ///   refusal for symmetry with decode.
    /// - panics: none.
    ///
    /// # Errors
    /// [`StoreError::Records`] is reserved for the record plane.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — a committed store's manifest equals the decode of its
    ///   own image.
    /// - witness: `tests::keyed::the_fixture_round_trips_through_the_block_store`
    #[inline]
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |manifest| manifest.schema == schema.identity()))]
    pub(crate) fn over<'tree, I>(
        schema: &Schema,
        params: TreeParams,
        tables: I,
    ) -> Result<Self, StoreError>
    where
        I: IntoIterator<Item = (PartKey, &'tree RecordTree)>,
    {
        let tables = tables
            .into_iter()
            .map(|(next, tree)| TableRoot {
                next,
                records: tree.root().record_count(),
                root_node: tree.root_node_hash(),
            })
            .collect();
        Ok(Self::sealed(
            schema.identity(),
            params.boundary_commitment(),
            tables,
        ))
    }

    /// Seals the fields, computing the root.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn sealed(
        schema: SchemaIdentity,
        commitment: ProfileCommitment,
        tables: Box<[TableRoot]>,
    ) -> Self
    {
        let mut manifest = Self {
            schema,
            commitment,
            tables,
            root: StoreRoot([0_u8; STORE_ROOT_LEN]),
        };
        manifest.root = StoreRoot(*blake3::hash(&manifest.encode().0).as_bytes());
        manifest
    }

    /// The canonical image.
    ///
    /// # Specification
    /// - ensures: the bytes are the layout the module documentation states.
    /// - panics: none.
    /// - executable: none — the layout's independent statement is the pinned
    ///   golden.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — against a hand-built golden image.
    /// - witness: `manifest::tests::the_image_is_golden_and_round_trips`
    #[inline]
    #[must_use]
    pub fn encode(&self) -> ManifestImageBuf
    {
        let commitment: &[u8] = self.commitment.as_ref();
        let mut image = Vec::with_capacity(
            MANIFEST_DOMAIN
                .len()
                .saturating_add(commitment.len())
                .saturating_add(self.tables.len().saturating_mul(48_usize))
                .saturating_add(58_usize),
        );
        image.extend_from_slice(MANIFEST_DOMAIN);
        image.extend_from_slice(&MANIFEST_VERSION.to_le_bytes());
        image.extend_from_slice(self.schema.as_ref());
        // A commitment and a table list are held in memory, so their lengths
        // fit sixty-four bits on every supported target.
        let commitment_length = u64::try_from(commitment.len()).unwrap_or(u64::MAX);
        image.extend_from_slice(&commitment_length.to_le_bytes());
        image.extend_from_slice(commitment);
        let table_count = u64::try_from(self.tables.len()).unwrap_or(u64::MAX);
        image.extend_from_slice(&table_count.to_le_bytes());
        for table in &self.tables {
            image.extend_from_slice(&u64::from(table.next).to_le_bytes());
            image.extend_from_slice(&u64::from(table.records).to_le_bytes());
            image.extend_from_slice(table.root_node.as_ref());
        }
        ManifestImageBuf(image.into_boxed_slice())
    }

    /// Reads a manifest back from its image.
    ///
    /// # Specification
    /// - requires: nothing; any bytes are admitted as input.
    /// - ensures: on success the manifest's image equals `image` byte for byte.
    /// - fails: [`StoreError::Manifest`] naming the first field, in image
    ///   order, that is foreign, unknown or cut short, then trailing bytes.
    /// - panics: none.
    ///
    /// # Errors
    /// [`StoreError::Manifest`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the golden round-trips; a changed domain, an unknown
    ///   version, every proper prefix and a trailing byte are each refused with
    ///   their fault.
    /// - witness: `manifest::tests::the_image_is_golden_and_round_trips`
    /// - witness: `manifest::tests::a_malformed_manifest_is_refused_by_field`
    #[inline]
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |manifest| manifest.encode().as_ref() == image.as_ref()))]
    pub fn decode(image: ManifestImage<'_>) -> Result<Self, StoreError>
    {
        let mut cursor = Cursor(image.0);
        let Some(rest) = cursor.0.strip_prefix(MANIFEST_DOMAIN)
        else {
            return Err(fault(ManifestFault::Domain));
        };
        cursor.0 = rest;

        let version = cursor.chunk::<2>()?;
        if u16::from_le_bytes(version.0) != MANIFEST_VERSION {
            return Err(fault(ManifestFault::Version));
        }
        let schema = cursor.chunk::<32>()?;
        let schema = SchemaIdentity::from(schema.0);
        let commitment_length = cursor.length()?;
        let Some((commitment, rest)) = cursor.0.split_at_checked(commitment_length.0)
        else {
            return Err(fault(ManifestFault::Truncated));
        };
        cursor.0 = rest;
        let commitment = ProfileCommitment::from(Vec::from(commitment));

        let table_count = cursor.length()?;
        let mut tables = Vec::new();
        for _table in 0_usize .. table_count.0 {
            let next = cursor.chunk::<8>()?;
            let records = cursor.chunk::<8>()?;
            let root_node = cursor.chunk::<32>()?;
            tables.push(TableRoot {
                next: PartKey::from(u64::from_le_bytes(next.0)),
                records: RecordCount(u64::from_le_bytes(records.0)),
                root_node: NodeHash::from(root_node.0),
            });
        }
        if !cursor.0.is_empty() {
            return Err(fault(ManifestFault::Trailing));
        }

        Ok(Self::sealed(schema, commitment, tables.into_boxed_slice()))
    }

    /// The root: BLAKE3 of the image.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn identity(&self) -> StoreRoot
    {
        self.root
    }

    /// The schema the store is of.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn schema(&self) -> SchemaIdentity
    {
        self.schema
    }

    /// Each table, in object order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn tables(&self) -> &[TableRoot]
    {
        &self.tables
    }

    /// Refuses a reader that does not share the manifest's schema, boundary
    /// parameters or table count.
    ///
    /// # Specification
    /// - ensures: success exactly when the schema identity, the boundary
    ///   commitment and the table count all match.
    /// - fails: [`StoreError::SchemaMismatch`], then
    ///   [`StoreError::ProfileMismatch`], then [`StoreError::TableCount`].
    /// - panics: none.
    ///
    /// # Errors
    /// As above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a proof checked under another schema, and a store
    ///   reopened under other parameters, are refused by name.
    /// - witness: `tests::proofs::a_proof_under_another_schema_is_refused`
    #[inline]
    #[spec(ensures: |ret| ret.is_err() || self.schema == schema.identity())]
    pub(crate) fn ensure_reader(
        &self,
        schema: &Schema,
        params: TreeParams,
    ) -> Result<(), StoreError>
    {
        if self.schema != schema.identity() {
            return Err(StoreError::SchemaMismatch {
                expected: schema.identity(),
                found: self.schema,
            });
        }
        if self.commitment != params.boundary_commitment() {
            return Err(StoreError::ProfileMismatch);
        }
        if self.tables.len() != usize::from(schema.object_count()) {
            return Err(StoreError::TableCount);
        }
        Ok(())
    }

    /// One table's tree root under the reader's parameters.
    ///
    /// # Specification
    /// - requires: [`StoreManifest::ensure_reader`] passed for `params`.
    /// - ensures: on success the record plane's root over the table's record
    ///   count and root node.
    /// - fails: [`StoreError::TableCount`] for an object past the tables, and
    ///   [`StoreError::Records`] for the record plane's refusal to seal.
    /// - panics: none.
    ///
    /// # Errors
    /// As above.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — every proof verifies through the table root this
    ///   recomputes; a substituted manifest changes the store root first.
    /// - witness: `tests::proofs::every_kind_of_proof_verifies_against_the_root`
    #[inline]
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |root| root.record_count() == self.tables.get(usize::from(object)).map_or(RecordCount(0), |table| table.records)))]
    pub(crate) fn tree_root(
        &self,
        object: ObjectId,
        params: TreeParams,
    ) -> Result<TreeRoot, StoreError>
    {
        let table = self
            .tables
            .get(usize::from(object))
            .ok_or(StoreError::TableCount)?;
        Ok(TreeRoot::seal(params, table.records, table.root_node)?)
    }
}

/// The manifest-fault refusal.
///
/// # Specification
/// trivial.
#[inline]
const fn fault(fault: ManifestFault) -> StoreError
{
    StoreError::Manifest { fault }
}

/// A length read from a manifest.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Length(usize);

/// A read position in a manifest image.
#[repr(transparent)]
struct Cursor<'image>(&'image [u8]);

impl Cursor<'_>
{
    /// Consumes a fixed-width field.
    ///
    /// # Specification
    /// - ensures: on success the next `WIDTH` bytes, consumed.
    /// - fails: [`ManifestFault::Truncated`] when fewer remain.
    /// - panics: none.
    /// - executable: none — the value is the decoding itself; the golden round
    ///   trip is its independent observation.
    ///
    /// # Errors
    /// [`StoreError::Manifest`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — every proper prefix of the golden is refused as
    ///   truncated.
    /// - witness: `manifest::tests::a_malformed_manifest_is_refused_by_field`
    #[inline]
    fn chunk<const WIDTH: usize>(&mut self) -> Result<Field<WIDTH>, StoreError>
    {
        let (bytes, rest) = self
            .0
            .split_first_chunk::<WIDTH>()
            .ok_or(fault(ManifestFault::Truncated))?;
        self.0 = rest;
        Ok(Field(*bytes))
    }

    /// Consumes a `u64le` length that this target can hold.
    ///
    /// # Specification
    /// - ensures: on success the length the eight bytes state.
    /// - fails: [`ManifestFault::Truncated`] when fewer remain or the length
    ///   exceeds this target's `usize`.
    /// - panics: none.
    /// - executable: none — the value is the decoding itself; the golden round
    ///   trip is its independent observation.
    ///
    /// # Errors
    /// [`StoreError::Manifest`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the golden's commitment and table counts decode; a
    ///   prefix ending inside either is refused.
    /// - witness: `manifest::tests::a_malformed_manifest_is_refused_by_field`
    #[inline]
    fn length(&mut self) -> Result<Length, StoreError>
    {
        let bytes = self.chunk::<8>()?;
        usize::try_from(u64::from_le_bytes(bytes.0))
            .map(Length)
            .map_err(|_overflow| fault(ManifestFault::Truncated))
    }
}

/// The fixed-width bytes of one manifest field.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Field<const WIDTH: usize>([u8; WIDTH]);

#[cfg(test)]
mod tests
{
    use alloc::vec::Vec;

    use gandr_storage_records::NodeHash;
    use gandr_storage_records::ProfileCommitment;
    use gandr_storage_records::RecordCount;

    use super::ManifestImage;
    use super::ManifestImageBuf;
    use super::StoreManifest;
    use super::TableRoot;
    use crate::error::ManifestFault;
    use crate::error::StoreError;
    use crate::parts::PartKey;
    use crate::schema::SchemaIdentity;

    /// A manifest with a three-byte commitment and two tables.
    ///
    /// # Specification
    /// trivial.
    fn golden() -> StoreManifest
    {
        StoreManifest::sealed(
            SchemaIdentity::from([0x11_u8; 32]),
            ProfileCommitment::from(Vec::from([0xc1_u8, 0xc2, 0xc3])),
            Vec::from([
                TableRoot {
                    next: PartKey::from(3_u64),
                    records: RecordCount(7),
                    root_node: NodeHash::from([0xaa_u8; 32]),
                },
                TableRoot {
                    next: PartKey::from(0x0102_u64),
                    records: RecordCount(0),
                    root_node: NodeHash::from([0xbb_u8; 32]),
                },
            ])
            .into_boxed_slice(),
        )
    }

    /// The golden image, written out field by field.
    ///
    /// # Specification
    /// trivial.
    fn golden_image() -> ManifestImageBuf
    {
        let mut image = Vec::from(&b"gandr:storage-schema:store:v1"[..]);
        image.extend_from_slice(&[0x01, 0x00]);
        image.extend_from_slice(&[0x11; 32]);
        image.extend_from_slice(&[0x03, 0, 0, 0, 0, 0, 0, 0]);
        image.extend_from_slice(&[0xc1, 0xc2, 0xc3]);
        image.extend_from_slice(&[0x02, 0, 0, 0, 0, 0, 0, 0]);
        image.extend_from_slice(&[0x03, 0, 0, 0, 0, 0, 0, 0]);
        image.extend_from_slice(&[0x07, 0, 0, 0, 0, 0, 0, 0]);
        image.extend_from_slice(&[0xaa; 32]);
        image.extend_from_slice(&[0x02, 0x01, 0, 0, 0, 0, 0, 0]);
        image.extend_from_slice(&[0x00, 0, 0, 0, 0, 0, 0, 0]);
        image.extend_from_slice(&[0xbb; 32]);
        ManifestImageBuf(image.into_boxed_slice())
    }

    #[test]
    fn the_image_is_golden_and_round_trips()
    {
        let manifest = golden();
        let image = golden_image().as_ref().to_vec();
        assert_eq!(
            manifest.encode().as_ref(),
            image.as_slice(),
            "the layout is the golden"
        );
        assert_eq!(
            manifest.identity().as_ref(),
            blake3::hash(&image).as_bytes(),
            "the root is BLAKE3 of the image"
        );
        let decoded = StoreManifest::decode(ManifestImage::from(image.as_slice()))
            .expect("the golden decodes");
        assert_eq!(decoded, manifest, "the golden round-trips");

        let mut perturbed = image;
        if let Some(byte) = perturbed.last_mut() {
            *byte ^= 0x01;
        }
        let other = StoreManifest::decode(ManifestImage::from(perturbed.as_slice()))
            .expect("a perturbed root node decodes");
        assert_ne!(
            other.identity(),
            manifest.identity(),
            "a changed field changes the root"
        );
    }

    #[test]
    fn a_malformed_manifest_is_refused_by_field()
    {
        let image = golden_image().as_ref().to_vec();
        let refusal = |bytes: &[u8]| StoreManifest::decode(ManifestImage::from(bytes)).err();

        let mut domain = image.clone();
        if let Some(byte) = domain.get_mut(5) {
            *byte = b'X';
        }
        assert_eq!(
            refusal(&domain),
            Some(StoreError::Manifest {
                fault: ManifestFault::Domain
            }),
            "the domain"
        );

        let mut version = image.clone();
        if let Some(byte) = version.get_mut(29) {
            *byte = 0x02;
        }
        assert_eq!(
            refusal(&version),
            Some(StoreError::Manifest {
                fault: ManifestFault::Version
            }),
            "the version"
        );

        for length in 29 .. image.len() {
            assert_eq!(
                refusal(image.get(.. length).expect("a prefix")),
                Some(StoreError::Manifest {
                    fault: ManifestFault::Truncated
                }),
                "the prefix of {length} bytes"
            );
        }

        let mut trailing = image;
        trailing.push(0x00);
        assert_eq!(
            refusal(&trailing),
            Some(StoreError::Manifest {
                fault: ManifestFault::Trailing
            }),
            "a trailing byte"
        );

        let faults = [
            ManifestFault::Domain,
            ManifestFault::Version,
            ManifestFault::Truncated,
            ManifestFault::Trailing,
        ];
        let rendered: Vec<alloc::string::String> = faults
            .iter()
            .map(alloc::string::ToString::to_string)
            .collect();
        for (index, phrase) in rendered.iter().enumerate() {
            assert!(
                rendered
                    .iter()
                    .skip(index.saturating_add(1))
                    .all(|other| other != phrase),
                "each fault renders apart"
            );
        }
    }
}
