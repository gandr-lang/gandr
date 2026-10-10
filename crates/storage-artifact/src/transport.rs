//! Durable certificate-step identities and their canonical BLAKE3 framing.
//!
//! The preimage starts with `gandr:transport-step:v1`. Integers are eight-byte
//! big-endian values; byte fields carry an eight-byte length before their
//! contents. A step includes resolved cell content and application position.
//! Build-local labels never enter this framing.

use alloc::boxed::Box;
use alloc::collections::BTreeMap;
use alloc::collections::btree_map::Entry;
use core::fmt;

use anodized::spec;
use gandr_theory_cell_complexes::Cell;
use gandr_theory_cell_complexes::CellId;
use gandr_theory_cell_complexes::CellStore;
use gandr_theory_cell_complexes::Pos;
use gandr_theory_decomposition_spaces::transport::CertificateField;
use gandr_theory_decomposition_spaces::transport::step_fields;
use gandr_theory_deep_inference::PrimCert;
use gandr_theory_deep_inference::PrimMultiplicity;
use gandr_theory_deep_inference::TraceletNf;
use quenchant_shape::shape::Maybe;

/// Domain and version included in every transport-step preimage.
pub const TRANSPORT_STEP_MAGIC: &[u8] = b"gandr:transport-step:v1";
/// The fixed width of a BLAKE3 step identity.
pub const TRANSPORT_STEP_ID_LEN: usize = 32;

/// A refused transport image or canonical integer width.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum StepIdError
{
    /// An identity image has the wrong byte length.
    ImageLength
    {
        /// Offered byte count.
        found: usize,
        /// Required byte count.
        expected: usize,
    },
    /// A count cannot be represented in the canonical u64 width.
    WidthOverflow
    {
        /// The unrepresentable count.
        found: usize,
    },
}

impl fmt::Display for StepIdError
{
    /// Render the refused width.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// Propagates formatter errors.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        match *self {
            | Self::ImageLength { found, expected } => {
                write!(f, "step identity length {found}, expected {expected}")
            },
            | Self::WidthOverflow { found } => write!(f, "step field count {found} exceeds u64"),
        }
    }
}
impl core::error::Error for StepIdError
{
}

/// The integer width admitted by the canonical step framing.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct CanonicalU64(u64);

impl From<u64> for CanonicalU64
{
    /// Wrap an already fixed-width integer.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: u64) -> Self
    {
        Self(value)
    }
}
impl From<CanonicalU64> for u64
{
    /// Recover the integer value.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: CanonicalU64) -> Self
    {
        value.0
    }
}
impl TryFrom<usize> for CanonicalU64
{
    type Error = StepIdError;

    /// Check a target-width count without truncation.
    ///
    /// # Specification
    /// - ensures: success preserves the value exactly.
    /// - fails: `WidthOverflow` when u64 cannot hold the count.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns `WidthOverflow` for an unrepresentable count.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the 32-bit ceiling and its successor distinguish
    ///   narrowing or truncating target-width counts.
    /// - witness: `transport::tests::the_checked_widening_encodes_past_the_32_bit_ceiling`
    #[inline]
    #[spec(ensures: |output| match output {
        Ok(narrow) => usize::try_from(narrow.0) == Ok(value),
        Err(StepIdError::WidthOverflow { found }) => found == value && u64::try_from(value).is_err(),
        Err(StepIdError::ImageLength { .. }) => false,
    })]
    fn try_from(value: usize) -> Result<Self, Self::Error>
    {
        u64::try_from(value)
            .map(Self)
            .map_err(|_overflow| StepIdError::WidthOverflow { found: value })
    }
}

/// Borrowed bytes with a width-checked length.
#[derive(Clone, Copy, Debug)]
pub struct CanonicalBytes<'source>
{
    /// The borrowed content.
    bytes: &'source [u8],
    /// The checked byte count.
    length: CanonicalU64,
}
impl<'source> TryFrom<&'source [u8]> for CanonicalBytes<'source>
{
    type Error = StepIdError;

    /// Check the length once before framing.
    ///
    /// # Specification
    /// - ensures: success retains the bytes and their exact u64 length.
    /// - fails: `WidthOverflow` if the length exceeds u64.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns `WidthOverflow` for an unrepresentable length.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the golden framed preimage separates missing length
    ///   prefixes and altered content.
    /// - witness: `transport::tests::the_identity_is_blake3_of_the_framed_preimage`
    #[inline]
    #[spec(ensures: |output| output.as_ref().map_or_else(
        |_| u64::try_from(bytes.len()).is_err(),
        |field| field.bytes == bytes && usize::try_from(field.length.0) == Ok(bytes.len())))]
    fn try_from(bytes: &'source [u8]) -> Result<Self, Self::Error>
    {
        let length = CanonicalU64::try_from(bytes.len())?;
        Ok(Self { bytes, length })
    }
}

/// A streaming, domain-separated step preimage encoder.
#[repr(transparent)]
#[derive(Clone, Debug)]
pub struct StepIdEncoder
{
    /// Incremental digest state; no preimage allocation is retained.
    hasher: blake3::Hasher,
}
impl StepIdEncoder
{
    /// Start the v1 preimage with its domain separator.
    ///
    /// # Specification
    /// - ensures: the initial digest covers exactly `TRANSPORT_STEP_MAGIC`.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the fixed golden separates altered domains.
    /// - witness: `transport::tests::the_v1_golden_vector_is_stable`
    #[inline]
    #[must_use]
    #[spec(ensures: |output| output.hasher.finalize() == blake3::hash(TRANSPORT_STEP_MAGIC))]
    pub fn begin() -> Self
    {
        let mut hasher = blake3::Hasher::new();
        hasher.update(TRANSPORT_STEP_MAGIC);
        Self { hasher }
    }

    /// Append one fixed-width big-endian integer.
    ///
    /// # Specification
    /// - ensures: exactly eight bytes are appended, most significant first.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the independent preimage fixes width and byte order.
    /// - witness: `transport::tests::the_identity_is_blake3_of_the_framed_preimage`
    #[inline]
    #[expect(
        clippy::big_endian_bytes,
        reason = "the v1 transport format pins big-endian u64 fields"
    )]
    #[spec(captures: expected = { let mut hash = self.hasher.clone(); hash.update(&value.0.to_be_bytes()); hash.finalize() }, ensures: self.hasher.finalize() == expected)]
    pub fn put_u64(
        &mut self,
        value: CanonicalU64,
    )
    {
        self.hasher.update(&value.0.to_be_bytes());
    }

    /// Append a checked length and its byte field.
    ///
    /// # Specification
    /// - ensures: the big-endian u64 length precedes the unchanged bytes.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the independent preimage fixes field framing.
    /// - witness: `transport::tests::the_identity_is_blake3_of_the_framed_preimage`
    #[inline]
    #[expect(
        clippy::big_endian_bytes,
        reason = "the v1 byte length prefix is big-endian"
    )]
    #[spec(captures: expected = { let mut hash = self.hasher.clone(); hash.update(&value.length.0.to_be_bytes()); hash.update(value.bytes); hash.finalize() }, ensures: self.hasher.finalize() == expected)]
    pub fn put_bytes(
        &mut self,
        value: CanonicalBytes<'_>,
    )
    {
        self.put_u64(value.length);
        self.hasher.update(value.bytes);
    }

    /// Finish the digest without retaining the preimage.
    ///
    /// # Specification
    /// - ensures: returns all 32 BLAKE3 output bytes, without truncation.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — a pinned golden and independent preimage distinguish
    ///   digest substitution or truncation.
    /// - witness: `transport::tests::the_v1_golden_vector_is_stable`
    /// - witness: `transport::tests::the_identity_is_blake3_of_the_framed_preimage`
    #[inline]
    #[must_use]
    #[spec(captures: expected = *self.hasher.finalize().as_bytes(), ensures: |output| output.0 == expected)]
    pub fn finish(self) -> TransportStepId
    {
        TransportStepId(*self.hasher.finalize().as_bytes())
    }
}

/// A durable step digest, nominally distinct from build-local primitive labels.
///
/// ```compile_fail,E0308
/// use gandr_storage_artifact::transport::TransportStepId;
/// use gandr_theory_deep_inference::PrimId;
/// let local: PrimId = TransportStepId::from([0_u8; 32]);
/// ```
///
/// ```compile_fail,E0277
/// use gandr_storage_artifact::transport::TransportStepId;
/// use gandr_theory_deep_inference::PrimId;
/// fn persist(local: PrimId) -> TransportStepId { local.into() }
/// ```
#[repr(transparent)]
#[derive(Clone, Copy, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct TransportStepId([u8; TRANSPORT_STEP_ID_LEN]);
impl From<[u8; TRANSPORT_STEP_ID_LEN]> for TransportStepId
{
    /// Ingest a fixed-width digest image.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(bytes: [u8; TRANSPORT_STEP_ID_LEN]) -> Self
    {
        Self(bytes)
    }
}
impl TryFrom<&[u8]> for TransportStepId
{
    type Error = StepIdError;

    /// Ingest exactly 32 bytes, refusing every other width.
    ///
    /// # Specification
    /// - ensures: success preserves every byte.
    /// - fails: `ImageLength` reports offered and required widths.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns `ImageLength` unless the image contains 32 bytes.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — zero, local-label width, and adjacent widths refuse;
    ///   a golden identity survives readback byte for byte.
    /// - witness: `transport::tests::ingest_refuses_anything_but_the_fixed_width`
    /// - witness: `transport::tests::an_identity_round_trips_through_its_byte_image`
    #[inline]
    #[spec(ensures: |output| match output {
        Ok(id) => id.0.as_slice() == image,
        Err(StepIdError::ImageLength { found, expected }) => found == image.len() && expected == TRANSPORT_STEP_ID_LEN && found != expected,
        Err(StepIdError::WidthOverflow { .. }) => false,
    })]
    fn try_from(image: &[u8]) -> Result<Self, Self::Error>
    {
        <[u8; TRANSPORT_STEP_ID_LEN]>::try_from(image)
            .map(Self)
            .map_err(|_length| StepIdError::ImageLength {
                found: image.len(),
                expected: TRANSPORT_STEP_ID_LEN,
            })
    }
}
impl AsRef<[u8]> for TransportStepId
{
    /// Borrow the digest bytes.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn as_ref(&self) -> &[u8]
    {
        &self.0
    }
}
impl fmt::Debug for TransportStepId
{
    /// Display the hexadecimal identity.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// Propagates formatter errors.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        fmt::Display::fmt(self, f)
    }
}
impl fmt::Display for TransportStepId
{
    /// Display all digest bytes as lowercase hexadecimal.
    ///
    /// # Specification
    /// - ensures: two lowercase hexadecimal digits per byte, in byte order.
    /// - fails: propagates formatter errors.
    /// - panics: none.
    /// - executable: none — the formatter exposes no output buffer.
    ///
    /// # Errors
    /// Propagates formatter errors.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the golden string distinguishes padding, case and
    ///   order.
    /// - witness: `transport::tests::the_v1_golden_vector_is_stable`
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

/// Canonically frame and hash one resolved sequent cell at its position.
///
/// # Specification
/// - ensures: hashes the v1 domain followed by every structural field from
///   `step_fields`; integers use checked u64 widths and names use byte lengths.
/// - fails: `WidthOverflow` for unrepresentable lengths or position indices.
/// - panics: none.
///
/// The executable predicate checks field-width admission; golden bytes
/// independently witness field order and the resulting digest.
///
/// # Errors
/// Returns `WidthOverflow` when a field does not fit u64.
///
/// # Adequacy
/// - hypothesis: L2 — the pinned frame golden fixes framing and field order;
///   rebuilt cells and permuted stores preserve identity. L3 — position and
///   content perturbations separate omitted fields.
/// - witness: `certificate_transport::tests::the_v1_golden_step_identity_is_stable`
/// - witness: `certificate_transport::tests::an_independently_rebuilt_cell_mints_the_same_identity`
/// - witness: `certificate_transport::tests::the_identity_reads_the_position`
/// - witness: `certificate_transport::tests::the_identity_reads_the_cell_content`
/// - witness: `certificate_transport::tests::the_identity_is_stable_across_store_insertion_orders`
/// - witness: `certificate_transport::tests::every_orientation_provenance_and_polarity_is_bound`
#[inline]
#[spec(ensures: |output| output.is_ok() == step_fields(cell, at).all(|field| match field {
    CertificateField::Tag(_) => true,
    CertificateField::Count(count) => u64::try_from(count).is_ok(),
    CertificateField::Bytes(bytes) => u64::try_from(bytes.len()).is_ok(),
}))]
pub fn transport_step_id(
    cell: &Cell,
    at: &Pos,
) -> Result<TransportStepId, StepIdError>
{
    let mut encoder = StepIdEncoder::begin();
    for field in step_fields(cell, at) {
        match field {
            | CertificateField::Tag(tag) => encoder.put_u64(CanonicalU64::from(tag)),
            | CertificateField::Count(count) => {
                let count = CanonicalU64::try_from(count)?;
                encoder.put_u64(count);
            },
            | CertificateField::Bytes(bytes) => {
                let bytes = CanonicalBytes::try_from(bytes)?;
                encoder.put_bytes(bytes);
            },
        }
    }
    Ok(encoder.finish())
}

/// A refused resolution, encoding or collision at the transport boundary.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum TransportStepObstruction
{
    /// A factor names a cell absent from the supplied store.
    UnknownCell
    {
        /// The unresolved local handle.
        cell: CellId,
    },
    /// A structural field exceeded the canonical width.
    Encoding(StepIdError),
    /// One digest was offered for distinct recorded factors.
    ContentAddressCollision
    {
        /// The contested digest.
        address: TransportStepId,
        /// The factor already held.
        held: Box<PrimCert>,
        /// The incompatible offered factor.
        offered: Box<PrimCert>,
    },
}
impl fmt::Display for TransportStepObstruction
{
    /// Render the transport refusal.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// Propagates formatter errors.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        match *self {
            | Self::UnknownCell { cell } => {
                write!(f, "unknown certificate cell {}", usize::from(cell))
            },
            | Self::Encoding(ref error) => fmt::Display::fmt(error, f),
            | Self::ContentAddressCollision { address, .. } => {
                write!(f, "distinct certificate factors at {address}")
            },
        }
    }
}
impl core::error::Error for TransportStepObstruction
{
}
impl From<StepIdError> for TransportStepObstruction
{
    /// Retain an encoding refusal at the index boundary.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(error: StepIdError) -> Self
    {
        Self::Encoding(error)
    }
}

/// A graded factorization keyed by durable step identity.
#[repr(transparent)]
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct TransportStepIndex
{
    /// Stored factors, retaining their local replay handles and multiplicities.
    entries: BTreeMap<TransportStepId, (PrimCert, PrimMultiplicity)>,
}
impl TransportStepIndex
{
    /// Borrow the graded factors in digest order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn entries(&self) -> &BTreeMap<TransportStepId, (PrimCert, PrimMultiplicity)>
    {
        &self.entries
    }

    /// Insert a graded factor, refusing a conflicting recorded primitive.
    ///
    /// # Specification
    /// - ensures: a vacant identity receives the factor; an equal factor sums
    ///   multiplicities with u32 saturation, matching normal-form grading.
    /// - fails: a different factor at an occupied identity leaves it unchanged.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns `ContentAddressCollision` for unequal factors at one identity.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — occupied slots distinguish equal-content addition,
    ///   saturation and refusal without mutation.
    /// - witness: `transport::tests::a_shared_identity_with_distinct_content_is_refused`
    /// - witness: `transport::tests::a_shared_identity_with_equal_content_sums_the_grading`
    #[inline]
    #[spec(captures: before = (self.entries.get(&address).cloned(), cert.clone()), ensures: |output| match before.0 {
        None => output.is_ok() && self.entries.get(&address) == Some(&(before.1.clone(), multiplicity)),
        Some((ref held, count)) => match output {
            Ok(()) => held == &before.1 && self.entries.get(&address).is_some_and(|graded| &graded.0 == held && u32::from(graded.1) == u32::from(count).saturating_add(u32::from(multiplicity))),
            Err(TransportStepObstruction::ContentAddressCollision { address: conflict, held: ref retained, ref offered }) => held != &before.1 && conflict == address && retained.as_ref() == held && offered.as_ref() == &before.1 && self.entries.get(&address) == Some(&(held.clone(), count)),
            Err(_) => false,
        },
    })]
    fn insert(
        &mut self,
        address: TransportStepId,
        cert: PrimCert,
        multiplicity: PrimMultiplicity,
    ) -> Result<(), TransportStepObstruction>
    {
        match self.entries.entry(address) {
            | Entry::Vacant(slot) => {
                slot.insert((cert, multiplicity));
                Ok(())
            },
            | Entry::Occupied(mut slot) => {
                let graded = slot.get_mut();
                if graded.0 != cert {
                    return Err(TransportStepObstruction::ContentAddressCollision {
                        address,
                        held: Box::new(graded.0.clone()),
                        offered: Box::new(cert),
                    });
                }
                graded.1 = PrimMultiplicity::from(
                    u32::from(graded.1).saturating_add(u32::from(multiplicity)),
                );
                Ok(())
            },
        }
    }
}

/// Resolve and re-key every normal-form factor under its durable identity.
///
/// # Specification
/// - ensures: each resolved factor and its grading survives under the hash of
///   its cell content and position; conflicting primitives are never merged.
/// - fails: an absent cell, width overflow or conflicting digest refuses the
///   entire index; no partial index is returned.
/// - panics: none.
///
/// # Errors
/// Returns `UnknownCell`, `Encoding` or `ContentAddressCollision`.
///
/// # Adequacy
/// - hypothesis: L2 — repeated normalization preserves the index and distinct
///   derivations keep distinct factorizations. L3 — exact graded entries and an
///   unresolved store distinguish lost factors and fabricated resolution.
/// - witness: `certificate_transport::tests::the_index_preserves_the_graded_factorization`
/// - witness: `certificate_transport::tests::the_index_is_deterministic_across_repeated_normalization`
/// - witness: `certificate_transport::tests::distinct_factorizations_index_distinctly`
/// - witness: `certificate_transport::tests::the_index_refuses_an_unresolved_cell`
#[inline]
#[spec(ensures: |output| output.as_ref().map_or(true, |index| normal_form.primitives.values().all(|graded|
    index.entries.values().any(|held| held.0 == graded.0 && held.1 >= graded.1))))]
pub fn transport_step_index(
    normal_form: &TraceletNf,
    store: &CellStore,
) -> Result<TransportStepIndex, TransportStepObstruction>
{
    let mut index = TransportStepIndex::default();
    for &(ref cert, multiplicity) in normal_form.primitives.values() {
        let step = cert.step();
        let Maybe::Present(cell) = store.get(step.cell)
        else {
            return Err(TransportStepObstruction::UnknownCell { cell: step.cell });
        };
        let address = transport_step_id(cell, &step.at)?;
        index.insert(address, cert.clone(), multiplicity)?;
    }
    Ok(index)
}

#[cfg(test)]
mod tests;
