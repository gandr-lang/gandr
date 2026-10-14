//! The crate's refusal vocabularies: [`Refusal`] for reads and edits,
//! [`StoreError`] for commits, reopening and proofs.

use core::fmt;

use gandr_storage_records::RecordTreeError;

use crate::manifest::StoreRoot;
use crate::parts::PartKey;
use crate::schema::Name;
use crate::schema::SchemaError;
use crate::schema::SchemaIdentity;

/// Every way a read or an edit is refused, each by name.
///
/// A refusal names the schema elements and the parts it concerns, so its
/// message stands on its own. An edit refused at any step changes nothing.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Refusal
{
    /// An identifier does not name an element of the store's schema.
    Schema(SchemaError),
    /// A reference names a part that is not live.
    NotLive
    {
        /// The table the part would be in.
        object: Name,
        /// The key.
        part: PartKey,
    },
    /// A delete would leave a live part referring to the deleted one.
    Referenced
    {
        /// The table of the part being deleted.
        object: Name,
        /// The part being deleted.
        part: PartKey,
        /// The arrow that refers to it.
        arrow: Name,
        /// The live part whose arrow refers to it.
        by: PartKey,
    },
    /// An edit closes with a live part whose arrow or attribute was never
    /// set.
    Unset
    {
        /// The arrow or attribute.
        field: Name,
        /// The part's table.
        object: Name,
        /// The part.
        part: PartKey,
    },
    /// An edit closes with a part whose two sides of an equation disagree.
    EquationViolated
    {
        /// The equation.
        equation: Name,
        /// The table the equation's paths leave.
        object: Name,
        /// The part the paths leave from.
        part: PartKey,
        /// Where the left side reaches.
        left: PartKey,
        /// Where the right side reaches.
        right: PartKey,
    },
    /// A preimage was asked of a column whose inverse is not kept.
    NotIndexed
    {
        /// The arrow or attribute.
        field: Name,
    },
    /// A row names an arrow or attribute that does not leave its table.
    ForeignField
    {
        /// The arrow or attribute.
        field: Name,
        /// The table the row is for.
        object: Name,
    },
    /// A table's counter has minted its last key.
    Exhausted
    {
        /// The table.
        object: Name,
    },
}

impl fmt::Display for Refusal
{
    /// Writes the refusal with every name and key it carries.
    ///
    /// # Specification
    /// - ensures: writes one line naming the refusal, its elements and its
    ///   parts.
    /// - fails: propagates the formatter's write failure unchanged.
    /// - panics: none.
    /// - executable: none — the formatter exposes no readable output buffer.
    ///
    /// # Errors
    /// Propagates the formatter's write failure.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the defect refusal renders the vertex object, both
    ///   keys and the arrow; the equation refusal renders the equation's name.
    /// - witness: `tests::defect::deleting_the_middle_vertex_refuses_by_name`
    /// - witness: `tests::equations::a_loop_that_leaves_its_vertex_is_refused_by_equation`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        match *self {
            | Self::Schema(ref error) => write!(f, "{error}"),
            | Self::NotLive { ref object, part } => write!(f, "`{object}` part {part} is not live"),
            | Self::Referenced {
                ref object,
                part,
                ref arrow,
                by,
            } => write!(
                f,
                "`{object}` part {part} is referred to by `{arrow}` of part {by}, so it is not deleted"
            ),
            | Self::Unset {
                ref field,
                ref object,
                part,
            } => write!(f, "`{object}` part {part} has no value for `{field}`"),
            | Self::EquationViolated {
                ref equation,
                ref object,
                part,
                left,
                right,
            } => write!(
                f,
                "equation `{equation}` fails at `{object}` part {part}: the left side reaches {left}, the right {right}"
            ),
            | Self::NotIndexed { ref field } => write!(f, "`{field}` keeps no inverse"),
            | Self::ForeignField {
                ref field,
                ref object,
            } => write!(f, "`{field}` is not a column of `{object}`"),
            | Self::Exhausted { ref object } => write!(f, "`{object}` has minted its last key"),
        }
    }
}

impl core::error::Error for Refusal
{
}

impl From<SchemaError> for Refusal
{
    /// Carries a schema lookup's refusal.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(error: SchemaError) -> Self
    {
        Self::Schema(error)
    }
}

/// What part of a stored table failed to read back.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum LayoutFault
{
    /// A key opens with no family this layout writes.
    Family,
    /// A key or value has the wrong width for its family.
    Width,
    /// A key names an arrow or attribute that does not leave the table.
    Column,
    /// A key names a part at or past the table's counter.
    Counter,
    /// The records do not rebuild the tree the manifest names.
    Root,
    /// The records are not the records this store writes for what they hold.
    NotCanonical,
}

impl fmt::Display for LayoutFault
{
    /// Writes the fault's phrase.
    ///
    /// # Specification
    /// - ensures: writes one phrase per fault, distinct for each.
    /// - fails: propagates the formatter's write failure unchanged.
    /// - panics: none.
    /// - executable: none — the formatter exposes no readable output buffer.
    ///
    /// # Errors
    /// Propagates the formatter's write failure.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a reopen over a doctored table renders its fault.
    /// - witness: `tests::keyed::a_doctored_table_is_refused_on_reopening`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        f.write_str(match *self {
            | Self::Family => "a key opens with no family of the layout",
            | Self::Width => "a key or value has the wrong width",
            | Self::Column => "a key names a column of another table",
            | Self::Counter => "a key names a part at or past the counter",
            | Self::Root => "the records do not rebuild the committed tree",
            | Self::NotCanonical => "the records are not the canonical records of what they hold",
        })
    }
}

/// Where a store manifest image stopped making sense.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum ManifestFault
{
    /// The image does not open with the manifest domain.
    Domain,
    /// The manifest version is not one this crate reads.
    Version,
    /// The image ends inside a field.
    Truncated,
    /// Bytes follow the last table.
    Trailing,
}

impl fmt::Display for ManifestFault
{
    /// Writes the fault's phrase.
    ///
    /// # Specification
    /// - ensures: writes one phrase per fault, distinct for each.
    /// - fails: propagates the formatter's write failure unchanged.
    /// - panics: none.
    /// - executable: none — the formatter exposes no readable output buffer.
    ///
    /// # Errors
    /// Propagates the formatter's write failure.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — each malformed manifest's refusal renders apart.
    /// - witness: `manifest::tests::a_malformed_manifest_is_refused_by_field`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        f.write_str(match *self {
            | Self::Domain => "the domain is not the store manifest domain",
            | Self::Version => "the manifest version is unknown",
            | Self::Truncated => "the manifest ends inside a field",
            | Self::Trailing => "bytes follow the last table",
        })
    }
}

/// Every way a commit, a reopening, a manifest or a proof is refused.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum StoreError
{
    /// The record plane refused a tree, a node or a proof.
    Records(RecordTreeError),
    /// A read or edit refusal met while reopening or proving.
    Refused(Refusal),
    /// The manifest commits another schema.
    SchemaMismatch
    {
        /// The schema the reader holds.
        expected: SchemaIdentity,
        /// The schema the manifest commits.
        found: SchemaIdentity,
    },
    /// The manifest commits boundary parameters the reader does not share.
    ProfileMismatch,
    /// The manifest's table count is not the schema's object count.
    TableCount,
    /// A manifest image is malformed.
    Manifest
    {
        /// Where it failed.
        fault: ManifestFault,
    },
    /// A proof's manifest does not hash to the root it is checked against.
    RootMismatch
    {
        /// The root the verifier holds.
        expected: StoreRoot,
        /// The root the proof's manifest hashes to.
        found: StoreRoot,
    },
    /// A stored table does not read back.
    Layout
    {
        /// The table.
        object: Name,
        /// What failed.
        fault: LayoutFault,
    },
    /// A proof answers a different question than the one it is checked
    /// against.
    WrongQuestion,
}

impl fmt::Display for StoreError
{
    /// Writes the refusal with what it carries.
    ///
    /// # Specification
    /// - ensures: writes one line naming the refusal and its payload.
    /// - fails: propagates the formatter's write failure unchanged.
    /// - panics: none.
    /// - executable: none — the formatter exposes no readable output buffer.
    ///
    /// # Errors
    /// Propagates the formatter's write failure.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a proof checked against another root renders both
    ///   roots; a doctored table renders its object and fault.
    /// - witness: `tests::proofs::a_proof_against_another_root_is_refused`
    /// - witness: `tests::keyed::a_doctored_table_is_refused_on_reopening`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        match *self {
            | Self::Records(ref error) => write!(f, "{error}"),
            | Self::Refused(ref refusal) => write!(f, "{refusal}"),
            | Self::SchemaMismatch { expected, found } => {
                write!(f, "the manifest commits schema {found}, not {expected}")
            },
            | Self::ProfileMismatch => {
                f.write_str("the manifest commits other boundary parameters")
            },
            | Self::TableCount => f.write_str("the manifest's table count is not the schema's"),
            | Self::Manifest { fault } => write!(f, "malformed store manifest: {fault}"),
            | Self::RootMismatch { expected, found } => {
                write!(f, "the proof's manifest hashes to {found}, not {expected}")
            },
            | Self::Layout { ref object, fault } => write!(f, "table `{object}`: {fault}"),
            | Self::WrongQuestion => f.write_str("the proof answers a different question"),
        }
    }
}

impl core::error::Error for StoreError
{
}

impl From<RecordTreeError> for StoreError
{
    /// Carries the record plane's refusal.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(error: RecordTreeError) -> Self
    {
        Self::Records(error)
    }
}

impl From<Refusal> for StoreError
{
    /// Carries a read or edit refusal.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(refusal: Refusal) -> Self
    {
        Self::Refused(refusal)
    }
}

impl From<SchemaError> for StoreError
{
    /// Carries a schema lookup's refusal.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(error: SchemaError) -> Self
    {
        Self::Refused(Refusal::Schema(error))
    }
}
