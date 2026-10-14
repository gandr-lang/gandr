//! Proofs of what a committed store holds, against its one root.
//!
//! A [`Proof`] answers one [`Question`] — is this part live, what does this
//! arrow or attribute map this part to, which parts does a kept inverse list
//! for this value — for the store's last commit. It carries the manifest and
//! one record-plane proof from the answering table's tree. Verifying needs
//! the store's root, the schema and the record plane's parameters, nothing
//! else: the manifest's BLAKE3 must be the root, its schema identity and
//! boundary commitment the reader's, and the record-plane proof must verify
//! against the table root the manifest binds.
//!
//! A preimage is answered from the kept inverse's contiguous key run, so the
//! range proof proves the list complete: no part is left out and none is
//! added. A preimage of an arrow or attribute the schema does not index is
//! refused rather than proved by a scan, because no record run would back
//! it.

use alloc::boxed::Box;
use alloc::vec::Vec;

use anodized::spec;
use gandr_storage_records::KeyBound;
use gandr_storage_records::KeyRange;
use gandr_storage_records::MembershipProof;
use gandr_storage_records::NonMembershipProof;
use gandr_storage_records::OwnedRecordKey;
use gandr_storage_records::RangeProof;
use gandr_storage_records::RecordKey;
use gandr_storage_records::RecordTree;
use gandr_storage_records::RecordValue;
use gandr_storage_records::TreeParams;

use crate::error::Refusal;
use crate::error::StoreError;
use crate::manifest::StoreManifest;
use crate::manifest::StoreRoot;
use crate::parts::Liveness;
use crate::parts::PartKey;
use crate::schema::ArrowId;
use crate::schema::AttributeId;
use crate::schema::Indexing;
use crate::schema::ObjectId;
use crate::schema::Ordinal;
use crate::schema::Schema;
use crate::store::AttributeValue;
use crate::store::Store;
use crate::store::layout::ARROW;
use crate::store::layout::ARROW_INDEX;
use crate::store::layout::KeyWriter;
use crate::store::layout::PART;
use crate::store::layout::VALUE;
use crate::store::layout::VALUE_INDEX;

/// What a proof answers.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum Question
{
    /// Whether a part of a table is live.
    Part
    {
        /// The table.
        object: ObjectId,
        /// The part.
        part: PartKey,
    },
    /// Where an arrow takes a live part.
    Arrow
    {
        /// The arrow.
        arrow: ArrowId,
        /// The part of its source.
        part: PartKey,
    },
    /// What an attribute holds for a live part.
    Value
    {
        /// The attribute.
        attribute: AttributeId,
        /// The part of its object.
        part: PartKey,
    },
    /// Which live parts an indexed arrow takes to a target.
    Preimage
    {
        /// The arrow.
        arrow: ArrowId,
        /// The part of its target.
        target: PartKey,
    },
    /// Which live parts an indexed attribute maps to a value.
    ValuePreimage
    {
        /// The attribute.
        attribute: AttributeId,
        /// The value.
        value: AttributeValue,
    },
}

/// What a verified proof states.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum Answer
{
    /// The part's liveness.
    Liveness(Liveness),
    /// The arrow's target.
    Target(PartKey),
    /// The attribute's value.
    Value(AttributeValue),
    /// The preimage, in key order and complete.
    Preimage(Box<[PartKey]>),
}

/// The record-plane proof inside a [`Proof`].
#[derive(Clone, Debug, Eq, PartialEq)]
enum Evidence
{
    /// The answering record is present.
    Present(MembershipProof),
    /// The answering record is absent.
    Absent(NonMembershipProof),
    /// The answering run of records.
    Run(RangeProof),
}

/// A proof of one answer against a store's root.
///
/// # Specification
/// - requires: construction by [`Store::prove`].
/// - ensures: [`Proof::verify`] answers its question exactly as the store
///   answered at its last commit.
/// - provides: verification against a root alone.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L2/L3 — every kind of question is proved and verified against
///   the root with the store's own answer; a proof checked against another
///   root, for another question, or under another schema is refused by name.
/// - witness: `tests::proofs::every_kind_of_proof_verifies_against_the_root`
/// - witness: `tests::proofs::a_proof_against_another_root_is_refused`
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Proof
{
    /// The manifest of the commit the proof is for.
    manifest: StoreManifest,
    /// The question.
    question: Question,
    /// The record-plane proof.
    evidence: Evidence,
}

/// Where a question is answered: the table and the key or key run.
struct Site
{
    /// The table whose tree answers.
    object: ObjectId,
    /// The answering key, or the run's lower bound.
    key: OwnedRecordKey,
    /// The run's exclusive upper bound, for a preimage.
    end: Run,
}

/// Whether a site is one key or a run of keys.
enum Run
{
    /// One key.
    Single,
    /// Every key from the site's key up to this exclusive bound.
    Before(OwnedRecordKey),
}

/// Locates the records answering a question.
///
/// # Specification
/// - ensures: on success the table and key, or key run, the module
///   documentation of the layout gives for the question.
/// - fails: [`StoreError::Refused`] carrying the schema's refusal of an
///   identifier, or [`Refusal::NotIndexed`] for a preimage of an unindexed
///   column; [`StoreError::Layout`] for an ordinal too wide to key.
/// - panics: none.
/// - executable: none — the site is checked by the record plane's proof
///   verifying at it.
///
/// # Errors
/// As above.
///
/// # Adequacy
/// - hypothesis: L2/L3 — every kind of question verifies against the committed
///   root; a preimage of an unindexed arrow is refused by name.
/// - witness: `tests::proofs::every_kind_of_proof_verifies_against_the_root`
/// - witness: `tests::proofs::an_unindexed_preimage_is_not_proved`
fn site(
    schema: &Schema,
    question: &Question,
) -> Result<Site, StoreError>
{
    let layout = |object| {
        let name = schema.object_name(object).cloned();
        move |fault| match name {
            | Ok(object) => StoreError::Layout { object, fault },
            | Err(ref refusal) => StoreError::Refused(Refusal::Schema(refusal.clone())),
        }
    };
    match *question {
        | Question::Part { object, part } => {
            schema.object_name(object).map_err(Refusal::Schema)?;
            Ok(Site {
                object,
                key: KeyWriter::family(PART).part(part).key(),
                end: Run::Single,
            })
        },
        | Question::Arrow { arrow, part } => {
            let object = schema.arrow_at(arrow).map_err(Refusal::Schema)?.source();
            let key = KeyWriter::family(ARROW)
                .column(Ordinal(usize::from(arrow)))
                .map_err(layout(object))?
                .part(part)
                .key();
            Ok(Site {
                object,
                key,
                end: Run::Single,
            })
        },
        | Question::Value { attribute, part } => {
            let object = schema
                .attribute_at(attribute)
                .map_err(Refusal::Schema)?
                .object();
            let key = KeyWriter::family(VALUE)
                .column(Ordinal(usize::from(attribute)))
                .map_err(layout(object))?
                .part(part)
                .key();
            Ok(Site {
                object,
                key,
                end: Run::Single,
            })
        },
        | Question::Preimage { arrow, target } => {
            let spec = schema.arrow_at(arrow).map_err(Refusal::Schema)?;
            if spec.indexing() != Indexing::Indexed {
                return Err(StoreError::Refused(Refusal::NotIndexed {
                    field: spec.name().clone(),
                }));
            }
            let object = spec.source();
            let prefix = KeyWriter::family(ARROW_INDEX)
                .column(Ordinal(usize::from(arrow)))
                .map_err(layout(object))?
                .part(target)
                .key();
            Ok(run(object, prefix))
        },
        | Question::ValuePreimage {
            attribute,
            ref value,
        } => {
            let spec = schema.attribute_at(attribute).map_err(Refusal::Schema)?;
            if spec.indexing() != Indexing::Indexed {
                return Err(StoreError::Refused(Refusal::NotIndexed {
                    field: spec.name().clone(),
                }));
            }
            let object = spec.object();
            let prefix = KeyWriter::family(VALUE_INDEX)
                .column(Ordinal(usize::from(attribute)))
                .map_err(layout(object))?
                .value(value)
                .map_err(layout(object))?
                .key();
            Ok(run(object, prefix))
        },
    }
}

/// The site of every key extending a prefix.
///
/// # Specification
/// - requires: the prefix opens with an inverse family byte, so it is not all
///   `0xff` and has a successor.
/// - ensures: the run from the prefix up to the least key greater than every
///   key extending it.
/// - panics: none.
/// - executable: none — the run's bounds are checked by the range proof
///   verifying exactly the preimage.
///
/// # Adequacy
/// - hypothesis: L3 — the preimage of one digest excludes a longer digest it
///   prefixes, and a target's run excludes the next target's.
/// - witness: `tests::proofs::a_value_preimage_excludes_a_value_it_prefixes`
#[inline]
fn run(
    object: ObjectId,
    prefix: OwnedRecordKey,
) -> Site
{
    let mut end: Vec<u8> = Vec::from(prefix.as_ref());
    while let Some(last) = end.pop() {
        if let Some(next) = last.checked_add(1_u8) {
            end.push(next);
            break;
        }
    }
    Site {
        object,
        key: prefix,
        end: Run::Before(OwnedRecordKey::from(end)),
    }
}

impl Site
{
    /// The record plane's range for a run.
    ///
    /// # Specification
    /// - ensures: on success the range from the key, inclusive, to the end,
    ///   exclusive.
    /// - fails: [`StoreError::Records`] for a range the record plane refuses; a
    ///   single-key site is refused as the wrong question.
    /// - panics: none.
    /// - executable: none — the range's independent observation is the range
    ///   proof verifying under it.
    ///
    /// # Errors
    /// As above.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — every preimage proof verifies under the range.
    /// - witness: `tests::proofs::every_kind_of_proof_verifies_against_the_root`
    #[inline]
    fn range(&self) -> Result<KeyRange<'_>, StoreError>
    {
        let Run::Before(ref end) = self.end
        else {
            return Err(StoreError::WrongQuestion);
        };
        Ok(KeyRange::new(
            KeyBound::included(self.key.as_borrowed()),
            KeyBound::excluded(end.as_borrowed()),
        )?)
    }
}

impl Store
{
    /// Proves the answer to a question for the last commit.
    ///
    /// # Specification
    /// - requires: nothing; the question is checked against the schema and the
    ///   committed tree.
    /// - ensures: on success the proof's question is `question` and it verifies
    ///   against [`Store::root`] to the committed answer.
    /// - fails: [`StoreError::Refused`] for an identifier outside the schema,
    ///   [`Refusal::NotIndexed`] for a preimage of an unindexed column, and
    ///   [`Refusal::NotLive`] for a cell of a part that was not live at the
    ///   commit; [`StoreError::Records`] for the record plane's refusal to
    ///   prove.
    /// - panics: none.
    /// - intension: answers for the last commit, not for edits since; a caller
    ///   commits first to prove them.
    ///
    /// # Errors
    /// As above.
    ///
    /// # Adequacy
    /// - hypothesis: L2/L3 — every kind of question verifies to the store's own
    ///   answer; an uncommitted edit is not what the proof states.
    /// - witness: `tests::proofs::every_kind_of_proof_verifies_against_the_root`
    /// - witness: `tests::proofs::an_unindexed_preimage_is_not_proved`
    #[inline]
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |proof| proof.question == *question))]
    pub fn prove(
        &self,
        question: &Question,
    ) -> Result<Proof, StoreError>
    {
        let site = site(&self.schema, question)?;
        let tree = self
            .committed
            .trees
            .get(usize::from(site.object))
            .ok_or(StoreError::TableCount)?;
        let evidence = match *question {
            | Question::Part { .. } => evidence_of(tree, site.key.as_borrowed())?,
            | Question::Arrow { part, .. } | Question::Value { part, .. } => {
                if tree.lookup(site.key.as_borrowed()).is_none() {
                    let object = self.object_name(site.object)?;
                    return Err(StoreError::Refused(Refusal::NotLive { object, part }));
                }
                Evidence::Present(tree.prove_membership(site.key.as_borrowed())?)
            },
            | Question::Preimage { .. } | Question::ValuePreimage { .. } => {
                let range = site.range()?;
                Evidence::Run(tree.prove_range(range)?)
            },
        };
        Ok(Proof {
            manifest: self.committed.manifest.clone(),
            question: question.clone(),
            evidence,
        })
    }
}

/// A membership or non-membership proof of one key.
///
/// # Specification
/// - ensures: on success membership when the tree holds the key and
///   non-membership otherwise.
/// - fails: [`StoreError::Records`] for the record plane's refusal.
/// - panics: none.
/// - executable: none — the choice is observed by verification answering live
///   or dead.
///
/// # Errors
/// [`StoreError::Records`].
///
/// # Adequacy
/// - hypothesis: L2 — a live part verifies live and a deleted one dead.
/// - witness: `tests::proofs::every_kind_of_proof_verifies_against_the_root`
#[inline]
fn evidence_of(
    tree: &RecordTree,
    key: RecordKey<'_>,
) -> Result<Evidence, StoreError>
{
    if tree.lookup(key).is_some() {
        Ok(Evidence::Present(tree.prove_membership(key)?))
    }
    else {
        Ok(Evidence::Absent(tree.prove_non_membership(key)?))
    }
}

impl Proof
{
    /// The question the proof answers.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn question(&self) -> &Question
    {
        &self.question
    }

    /// The manifest of the commit the proof is for.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn manifest(&self) -> &StoreManifest
    {
        &self.manifest
    }

    /// Verifies the proof against a store root and returns its answer.
    ///
    /// # Specification
    /// - requires: nothing; every input is checked.
    /// - ensures: on success the answer the store held for `question` at the
    ///   commit `root` names.
    /// - fails: [`StoreError::WrongQuestion`] when the proof answers another
    ///   question or carries evidence of the wrong kind;
    ///   [`StoreError::RootMismatch`] when the manifest is not `root`'s;
    ///   [`StoreError::SchemaMismatch`], [`StoreError::ProfileMismatch`] and
    ///   [`StoreError::TableCount`] for a reader of another schema or
    ///   parameters; [`StoreError::Refused`] for a question the schema refuses;
    ///   [`StoreError::Records`] for a record-plane proof that does not verify
    ///   against the table root; [`StoreError::Layout`] for a record whose
    ///   bytes are not the layout's.
    /// - panics: none.
    /// - executable: none — the answer is the verification itself; the
    ///   witnesses compare it with the store's own reads.
    ///
    /// # Errors
    /// As above.
    ///
    /// # Adequacy
    /// - hypothesis: L2/L3 — each kind of proof verifies to the store's answer;
    ///   another root, another question and another schema are each refused by
    ///   name.
    /// - witness: `tests::proofs::every_kind_of_proof_verifies_against_the_root`
    /// - witness: `tests::proofs::a_proof_against_another_root_is_refused`
    /// - witness: `tests::proofs::a_proof_under_another_schema_is_refused`
    #[inline]
    pub fn verify(
        &self,
        root: StoreRoot,
        schema: &Schema,
        params: TreeParams,
        question: &Question,
    ) -> Result<Answer, StoreError>
    {
        if self.question != *question {
            return Err(StoreError::WrongQuestion);
        }
        if self.manifest.identity() != root {
            return Err(StoreError::RootMismatch {
                expected: root,
                found: self.manifest.identity(),
            });
        }
        self.manifest.ensure_reader(schema, params)?;
        let site = site(schema, question)?;
        let tree_root = self.manifest.tree_root(site.object, params)?;
        let malformed = || match schema.object_name(site.object) {
            | Ok(object) => StoreError::Layout {
                object: object.clone(),
                fault: crate::error::LayoutFault::Width,
            },
            | Err(refusal) => StoreError::Refused(Refusal::Schema(refusal)),
        };

        match (question, &self.evidence) {
            | (&Question::Part { .. }, &Evidence::Present(ref proof)) => {
                proof.verify(&tree_root, site.key.as_borrowed(), RecordValue::from(&[]))?;
                Ok(Answer::Liveness(Liveness::Live))
            },
            | (&Question::Part { .. }, &Evidence::Absent(ref proof)) => {
                proof.verify(&tree_root, site.key.as_borrowed())?;
                Ok(Answer::Liveness(Liveness::Dead))
            },
            | (&Question::Arrow { .. }, &Evidence::Present(ref proof)) => {
                proof.verify(&tree_root, site.key.as_borrowed(), proof.value())?;
                let value: &[u8] = proof.value().into();
                let target: [u8; 8] = value.try_into().map_err(|_width| malformed())?;
                Ok(Answer::Target(PartKey::from(u64::from_le_bytes(target))))
            },
            | (&Question::Value { .. }, &Evidence::Present(ref proof)) => {
                proof.verify(&tree_root, site.key.as_borrowed(), proof.value())?;
                let value: &[u8] = proof.value().into();
                Ok(Answer::Value(AttributeValue::from(value)))
            },
            | (
                &Question::Preimage { .. } | &Question::ValuePreimage { .. },
                &Evidence::Run(ref proof),
            ) => {
                let range = site.range()?;
                let records = proof.verify(&tree_root, range)?;
                let mut parts = Vec::with_capacity(records.len());
                for record in &records {
                    let key: &[u8] = record.key().into();
                    let (_prefix, part) = key.split_last_chunk::<8>().ok_or_else(malformed)?;
                    let mut part = *part;
                    part.reverse();
                    parts.push(PartKey::from(u64::from_le_bytes(part)));
                }
                Ok(Answer::Preimage(parts.into_boxed_slice()))
            },
            | _ => Err(StoreError::WrongQuestion),
        }
    }
}
