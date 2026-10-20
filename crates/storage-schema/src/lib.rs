//! The record plane under the C-set discipline: a schema of objects, total
//! arrows, typed attributes and path equations, and a store of its parts
//! over authenticated record trees, with one root per store.
//!
//! A [`Schema`] is a finite presentation of a category with attributes: its
//! objects are tables, its arrows total foreign keys between them, its
//! attributes typed columns, and its equations pairs of parallel arrow paths
//! that every store must agree on. It is a canonical value: its image is
//! fixed by its contents, not the order they were stated in, and its
//! [`SchemaIdentity`] is BLAKE3 of that image. A [`Store`] holds, for each
//! object, a set of parts under stable keys and, for each arrow and
//! attribute, a column; it keeps the inverse of each column the schema
//! indexes; it refuses, by name, every edit that would leave a dangling
//! reference, an unset cell or a broken equation; it commits each table as
//! one record tree and names the whole store by one [`StoreRoot`]; and it
//! proves part membership, arrow values, attribute values and complete
//! preimages against that root.
//!
//! # The discipline adopted
//!
//! The representation is the one categorical data structures give a
//! C-set: a column per arrow and per attribute, a part set per object, and
//! a materialized inverse per indexed column, so a preimage is a lookup and
//! not a scan. Parts are deleted by clearing a bit in their table's live set
//! and nothing is renumbered.
//!
//! **Choice: an inverse may be declared on an attribute as well as on an
//! arrow.** The discipline declares indexes per arrow; this crate lets an
//! attribute declare one too, kept the same way. **Why:** the keyed indexes
//! a consumer replaces are entered by a task's name and by a subject's
//! digest, and without an attribute's inverse each such lookup is a scan of
//! its table. **Reversal:** a consumer whose every entry point is a part
//! key, where the attribute inverses cost memory and proof records for no
//! lookup.
//!
//! **Choice: the schema is a value, not a type.** A [`Store`] holds its
//! [`Schema`] and checks every identifier against it, rather than taking the
//! schema as a type parameter. A schema's identity is what a manifest and a
//! proof commit, a reader may hold a schema it decoded rather than compiled,
//! and a schema map relates two schemas as data. **Reversal:** a consumer
//! with one fixed schema whose identifier checks show in its measurements,
//! where a schema type would move them to compile time.
//!
//! **Choice: counter-minted stable keys.** Each table mints keys from a
//! monotone counter — never reused, never renumbered, committed in the
//! manifest so a reopened store continues it, and advanced even by an edit
//! that is then abandoned. A key names one part for the store's whole life,
//! so an arrow cell, an index entry or a proof that names a part goes on
//! naming it whatever else is deleted.
//!
//! **Alternatives.** Positional identifiers — the part's index in a dense
//! table, renumbered on delete — make every delete rewrite every reference
//! past it, every hash over those references, and every proof a reader
//! held; they are what this crate replaces. Content-derived keys make two
//! parts with equal contents one part, and make setting an arrow change the
//! part's key and with it every key that refers to it.
//!
//! **Reversal.** Identity depends on mint order: two stores holding
//! isomorphic contents minted in different orders have different roots, and
//! dense columns follow the counter, not the live count. A workload where
//! that difference, or the memory of a long-deleted range, costs more than
//! the hash rewrite positional identifiers would need is the reversal; an
//! explicit compaction that returns its renumbering is the economy ceiling
//! before it.
//!
//! # The equation check
//!
//! An [`Edit`] collects mutations and checks at [`Edit::finish`]: first that
//! every cell of every part it added is set, then every equation whose
//! value the edit could have changed. That is each equation rooted at an
//! added part, and, for each arrow cell it set, each equation that crosses
//! that arrow at each part from which the equation's path reaches the cell —
//! found by walking the path's prefix backward through the kept inverses,
//! or by a scan where an arrow on it is not indexed. The cost is
//! proportional to the parts whose equations an edit can reach, not to the
//! store. A refused close rolls the edit back; dropping an edit unfinished
//! does too.
//!
//! **Choice.** Equations are checked by the store, on every edit, and a
//! reopened store is audited in full. **Alternatives.** Checking at commit
//! would let an uncommitted store be read in a state no commit could hold;
//! leaving equations to the caller is the limitation this crate removes.
//! **Reversal.** A bulk load whose equations hold by construction may want a
//! path that audits once at the end instead of per edit.
//!
//! # Schema maps
//!
//! [`SchemaMap`] and [`Store::pull_back`] provide the data migration `Δ_F`
//! along a schema map; [`migrate`] states what it preserves and how a map's
//! equations are checked.
//!
//! # Limits
//!
//! Attributes are columns of opaque canonical bytes: the store compares and
//! indexes them by bytes and does not compute with them. The pushout and the
//! other migrations of a schema map are not provided.
//!
//! # References
//!
//! - Patterson, Lynch and Fairbanks, *Categorical Data Structures for Technical
//!   Computing*, Compositionality 4, 2022 — C-sets with attributes, their
//!   column representation with materialized inverses, and the functorial data
//!   migrations.
//! - Brown, Patterson, Hanks and Fairbanks, *Computational Category-Theoretic
//!   Rewriting*, ICGT 2022, §2.3 — the dangling condition a deletion of a
//!   referenced part violates.
//! - Spivak, *Functorial Data Migration*, Information and Computation 217, 2012
//!   — schemas as finitely presented categories and `Δ_F`.

// Module documentation that predates the shape lint: 12 headings outside the
// vocabulary, 7 decision records and 2 budgets exceeded. Each allow leaves with
// the rewrite that clears its count.
#![cfg_attr(
    dylint_lib = "quenchant_dylints",
    allow(
        module_doc_heading,
        doc_decision_record,
        module_doc_budget,
        reason = "module documentation that predates the shape lint"
    )
)]
#![no_std]
#![cfg_attr(
    dylint_lib = "quenchant_dylints",
    expect(
        allocation_in_repeated_body,
        reason = "2 cost-shape sites; #814 lists them"
    )
)]
#![cfg_attr(
    dylint_lib = "quenchant_dylints",
    expect(clone_in_loop, reason = "4 cost-shape sites; #814 lists them")
)]

extern crate alloc;
// The profiler's instrumentation names `std`; it links only into the
// benchmark build.
#[cfg(feature = "hotpath")]
extern crate std;

pub mod error;
pub mod keyed;
pub mod manifest;
pub mod migrate;
pub mod parts;
pub mod schema;
pub mod store;

pub use crate::error::LayoutFault;
pub use crate::error::ManifestFault;
pub use crate::error::Refusal;
pub use crate::error::StoreError;
pub use crate::manifest::MANIFEST_DOMAIN;
pub use crate::manifest::ManifestImage;
pub use crate::manifest::ManifestImageBuf;
pub use crate::manifest::STORE_ROOT_LEN;
pub use crate::manifest::StoreManifest;
pub use crate::manifest::StoreRoot;
pub use crate::manifest::TableRoot;
pub use crate::migrate::MapBuilder;
pub use crate::migrate::MapError;
pub use crate::migrate::SchemaMap;
pub use crate::parts::LiveParts;
pub use crate::parts::Liveness;
pub use crate::parts::PartCount;
pub use crate::parts::PartKey;
pub use crate::schema::Arrow;
pub use crate::schema::ArrowId;
pub use crate::schema::Attribute;
pub use crate::schema::AttributeId;
pub use crate::schema::AttributeTypeId;
pub use crate::schema::ElementCount;
pub use crate::schema::ElementKind;
pub use crate::schema::Equation;
pub use crate::schema::EquationId;
pub use crate::schema::ImageFault;
pub use crate::schema::Indexing;
pub use crate::schema::Name;
pub use crate::schema::ObjectId;
pub use crate::schema::Occurrence;
pub use crate::schema::Ordinal;
pub use crate::schema::Path;
pub use crate::schema::PathPosition;
pub use crate::schema::Presentation;
pub use crate::schema::SCHEMA_DOMAIN;
pub use crate::schema::SCHEMA_IDENTITY_LEN;
pub use crate::schema::Schema;
pub use crate::schema::SchemaError;
pub use crate::schema::SchemaIdentity;
pub use crate::schema::SchemaImage;
pub use crate::schema::Side;
pub use crate::store::AttributeValue;
pub use crate::store::Row;
pub use crate::store::Store;
pub use crate::store::edit::Edit;
pub use crate::store::prove::Answer;
pub use crate::store::prove::Proof;
pub use crate::store::prove::Question;
