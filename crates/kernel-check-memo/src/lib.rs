//! The **check-memo seam**: a statically dispatched interface letting a checker
//! skip a question it has already answered in this process, with the storage,
//! the policy, and the lifetime owned outside the checker.
//!
//! This crate names no term, type, or identifier of its own. The support a
//! checker keys on and the outcome it caches are type parameters the consumer
//! supplies, so the constraint is the generics. The certified kernel depends
//! on this crate without a cycle, the table's storage and its lifetime live
//! outside the checker, and no interning table enters the trusted base.
//!
//! # Items
//!
//! [`CheckMemo`] carries an associated [`MemoActivity`] constant, so a consumer
//! branches on liveness at compile time. Instantiated at [`NullMemo`], every
//! memo interaction — the support construction included, when the consumer
//! guards it — is a constant-false branch that monomorphization removes. The
//! unmemoized path compiles to the code it would have with no memo, and the
//! memoized path is that same function at a different type parameter.
//!
//! [`HashedMemo`] stores entries densely, in recording order, and files each
//! one's position in a [`HashIndex`] under the hash of its [`ContentDigest`].
//! A content key is that digest beside [`MemoKey::agreement`]: the digest
//! narrows the search and the deciding comparison runs over each candidate. A
//! key is content-derived, so it survives relocation and two equal obligations
//! key equally wherever they arise. Different digests prove disagreement;
//! equal digests hand off to agreement over the supports' canonical content
//! and never decide it. A collision costs one comparison and degrades to a
//! miss, priced as recomputation.
//!
//! The [`table`] module's index is open addressing with linear probing, kept
//! at most half full: a slot holds a 32-bit hash and a position, and the
//! consumer's own comparison decides each candidate. It is the kernel's one
//! hash index — the content table's interning, a node's binder reach, the
//! rewrite walk's local answers and the staging arena's descriptor lookup
//! file on it too.
//!
//! Entry counts are maintained per plane and in total. A checker running two
//! machines over one shared graph gives each machine its own plane, so each
//! collapse is asserted on its own numbers. `remember` returns a [`MemoRecord`]
//! and refuses with [`MemoError::EntryCountOverflow`] at the ceiling, leaving
//! the memo as it was. [`MemoHit`] hands back the support the entry was
//! recorded under beside the outcome, so a consumer compares demanded against
//! supplied pointwise.
//!
//! # Boundaries
//!
//! A hit claims exactly this: **this process already computed this answer for
//! this support**. It does not claim the answer is right, that the support was
//! well formed, or that anything was validated. A memo is sound only when its
//! consumer's support is the whole input to the computation it indexes. If two
//! calls with equal supports could differ, the memo is a defect and no property
//! of this crate can rescue it. The consumer owns that argument.
//!
//! Nothing here persists, and nothing here is a wire format.
//!
//! No enum is `#[non_exhaustive]`. The workspace does not publish, so the
//! attribute would protect no external consumer while forcing a wildcard arm
//! at every match, defeating exhaustiveness where a new variant should break
//! every consumer.
//!
//! # Dependencies
//!
//! The crate is `no_std` and depends only on `core`, `alloc` and the
//! specification facade. No hasher crate enters the kernel's dependency wall:
//! [`TableHash::of`] is an unkeyed fold this crate owns, so a run's hashes,
//! and every measurement over the memo, are re-derivable. Iteration order is
//! never promised; nothing reads the memo in order.
//!
//! # Witnesses
//!
//! The `# Specification` prose states the obligation; `#[spec(...)]` mirrors
//! clauses that can be checked over one call. Each nontrivial item has a
//! `# Adequacy` hypothesis naming the bounded evidence and the deviations its
//! observer distinguishes.
//!
//! - Checked arithmetic specifies the exact successor, per-plane lookup and
//!   overflow refusal, including unchanged accounting on failure.
//! - Hashed storage specifies digest lookup, support agreement, insertion
//!   versus replacement, and unchanged counts on refusal. Collision and ceiling
//!   tests also observe retained answers, rather than counts alone; the index's
//!   own tests observe probing across wrap-around and growth.
//! - The differential workload specifies its arena topology, framed content
//!   identity, folds and census arithmetic. Closed-form counts and ordinary
//!   versus memoized runs distinguish missing work from reused work.
//!
//! Anodized evaluates postconditions after early `?` returns, so refusal paths
//! are included. Production predicates capture scalar counts and membership
//! facts, not owned snapshots; additional predicate traversals run only when
//! enforcement is enabled.
//!
//! A final `- executable: none` clause identifies the remaining data,
//! declaration or external-context obligation. Instrumenting [`CheckMemo`] or
//! [`MemoKey`] declarations would change the implementation interface;
//! data-item expansion does not check construction. The bounded witnesses
//! exercise the shipped implementations and fixture relations. They do not
//! certify arbitrary consumer implementations of the semantic agreement laws.
//!
//! # References
//!
//! The paper the crate draws on is in its `README.md`, § References.
#![no_std]

extern crate alloc;

pub mod accounting;
pub mod digest;
pub mod key;
pub mod memo;
pub mod table;

pub use crate::accounting::MemoBucketCount;
pub use crate::accounting::MemoEntryCount;
pub use crate::accounting::MemoError;
pub use crate::digest::ContentAgreement;
pub use crate::digest::ContentDigest;
pub use crate::digest::DigestWord;
pub use crate::key::MemoKey;
pub use crate::memo::CheckMemo;
pub use crate::memo::HashedMemo;
pub use crate::memo::MemoActivity;
pub use crate::memo::MemoHit;
pub use crate::memo::MemoRecord;
pub use crate::memo::NullMemo;
pub use crate::table::HashIndex;
pub use crate::table::Probe;
pub use crate::table::TableFull;
pub use crate::table::TableHash;
pub use crate::table::TablePosition;
pub use crate::table::TableSlot;
