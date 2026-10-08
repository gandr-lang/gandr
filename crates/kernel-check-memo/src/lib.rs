//! The **check-memo seam**: a statically dispatched interface letting a checker
//! skip a question it has already answered in this process, with the storage,
//! the policy, and the lifetime owned outside the checker.
//!
//! # The seam names no term type
//!
//! This crate names no term, type, or identifier of its own. The support a
//! checker keys on and the outcome it caches are both **type parameters**
//! supplied by the consumer, and the constraint is enforced by the generics
//! rather than by review. Three properties follow.
//!
//! The certified kernel can depend on this crate without a cycle, since this
//! crate cannot mention the kernel's types. The table's storage and its
//! lifetime live outside the checker, so what the checker holds is a seam and
//! not a cache. And no interning table enters the trusted base.
//!
//! # What a hit claims
//!
//! A hit claims exactly this: **this process already computed this answer for
//! this support**. It does not claim the answer is right, that the support was
//! well formed, or that anything was validated. A memo is sound only when its
//! consumer's support is the *whole* input to the computation it indexes — if
//! two calls with equal supports could differ, the memo is a defect and no
//! property of this crate can rescue it. The consumer owns that argument.
//!
//! A hit nonetheless *carries* its support rather than asserting one: a
//! [`MemoHit`] hands back the support the entry was recorded under beside the
//! outcome, so a consumer checking adoption compares demanded against supplied
//! pointwise instead of intersecting footprints.
//!
//! Nothing here persists, and nothing here is a wire format.
//!
//! # The static-dispatch discipline
//!
//! [`CheckMemo`] carries an associated [`MemoActivity`] constant so a consumer
//! can branch on liveness at **compile** time. Instantiated at [`NullMemo`],
//! every memo interaction — the support construction included, when the
//! consumer guards it — is a constant-false branch that monomorphization
//! removes, so the unmemoized path compiles to the code it would have with no
//! memo at all. That is what makes the memoized and unmemoized paths
//! comparable: the differential's fresh side is not a re-implementation, it is
//! **the same function at a different type parameter**.
//!
//! # The digest is a fast path and never a decision
//!
//! A key is content-derived, so it survives relocation and two equal
//! obligations key equally wherever they arise. A content key is carried
//! as a [`ContentDigest`] beside a deciding comparison, and the direction of
//! error is the whole of the contract: **equal digests never decide
//! agreement**. Different digests prove disagreement; equal digests hand off to
//! [`MemoKey::agreement`] over the supports' canonical content. [`OrderedMemo`]
//! realizes that as storage — the digest picks a bucket, the deciding
//! comparison scans it — so a collision costs one comparison and degrades to a
//! miss, priced strictly as recomputation and never as a wrong answer.
//!
//! # Accounting
//!
//! Entry counts are maintained per plane as well as in total. A checker running
//! two machines over one shared graph gives each machine its own plane, so the
//! collapse of each is asserted separately and neither hides behind the other's
//! numbers. The counts are a contract rather than telemetry, so they are
//! maintained with checked arithmetic and a typed refusal at the ceiling.
//!
//! The crate is `no_std` and depends only on `core`, `alloc` and the
//! specification facade.
//!
//! The paper the crate draws on is in its `README.md`, § References.

#![no_std]

extern crate alloc;

pub mod accounting;
pub mod digest;
pub mod key;
pub mod memo;

pub use crate::accounting::MemoBucketCount;
pub use crate::accounting::MemoEntryCount;
pub use crate::accounting::MemoError;
pub use crate::digest::ContentAgreement;
pub use crate::digest::ContentDigest;
pub use crate::digest::DigestWord;
pub use crate::key::MemoKey;
pub use crate::memo::CheckMemo;
pub use crate::memo::MemoActivity;
pub use crate::memo::MemoHit;
pub use crate::memo::MemoRecord;
pub use crate::memo::NullMemo;
pub use crate::memo::OrderedMemo;
