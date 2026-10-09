//! Certificates of value-level isomorphism between monomorphic descriptions,
//! and what the crate's generic programs do across them.
//!
//! A certificate ([`harness::CodeIso`]) pairs two description-driven value
//! translators between two parameter-free descriptions. It is data, not a
//! proof: its evidence is the replay of its round trips against
//! `generic_eq`, and two certificates over one boundary are the same
//! transformation exactly when they replay alike. That is the shape of a
//! protype isomorphism — two proterms mutually inverse to each other — in
//! Hayato Nasu, *Logical Aspects of Virtual Double Categories*,
//! arXiv:2501.17869, § 3.2.3, instantiated at monomorphic codes.
//!
//! Every translator maps real `DescValue`s, every round trip is judged by the
//! crate's `generic_eq`, every description is a real `SignDesc` (the `Boolean`
//! side is the crate's `bool_desc` retrofit), and every consumer transported
//! is the crate's own. The certificate type is the suite's; translators are
//! opaque closures, since an inspectable code-edit vocabulary is not this
//! crate's to define.
//!
//! The areas:
//!
//! * `certificates` — the certificate discipline and the invertible-mode
//!   groupoid (identity, inverse, composition), all up to replay;
//! * `transport` — `generic_eq` agreement, `serialize_value` naturality up to
//!   re-encoding, and code-table coherence across every certificate;
//! * `negation_guard` — the identity and negation auto-isomorphisms of
//!   `Boolean` share their boundary codes yet replay differently, so the
//!   identity of certificates is never decidable code equality;
//! * `leaf_shift_guard` — over a one-constructor description with an unbounded
//!   `Integer` leaf, the successor shift round-trips yet differs from the
//!   identity, the only structural auto-isomorphism there; a completeness
//!   statement about certificates therefore ranges over translators uniform in
//!   leaf contents.

mod certificates;
mod fixtures;
mod harness;
mod leaf_shift_guard;
mod negation_guard;
mod transport;
