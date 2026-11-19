//! The record of Rust functions that the pinned toolchain gives: each
//! function's symbol, its convention and the layout of each type of its
//! signature.
//!
//! gandr calls Rust under the convention that rustc computes for one build.
//! No table holds that convention, and it differs by target. So a reader on
//! rustc's own libraries reads it from the crate, and this crate holds the
//! answer. This crate links no library of rustc: the reader is a program of
//! its own, and it writes the answer in the form that this crate reads.
//!
//! [`Record`] is the answer for one [`Request`]: the toolchain's
//! [`Identity`], then one [`Function`] for each requested path, or one
//! [`Refusal`] for each path that the record cannot state. [`Entry`] is a
//! record beside the digest of each source file that the reader read, and
//! [`Entry::encode`] gives its one canonical byte form. [`Entry::decode`]
//! reads that form back under a bound of the input's length, and it refuses
//! a record of another toolchain or of another target. [`Cache::read`]
//! answers from an entry when each of its sources is unchanged, and it runs
//! the reader once when no entry stands.
//!
//! # Boundaries
//!
//! The record states a plain function: public, with no generic parameter,
//! and with a symbol in the build. A layout states a scalar, a struct, a
//! tuple or an enum; the record refuses an array, a union, an unsized type
//! and a type with no value by name. A crate depends on the standard library
//! alone. The reader trusts rustc's front end, and the record holds the
//! toolchain's answer, never a second computation of it.
//!
//! # References
//!
//! - `vault:01a1e7b4-8c77-7a81-9165-ff37ea870424` — newest: the record of a
//!   Rust function comes from the toolchain that compiles it (§
//!   io-direction-interop).

extern crate alloc;

mod bytes;
mod cache;
mod names;
mod record;
mod request;

#[cfg(test)]
mod tests;

pub use crate::bytes::Canonical;
pub use crate::bytes::Digest;
pub use crate::bytes::Encoded;
pub use crate::bytes::Entry;
pub use crate::bytes::SourceFile;
pub use crate::bytes::Undecoded;
pub use crate::cache::Answer;
pub use crate::cache::Cache;
pub use crate::cache::ENTRY;
pub use crate::cache::Exit;
pub use crate::cache::FUNCTIONS;
pub use crate::cache::Origin;
pub use crate::cache::Program;
pub use crate::cache::Unread;
pub use crate::names::Available;
pub use crate::names::Bytes;
pub use crate::names::Commit;
pub use crate::names::CrateName;
pub use crate::names::FieldName;
pub use crate::names::FunctionPath;
pub use crate::names::LlvmType;
pub use crate::names::Offset;
pub use crate::names::SourcePath;
pub use crate::names::Status;
pub use crate::names::Symbol;
pub use crate::names::Target;
pub use crate::names::TypeName;
pub use crate::names::VariantName;
pub use crate::record::Arm;
pub use crate::record::Discriminant;
pub use crate::record::Extension;
pub use crate::record::Field;
pub use crate::record::Function;
pub use crate::record::Identity;
pub use crate::record::Layout;
pub use crate::record::Niche;
pub use crate::record::Operand;
pub use crate::record::Outcome;
pub use crate::record::Part;
pub use crate::record::Passage;
pub use crate::record::Record;
pub use crate::record::Refusal;
pub use crate::record::Shape;
pub use crate::record::Unstatable;
pub use crate::request::Edition;
pub use crate::request::Request;
