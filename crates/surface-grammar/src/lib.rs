//! The checked precedence-bounded grammar of the gandr surface.
//!
//! A [`Pbg`] is a set of [`Rule`]s over a precedence DAG that has passed three
//! build-time gates: Operator Form, Unique Tiles and Assumption 3 (Moon,
//! Blinn, Porter and Omar 2025). Building it assigns every tile occurrence a
//! mold — its zipper into the grammar — with precedence bounds, zipper steps,
//! same-form adjacency and closing class precomputed, and folds the whole
//! table into a fingerprint a tree's [`MoldId`]s are read under.
//!
//! - [`Pbg`], [`Rule`], [`Regex`], [`Sort`] and [`PbgError`] are the model;
//!   [`validate_operator_form`], [`validate_unique_tiles`] and
//!   [`validate_assumption_3`] are the gates on their own.
//! - [`walk_index`] instantiates the theory-graphs walk machine over a
//!   grammar's molds; [`comparison_table`] reads the operator-precedence
//!   relation off it.
//! - [`built_in`] is the gandr surface: [`built_in_prec_table`]'s groups and
//!   the term, type-and-shell and circuit forms.
//! - [`named_kind_parity`] is the inventory of how each named kind of the
//!   surface's tree-sitter grammar is realised.
//! - [`RoleTable`] is the mold highlighter: one highlight role per mold, read
//!   off the grammar, and the spans of a molded tree's tiles read through it.
//!
//! The crate is `no_std` and depends on `core`, `alloc`,
//! `gandr-surface-render-remote`, `gandr-surface-syntax` and
//! `gandr-theory-graphs`. It parses nothing: a parser reads a [`Pbg`], and the
//! highlighter reads the tree a parser committed.
//!
//! [`MoldId`]: gandr_surface_syntax::MoldId

#![no_std]

extern crate alloc;

mod check;
mod highlight;
mod model;
mod mold;
mod parity;
mod surface;
mod walk;

pub use crate::check::validate_assumption_3;
pub use crate::check::validate_operator_form;
pub use crate::check::validate_unique_tiles;
pub use crate::highlight::HighlightError;
pub use crate::highlight::RoleTable;
pub use crate::model::Adaptation;
pub use crate::model::AdaptationReason;
pub use crate::model::CandidateCount;
pub use crate::model::MoldCount;
pub use crate::model::Pbg;
pub use crate::model::PbgError;
pub use crate::model::PrecName;
pub use crate::model::PrecPresence;
pub use crate::model::PrecTable;
pub use crate::model::Provenance;
pub use crate::model::Regex;
pub use crate::model::RegexShape;
pub use crate::model::RegexView;
pub use crate::model::Rule;
pub use crate::model::RuleName;
pub use crate::model::Sort;
pub use crate::model::SortName;
pub use crate::model::SurfaceForm;
pub use crate::model::Sym;
pub use crate::model::Tile;
pub use crate::model::TileLabel;
pub use crate::mold::MoldDef;
pub use crate::mold::MoldHasPredecessor;
pub use crate::mold::MoldHasRequiredTail;
pub use crate::mold::MoldHasSuccessor;
pub use crate::mold::MoldIsFormFirst;
pub use crate::mold::MoldIsFormLast;
pub use crate::mold::MoldsAdjacent;
pub use crate::mold::RCtxId;
pub use crate::mold::RCtxStep;
pub use crate::mold::StepSym;
pub use crate::parity::NamedKind;
pub use crate::parity::NamedKindEntry;
pub use crate::parity::NamedKindRealization;
pub use crate::parity::named_kind_parity;
pub use crate::parity::named_kind_realization;
pub use crate::surface::PBG_ONLY_KINDS;
pub use crate::surface::TREE_SITTER_NAMED_KINDS;
pub use crate::surface::built_in;
pub use crate::surface::built_in_prec_table;
pub use crate::walk::Comparison;
pub use crate::walk::ComparisonRow;
pub use crate::walk::GrammarNonterminal;
pub use crate::walk::GrammarTile;
pub use crate::walk::GrammarWalkSym;
pub use crate::walk::MAX_WALK_CHAIN_LEN;
pub use crate::walk::comparison_table;
pub use crate::walk::reachable_molds;
pub use crate::walk::seen_key_verdict;
pub use crate::walk::walk_index;
