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
//! - [`Pbg::tile_kind`], [`Pbg::observation`] and [`Pbg::tile_set`] read the
//!   tile automaton: each mold's kind and observation class, and the sets a
//!   parser admits by kind and sort, as bitsets derived once per grammar.
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
//!
//! # Scope
//!
//! The crate holds the grammar and what is computed from it; it parses nothing.
//! The highlighter is here because a role is read off the mold table alone; the
//! role vocabulary is not, since every renderer reads it, and it lives in the
//! renderer seam, `gandr-surface-render-remote`. The contract suite that drives
//! a parser over the built-in surface is not here either: it needs the parser,
//! and it lives with the parser crate; the highlighter's corpus suite runs the
//! parser as a dev-dependency. User-declared operators are not in the grammar:
//! the built-in surface's `operator_declaration` rule parses a fixity
//! declaration so the elaborator can decline it by name, and a grammar is never
//! extended at run time. Adding them adds an extension entry point together
//! with its fixity vocabulary.
//!
//! # Specification evidence
//!
//! Executable predicates cover regex shapes, rule assembly, validation
//! refusals, context and mold identities, walk projections, precedence
//! relations and highlighting. Each nontrivial item's adequacy block names its
//! input domain, observer, mutation classes and boundary, with crate-local
//! witnesses. The enforcing test lane runs the same corpus and boundary cases
//! through the predicates. Exact grammar identity and role goldens complement
//! structural observations; they do not prove every possible user-defined
//! grammar.
//!
//! Resolution predicates mark output positions as input keys resolve,
//! preserving exact coverage with aliases without a quadratic reverse search.
//! Adjacency ordering, ownership and exact incoming/outgoing flags are checked
//! at construction. Read-only queries check the stored answer or borrowed-table
//! identity instead of rescanning immutable edges on every parser lookup.
//!
//! Opaque iterator returns, write-only formatters and the fingerprint getter's
//! opaque const result have explicit executable exemptions. Their witnesses
//! observe yielded identities, formatted payloads and sink failure, or concrete
//! fingerprint framing instead of asserting properties the item cannot inspect.
//!
//! # References
//!
//! - David Moon, Andrew Blinn, Thomas J. Porter, and Cyrus Omar. "Syntactic
//!   Completions with Material Obligations." _Proceedings of the ACM on
//!   Programming Languages_ 9, OOPSLA2 (October 2025). `doi:10.1145/3763182`;
//!   preprint `arXiv:2508.16848` — the precedence-bounded grammar, the Operator
//!   Form, Unique Tiles and Assumption 3 conditions of § 3, molds, the walk
//!   vocabulary, and the melder's Reduce of figure 29 that decides which forms
//!   an operator may take.
//! - Nils Anders Danielsson and Ulf Norell. "Parsing Mixfix Operators." In
//!   _Implementation and Application of Functional Languages (IFL 2008)_,
//!   Lecture Notes in Computer Science 5836, pages 80–99, 2011.
//!   `doi:10.1007/978-3-642-24452-0_5` — precedence as a graph of groups that
//!   need not be totally ordered, which the built-in surface's bands are.
//! - Micha Sharir. "A Strong-Connectivity Algorithm and Its Applications in
//!   Data Flow Analysis." _Computers & Mathematics with Applications_ 7, 1
//!   (1981), pages 67–72. `doi:10.1016/0898-1221(81)90008-0` — the condensation
//!   the closing-class derivation folds over.
//! - Glenn Fowler, Landon Curt Noll, Kiem-Phong Vo, Donald Eastlake 3rd, and
//!   Tony Hansen. "The FNV Non-Cryptographic Hash Algorithm." RFC 9923,
//!   February 2026. `doi:10.17487/RFC9923` — the accumulator the grammar
//!   fingerprint is computed with.

#![no_std]

extern crate alloc;

mod automaton;
mod check;
mod highlight;
mod model;
mod mold;
mod parity;
mod surface;
mod walk;

pub use crate::automaton::MoldSet;
pub use crate::automaton::MoldWord;
pub use crate::automaton::MoldWordIndex;
pub use crate::automaton::Observation;
pub use crate::automaton::TileKind;
pub use crate::automaton::TileSet;
pub use crate::automaton::TileTableBytes;
pub use crate::check::validate_assumption_3;
pub use crate::check::validate_operator_form;
pub use crate::check::validate_unique_tiles;
pub use crate::highlight::HighlightError;
pub use crate::highlight::RoleTable;
pub use crate::model::Adaptation;
pub use crate::model::AdaptationReason;
pub use crate::model::CandidateCount;
pub use crate::model::LabelText;
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
pub use crate::mold::MoldInSet;
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
