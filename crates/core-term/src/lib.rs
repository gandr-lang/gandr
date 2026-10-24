//! The core call-by-push-value language: its syntax in a flat arena, the one
//! unified typing context, the definition chain, and the per-scope
//! definitional environment.
//!
//! - [`CoreArena`] owns every [`Value`], [`Computation`], [`ValueType`] and
//!   [`CompType`] node, addressed by four typed ids.
//! - [`Classifier`] is what a type's own type is: a ground sort and a level.
//!   `Type[+, l]` and `Type[-, l]` are the two universe families, and a quote
//!   is the code of a type in one of them.
//! - The static calculus is three formers over codes: the static Pi classifies
//!   a type operator, and the static lambda and the static application are
//!   values, so a type operator is a value like any code.
//! - [`shift_value_type`], [`shift_comp_type`], [`strengthen_comp_type`] and
//!   [`strengthen_value_type`] are root updates: each answers a [`Relocated`]
//!   id — the subject's node under a [`Relocation`] — minting nothing, and
//!   [`Relocated::settle`] reads one into a plain id by the one eager walk;
//!   [`instantiate_comp_type`] and [`instantiate_value`], the substitution
//!   static beta takes, are iterative machines memoized per node, and every
//!   walk enters only the nodes whose support reaches what it moves;
//!   [`constructor_classifier`] reads a constructor's field telescope as the
//!   function its name answers at; [`rename_value_traced`] and
//!   [`rename_value_type_traced`] rename constants, atoms and region binders by
//!   a [`Renaming`], the step a functor application instantiates its body by
//!   and a call places a definition's regions by.
//! - [`Context`] is the two-zone typing context `Γ; Σ`: flat, de Bruijn,
//!   id-addressed and name-free. Names live in the surface syntax and in
//!   diagnostics, above this crate.
//! - [`DefinitionChain`] records each definition's body, as a canonical
//!   subterm-table entry index, and its unfolding height.
//! - [`DefinitionalEnvironment`] decides, scope by scope, whether a definition
//!   is manifest.
//! - [`identity`] derives `back`, `then` and `cong` as transports in families
//!   of paths, so element identity has one eliminator, `tr`, beside its type
//!   `Path` and its reflexivity `here`.
//! - [`ua`] holds what univalence at a stratum reads: the stratum a statement
//!   fixes and the two descriptions it relates, read as graphical species.
//! - [`world`] holds the located vocabulary: the handle type `A at w`, the
//!   capability `cap_w` a migration spends, and the computations `hold`, `leta`
//!   and `migrate [w]`, one former each beside the rest of the core.
//! - [`support`] is the co-de Bruijn carrier: a two-zone selection
//!   [`support::Thinning`] selects a node's support from its scope, every arena
//!   node carries its support from the moment it is minted, a
//!   [`support::Cover`] embeds each child's support in its parent's, and
//!   placing the edges from a root's support recovers the de Bruijn term. The
//!   incremental content table keys and footprints its nodes by it; the kernel
//!   term stays de Bruijn.
//! - [`row`] holds the closed [`row::Row`]: a finite map from labels to
//!   entries, each label once, in canonical order. The returner's
//!   [`effect::EffectRow`] is its effects reading, the interfaces a computation
//!   may perform.
//! - [`FailureClass`] is the four-class vocabulary every refusal of the core
//!   pipeline answers to, whichever crate produced it; an unimplemented one
//!   names its [`TrackingIssue`].
//!
//! The crate holds syntax and contexts; evaluation and readback live in
//! `gandr-core-nbe`, which consumes this vocabulary. Each module's
//! documentation states its mechanism and its decisions.
//!
//! # The dependent pair beside the product
//!
//! The dependent pair `Σ (x : A). B` is [`ValueType::Sigma`]: binary, its
//! second factor under one binder of the first. The eager product stays its
//! own former of any arity, and nothing converts between the two: a Σ whose
//! second factor does not read its binder is still a Σ. The pair is
//! [`Value::Tuple`] of two, which checks against a Σ and synthesises only a
//! product. [`Computation::TupleProjection`] projects a Σ, the second
//! projection's type reading the first projection; [`Computation::Split`]
//! under [`SplitMotive::Scrutinee`] eliminates it into a motive that reads
//! the scrutinee. A Σ has no η: a pair variable is not the pair of its
//! projections.
//!
//! - Alternatives: the product read as the Σ that ignores its binder, nested
//!   binary, which changes every product's arity, every tuple's shape and the
//!   product's kernel node; a dependent record former keyed by labels, which
//!   keeps the labels the surface erases at the cost of an eliminator beside
//!   the split; a package-style existential, opaque in its first component,
//!   which has no projections for a path at a Σ to read.
//! - Reversal: an n-ary Σ telescope former subsumes the product; a former keyed
//!   by labels carries the surface's labels into the core.
//!
//! # The co-de Bruijn carrier
//!
//! [`support`] keeps a term's syntactic support on the term. A selection is a
//! [`support::Thinning`]: per zone, the de Bruijn indices of a scope it keeps,
//! strictly ascending, read as an embedding of a compact scope into the one
//! it was selected from. A cover is one thinning per child of a node,
//! embedding the child's compact scope into the node's extended by the
//! binders the child's slot crosses, so a node's scope is exactly the
//! variables beneath it and one subterm under different unused binders is
//! one compact node. Placing every edge from a root's thinning recovers the
//! de Bruijn term, refusing an index past `u32` instead of saturating.
//!
//! - Choice: the carrier lives here, beside the zones and binder depths it is
//!   stated over, so every core vocabulary that adopts co-de Bruijn scoping
//!   shares one algebra and one witness set; the incremental content table is
//!   its first consumer, and the kernel term and the kernel wire stay de
//!   Bruijn.
//! - Alternatives: the carrier in the content table's crate, which the next
//!   consumers would depend on or copy; a crate of its own, apart from the
//!   zones it is stated over.
//! - Reversal: a consumer whose zones are not `Γ; Σ` moves the carrier into a
//!   crate of its own.
//!
//! A thinning is a tiered, self-describing code of words ([`support`] § The
//! tiered code), and every node of a [`CoreArena`] carries its support from
//! the moment it is minted (the arena module's § Carried supports), so a
//! support is read in constant time and nothing walks a term to find one.
//! The support is syntactic and over-approximates dependence; it keys,
//! footprints, schedules and decides the syntactic strengthening, never a
//! semantic one.
//!
//! # Specification attributes
//!
//! Nontrivial operations carry executable `#[spec(...)]` predicates and `#
//! Adequacy` hypotheses linked to runnable witnesses. The predicates observe
//! allocation indices and family lengths, lookup identity, the selected context
//! slot, and rewrite scheduling and reconstruction. `Context::open` and
//! `Context::occurrence` capture only bounded entry state: depth and
//! selected-slot observations are executable without cloning the context.
//! Finite transition witnesses distinguish changes to neighbouring slots.
//!
//! The choice is constant-size captures and local observations rather than
//! whole-arena or whole-context snapshots, which would allocate and can turn a
//! linear walk into a quadratic one. The variable rule checks the
//! below/equal/above-depth boundaries, including saturated arithmetic and
//! substitution beneath a binder. Independent level-based construction checks
//! 600 deterministic bounded codomains; fixed asymmetric goldens constrain that
//! reference observer, and the small-stack integration witness walks 50,000
//! static applications. These are scoped witnesses, not a proof of equivalence
//! for ungenerated terms.
//!
//! Run the crate with executable specifications enabled:
//!
//! ```sh
//! RUSTFLAGS="--cfg anodized_panic" cargo test -p gandr-core-term --all-targets
//! ```
//!
//! # References
//!
//! - Paul Blain Levy. _Call-By-Push-Value: A Functional/Imperative Synthesis_.
//!   Semantics Structures in Computation 2, Kluwer Academic Publishers, 2003.
//!   `isbn:978-1-4020-1730-8`, `doi:10.1007/978-94-007-0954-6` — the polarity
//!   split that makes values and computations two vocabularies.
//! - Nathanaëlle Courant and Xavier Leroy. "A Lazy, Concurrent Convertibility
//!   Checker." _Proceedings of the ACM on Programming Languages_ 10 (POPL),
//!   Article 53, January 2026. `doi:10.1145/3776695` — §6.4's hash-consed
//!   subterm DAG, whose entry index the definition chain carries as an
//!   arena-independent name for a body.
//! - Pierre-Marie Pédrot and Nicolas Tabareau. "The Fire Triangle: How to Mix
//!   Substitution, Dependent Elimination, and Effects." _Proceedings of the ACM
//!   on Programming Languages_ 4 (POPL), 2020. `doi:10.1145/3371126` — ∂CBPV's
//!   two levelled universe towers, and no kind layer above them.
//! - Josselin Poiret, Gaëtan Gilbert, Kenji Maillard, Pierre-Marie Pédrot,
//!   Matthieu Sozeau, Nicolas Tabareau and Éric Tanter. "All Your Base Are
//!   Belong to Us: Sort Polymorphism for Proof Assistants." _Proceedings of the
//!   ACM on Programming Languages_ 9 (POPL), 2025. `doi:10.1145/3704912` — the
//!   sort separated from the level and quantified over, which `Sort::Parameter`
//!   leaves room for.
//! - Cyrus Omar, Ian Voysey, Michael Hilton, Jonathan Aldrich and Matthew A.
//!   Hammer. "Hazelnut: A Bidirectionally Typed Structure Editor Calculus."
//!   _POPL 2017_. <https://doi.org/10.1145/3009837.3009900> — the hole and mark
//!   formers, the unknown type and the matched-type operations.
//! - Cyrus Omar, Ian Voysey, Ravi Chugh and Matthew A. Hammer. "Live Functional
//!   Programming with Typed Holes." _Proceedings of the ACM on Programming Languages_
//!   3 (POPL), 2019. <https://doi.org/10.1145/3290327> — filling as
//!   substitution of the hole by its fill, the syntactic half `fill_hole`
//!   provides.
//! - Yongwei Yuan et al. "Live Pattern Matching with Typed Holes." _Proceedings
//!   of the ACM on Programming Languages_ 7 (OOPSLA1), 2023. <https://doi.org/10.1145/3586048>
//!   — the pattern hole and the three answers a branch can get.
//! - Eric Zhao et al. "Total Type Error Localization and Recovery with Holes."
//!   _Proceedings of the ACM on Programming Languages_ 8 (POPL), 2024.
//!   <https://doi.org/10.1145/3632910> — the mark former as the place an error
//!   stands, and `wrap_marks` as the elaboration's last step.
//! - Luc Maranget. "Warnings for pattern matching." _Journal of Functional
//!   Programming_ 17(3) (2007). <https://doi.org/10.1017/S0956796807006223> —
//!   the coverage questions the pattern table is read for, answered in
//!   `gandr-core-checker`.

// Module documentation that predates the shape lint: 81 headings outside the
// vocabulary, 35 decision records, 14 issue references and 11 budgets exceeded.
// Each allow leaves with the rewrite that clears its count.
#![cfg_attr(
    dylint_lib = "quenchant_dylints",
    allow(
        module_doc_heading,
        doc_decision_record,
        doc_issue_reference,
        module_doc_budget,
        reason = "module documentation that predates the shape lint"
    )
)]
#![no_std]

extern crate alloc;

mod arena;
mod classifier;
mod context;
pub mod control;
mod definition;
pub mod description;
pub mod effect;
mod failure;
pub mod hole;
pub mod identity;
mod import;
pub mod memory;
pub mod model;
pub mod pattern;
pub mod primitive;
mod relocation;
mod rewrite;
pub mod row;
pub mod session;
pub mod staged;
pub mod support;
mod syntax;
pub mod ua;
pub mod world;

pub use gandr_kernel_term::CellIndex;
pub use gandr_kernel_term::Component;
pub use gandr_kernel_term::ConstructorTag;
pub use gandr_kernel_term::FieldLabel;
pub use gandr_kernel_term::FreeCell;
pub use gandr_kernel_term::FreeCells;
pub use gandr_kernel_term::Presentation;
pub use gandr_kernel_term::PresentedRule;
pub use gandr_kernel_term::RuleNode;
pub use gandr_kernel_term::RuleVariable;
pub use gandr_kernel_term::Summand;

pub use crate::arena::ArenaWatermark;
pub use crate::arena::BinderPrecedence;
pub use crate::arena::CompTypeId;
pub use crate::arena::ComputationId;
pub use crate::arena::CoreArena;
pub use crate::arena::ValueId;
pub use crate::arena::ValueTypeId;
pub use crate::classifier::Classifier;
pub use crate::classifier::Sort;
pub use crate::classifier::SortParameter;
pub use crate::context::BinderDepth;
pub use crate::context::Context;
pub use crate::context::ContextError;
pub use crate::context::LinearUse;
pub use crate::context::LinearZone;
pub use crate::definition::DefinitionChain;
pub use crate::definition::DefinitionEntry;
pub use crate::definition::DefinitionError;
pub use crate::definition::DefinitionHeight;
pub use crate::definition::DefinitionalEnvironment;
pub use crate::definition::ScopeId;
pub use crate::definition::Transparency;
pub use crate::failure::FailureClass;
pub use crate::failure::TrackingIssue;
pub use crate::failure::tracked;
pub use crate::import::ImportFault;
pub use crate::import::TypeImporter;
pub use crate::relocation::Relocated;
pub use crate::relocation::Relocation;
pub use crate::rewrite::Binders;
pub use crate::rewrite::Carried;
pub use crate::rewrite::Crossing;
pub use crate::rewrite::Nesting;
pub use crate::rewrite::Renaming;
pub use crate::rewrite::Unenclosed;
pub use crate::rewrite::abstract_constant_value_type;
pub use crate::rewrite::build_type_updates;
pub use crate::rewrite::build_updates;
pub use crate::rewrite::constructor_classifier;
pub use crate::rewrite::cross_reducts;
pub use crate::rewrite::delinearise;
pub use crate::rewrite::elaborate_nested_traced;
pub use crate::rewrite::fill_comp_type_hole;
pub use crate::rewrite::fill_hole;
pub use crate::rewrite::fill_value_hole;
pub use crate::rewrite::fill_value_type_hole;
pub use crate::rewrite::instantiate_comp_type;
pub use crate::rewrite::instantiate_comp_type_at_call;
pub use crate::rewrite::instantiate_computation_traced;
pub use crate::rewrite::instantiate_value;
pub use crate::rewrite::instantiate_value_type;
pub use crate::rewrite::instantiate_value_type_under;
pub use crate::rewrite::raise_linear_traced;
pub use crate::rewrite::relevel_value_type;
pub use crate::rewrite::rename_value_traced;
pub use crate::rewrite::rename_value_type_traced;
pub use crate::rewrite::shift_comp_type;
pub use crate::rewrite::shift_comp_type_under;
pub use crate::rewrite::shift_computation_under;
pub use crate::rewrite::shift_value;
pub use crate::rewrite::shift_value_type;
pub use crate::rewrite::shift_value_type_under;
pub use crate::rewrite::strengthen_comp_type;
pub use crate::rewrite::strengthen_value;
pub use crate::rewrite::strengthen_value_type;
pub use crate::rewrite::strengthening;
pub use crate::rewrite::substitute_environment;
pub use crate::rewrite::substitute_environment_traced;
pub use crate::rewrite::wrap_marks;
pub use crate::syntax::CertificateEquality;
pub use crate::syntax::CodataSignature;
pub use crate::syntax::CompType;
pub use crate::syntax::ComponentCount;
pub use crate::syntax::Computation;
pub use crate::syntax::DataSignature;
pub use crate::syntax::SplitMotive;
pub use crate::syntax::Value;
pub use crate::syntax::ValueType;
pub use crate::syntax::Zone;
pub use crate::syntax::decoded_comp_reading;
pub use crate::syntax::equal_certificate_syntax;
pub use crate::syntax::equal_comp_type_syntax;
pub use crate::syntax::equal_type_reading;
pub use crate::syntax::equal_type_syntax;
pub use crate::syntax::identified_words;
pub use crate::syntax::unworded;
