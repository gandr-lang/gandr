//! **Lowering the gandr surface into the core language**: the type-head and
//! term-name resolution tables, the module collection pass that pairs
//! signatures with definitions and flattens module declarations to named
//! members, the reserved-form decline, the attribute registry with its five
//! diagnostics and its side table, the origin table over terms and types
//! alike, the failure classifier every refusal answers to, and the
//! [`namespace`] engine the module's imports, outermost names and module paths
//! are bound by.
//!
//! The crate reads the molded tree the parser builds and writes a core arena.
//! There is no lexer here, no parser, and no checker: the tree arrives built,
//! the core nodes leave minted, and what a term *means* is decided above.
//!
//! # The grammar names every form
//!
//! Every node is dispatched on the named kind the grammar gives its mold, and
//! every token the grammar folded into a form is read by its label among the
//! form's own tiles, apart from the form's operands. A parser repair — grout
//! where the source wrote no term, a closing delimiter the source never wrote —
//! is reported where it stands rather than lowered around.
//!
//! # Seven decisions that interlock
//!
//! **Names resolve through tables with no fallthrough.** `Unit`, `Integer`,
//! `String`, `+U` and `-F` answer from a type-head table indexed by arity, and
//! a term name answers from the enclosing binders, then the module's earlier
//! declarations, then the operations earlier `data` families run (the
//! decisions are in `operation`). Nothing falls through to an opaque atom: an
//! unanswered name is a refusal with a span, so a misspelling is a mistake
//! rather than a new nominal type.
//!
//! **A module is collected by name and resolved by position.** A signature
//! pairs with its definition wherever the two sit, so the
//! signature-then-definition form stays spellable; references still resolve by
//! admission position, so self-reference and mutual reference are refused.
//!
//! **A module declaration flattens to named members.** Each member of
//! `module M { … }`, at every depth, is one declaration admitted in source
//! order under its structured name, the enclosing modules' names then its
//! own; a path is governed by the module that binds it, and an inline
//! signature reorders the exports and hides what it omits, checking each
//! component at its member.
//!
//! **A signature no definition completes is what an artifact owes.** That case
//! is its own outcome, because it is the producer an obligation ledger reads —
//! and because nothing the lowering *refuses* may become an obligation, which
//! the failure classifier states by leaving its absence class empty.
//!
//! **Type operators lower to the static calculus over codes.** `\A. T` is a
//! static lambda over the code of its body, an arrow where a value type is
//! read is a static Pi, and an operator a binder or a declaration names,
//! applied to arguments, is a static application — the decode of one where a
//! type is read. `A * B` and `(a, b)` are the eager product and its pair, and
//! `(A1, …, An) => B` is exactly `+U (A1 -> … -> An -> -F B)`.
//!
//! **Reserved forms are declined by name.** The lazy product parses and then
//! refuses, so the classifier's unrepresentable class keeps a real
//! inhabitant.
//!
//! **Origins are carried for types as well as terms.** Every minted core node
//! records the syntax node that produced it, and a declaration's own origin
//! travels as an opaque token a checker echoes back, which keeps spans and
//! names out of the core.
//!
//! **Imports bind an alias and resolve nothing.** `import "URI" as name ;` is
//! kept in source order and its alias bound in the module's import scope by
//! the namespace engine's `alias_as`; the address waits for the pass that
//! resolves it.
//!
//! # Two sweeps, no recursion
//!
//! The tree is laid out in level order, so ascending position order visits
//! every parent before its children and descending order visits every child
//! before its parent. Lowering classifies on the way down and mints on the way
//! up, each as a plain loop: no descent, no explicit frame stack, and no depth
//! a real module can overflow.
//!
//! # Early exits leave by a direct cut
//!
//! `return v` and `become c` leave the nearest function, lambda or thunk from
//! wherever a path through its body passes: a nested match, the computation
//! of a `run`, a block inside an arm. The lowering puts every exit where its
//! body ends. A statement `x ← M; N` whose `M` holds an exit commutes: the
//! rest `N` moves into every local end of `M`, the commuting conversion of
//! call-by-push-value (Levy, *Call-By-Push-Value: A Functional/Imperative
//! Synthesis*, 2003), and a local end `return w` continues by the beta step
//! `N[w/x]`. Each exit then stands in tail position, and focusing makes it
//! the cut `⟨v | k⟩` of its value against the body's own return
//! continuation `k` — the one `μ` the body binds (Downen and Ariola, *A
//! tutorial on computational classical logic and the sequent calculus*,
//! 2018). No handler frame is installed, no resumption is captured, and no
//! core or kernel former is new: the checker and the kernel read the
//! commuted body as any other, and a `become` loop leaving early still runs
//! in constant continuation. The rest is copied once per binder depth it
//! reaches, the price of having no join point.
//!
//! The alternatives were two. An effect per function, its exits performed
//! and its call handled, was declined because the handler frame breaks the
//! constant continuation of `become`, every exit captures a stack, and the
//! kernel admits no handler. A core control binder with a jump to it was
//! declined because every consumer of the core and the bridge to the kernel
//! would learn a new former, and the kernel would still need the commuted
//! form. Reversal: when the lowering fragment reaches handlers, or the core
//! and the kernel gain join points, an exit lowers to a jump and the rest is
//! no longer copied.
//!
//! # Example
//!
//! ```
//! use gandr_core_term::CoreArena;
//! use gandr_surface_grammar::built_in;
//! use gandr_surface_lowering::DeclarationOutcome;
//! use gandr_surface_lowering::LoweringBudget;
//! use gandr_surface_lowering::lower_module;
//! use gandr_surface_lowering::namespace::Recognition;
//! use gandr_surface_parser::parse;
//! use gandr_surface_syntax::SourceText;
//!
//! let pbg = built_in()?;
//! let tree = parse(&pbg, SourceText::from("def x : Integer ; def x = 3 ;"))?.into_tree();
//! let mut arena = CoreArena::new();
//! let module = lower_module(
//!     &pbg,
//!     &tree,
//!     &mut arena,
//!     LoweringBudget::DEFAULT,
//!     Recognition::default(),
//! )?;
//!
//! let [declaration] = module.declarations()
//! else {
//!     unreachable!("one name is declared");
//! };
//! assert!(
//!     matches!(declaration.outcome(), DeclarationOutcome::Completed { .. }),
//!     "the signature and the definition pair into one completed declaration"
//! );
//! # Ok::<(), Box<dyn core::error::Error>>(())
//! ```
//!
//! Each of the seven decisions, with the alternative it was chosen over and
//! what would reverse it, is in the module that owns it.
//!
//! # References
//!
//! - Paul Blain Levy. "Call-by-Push-Value: A Subsuming Paradigm." _Typed Lambda
//!   Calculi and Applications (TLCA 1999)_, LNCS 1581, Springer (1999). <https://doi.org/10.1007/3-540-48959-2_17>
//!   — the value and computation sorts, thunks and returners (`U` and `F`), and
//!   the arrow as a computation type, which fix every sort a position demands.
//! - N. G. de Bruijn. "Lambda calculus notation with nameless dummies."
//!   _Indagationes Mathematicae_ 75(5) (1972).
//!   <https://doi.org/10.1016/1385-7258(72)90034-0> — the binder indices a
//!   lambda's parameter lowers to.
//! - Thierry Coquand and Christine Paulin. "Inductively defined types."
//!   _COLOG-88_, LNCS 417, Springer (1990), 50–66.
//!   <https://doi.org/10.1007/3-540-52335-9_47> — the uniform parameters a
//!   recursive function's leading parameters are, passed unchanged by every
//!   recursive call.
//! - Eduardo Giménez. "Structural recursive definitions in type theory." _ICALP
//!   1998_, LNCS 1443, Springer (1998). <https://doi.org/10.1007/BFb0055070> —
//!   the guarded fixpoint `fix x. λy. case y` a recursive function lowers to,
//!   every recursive call at a field of the scrutinised constructor.
//! - Conor `McBride`. "Elimination with a Motive." _Types for Proofs and Programs
//!   (TYPES 2000)_, LNCS 2277, Springer (2002).
//!   <https://doi.org/10.1007/3-540-45842-5_13> — the alternative not taken:
//!   later parameters pushed into the motive, which would let a recursive call
//!   vary them.
//! - Pierre-Marie Pédrot and Nicolas Tabareau. "The Fire Triangle: How to Mix
//!   Substitution, Dependent Elimination, and Effects." _Proceedings of the ACM
//!   on Programming Languages_ 4 (POPL), 2020. `doi:10.1145/3371126` — ∂CBPV's
//!   universe of value types and universe of computation types, a type's code
//!   as a value, and dependency on values only, which fix what a quote, a
//!   decode and a dependent arrow lower to.
//! - Thorsten Altenkirch, James Chapman and Tarmo Uustalu. "Monads Need Not Be
//!   Endofunctors." _Logical Methods in Computer Science_ 11(1) (2015).
//!   <https://doi.org/10.2168/LMCS-11(1:3)2015> — the relative monad, whose raw
//!   signature is the type operator `static_operators` declares in both
//!   spellings.
//! - David Moon, Andrew Blinn, Thomas J. Porter and Cyrus Omar. "Syntactic
//!   Completions with Material Obligations." _Proceedings of the ACM on
//!   Programming Languages_ 9, OOPSLA2 (2025).
//!   <https://doi.org/10.1145/3763182>, arXiv:2508.16848 — molds, grout and the
//!   minted closing tiles a repaired tree carries, which the lowering reads and
//!   refuses.
//! - V. I. Levenshtein. "Binary codes capable of correcting deletions,
//!   insertions, and reversals." _Soviet Physics Doklady_ 10(8) (1966) — the
//!   edit distance that bounds an unknown attribute's suggestion.
//! - `RedPRL`. _yuujinchou_ 5.2.0. <https://github.com/RedPRL/yuujinchou> — the
//!   namespace design: tries of hierarchical names, the modifier language, the
//!   not-found, shadow and hook events a handler settles, and scopes with
//!   sections.

#![no_std]

extern crate alloc;

mod attribute;
pub mod circuit;
mod classify;
pub mod desc_cells;
pub mod description;
mod doc;
mod error;
#[cfg(test)]
mod fixture;
mod form;
mod import;
mod lower;
mod module;
pub mod namespace;
mod operation;
mod origin;
mod resolve;

pub use crate::attribute::AttributeEntry;
pub use crate::attribute::AttributeRegistry;
pub use crate::attribute::AttributeSchema;
pub use crate::attribute::AttributeTable;
pub use crate::attribute::AttributedCount;
pub use crate::attribute::EditDistance;
pub use crate::attribute::PayloadForm;
pub use crate::attribute::PayloadVerdict;
pub use crate::attribute::RegisteredAttribute;
pub use crate::attribute::payload_form;
pub use crate::attribute::payload_verdict;
pub use crate::classify::FailureClass;
pub use crate::doc::DocLink;
pub use crate::doc::Documentation;
pub use crate::doc::DocumentationText;
pub use crate::doc::documentation;
pub use crate::error::AscriptionForm;
pub use crate::error::FormFault;
pub use crate::error::FragmentBoundary;
pub use crate::error::FragmentSort;
pub use crate::error::LoweringRefusal;
pub use crate::form::FormName;
pub use crate::form::Former;
pub use crate::form::Repair;
pub use crate::form::former_of;
pub use crate::import::ImportDeclaration;
pub use crate::import::ImportIndex;
pub use crate::import::ImportUri;
pub use crate::import::ModuleImports;
pub use crate::lower::Fuel;
pub use crate::lower::LoweringBudget;
pub use crate::lower::lower_module;
pub use crate::module::Coerced;
pub use crate::module::Container;
pub use crate::module::DataIndex;
pub use crate::module::DeclarationCount;
pub use crate::module::DeclarationOutcome;
pub use crate::module::LoweredDeclaration;
pub use crate::module::LoweredModule;
pub use crate::module::LoweredStructure;
pub use crate::module::ManifestComponent;
pub use crate::module::Role;
pub use crate::module::StructureIndex;
pub use crate::module::ValueComponent;
pub use crate::module::manifest_type;
pub use crate::origin::ArmOrigin;
pub use crate::origin::CaseOrigin;
pub use crate::origin::Insertion;
pub use crate::origin::Origin;
pub use crate::origin::OriginCount;
pub use crate::origin::OriginTable;
pub use crate::origin::OriginToken;
pub use crate::origin::Provenance;
pub use crate::resolve::Bound;
pub use crate::resolve::Frame;
pub use crate::resolve::HeadArity;
pub use crate::resolve::Mentioned;
pub use crate::resolve::OperandCount;
pub use crate::resolve::Scope;
pub use crate::resolve::ScopeId;
pub use crate::resolve::SurfaceName;
pub use crate::resolve::TypeAtom;
pub use crate::resolve::TypeFormer;
pub use crate::resolve::type_atom;
pub use crate::resolve::type_former;
