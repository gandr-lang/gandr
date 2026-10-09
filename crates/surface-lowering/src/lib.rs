//! **Lowering the gandr surface into the core language**: the type-head and
//! term-name resolution tables, the module collection pass that pairs
//! signatures with definitions, the reserved-form decline, the attribute
//! registry with its five diagnostics and its side table, the origin table
//! over terms and types alike, the failure classifier every refusal answers
//! to, and the [`namespace`] engine the module's imports and outermost names
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
//! # Six decisions that interlock
//!
//! **Names resolve through tables with no fallthrough.** `Unit`, `Integer`,
//! `String`, `+U` and `-F` answer from a type-head table indexed by arity, and
//! a term name answers from the enclosing binders, then the module's earlier
//! declarations. Nothing falls through to an opaque atom: an unanswered name is
//! a refusal with a span, so a misspelling is a mistake rather than a new
//! nominal type.
//!
//! **A module is collected by name and resolved by position.** A signature
//! pairs with its definition wherever the two sit, so the
//! signature-then-definition form stays spellable; references still resolve by
//! admission position, so self-reference and mutual reference are refused.
//!
//! **A signature no definition completes is what an artifact owes.** That case
//! is its own outcome, because it is the producer an obligation ledger reads —
//! and because nothing the lowering *refuses* may become an obligation, which
//! the failure classifier states by leaving its absence class empty.
//!
//! **Reserved forms are declined by name.** The product type and the pair parse
//! and then refuse, so the classifier's unrepresentable class has a real
//! inhabitant from the first landing.
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
//! Each decision, with the alternative it was chosen over and what would
//! reverse it, is in this crate's `README.md`.

#![no_std]

extern crate alloc;

mod attribute;
mod classify;
mod error;
#[cfg(test)]
mod fixture;
mod form;
mod import;
mod lower;
mod module;
pub mod namespace;
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
pub use crate::module::DeclarationCount;
pub use crate::module::DeclarationOutcome;
pub use crate::module::LoweredDeclaration;
pub use crate::module::LoweredModule;
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
