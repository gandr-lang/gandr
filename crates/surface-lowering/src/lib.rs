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
//! # Ten decisions that interlock
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
//! admission position, so self-reference and mutual reference are refused
//! outside a `rec { }` block, whose members are admitted as one.
//!
//! **A module declaration flattens to named members.** Each member of
//! `module M { … }`, at every depth, is one declaration admitted in source
//! order under its structured name, the enclosing modules' names then its
//! own; a path is governed by the module that binds it, and an inline
//! signature reorders the exports and hides what it omits, checking each
//! component at its member.
//!
//! **An opaque ascription mints one atom per abstract component.** `module M
//! :> #{ type T, … } { type T = τ ; … }` checks its body against `τ`, declares
//! one abstract type per abstract component when the module opens — keyed by
//! its site, the module and the component's place in the signature, never a
//! name — and exports every type naming `T` at that atom, which past the
//! module relates to nothing but itself; `:` keeps `τ` visible (the decisions
//! are in `module::sealing`).
//!
//! **`Model(S)` is derived, never written.** `module M : Model(S) { … }` is
//! checked against the signature the lowering derives from the presentation
//! of the `theory S` declared before it: a type component per sort, a type
//! family per indexed sort over its index telescope, a member per operation
//! binding its free sorts first, and a `Path`-typed member per rule — node for
//! node what the hand-written spelling lowers to. A type member with
//! parameters, `type Hom(a : Ob, b : Ob) = τ`, expands where it is applied
//! (the decisions are in `model` and `module::model`). For a member written as
//! a `def` to meet its component, a telescope entry and a dependent arrow
//! `(x : A) -> C` bind exactly where a later type names their binder, as a
//! function's parameters do. The alternative, #266's choice, reads every named
//! binder of `(x : A) -> C` as dependent, the spelling taken as written; it
//! makes `(n : Integer) => Integer` and `def g(n : Integer) -> -F Integer` two
//! types (#577). Transport motives still read, the motive reader taking either
//! arrow (the decision is in `lower::arity`).
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
//! type is read. `A * B` and `(a, b)` are the eager product and its pair,
//! `A + B` is the sum, `(A1, …, An) => B` is exactly `+U (A1 -> … -> An ->
//! -F B)`, and the arity-shaped formers `#{…}`, `+{…}` and `&{…}` lower to
//! the core's product, record, sum and lazy product.
//!
//! **Reserved forms are declined by name.** A recursive call's claim other
//! than `<` parses and then refuses as unimplemented, naming the issue that
//! tracks it.
//!
//! **Origins are carried for types as well as terms.** Every minted core node
//! records the syntax node that produced it, and a declaration's own origin
//! travels as an opaque token a checker echoes back, which keeps spans and
//! names out of the core.
//!
//! **An import brings a sibling's declarations in.** `import "<path>" ;` and
//! `import "<path>" as name ;` are kept in source order; [`lower_unit`] lowers
//! the sources a [`Unit`] lays end to end into one arena, each path import
//! resolved to an earlier source, so a sibling's declarations are the prefix of
//! its importer's constants. The [`import`] module states the
//! mechanism, the refusals and the reversal.
//!
//! # Two sweeps, no recursion
//!
//! The tree is laid out in level order, so ascending position order visits
//! every parent before its children and descending order visits every child
//! before its parent. Lowering classifies on the way down and mints on the way
//! up, each as a plain loop over one source's positions: no descent, no
//! explicit frame stack, and no depth a real module can overflow.
//!
//! # A unit is lowered a source at a time
//!
//! **Choice.** [`lower_unit`] lowers a unit's sources one at a time, in the
//! unit's order: a source's top-level forms are collected after the earlier
//! sources' and every pass runs over that source alone, against what the
//! earlier sources left (the names, modules, data, constructors, signatures
//! and exported paths), before the next source is collected. The arena is
//! one; each source mints into it after the sources it imports. What a source
//! lowers to — its declarations and its arena rows, ids included — is
//! therefore the same whether or not other sources follow it, and a unit's
//! lowering starts with the lowering of its leading sources.
//!
//! **Why.** Run pass by pass over the whole unit, every source's types were
//! minted before any source's terms, so an importer's nodes stood among its
//! imports' and nothing lowered for an import closure could be kept across
//! edits to the importer: on the λ-calculus model record of #776, 11 of the
//! 109 declarations of a 19-source unit kept their ids when the last source
//! followed, against all 107 of the closure's matching by name and outcome.
//! Imports point only backward, so no pass over a source needs a later one.
//!
//! **Alternatives.** Keeping a snapshot of the pass-by-pass lowering cannot
//! resume, since its ids depend on the last source. Lowering each source
//! alone against an interface of external constants would give the lowering
//! and the checker a second way to name an imported declaration.
//!
//! **Reversal.** A pass that must read a later source, a forward import, would
//! run its share of the unit after the sources it reads.
//!
//! # Early exits leave by a direct cut
//!
//! `return v` and `become c` leave the nearest function, lambda or thunk from
//! wherever a path through its body passes: a nested match, the computation
//! of a `run`, a block inside an arm. Where a path ends the keyword may go
//! unwritten: the lowering infers the exit the tail's polarity names —
//! `return` over a value, `become` over a computation — checks it as a
//! written one, and lists it in [`LoweredModule::inferred_exits`]; the
//! `explicit-exits` lint asks for it written. The lowering puts every exit
//! where its body ends. A statement `x ← M; N` whose `M` holds an exit
//! commutes: the rest `N` moves into every local end of `M`, the commuting
//! conversion of call-by-push-value (Levy, *Call-By-Push-Value: A
//! Functional/Imperative Synthesis*, 2003), and a local end `return w`
//! continues by the beta step `N[w/x]`. Each exit then stands in tail
//! position, and focusing makes it
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
//! form. Reversal: when the core and the kernel gain join points, an exit
//! lowers to a jump and the rest is not copied.
//!
//! # A handler's frame is crossed by `return` alone
//!
//! A capability scope's subject runs inside its handler's frame, so an exit
//! written there acts past that frame (#127, #216). A `return v` in the
//! subject leaves the body around the scope with `v`: every handler frame
//! between is unwound, and no return clause runs. A `become`, and a `break`
//! or a `continue` whose loop holds the scope, are refused as
//! [`LoweringRefusal::AcrossHandler`]: each would run code in place of a live
//! frame, which is no tail. The subject's own tail is its result, which the
//! `pure` clause receives, and is no exit; each clause is a body of its own,
//! so an exit there is the scope's value. A loop inside the subject is a loop
//! as any other.
//!
//! The commuting above stays the mechanism of every other exit, and of a
//! subject's own statements. The `return` across a frame is the one exit
//! that leaves by the core's delimited control: it lowers to a shift that
//! discards what it captures, and the body it leaves is minted under a
//! reset. The machine's shift captures through handler frames to the nearest
//! reset, as the checker types it, so no core or kernel former is new and no
//! clause runs while unwinding. The price is that body's reset frame, under
//! which its own tail calls do not run in constant continuation; the
//! `lower::capability` module docs state the alternatives and the reversal.
//!
//! # Loops are partial fixpoints
//!
//! `loop { b }` lowers to `fix k. b'` and `while c { b }` to `fix k. x ← c;
//! case x { inl _ => b', inr _ => return () }`, each with partial evidence: a
//! loop need not end, so it claims no descent. In `b'` every path through the
//! body that ends without an exit runs the loop again, `x ← e; split x ();
//! force k`, and `continue` is `force k` where it stands. `break(v)` and a
//! bare `break` are the loop's local ends, `return v` and `return ()`, which
//! the commuting above continues with what follows the loop; `return` and
//! `become` inside a loop leave the function as anywhere else. A `break` or
//! `continue` on no path through a loop's body, a thunk's or a lambda's inside
//! one among them, is refused as [`LoweringRefusal::OutsideLoop`]. The
//! machine unfolds a loop's fixpoint against the continuation that forces it,
//! so a loop runs in constant continuation however many passes it takes. No
//! state is carried from pass to pass: each reads the frame the loop was
//! entered with. `for x in xs` is the structural fixpoint over the case of
//! the remaining list, applied to `xs`: the empty list leaves the loop, and a
//! pass runs again on the tail. The `lower::loops` module docs state each
//! reading.
//!
//! # The fourth bridge is the checker's
//!
//! Three sort-directed bridges are the lowering's, each read off the syntax:
//! a value at an application's head is forced, a computation at a function's
//! body is thunked, and a value type at a function's result gains a returner.
//! A computation written anywhere else a value is read — `Succ(plus(n, p))`
//! — lowers to a nested node, [`Insertion::Nested`], at the computation's own
//! bytes, and the checker decides it by three rules. *Direction*: against a
//! thunk type it is suspended, against any other type it runs, and with no
//! type expected it is refused by name (`NotSynthesisable`, the form
//! `Nested`). *Order*: runs bind in written order around the innermost
//! enclosing computation, never out of a `thunk` or a `case` arm. *Where*:
//! the checker's elaboration, each minted bind carrying the nested call's
//! span. `run c` is the written spelling of the same run, an expression
//! wherever a value is read; first in a block's statement it is
//! parenthesised, `(run c)`, because there `run` opens a bind.
//!
//! The recorded decision was the lowering's: it inserted every bridge,
//! because the checker returned verdicts rather than terms, so a computation
//! in value position was refused as the wrong sort and every non-tail call
//! had to be a statement. Whether a nested computation runs is the type
//! expected there, which only the checker reads, so that insertion moved to
//! the checker, which now answers the elaborated body. The record also fenced
//! effect sequencing: none is inserted outside an explicit opt-in. A run the
//! checker infers sequences its computation where the source wrote none, so
//! the opt-in is the `explicit-runs` lint: [`LoweredModule::inferred_runs`]
//! lists every inferred run, an `explicit_runs` attribute asks for each to
//! be written, and its `effects` option asks only for the runs that perform
//! an effect. The alternatives were a run inserted wherever the written form
//! is a call, which is wrong at every thunk-typed parameter, and keeping the
//! refusal. Reversal: a surface whose effects must stay visible turns the
//! lint on by default.
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
//! Each of the ten decisions, with the alternative it was chosen over and
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
//!   <https://doi.org/10.1007/3-540-45842-5_13> — the methods shape a
//!   recursive function lowers to: the parameter its matches take apart first,
//!   the later ones varying under it, here bound under its lambda rather than
//!   pushed into the motive.
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

// Module documentation that predates the shape lint: 166 headings outside the
// vocabulary, 93 decision records, 40 issue references and 33 budgets exceeded.
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

mod attribute;
mod certify;
pub mod circuit;
mod classify;
pub mod coincide;
pub mod desc_cells;
pub mod described;
pub mod description;
mod doc;
mod error;
#[cfg(test)]
mod fixture;
mod form;
mod import;
mod lower;
pub mod model;
mod module;
pub mod namespace;
mod operation;
mod origin;
mod resolve;
mod unit;

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
pub use crate::classify::TrackingIssue;
pub use crate::doc::DocLink;
pub use crate::doc::Documentation;
pub use crate::doc::DocumentationText;
pub use crate::doc::documentation;
pub use crate::doc::read_doc;
pub use crate::error::AscriptionForm;
pub use crate::error::CrossedExit;
pub use crate::error::FormFault;
pub use crate::error::FragmentBoundary;
pub use crate::error::FragmentSort;
pub use crate::error::LoopExit;
pub use crate::error::LoweringRefusal;
pub use crate::error::TelescopeFault;
pub use crate::form::Ending;
pub use crate::form::FormName;
pub use crate::form::Former;
pub use crate::form::Offer;
pub use crate::form::Repair;
pub use crate::form::StrayKeyword;
pub use crate::form::TileName;
pub use crate::form::former_of;
pub use crate::import::ImportBinding;
pub use crate::import::ImportDeclaration;
pub use crate::import::ImportIndex;
pub use crate::import::ImportResolution;
pub use crate::import::ImportUri;
pub use crate::import::ModuleImports;
pub use crate::import::alias_scope;
pub use crate::import::aliased;
pub use crate::lower::AskedRuns;
pub use crate::lower::CarriedOrigins;
pub use crate::lower::ClosureLowering;
pub use crate::lower::ElidableExit;
pub use crate::lower::Exit;
pub use crate::lower::Explicitness;
pub use crate::lower::Fuel;
pub use crate::lower::InferredExit;
pub use crate::lower::InferredRun;
pub use crate::lower::LinearRun;
pub use crate::lower::LoweringBudget;
pub use crate::lower::NestedSite;
pub use crate::lower::Onto;
pub use crate::lower::RunOperand;
pub use crate::lower::RunSpelling;
pub use crate::lower::lower_module;
pub use crate::lower::lower_unit;
pub use crate::module::Address;
pub use crate::module::CodataIndex;
pub use crate::module::Coerced;
pub use crate::module::ComponentPlace;
pub use crate::module::Container;
pub use crate::module::DataIndex;
pub use crate::module::DeclarationCount;
pub use crate::module::DeclarationOutcome;
pub use crate::module::FunctorIndex;
pub use crate::module::HalfAt;
pub use crate::module::Halves;
pub use crate::module::InstanceIndex;
pub use crate::module::LoweredDeclaration;
pub use crate::module::LoweredModule;
pub use crate::module::LoweredStructure;
pub use crate::module::ManifestComponent;
pub use crate::module::Mark;
pub use crate::module::Role;
pub use crate::module::SealedComponent;
pub use crate::module::Sealing;
pub use crate::module::Stratum;
pub use crate::module::StructureIndex;
pub use crate::module::ValueComponent;
pub use crate::module::WrittenImport;
pub use crate::module::manifest_type;
pub use crate::module::unaliased;
pub use crate::module::written_imports;
pub use crate::origin::ArmOrigin;
pub use crate::origin::CaseOrigin;
pub use crate::origin::ComponentName;
pub use crate::origin::Insertion;
pub use crate::origin::Label;
pub use crate::origin::Labelled;
pub use crate::origin::Origin;
pub use crate::origin::OriginCount;
pub use crate::origin::OriginTable;
pub use crate::origin::OriginToken;
pub use crate::origin::PatternReading;
pub use crate::origin::PatternSpan;
pub use crate::origin::Provenance;
pub use crate::origin::SplitComponent;
pub use crate::origin::scrutinised;
pub use crate::resolve::Bound;
pub use crate::resolve::Frame;
pub use crate::resolve::HeadArity;
pub use crate::resolve::InScope;
pub use crate::resolve::Mentioned;
pub use crate::resolve::OperandCount;
pub use crate::resolve::Resolution;
pub use crate::resolve::Scope;
pub use crate::resolve::ScopeId;
pub use crate::resolve::SurfaceName;
pub use crate::resolve::TypeAtom;
pub use crate::resolve::TypeFormer;
pub use crate::resolve::binder_site;
pub use crate::resolve::type_atom;
pub use crate::resolve::type_former;
pub use crate::unit::ImportTarget;
pub use crate::unit::PathImportOrdinal;
pub use crate::unit::SourceIndex;
pub use crate::unit::Unit;
pub use crate::unit::UnitFault;
pub use crate::unit::UnitKey;
pub use crate::unit::UnitSource;
