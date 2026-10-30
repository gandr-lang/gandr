//! Native data in the lowering: a data family where a type is read, a
//! constructor applied to its fields, a data declaration's signature, and a
//! match compiled to native eliminations.
//!
//! # A constructor carries its whole classifier
//!
//! The core's constructor value names the nominal type it builds, arguments
//! and all, so the lowering has to know them where the constructor is
//! written. A family without parameters has one classifier, which the
//! lowering inserts. A family with parameters takes it from the type the
//! constructor's position states: an annotation `(C(…) : T(…))`; the
//! signature of the definition it is, `def x : T(…) ; def x = C(…) ;`; the
//! answer of the body it ends, `+U (-F T(…))`, `() => T(…)` or a function's
//! stated result, through a tail, a `pure` there or a `return` — a result
//! written as a top-level definition's application, `-> opt(Integer)` with
//! `opt = \A. -F Maybe(A)`, read through the definition's body; its parent's
//! classifier, for a field typed by the family itself or by one of its
//! parameters; and, where it is written as an argument of a data family, that
//! family's parameter at its place with the parameters before it replaced by
//! the arguments written for them: `Inl(a)` in `Tagged(Integer, String,
//! Inl(a))`, whose third parameter is `s : SumOb(l, r)`, is a
//! `SumOb(Integer, String)`. The arguments before the place are its
//! siblings, which the mint sweep reaches after it, so the application mints
//! such a constructor before itself. A constructor no position types is
//! refused as unannotated.
//!
//! The alternative was the checker's check mode: a constructor synthesised
//! against its expected type, which needs the certificate to carry a
//! classifier the checker fills in, a kernel change. Every type the lowering
//! reads here is written in the source and closed at the position it is read
//! from, or closed by the arguments written beside it, so the lowering
//! carries it. Reversal: a checker that elaborates a constructor against an
//! expected type makes the classifier the checker's, and this reading is
//! deleted.
//!
//! # A match is a decision tree of eliminations
//!
//! The core has no match: it eliminates native data by a data case with a
//! motive, a sum by a case, and compares integers by a primitive. A match
//! compiles to a tree of those over the scrutinee value itself, never bound,
//! by the column-wise pattern-matrix construction (Maranget, *Compiling
//! Pattern Matching to Good Decision Trees*, ML 2008): the leftmost column
//! the first row tests is switched on, each constructor's branch binds its
//! fields with ordinary lambdas, and the rows that survive it are
//! specialised. A leaf runs its arm, a hole the first surviving row holds
//! leaves the tree stuck on that hole, and a matrix no row survives is a
//! non-exhaustive match, refused where it is written.
//!
//! An arm body reached from several leaves is copied, not joined: every arm
//! body is read under the case's frame and its own variables alone, and each
//! leaf substitutes the body's variables by the tree binders that settled
//! them and its frame by the case's context shifted under the leaf's depth.
//! No thunk of unknown type is bound and no binder is padded, so nothing the
//! checker cannot type is introduced; reversal: a join point becomes worth
//! its thunk once an arm body's duplication costs more than the binding of
//! its type, which needs the answer type at every join.
//!
//! # The motive is the answer the source states
//!
//! A data case checks against a motive under one scrutinee binder. The
//! lowering reads it from the match's own answer, `case e -> T { … }`, or
//! from the result type of the function whose body ends in the match,
//! relocated into the match's context; a match with neither is refused as
//! unannotated when its tree eliminates native data. Reversal: a checker that
//! takes the motive from the checking direction makes the answer optional.
//!
//! A pattern at a scrutinee written with a dependent record (`lower::arity`)
//! splits each link of its nesting: a link the type binds by a dependent
//! split, whose motive is the answer with the split's scrutinee abstracted,
//! and a product link by a split of two. The answers are read from the root
//! down: a data case passes its answer to its branches under their fields,
//! a dependent split's arm answers the motive at the pair of its two
//! binders, and every other test passes its answer under the binders it
//! opens. A scrutinee that is a variable is abstracted wherever the answer
//! reads it, so an arm's answer reads the pair it matched; any other
//! scrutinee gives the motive that ignores its binder. A match with a
//! dependent split and no answer is refused as unannotated.
//!
//! - Alternatives: projections in place of the split, which leave the arm's
//!   answer reading the scrutinee rather than its components; a motive left for
//!   the checker to infer, which is higher-order unification.
//! - Reversal: a checker that infers the motive from the checking direction
//!   makes the abstraction here unnecessary.
//!
//! A data case over a variable is the dependent eliminator the same way: its
//! motive is the answer with the scrutinee abstracted, and each branch
//! answers the motive at its constructor over the branch's fields. A
//! recursive call at a field, `f[<](x)`, then answers the motive at `x`, and
//! the `Loop(x)` arm the motive at `Loop(x)`; a leaf under such a root reads
//! the scrutinee's variable as the constructor its branch matched, over the
//! root's fields. A nested switch on a field abstracts that field from the
//! branch's answer in turn, so a leaf reads every level a dependent switch
//! above it matched as that switch's constructor over its own fields, read
//! so in turn: an arm variable at such a level, and the scrutinee's variable
//! through its fields, read as the answer does. A parameterless family is
//! refined so, and so are the words over a looped point: a case over
//! `p : Path(Circle, Base, Base)` answers its motive at `here(Base)`,
//! `loop ∷ q` and `back(loop) ∷ q`, each the words' own constructor, which
//! both checkers read at the path type. A family with parameters and the
//! presentation's own keep the answer as written under the fields, and an
//! answer that does not read the scrutinee is unchanged, its motive ignoring
//! its binder.
//!
//! - Alternatives: a motive clause written on the case, a second spelling of
//!   what the result type already states.
//! - Reversal: a motive that is not the answer with the scrutinee abstracted —
//!   one reading an index of the scrutinee's type — needs the clause.
//!
//! A match in an arm of another, with no answer of its own, takes the
//! answer the arm passes its body, read as the arm's leaf reads that body:
//! where the arm names every field of the root constructor it matched, by a
//! variable or by a nested pattern whose own fields it names so, the outer
//! scrutinee's variable reads as that constructor over what the arm names,
//! through every such arm from the outermost in. Its motive abstracts its own
//! scrutinee from that answer, and its leaves read their bodies' variables
//! the same way before their own refinement, so a branch naming the outer
//! scrutinee reads it at both constructors. An arm that leaves a field
//! unnamed passes the answer as written, and its own leaf alone reads the
//! scrutinee at the constructor.
//!
//! - Alternatives: refusing a match in an arm that leaves a field unnamed as
//!   unannotated, which rejects one whose branches read only the whole
//!   scrutinee and check against the answer as written.
//! - Reversal: an arm body read under a binder for each field its arm leaves to
//!   a wildcard lets such an arm name that field, and its answer then reads so
//!   too.
//!
//! # The patterns are kept beside the tree
//!
//! The tree does not keep the patterns, so the origin table does: per match,
//! the core pattern table its arms are written in, one record per arm
//! alternative, and the syntax nodes of the scrutinee and every pattern and
//! body. A pattern hole's identity is its syntax node's position, the
//! identity a term hole takes, so a live match reads one seam.
//!
//! # A recursive function is one fixpoint over the parameter its matches take apart
//!
//! The core's fixpoint `fix x. λy. M` binds its own thunk, and the checker
//! and the kernel type it by stages: `y` stands at a fresh stage, a case on it
//! binds its constructor's recursive fields one stage below, and every self
//! call `(force x) a` takes `a` strictly below the stage `y` stands at
//! (`gandr-core-checker`'s crate documentation, § Recursion). The lowering
//! writes what that typing admits, reading the staged parameter off the body:
//! it is the parameter the innermost match above a claim scrutinises, written
//! as a bare name, and the last parameter where no match on a parameter stands
//! above the claim. Nested matches on that parameter's fields keep it. The
//! reading passes over a match on a parameter whose type decodes a code,
//! `v : elL(c)`, when a match on another parameter encloses it: a decode
//! carries no stage, so the claim descends on the code (`Lowerer::decodes`).
//! So `def rec f(p₁, …, pₖ, y, q₁, …, qₘ) -> C { b }` staging `y` lowers to
//! `thunk (λp₁ … λpₖ. fix f. λy. λq₁ … λqₘ. b)`, and a call `f[<](p₁, …, pₖ,
//! a, c₁, …, cₘ)` to `(force f) a c₁ … cₘ`. The staged parameter is always the
//! fixpoint's first binder, its evidence `StructuralDescent`, and whether `a`
//! stands below its stage is the checkers' to judge: a call at anything else,
//! the parameter's own value among them, fails as `StageNotBelow`. The
//! lowering neither searches for a decreasing argument nor duplicates the
//! check.
//!
//! The parameters before the staged one are the uniform parameters of an
//! inductive definition (Coquand and Paulin, *Inductively defined types*,
//! COLOG 1988): bound outside the fixpoint, so every recursive call passes
//! them as themselves, and a call passing anything else is `OutOfFragment`
//! with the `NonUniform` boundary, at the argument. The parameters after it
//! are bound under the staged one inside the fixpoint, so a call varies them
//! freely, an accumulator among them. Every claim of one definition descends
//! on one parameter: the first claim in source order fixes it before the body
//! binds anything (`Lowerer::staged_by_body`), and a later claim under a match
//! on another parameter is `DescentOnSeveralParameters`, naming both.
//!
//! `<` is the claim. A fixpoint carries structural evidence when one of its
//! claims writes it and partial evidence when none does, so the checker and
//! the kernel type every recursion the source claims and none it does not.
//! The function's own name is bound by one more frame, between the staged
//! parameter and the ones before it, typed by the declaration form so no
//! signature telescope counts it — the binder exists in the body alone. It
//! resolves only under a claim: heading a call, `f[<](…)`; standing alone,
//! `f[<]` is the fixpoint's own thunk, a value a call may pass on; written
//! bare, it is `UnmarkedSelfReference`, whose message spells the claim. A
//! parameter of the same name shadows it. A function with no parameter has
//! nothing to recurse on and is declined. `>` is the productivity claim: a
//! call `f[>](…)` that is the whole arm of a copattern block, so every
//! observation of a codata result yields before the function runs again; it
//! leaves the fixpoint partial, which unfolds only under an observation, and
//! anywhere else it is `UnguardedCorecursion`. Every other resident of the
//! instantiation — a measure, a size, a cost — is reserved until its
//! termination rung lands. The fixpoint is marked
//! `Insertion::Fixpoint` at the function form's origin, since the source
//! writes no `fix`. A block stands as a match arm, so the programs the corpus
//! carries in `fixture/model/data/recursive-addition.gandr`,
//! `recursive-lists.gandr`, `recursive-nat-lists.gandr` and `descent.gandr`
//! are written in the surface's intended spelling.
//!
//! The shape is `McBride`'s methods (*Elimination with a Motive*, TYPES 2000)
//! with one departure. An eliminator's methods take the recursive argument
//! first and push every later parameter into the case's motive, re-bound
//! under each branch's fields; here the later parameters stand under the
//! staged parameter's lambda instead, `fix f. λy. λq. case y { … }`. The
//! checkers' typing and their unfolding gate read only the fixpoint's first
//! binder, so the later lambdas need no re-indexing of the branches, and a
//! definition staging its last parameter — every one the corpus held before —
//! lowers byte for byte as it did. Reversal: a presented type's rule check
//! reads a fixpoint as a fold only when the case stands directly under its
//! first lambda, so a definition over a presented type with a parameter after
//! its staged one needs the arms to take that parameter.
//!
//! Alternative, retired: every parameter inside the fixpoint, `fix f. λp₁ …
//! λpₙ. b`, with evidence naming the staged position. The checkers type that
//! position, but their evaluation sticks a fixpoint on its first argument and
//! reads a fold only over its first binder, so `plus` over the presented
//! integers stopped respecting its rules (#626). Reversal: a fixpoint stuck at
//! a later position carrying its leading arguments, which is the sized rung's
//! (#392). Descent on several parameters at once — lexicographic or measured
//! — is the sized rung's too, and replaces the one position by a measure.
//!
//! A mutual block, `rec { … }`, collects its members as declarations admitted
//! as one block. Two or more recursive functions of one block recurse through
//! one another as one fixpoint over the sum of their domains: each member is
//! `thunk (λx. (fix f. λy. case y { b₀ | … | bₙ }) (injᵢ x))`, and a descent
//! through a sibling, `g[<](a)`, lowers to `(force f) (inj_g a)`. The
//! checkers stage that sum at the one stage the block's families share, so a
//! call descends through any of them; `Lowerer::mint_joints` states the
//! choice. A member of the joint stages its first parameter. A claim through
//! a sibling stages it as a claim through the member itself does, since both
//! run the one fixpoint. The parameters after it stay the lambdas of the
//! member's branch `bᵢ`, so a descent `g[<](a, c)` lowers to `(force f)
//! (inj_g a) c` and varies `c` freely. A call through a member with a
//! parameter before its staged one refuses it as non-uniform, or as
//! unadmitted when the calls vary it. A member's claim standing alone, the
//! joint's thunk at the sum, is unadmitted.
//! A block holding a member the lowering refused forms no joint: each other
//! member is its own fixpoint, and a call through a sibling names the
//! sibling's declaration, so its refusal is reported as that one's
//! consequence (`Lowerer::unjoin_refused`).
//!
//! # Native data and the match
//!
//! `lower::native` lowers a `data` declaration at the root to the core's native
//! `DataSignature`, a constructor to a native constructor value carrying its
//! whole classifier, a `case` to a decision tree of native eliminations, and a
//! `def rec` function to one fixpoint over the parameter its matches take
//! apart, recursive calls written with the descent claim `f[<](…)`.
//!
//! `data T(a : A) : Type { C : (x : X) --> T(a); … }` at the root lowers to the
//! core's native `DataSignature`: the parameters as a telescope, each
//! generator's fields as one constructor, in source order. A field may name the
//! family it belongs to, applied to its own parameters, which is how `List(a)`
//! holds its tail; whether every such occurrence is strictly positive is the
//! checker's judgment, not the lowering's. `DeclarationOutcome::Data` carries a
//! `DataIndex` into `LoweredModule::data`, so the outcome stays `Copy` and the
//! signature is shared, not cloned, with the checker's declaration. A kind
//! written as an arrow, `data V(a : A) : I -> Type { … }`, indexes the family:
//! each domain is an index classifier read under the parameters, and each
//! generator's result applies the family to its own parameters and then one
//! term per index, the index its value stands at, read under the parameters
//! and the generator's fields (`tests::an_indexed_family_lowers_its_indices`).
//! A generator whose result applies the family to anything else, and a cell on
//! an indexed family, are declined as `OutOfFragment` with the `Indexed`
//! boundary; the constructor-block spelling and a field's attributes or grade
//! are declined by name
//! (`tests::members_outside_the_fragment_are_declined_by_name`); a constructor
//! named twice is `DuplicateDefinition`. Each of these is decided while the
//! declaration is collected, so the declaration records no half and its
//! attributes are not filed: a corpus source holding one stays pending.
//! Operation and rule members, `oper`, `op` and `rule`, are passed over: the
//! description route (the `description` module) reads them and holds any
//! refusal among them at the member, so the family keeps its generators.
//!
//! A constructor `C(e, …)` is a native constructor value, which names its whole
//! classifier, taken from the type its position states as the opening section
//! reads it.
//!
//! `case e -> T? { p => c, … }` compiles to a decision tree of native
//! eliminations by the pattern-matrix construction of Maranget's _Compiling
//! Pattern Matching to Good Decision Trees_ (ML 2008): a data case per
//! constructor column, a sum case per boolean column, the integer primitive
//! `int.eq` cased on per integer literal, and the native list case per list
//! column. Patterns nest: constructors, variables, `_`, integer and boolean
//! literals, or-patterns binding nothing, list patterns `[p, …]` and
//! `[p, …, ..r]`, read as cells over the empty list or the rest `r`, an
//! as-pattern `p as x` binding the value `p` matches where its column stands,
//! and a pattern hole `?` or `?name` in any position, which leaves the leaf it
//! reaches stuck on a hole whose identity is the pattern's syntax node. The
//! scrutinee is never bound; each leaf substitutes its arm body's variables by
//! the tree binders that settled them, so an arm reached twice is copied, not
//! joined through a thunk whose type the checker would have to know. The data
//! case's motive is the written answer or the result of the function whose body
//! ends in the match, and a match that eliminates native data with neither is
//! unannotated; the list case only checks, against the answer its position
//! gives. Rows exhausted before a leaf are `NonExhaustiveMatch`, classed as
//! malformed source; string patterns, a rest pattern outside a list, an
//! or-pattern binding a variable and the view `with e` are declined by name.
//! Reversal: a join point earns its thunk once duplication costs more than
//! binding the answer type at every join.
//!
//! A match of no arms, `case e {}`, names no family to compile against, so it
//! reads its scrutinee's stated type, as a sum pattern reads its arity: a
//! parameter's written type, or a lambda binder's where the lambda answers a
//! written arrow `A -> C`, its domain `A`. Over a data type with no
//! constructor it lowers to that type's data case of no branch; over a path
//! type, to a data case of no branch whose admission the checker decides by
//! apartness (`gandr-core-checker`'s `former` § Apartness); over a data type
//! with a constructor it is `NonExhaustiveMatch`; over anything else, `Void`
//! among them, it is the case of no branches, the empty sum's eliminator,
//! which checks at any answer. The data case reads its answer as any match
//! does, `case e -> T {}` or the enclosing result type; the empty sum's case
//! takes none written, since no branch would answer it.
//!
//! **Choice.** The empty match read by its scrutinee's written type, so `data
//! Empty : Type {}` and a path between apart terms each have an eliminator.
//! **Alternatives.** One reading of `case e {}`, the empty sum's eliminator,
//! which leaves every empty nominal family without one; a reading by the
//! checked type, which the lowering does not compute. **Reversal.** A
//! scrutinee with no written type — a nested expression — takes the reading
//! once the lowering learns synthesized types.
//!
//! The tree forgets its patterns, so `OriginTable::case` keeps them: per match,
//! the `gandr_core_term` pattern table the arms are written in, one `ArmOrigin`
//! per arm alternative, and the syntax nodes of the scrutinee and of each
//! pattern and body, keyed by the tree's root. A live match and a hole report
//! read that one seam rather than parsing the tree back.
//!
//! # A theory's terms are a data declaration it derives
//!
//! `Terms(S)` is the data type of a theory's closed terms, the initial model
//! the theory's models are read against. The collector mints one declaration
//! per theory a unit asks for, before its first asker, and
//! `Lowerer::mint_terms` lowers it as a written data block would lower: one
//! constructor per operation at its arity, named `S.op`, and the theory's
//! oriented rules as its presentation, each side read by `rule_side` under
//! `Heads::Operations`. The checker judges the presentation as it judges a
//! written block's, and a monoid's associativity is `RuleNotPresentable` at
//! `Terms(S)`. The derived declaration and the block written by hand are one
//! signature
//! (`tests::modules::models::a_theory_s_terms_are_its_operations_over_its_rules_4143`).
//! A theory of several sorts, an indexed or binding operation, and a stated law
//! are refused by name before anything is minted, as `TermsType` and
//! `LawTerms`.
//!
//! **Choice.** The terms as a derived data declaration, checked and readmitted
//! as if written, so the derivation is never trusted. **Alternatives.** A
//! former of its own in the core, which the kernel would have to learn; a
//! derived declaration per asker, which makes two askers' terms two types.
//! **Reversal.** The terms take a model instance of their theory once a derived
//! declaration can carry a stated law as its cell.
//!
//! # References
//!
//! - `vault:01a156e3-93c7-7e62-9a50-b38b2da60284` — lineage: the loops and
//!   termination design (§ the decoder) — the fixpoint stages the code, and a
//!   decode carries no stage, so a match on a decoded value under another match
//!   leaves the staged parameter to the outer one (`Lowerer::decodes`).
//! - `vault:01a178ab-289d-7702-b010-1c47ae9fd427` — lineage: the univalence
//!   design (§ The formers, and where each stands) — `Terms(S, Γ ⊢ s)` is a
//!   theory's initial model, its operations the constructors and its rules the
//!   oriented theory.

use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use alloc::string::String;
use alloc::sync::Arc;
use alloc::vec::Vec;

use anodized::spec;
use gandr_core_term::Binders;
use gandr_core_term::Carried;
use gandr_core_term::CompType;
use gandr_core_term::CompTypeId;
use gandr_core_term::ComponentCount;
use gandr_core_term::Computation;
use gandr_core_term::ComputationId;
use gandr_core_term::ConstructorTag;
use gandr_core_term::CoreArena;
use gandr_core_term::DataSignature;
use gandr_core_term::Sort;
use gandr_core_term::Value;
use gandr_core_term::ValueId;
use gandr_core_term::ValueTypeId;
use gandr_core_term::Zone;
use gandr_core_term::hole::HoleId;
use gandr_core_term::hole::TermId;
use gandr_core_term::pattern::Pattern;
use gandr_core_term::pattern::PatternId;
use gandr_core_term::pattern::Patterns;
use gandr_core_term::primitive::Arguments;
use gandr_core_term::primitive::PRELUDE;
use gandr_core_term::staged::Part;
use gandr_kernel_strata::Level;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::FieldLabel;
use gandr_kernel_term::FixpointEvidence;
use gandr_kernel_term::GroundSort;
use gandr_kernel_term::Literal;
use gandr_kernel_term::Side;
use gandr_kernel_term::StagedPosition;
use gandr_kernel_term::Summand;
use gandr_surface_syntax::ByteSpan;
use gandr_surface_syntax::NodeIndex;
use gandr_surface_syntax::SourceFragment;
use gandr_theory_levitation::DeclPolarity;
use gandr_theory_levitation::THEORY_CONSTRUCTORS;
use quenchant_shape::shape::Maybe;

use super::Code;
use super::FormName;
use super::Former;
use super::Function;
use super::LabelRead;
use super::LabelSite;
use super::Lowered;
use super::Lowerer;
use super::Plan;
use super::Produced;
use super::Reading;
use super::Resolved;
use super::Sink;
use super::Site;
use super::Stretch;
use super::arguments;
use super::arity;
use super::arity::Dependent;
use super::closed;
use super::exhausted;
use super::exits;
use super::identity::Layout;
use super::identity::related;
use super::lowered;
use super::parse_literal;
use super::recursion;
use super::stretch;
use crate::error::FormFault;
use crate::error::FragmentBoundary;
use crate::error::FragmentSort;
use crate::error::LoweringRefusal;
use crate::form::Cursor;
use crate::form::Piece;
use crate::form::Pieces;
use crate::form::Placed;
use crate::form::Run;
use crate::form::Shape;
use crate::form::TileName;
use crate::form::read_pieces;
use crate::form::shape_of;
use crate::module::Collected;
use crate::module::Constructor;
use crate::module::Container;
use crate::module::DataIndex;
use crate::module::Generators;
use crate::module::Half;
use crate::module::Operand;
use crate::module::SlotIndex;
use crate::module::TermsForm;
use crate::module::WordsForm;
use crate::module::closed_term;
use crate::module::term_generators;
use crate::namespace::NamePath;
use crate::namespace::PathResolution;
use crate::namespace::Recognized;
use crate::namespace::Segment;
use crate::origin::ArmOrigin;
use crate::origin::CaseOrigin;
use crate::origin::ComponentName;
use crate::origin::Insertion;
use crate::origin::Origin;
use crate::origin::PatternReading;
use crate::origin::PatternSpan;
use crate::origin::SplitComponent;
use crate::origin::scrutinised;
use crate::resolve::Frame;
use crate::resolve::OperandCount;
use crate::resolve::ScopeId;
use crate::resolve::SurfaceName;
use crate::resolve::Telescope;
use crate::resolve::TypeAtom;
use crate::resolve::TypeFormer;
use crate::resolve::binder_site;
use crate::resolve::binder_type;
use crate::resolve::type_atom;
use crate::resolve::type_former;
use crate::unbuilt::Unbuilt;

#[cfg(test)]
pub(super) mod tests;

quenchant_shape::reason_enum! {
    /// Why a match states no answer.
    pub mod answered {
        /// Neither the match nor its position states one.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// No `-> T` follows the scrutinee and no function result reaches
            /// the match.
            Unstated,
        }
    }
}

quenchant_shape::reason_enum! {
    /// Why an answer is read at no arm of an enclosing match.
    pub mod passed {
        /// No match passed the answer into one of its arms on its way here,
        /// or none that did reads its scrutinee at a constructor.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The answer is stated here, or reaches here through no arm.
            Unpassed,
            /// Every arm the answer was passed into reads its scrutinee as
            /// written.
            Unsettled,
        }
    }
}

quenchant_shape::reason_enum! {
    /// Why an arm reads its match's scrutinee at no constructor over the
    /// arm's own variables.
    pub mod settled {
        /// The arm's body reads the scrutinee as the source writes it.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The tree's root is no data switch on the scrutinee over a bare
            /// family.
            Unswitched,
            /// The scrutinee is no name the case's frame binds
            /// intuitionistically.
            Unbound,
            /// The arm's leaves stand under no one branch of the root, or a
            /// field of that branch is settled by no variable of the arm.
            Unnamed,
        }
    }
}

quenchant_shape::reason_enum! {
    /// Why a written type gives a field no classifier.
    pub mod inherited {
        /// The field's type is neither its family over its own parameters nor
        /// a parameter a written classifier gives an argument for.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// No classifier is read off the type.
            Unclassified,
        }
    }
}

quenchant_shape::reason_enum! {
    /// Why a node names no constructor.
    pub mod constructed {
        /// No data family declared strictly earlier has a constructor so named.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The name is no constructor's, or its family is not yet declared.
            Unnamed,
            /// The name stands at a place its data family declares a universe,
            /// where it names a type.
            TypePlace,
        }
    }
}

quenchant_shape::reason_enum! {
    /// Why a name is no data family.
    pub mod family {
        /// The declaration at the constant is not a data declaration.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The declaration writes a value, a function or nothing.
            Undeclared,
        }
    }
}

quenchant_shape::reason_enum! {
    /// Why a constant has no body a decode of it reads through.
    pub mod unfolding {
        /// The constant stands for itself where a type decodes it.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The constant is no top-level definition written as one form,
            /// or its declaration refused.
            Opaque,
            /// The definition's body did not lower.
            Unlowered,
        }
    }
}

quenchant_shape::reason_enum! {
    /// Why the nodes minted since a mark carry no written root.
    pub mod rooted {
        /// No node among them is the written form's own.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The tree did not lower, so what was minted toward it is all
            /// inserted.
            Unminted,
            /// The match is its first arm's body, minted before and adopted.
            Adopted,
            /// The nodes carry a classifier the lowering inserted.
            Classifier,
        }
    }
}

quenchant_shape::reason_enum! {
    /// Why a declaration is no member of a joint fixpoint.
    pub mod joint {
        /// The declaration is outside a joint, the name is not one, or the
        /// member did not lower to one.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The declaration's mutual block declares fewer than two
            /// recursive functions, or the declaration is none of them.
            Alone,
            /// The name names no recursive function of the block.
            Outside,
            /// The member did not lower to a fixpoint over one parameter at a
            /// plain arrow.
            Unjoined,
        }
    }
}

quenchant_shape::reason_enum! {
    /// Why a constant is a word of no words.
    pub mod worded {
        /// The constant names no words.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The constant is neither a loop nor the words a loop is a
            /// letter of.
            Unworded,
        }
    }
}

quenchant_shape::reason_enum! {
    /// Why a row is not stuck.
    pub mod stuck {
        /// The row has matched through no hole.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// Its own written patterns decide whether it matches.
            Decided,
        }
    }
}

quenchant_shape::reason_enum! {
    /// Why a data switch names no classifier for the constructors it splits
    /// into.
    pub mod bare {
        /// The switch reads no family the bare family type classifies.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The family has parameters, or is the presentation's own, so a
            /// constructor needs a written classifier the switch does not hold.
            Parameterised,
        }
    }
}

quenchant_shape::reason_enum! {
    /// Why a data switch names no declaration whose constructors it splits
    /// into.
    pub mod eliminated {
        /// The switch's constructors are named by no declaration it records.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The family holds no slot the switch reads: the presentation
            /// code in a module that mints no `Theory`, or a declaration the
            /// collection filed no slot for.
            Unslotted,
            /// The switch has no branch to name: a match of no arms over a
            /// family the bare family type does not classify.
            Armless,
        }
    }
}

quenchant_shape::reason_enum! {
    /// Why a match of no arms switches on no data.
    pub mod switched {
        /// Its scrutinee states no data type and no path type.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The scrutinee is no name written with a type.
            Untyped,
            /// The stated type is another former: the empty sum among them.
            Otherwise,
        }
    }
}

/// How many tree binders stand above a node of a match's decision tree; as a
/// variable's index, how many binders stand between the variable and its
/// binder.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct Depth(usize);

/// A value a match's decision tree scrutinises: level zero is the scrutinee
/// itself, and the binder a node under `depth` tree binders introduces for
/// its field `field` is level `depth + field + 1`.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct TreeLevel(usize);

/// A column of a pattern matrix.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct Column(usize);

/// A node of a decision tree, by its position in the tree's node list.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct TestAt(usize);

/// A pattern, by its position in one match's pattern store.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct PatternAt(usize);

/// An arm of a match, by its position in source order.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct ArmAt(usize);

/// An arm variable, numbered in source order.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct VariableAt(usize);

/// A match, by its position in the lowering's match store.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub(super) struct CaseIndex(usize);

/// A match's constructor arm, by its position in the lowering's store of the
/// arms an answer is passed into.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub(super) struct ArmIndex(usize);

/// A field read off a data value by name, by its position in the lowering's
/// store of them.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub(super) struct ProjectedIndex(usize);

/// Whether a written type spells one of the names a constructor binds before
/// the field it types.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct Spelled(bool);

/// Whether a recursive call claims descent.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub(super) struct Claimed(pub bool);

/// Whether a parameter's written type is a decode, a declaration defined by a
/// body: such a parameter carries no stage.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub(super) struct Decoded(pub bool);

/// Whether a type application writes a recursive function's descent where a
/// type is read, `own[<](…)`.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct TypeDescent(bool);

/// What an instantiation's resident claims of the self-call it heads.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Claim
{
    /// `<`: the call descends structurally on the staged parameter.
    Descent,
    /// `>`: the call is productive, the whole arm of a copattern block.
    Productive,
}

/// A recursive function's parameter, by its position in the function's
/// parameter list.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub(super) struct ParameterAt(pub usize);

/// Where a recursive function closes its fixpoint and which parameter the
/// fixpoint stages, read off its body ([`Lowerer::staged_by_body`]).
///
/// # Specification
/// - ensures: `kept <= staged`; the parameters before `kept` stand outside the
///   fixpoint, and the ones from `kept` to `staged` are its leading binders.
/// - executable: none — a plain pair of positions its producer establishes.
///
/// # Adequacy
/// - hypothesis: L3 — a function whose recursive calls pass its first parameter
///   unchanged keeps it outside; one whose calls change it carries it as a
///   leading binder before the staged one.
/// - witness: `lower::native::tests::a_definition_descends_on_the_parameter_its_cases_scrutinise`
/// - witness: `lower::native::tests::a_varying_parameter_before_the_staged_one_is_a_leading_binder_626`
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct Staging
{
    /// How many parameters, from the first, every recursive call passes
    /// unchanged: the fixpoint closes after them.
    pub kept: ParameterAt,
    /// The parameter the fixpoint stages, counted from the function's first.
    pub staged: ParameterAt,
}

/// A recursive function's own name, which the frame of its fixpoint binds.
///
/// # Specification
/// - requires: coordinates, when present, are interpreted in their originating
///   run.
/// - ensures: the function's parameters, the ones before the fixpoint that
///   every recursive call passes unchanged, the staged one, whether a call
///   claims descent and the tile writing the name stay together under the frame
///   binding the name.
/// - provides: what a descent claim checks its call against, the evidence the
///   fixpoint carries, and the name its binder is read by.
/// - fails: none as a data value; interpretation belongs to its consumers.
/// - panics: none as a data value.
/// - executable: none — the scope and the parameter store are not retained;
///   `function`, `instantiation` and `mint_function` interpret the record.
///
/// # Adequacy
/// - hypothesis: L3 — a recursive function over one parameter, over a uniform
///   leading parameter and over a varying later one each close their fixpoint
///   over the parameter their matches scrutinise, with descent evidence exactly
///   when a call claims it.
/// - witness: `lower::native::tests::a_recursive_function_closes_a_fixpoint_over_its_staged_parameter`
/// - witness: `lower::native::tests::a_definition_descends_on_the_parameter_its_cases_scrutinise`
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct Recursion
{
    /// Every parameter, in the lowerer's parameter store.
    pub parameters: Stretch,
    /// The parameters before the fixpoint, in the lowerer's parameter store:
    /// the ones every recursive call passes unchanged.
    pub uniform: Stretch,
    /// The parameter the fixpoint stages, counted from the function's first:
    /// at or past the uniform ones.
    pub staged: ParameterAt,
    /// Whether a call claims descent, which makes the fixpoint's evidence
    /// structural rather than partial.
    pub claimed: Claimed,
    /// The tile writing the function's own name: where its fixpoint's binder
    /// is named.
    pub named: NodeIndex,
}

/// A recursive function's parameter as a match on it reads it: the frame
/// naming the function and the parameter's position in its list.
///
/// # Specification
/// - requires: coordinates, when present, are interpreted in their originating
///   run.
/// - ensures: the recursion and the position stay together.
/// - provides: what an arm under a match on a parameter hands down to the
///   claims inside it.
/// - fails: none as a data value; interpretation belongs to its consumers.
/// - panics: none as a data value.
/// - executable: none — `case` records it and `claim` reads it.
///
/// # Adequacy
/// - hypothesis: L3 — as [`Recursion`].
/// - witness: `lower::native::tests::claims_under_cases_on_two_parameters_are_refused_by_name`
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct Scrutiny
{
    /// The frame binding the recursive function's own name.
    pub recursion: ScopeId,
    /// The parameter's position in the function's list.
    pub position: ParameterAt,
}

/// A recursive call as its call form read it: what its head's claim checks.
///
/// # Specification
/// - requires: coordinates, when present, are interpreted in their originating
///   run.
/// - ensures: the call form and every argument it wrote, the leading ones
///   included, which the call itself neither reads nor applies.
/// - provides: the arguments a descent claim checks for uniformity and arity.
/// - fails: none as a data value; interpretation belongs to its consumers.
/// - panics: none as a data value.
/// - executable: none — the operand store is not retained; `instantiation`
///   reads it.
///
/// # Adequacy
/// - hypothesis: L3 — a call passing a leading parameter as itself, as
///   something else and with the wrong argument count each meet their own
///   outcome at the claim.
/// - witness: `lower::native::tests::a_recursive_call_passes_its_leading_parameters_unchanged`
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct Descent
{
    /// The call form.
    pub call: Site,
    /// Every argument the call wrote, in the lowerer's operand store.
    pub arguments: Stretch,
}

/// The recursive functions of a mutual block, which recurse through one
/// another as one fixpoint over the sum of their domains: a member's summand
/// is its position in the block.
///
/// # Specification
/// - requires: the slots are one mutual block's `def rec` declarations in block
///   order.
/// - ensures: the members and the declaration being read, with its summand when
///   it is a member of a joint of at least two.
/// - provides: what a descent through a sibling reads its summand from.
/// - fails: none as a data value; interpretation belongs to its consumers.
/// - panics: none as a data value.
/// - executable: none — the collected slots are not retained; `instantiation`
///   and `mint_joints` interpret the record.
///
/// # Adequacy
/// - hypothesis: L3 — a rose tree's two measures, one block, descend through
///   each other's summands of one fixpoint.
/// - witness: `lower::native::tests::a_mutual_blocks_recursive_functions_share_one_fixpoint`
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct Joint
{
    /// The members, in block order.
    pub members: Vec<SlotIndex>,
    /// The declaration being read and its summand.
    pub own: Maybe<(SlotIndex, Summand), joint::Absent>,
}

/// A member of a joint fixpoint as its own lowering left it: `thunk (fix. λ.
/// branch)` at `+U (domain -> codomain)`.
///
/// # Specification
/// - requires: the ids are live in the arena the member was minted into.
/// - ensures: the declaration form, its declared type with the arrow's two
///   halves, its body under its own fixpoint binder and parameter, its
///   fixpoint's claim, and the declaration's origin, together.
/// - provides: what the joint fixpoint is built from.
/// - fails: none as a data value; interpretation belongs to its consumers.
/// - panics: none as a data value.
/// - executable: none — `joinable` reads it from the arena and `join`
///   interprets it.
///
/// # Adequacy
/// - hypothesis: L3 — as [`Joint`].
/// - witness: `lower::native::tests::a_mutual_blocks_recursive_functions_share_one_fixpoint`
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Joinable
{
    /// The declaration form, where its function lowered.
    declaration: NodeIndex,
    /// Its declared type, `+U (domain -> codomain)`.
    signature: ValueTypeId,
    /// The parameter's type.
    domain: ValueTypeId,
    /// The result type.
    codomain: CompTypeId,
    /// The body, under the fixpoint binder and the parameter.
    branch: ComputationId,
    /// The fixpoint's claim.
    evidence: FixpointEvidence,
    /// The declaration's origin.
    origin: Origin,
}

impl Joint
{
    /// No joint: the declaration being read is no member of one.
    ///
    /// # Specification
    /// trivial.
    #[must_use]
    pub(super) const fn alone() -> Self
    {
        Self {
            members: Vec::new(),
            own: Maybe::Absent(joint::Absent::Alone),
        }
    }

    /// The summand of the declaration being read.
    ///
    /// # Specification
    /// trivial.
    pub(super) const fn summand(&self) -> Maybe<Summand, joint::Absent>
    {
        match self.own {
            Maybe::Present((_, summand)) => Maybe::Present(summand),
            Maybe::Absent(reason) => Maybe::Absent(reason),
        }
    }

    /// The summand of the member `name` names, read where the declaration
    /// being read is declared.
    ///
    /// # Specification
    /// - requires: `collected` is the module the joint was read from.
    /// - ensures: the position of the member declared under `name` beside the
    ///   declaration being read, when one is.
    /// - fails: [`joint::Absent::Alone`] outside a joint;
    ///   [`joint::Absent::Outside`] for a name no member is declared under.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Joint`].
    /// - witness: `lower::native::tests::a_mutual_blocks_recursive_functions_share_one_fixpoint`
    #[spec(ensures: |ret| match ret {
        Maybe::Present(summand) => self.members.get(usize::from(summand)).is_some(),
        Maybe::Absent(_) => true,
    })]
    pub(super) fn member<'source>(
        &self,
        collected: &Collected<'source>,
        name: SurfaceName<'source>,
    ) -> Maybe<Summand, joint::Absent>
    {
        let Maybe::Present((owner, _)) = self.own
        else {
            return Maybe::Absent(joint::Absent::Alone);
        };
        let Some(container) = collected
            .slots
            .get(usize::from(owner))
            .map(|slot| slot.container)
        else {
            return Maybe::Absent(joint::Absent::Alone);
        };
        collected
            .by_name
            .get(&(container, name))
            .and_then(|target| self.members.iter().position(|member| member == target))
            .map_or(Maybe::Absent(joint::Absent::Outside), |at| {
                Maybe::Present(Summand::from(at))
            })
    }
}

/// The column entry no written pattern fills: it matches anything and binds
/// nothing, as a field a catch-all row was specialised over.
///
/// # Specification
/// trivial.
const UNWRITTEN: PatternAt = PatternAt(usize::MAX);

/// The computation type a position answers, as a function's result or a
/// match's answer states it, with the frame it was read under and the
/// innermost match arm it was passed into on its way to the position.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: the node is read where a result is read, under `frame`; `arm`
///   names an arm whose frame stands between `frame` and the position.
/// - executable: none — the coordinates hold no tree to check them against.
///
/// # Adequacy
/// - hypothesis: L3 — an answer written on the match and one taken from the
///   function result each become the motive of the same tree, and one passed
///   into an arm is read at the constructor the arm matched.
/// - witness: `lower::native::tests::a_match_takes_its_answer_from_the_function_result`
/// - witness: `lower::native::tests::a_match_in_an_arm_reads_the_answer_at_the_arm_s_constructor_2994`
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(super) struct Answer
{
    /// The type's syntax node.
    pub node: NodeIndex,
    /// The frame the type was read under.
    pub frame: Frame,
    /// What the position answers of the type the node writes.
    pub over: Over,
    /// The innermost arm the answer was passed into, whose reading of its
    /// match's scrutinee the answer is read under.
    pub arm: Maybe<ArmIndex, passed::Absent>,
}

/// What a position answers of the type its answer's node writes.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: a loop arm's frame binds the answer at the loop's point
///   innermost.
/// - executable: none — the frame is a coordinate.
///
/// # Adequacy
/// - hypothesis: L3 — `loop => back(loop)` takes its endpoints from the path
///   over the loop, and a written answer from itself.
/// - witness: `lower::native::tests::a_loop_arm_follows_the_constructors_branches`
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(super) enum Over
{
    /// The written type itself.
    Written,
    /// The path over a loop of a case answering the written type `B`:
    /// `Path(B, y, y)`, `y` the case's answer at the loop's point, which the
    /// arm's frame `arm` binds innermost. Once the case is minted the lowering
    /// substitutes for `y` the answer [`gandr_core_term::identity::answer_at`]
    /// reads at the point.
    Loop
    {
        /// The arm's frame.
        arm: Frame,
    },
    /// The returner over the written value type, `-F B`: the answer of a
    /// thunk's body whose signature writes the alias `() => B`.
    Returning,
    /// The arrows the value function space `(A1, …, An) => B` the node writes
    /// stands for, past its first `taken` domains: `Aₜ₊₁ -> … -> An -> -F B`.
    /// The answer of a thunk's body whose signature writes the alias, and of
    /// each lambda under it but the last, which answers `B` returning.
    Valued
    {
        /// How many domains the lambdas around the position took.
        taken: usize,
    },
}

/// Where a constructor takes its whole classifier from.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: a written classifier is a type node read under the constructor's
///   frame; an answered one names the frame the constructor stands under; a
///   slot names a data family's form, the argument's place among its parameters
///   and the stretch of the operand store the application's arguments occupy.
/// - executable: none — the coordinates hold no tree to check them against.
///
/// # Adequacy
/// - hypothesis: L3 — an annotated constructor, one at the tail of a body a
///   signature answers, a field of either, one written as a data family's
///   argument, and a family without parameters.
/// - witness: `lower::native::tests::a_parameterized_constructor_needs_its_classifier`
/// - witness: `lower::native::tests::a_constructor_takes_its_classifier_from_the_type_it_answers_402`
/// - witness: `lower::native::tests::a_constructor_takes_its_slot_as_a_family_argument_421`
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(super) enum Classifier
{
    /// A type the source wrote for the constructor: its annotation, the
    /// signature of the definition it is, or, for a field, the argument the
    /// classifier of the constructor around it writes at the parameter the
    /// field is typed by.
    Written(NodeIndex),
    /// The value type the answer of the position returns, the answer read
    /// under its own frame and carried to `frame`, the constructor's.
    Answered
    {
        /// The answer the position states.
        answer: Answer,
        /// The frame the constructor stands under.
        frame: Frame,
    },
    /// The constructor is written as an argument of a data family: the
    /// family's parameter at its place, under the arguments before it.
    Slot(Argued),
    /// The constructor is written as an argument of a call naming a
    /// declaration: the type the declaration writes for the parameter at its
    /// place, under the parameters before it, with those replaced by the
    /// arguments written for them.
    Parameter(CalledAt),
    /// The constructor is written in a field of another: the field's declared
    /// type, read under the family's parameters and the fields before it, with
    /// those replaced by the arguments of the other's classifier and the fields
    /// it is written with.
    Field(FieldOf),
    /// The constructor is written as an index a generator's result states:
    /// the family's index type at its place, read under the family's
    /// parameters and the indices before it, with those replaced by the
    /// generator's own parameters and the indices it states before it (#4027).
    Stated(StatedIndex),
    /// The family's one classifier, which the lowering inserts: the family
    /// has no parameters.
    Inserted,
}

/// A field of a written constructor, as [`Classifier::Field`] reads it.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: `around` is the constructor's node and `declared` the field's
///   declared type, read under the family's `parameters` and the `index` fields
///   before it.
/// - executable: none — the coordinates hold no tree to check them against.
///
/// # Adequacy
/// - hypothesis: L3 — as [`Classifier::Field`].
/// - witness: `lower::native::tests::a_field_classifies_the_constructor_written_in_it_1171`
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(super) struct FieldOf
{
    /// The constructor the field belongs to.
    pub around: NodeIndex,
    /// The field's declared type.
    pub declared: NodeIndex,
    /// How many parameters the family declares.
    pub parameters: usize,
    /// The field's place among its constructor's fields.
    pub index: usize,
}

/// An index a generator's result states, as [`Classifier::Stated`] reads it.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: `form` is the family's position in the collection's data list,
///   `generator` the generator's among its generators, and `place` the index's
///   among the indices the generator states.
/// - executable: none — the coordinates hold no tree to check them against.
///
/// # Adequacy
/// - hypothesis: L3 — as [`Classifier::Stated`].
/// - witness: `lower::native::tests::a_constructor_at_a_family_s_index_takes_the_index_s_type_4027`
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(super) struct StatedIndex
{
    /// The family's position in the collection's data list.
    pub form: usize,
    /// The generator's place among the family's generators.
    pub generator: usize,
    /// The index's place among the indices the generator states.
    pub place: usize,
}

/// A form with its parentheses stripped, as [`Lowerer::unwrapped`] reads it.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: the operands keep source order.
/// - executable: none — the coordinates hold no tree to check them against.
///
/// # Adequacy
/// - hypothesis: L3 — as [`Lowerer::unwrapped`].
/// - witness: `lower::native::tests::a_constructor_takes_its_classifier_from_the_type_it_answers_402`
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct Unwrapped
{
    /// The form's node.
    pub node: NodeIndex,
    /// Its former.
    pub former: Former,
    /// The first tile it is written with.
    pub keyword: Option<Placed>,
    /// Its operands, left to right.
    pub operands: Vec<NodeIndex>,
}

/// The place a value argument takes in a data family's application.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: `form` is the family's position in the collection's data list,
///   `place` the argument's among the family's parameters, and `applied` the
///   operand stretch of the application's arguments, `place` within it.
/// - executable: none — the plan holds no store to check its stretch against.
///
/// # Adequacy
/// - hypothesis: L3 — as [`Classifier`]'s slot row.
/// - witness: `lower::native::tests::a_constructor_takes_its_slot_as_a_family_argument_421`
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(super) struct Argued
{
    /// The family's position in the collection's data list.
    pub form: usize,
    /// The argument's place among the family's parameters.
    pub place: usize,
    /// The application's arguments, in the operand store.
    pub applied: Stretch,
}

/// The parameter a value argument stands at in a call naming a declaration.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: `typed` is the type the declaration at `slot` writes for the
///   parameter, read under the parameters before it, and `applied` the operand
///   stretch of the call's arguments, one per explicit parameter from the
///   first.
/// - executable: none — the plan holds no store to check its stretch against.
///
/// # Adequacy
/// - hypothesis: L3 — as [`Classifier`]'s parameter row.
/// - witness: `lower::native::tests::a_constructor_argument_reads_the_arguments_before_it_1876`
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(super) struct CalledAt
{
    /// The type the declaration writes for the parameter.
    pub typed: Placed,
    /// The declaration's slot.
    pub slot: SlotIndex,
    /// The call's arguments, in the operand store.
    pub applied: Stretch,
}

/// One field of one generator of a written data family.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: `form` is the family's position in the collection's data list,
///   `tag` the generator's among the family's, and `index` the field's among
///   the generator's.
/// - executable: none — the coordinates hold no collection to check them
///   against.
///
/// # Adequacy
/// - hypothesis: L3 — as [`Lowerer::field_classifier`].
/// - witness: `lower::native::tests::a_constructor_takes_its_classifier_from_the_type_it_answers_402`
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct FieldAt
{
    /// The family's position in the collection's data list.
    form: usize,
    /// The generator's tag.
    tag: usize,
    /// The field's position among the generator's.
    index: usize,
}

/// A constructor applied to its fields, as the classification planned it.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: the fields are a stretch of the operand store, as many as the
///   constructor takes.
/// - executable: none — the plan holds no store to check its stretch against.
///
/// # Adequacy
/// - hypothesis: L3 — nullary and three-field constructors, annotated and not,
///   lower to the constructor value over their fields.
/// - witness: `lower::native::tests::a_constructor_applies_to_its_fields`
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(super) struct Constructed
{
    /// The family's admission position.
    pub family: ConstantIndex,
    /// The constructor's tag.
    pub tag: ConstructorTag,
    /// The fields, in the operand store.
    pub fields: Stretch,
    /// Where its classifier comes from.
    pub classifier: Classifier,
}

/// One pattern, as the match compiler reads it.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: a constructor's, a tuple's, a record's and a cell's fields are a
///   stretch of the match's part store, a cell's two, a record's labels one per
///   field; a binder numbers its arm variable; an as-pattern's alias is a
///   binder minted after it.
/// - executable: none — the pattern holds no store to check its stretch
///   against.
///
/// # Adequacy
/// - hypothesis: L3 — the witnesses compile every shape into the tree they
///   assert.
/// - witness: `lower::native::tests::nested_constructor_patterns_compile_to_nested_cases`
/// - witness: `lower::native::tests::telescope_patterns_split_and_project`
/// - witness: `lower::native::tests::sum_patterns_case_on_the_stated_arity`
/// - witness: `lower::native::tests::list_patterns_case_on_the_native_list`
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
enum Matcher
{
    /// `_`: matches anything, binds nothing.
    Wild,
    /// A name: matches anything and binds the arm variable numbered here.
    Binder(VariableAt),
    /// `?`: a pattern the author has not written.
    Hole(HoleId),
    /// A constructor of the family `form` reads its generators from, with its
    /// fields.
    Constructor
    {
        /// Where the family's generators are read from.
        form: Generators,
        /// The constructor's tag.
        tag: usize,
        /// The field patterns, in the part store.
        fields: Stretch,
    },
    /// `true` or `false`.
    Boolean(bool),
    /// An integer literal.
    Integer(Literal),
    /// A positional telescope `#{p, …}` or a tuple `(p, …)`: its components,
    /// in index order.
    Tuple
    {
        /// The component patterns, in the part store.
        fields: Stretch,
        /// Whether its split reads the motive at the scrutinee: a link of a
        /// dependent record whose label a later entry names.
        dependent: Dependent,
    },
    /// A labelled telescope `#{.l = p, …}`: the fields it names.
    Record
    {
        /// The labels, one per field.
        labels: Vec<FieldLabel>,
        /// The field patterns, in the part store.
        fields: Stretch,
    },
    /// An injection `+{ .l = p }` into the summand `summand` of a sum of
    /// `arity` summands.
    Injection
    {
        /// The summand's index.
        summand: usize,
        /// How many summands the sum has.
        arity: usize,
        /// The payload's pattern.
        field: PatternAt,
    },
    /// `[]`: the empty native list.
    Nil,
    /// A native list's cell: its head's and its tail's patterns, in the part
    /// store, the head first.
    Cell
    {
        /// The head's and the tail's patterns.
        fields: Stretch,
    },
    /// `p as x`: the pattern `inner` matches, and the binder `alias` binds
    /// the whole value.
    Alias
    {
        /// The pattern the value matches.
        inner: PatternAt,
        /// The binder of the whole value.
        alias: PatternAt,
    },
}

/// One row of a pattern matrix.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: one pattern per column of its matrix; every binding names a tree
///   level its variable was settled at.
/// - executable: none — the row holds no matrix to check its width against.
///
/// # Adequacy
/// - hypothesis: L3 — as [`Matcher`].
/// - witness: `lower::native::tests::nested_constructor_patterns_compile_to_nested_cases`
#[derive(Clone, Debug, Eq, PartialEq)]
struct Row
{
    /// The patterns still to test, one per column.
    columns: Vec<PatternAt>,
    /// The arm the row runs.
    arm: ArmAt,
    /// Each arm variable settled so far, with the level that settled it.
    bindings: Vec<(VariableAt, TreeLevel)>,
    /// The first hole the row matched through, which decides whether it
    /// matches.
    stuck: Maybe<HoleId, stuck::Absent>,
}

/// One node of a match's decision tree.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: a child's position is after its parent's, so minting the tree in
///   descending position order mints every child first; level zero is the
///   scrutinee itself, and the binder a node introduces under `depth` tree
///   binders is level `depth + 1`.
/// - executable: none — the node holds no tree to check its children against.
///
/// # Adequacy
/// - hypothesis: L3 — the witnesses read each kind of node back out of the
///   arena.
/// - witness: `lower::native::tests::nested_constructor_patterns_compile_to_nested_cases`
/// - witness: `lower::native::tests::literal_patterns_compare_and_branch`
/// - witness: `lower::native::tests::a_pattern_hole_leaves_its_leaf_stuck`
/// - witness: `lower::native::tests::telescope_patterns_split_and_project`
/// - witness: `lower::native::tests::sum_patterns_case_on_the_stated_arity`
#[derive(Clone, Debug, Eq, PartialEq)]
enum Test
{
    /// A node the compiler has not reached yet.
    Pending,
    /// Run arm `arm`, reached under `depth` tree binders, its variables
    /// settled at these levels, in variable order.
    Leaf
    {
        /// The arm.
        arm: ArmAt,
        /// The tree binders above the leaf.
        depth: Depth,
        /// The level that settled each arm variable.
        bindings: Vec<TreeLevel>,
    },
    /// The hole that decides whether the first surviving row matches.
    Stuck(HoleId),
    /// A branch whose constructor no row admits, at a family of one index:
    /// the case of no branches on its equation, the innermost binder, which
    /// the checker admits when the constructor's index is apart from the
    /// scrutinee's.
    Absurd,
    /// Switch on the native data value at `level`: one child per
    /// constructor, with the constructor's arity.
    Data
    {
        /// The scrutinised level.
        level: TreeLevel,
        /// The tree binders above the switch.
        depth: Depth,
        /// The family, when the family over no arguments classifies its
        /// constructors.
        family: Maybe<ConstantIndex, bare::Absent>,
        /// The data declaration whose constructors the branches are, by
        /// which a printer names them.
        eliminated: Maybe<ConstantIndex, eliminated::Absent>,
        /// The equations each branch binds past its fields, one per index of
        /// the family; its child stands under both.
        equations: usize,
        /// Each constructor's arity and child.
        branches: Vec<(usize, TestAt)>,
    },
    /// Switch on the boolean at `level`: true on the left.
    Boolean
    {
        /// The scrutinised level.
        level: TreeLevel,
        /// The tree binders above the switch.
        depth: Depth,
        /// The child for `true`.
        yes: TestAt,
        /// The child for `false`.
        no: TestAt,
    },
    /// Compare the integer at `level` with `literal`.
    Integer
    {
        /// The scrutinised level.
        level: TreeLevel,
        /// The tree binders above the test.
        depth: Depth,
        /// The literal compared with.
        literal: Literal,
        /// The child for an equal integer.
        yes: TestAt,
        /// The child for any other.
        no: TestAt,
    },
    /// Split the tuple at `level` into its `arity` components, component
    /// zero outermost.
    Split
    {
        /// The scrutinised level.
        level: TreeLevel,
        /// The tree binders above the split.
        depth: Depth,
        /// How many components it binds.
        arity: usize,
        /// Whether the split reads its motive at the scrutinee.
        dependent: Dependent,
        /// The label of each component some row leaves unwritten under a
        /// label pattern, or that holds the rest of a dependent record from
        /// that label's field on, by component, ascending.
        unwritten: Vec<(usize, FieldLabel)>,
        /// The child under them.
        child: TestAt,
    },
    /// Project each of `labels` off the record at `level`, binding them in
    /// order.
    Record
    {
        /// The scrutinised level.
        level: TreeLevel,
        /// The tree binders above the projections.
        depth: Depth,
        /// The labels projected, in order.
        labels: Vec<FieldLabel>,
        /// The child under them.
        child: TestAt,
    },
    /// Switch on the summand of the sum at `level`: one child per summand,
    /// under its payload's binder.
    Sum
    {
        /// The scrutinised level.
        level: TreeLevel,
        /// The tree binders above the switch.
        depth: Depth,
        /// Each summand's child.
        branches: Vec<TestAt>,
    },
    /// Case on the native list at `level`: the empty list's child under no
    /// binder, and the cell's under its head's and its tail's, the head
    /// outermost.
    List
    {
        /// The scrutinised level.
        level: TreeLevel,
        /// The tree binders above the case.
        depth: Depth,
        /// The child for the empty list.
        nil: TestAt,
        /// The child for a cell.
        cell: TestAt,
    },
}

/// One match, compiled to its decision tree.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: the tree's first node is its root; every arm body is read under
///   the case's frame and the arm's variables.
/// - executable: none — the record holds no tree to check its nodes against.
///
/// # Adequacy
/// - hypothesis: L3 — the witnesses lower matches of each shape and read the
///   tree back.
/// - witness: `lower::native::tests::nested_constructor_patterns_compile_to_nested_cases`
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct CaseForm
{
    /// The scrutinee's syntax node.
    scrutinee: NodeIndex,
    /// The frame the match is read under.
    frame: Frame,
    /// The answer the motive is read from.
    answer: Maybe<Answer, answered::Absent>,
    /// The answer written on the match itself, `case e -> C { … }`, which
    /// the tree's root is ascribed; absent where only its position states
    /// one.
    ascribed: Maybe<Answer, answered::Absent>,
    /// Each constructor arm's body.
    bodies: Vec<NodeIndex>,
    /// The decision tree.
    tests: Vec<Test>,
    /// The loop arms, one per loop of the root's sort in the order its loop
    /// branches follow its constructors' branches, or none.
    loops: Vec<LoopArm>,
    /// What the origin table keeps of the arms.
    origin: CaseOrigin,
    /// Each constructor arm's variables, in the order its leaves settle
    /// them.
    variables: Vec<Vec<Placed>>,
}

/// What one constructor arm of a match reads the match's scrutinee as, for
/// the answer the match passes the arm's body.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: `outer` names an arm stored before this one.
/// - executable: none — the reading names binders of the lowering's scope and
///   an arm of its store, which the record cannot reach.
///
/// # Adequacy
/// - hypothesis: L3 — a match in an arm, on the variable naming the arm's
///   field, reads the answer and the outer scrutinee at the arm's constructor;
///   one in an arm that leaves a field unnamed reads them as written.
/// - witness: `lower::native::tests::a_match_in_an_arm_reads_the_answer_at_the_arm_s_constructor_2994`
/// - witness: `lower::native::tests::an_arm_leaving_a_field_unnamed_passes_the_answer_as_written_2994`
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct ArmReading
{
    /// The constructor the arm reads the scrutinee at.
    settled: Maybe<Settled, settled::Absent>,
    /// The arm the match's own answer was passed into.
    outer: Maybe<ArmIndex, passed::Absent>,
}

/// The constructor an arm reads its match's scrutinee at, over what it
/// reads each field at.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: `scrutinee` is the binder the case's frame reads the scrutinee
///   by, intuitionistic; `read` spells one term in prefix order, a constructor
///   first.
/// - executable: none — the binders are coordinates of the lowering's scope.
///
/// # Adequacy
/// - hypothesis: L3 — as [`ArmReading`].
/// - witness: `lower::native::tests::a_match_in_an_arm_reads_the_answer_at_the_arm_s_constructor_2994`
/// - witness: `lower::native::tests::an_arm_variable_at_a_switched_field_reads_its_constructor_3008`
#[derive(Clone, Debug, Eq, PartialEq)]
struct Settled
{
    /// The scrutinee's binder.
    scrutinee: ScopeId,
    /// What the arm reads the scrutinee at, in prefix order.
    read: Vec<Built>,
}

/// One node of what an arm reads a level of its match's tree at, in prefix
/// order: the binder of the arm variable settled there, or the constructor a
/// switch above the arm's leaf matched there, whose fields' readings follow
/// it.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: a constructor's `arity` is its field count, and `family` the bare
///   family that classifies it.
/// - executable: none — the binders are coordinates of the lowering's scope.
///
/// # Adequacy
/// - hypothesis: L3 — as [`ArmReading`].
/// - witness: `lower::native::tests::a_match_in_an_arm_reads_the_answer_at_the_arm_s_constructor_2994`
/// - witness: `lower::native::tests::an_arm_variable_at_a_switched_field_reads_its_constructor_3008`
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Built
{
    /// The arm variable's binder.
    Bound(ScopeId),
    /// A constructor, its fields' readings after it.
    Constructed
    {
        /// The bare family the switch eliminates.
        family: ConstantIndex,
        /// The branch's constructor.
        tag: ConstructorTag,
        /// The constructor's field count.
        arity: usize,
    },
}

/// A field read off a data value by its name, `e.l`: the case over `e` whose
/// branch for each constructor returns that constructor's field `l`.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: `branches` holds, per constructor in tag order, its field count
///   and the position of its field `l`, which is below that count; the subject
///   is read as a value under `frame`.
/// - executable: none — the coordinates hold no tree to check them against.
///
/// # Adequacy
/// - hypothesis: L3 — as [`Lowerer::data_field`].
/// - witness: `lower::native::tests::a_data_field_is_the_case_returning_it_1106`
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct Projected
{
    /// The data value's syntax node, a name.
    subject: NodeIndex,
    /// The frame the projection is read under.
    frame: Frame,
    /// The family the case eliminates.
    family: ConstantIndex,
    /// Per constructor, its field count and the position of the field read.
    branches: Vec<(usize, usize)>,
    /// Where the type the projection returns is read from.
    typed: Typed,
}

/// Where the type a field projection returns is read from.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: an answer is the projection's position's; a field names its first
///   constructor's field, whose type names no field before it.
/// - executable: none — the coordinates hold no tree to check them against.
///
/// # Adequacy
/// - hypothesis: L3 — as [`Lowerer::data_field`].
/// - witness: `lower::native::tests::a_data_field_is_the_case_returning_it_1106`
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Typed
{
    /// The answer the projection's position states.
    Answered(Answer),
    /// The field's declared type, with the family's parameters replaced by the
    /// arguments of the type the subject is stated at.
    Field
    {
        /// The subject's stated type's syntax node.
        stated: NodeIndex,
        /// The field's declared type's syntax node.
        declared: NodeIndex,
        /// How many fields come before it in its constructor.
        earlier: usize,
        /// How many parameters the family takes.
        parameters: usize,
    },
}

impl Projected
{
    /// The nodes a projection typed by its field reads its type off: its
    /// subject, the subject's stated type and the field's declared type.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: present exactly when the projection is typed by its field,
    ///   with the subject first.
    /// - provides: the types the mint sweep lowers before the projection.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a field read in an operand, where no answer is
    ///   stated, is typed by its declaration.
    /// - witness: `lower::native::tests::a_data_field_is_the_case_returning_it_1106`
    #[spec(ensures: |ret| ret.is_some() == matches!(self.typed, Typed::Field { .. }))]
    pub(super) const fn typed_by(&self) -> Option<(NodeIndex, NodeIndex, NodeIndex)>
    {
        match self.typed {
            Typed::Field {
                stated, declared, ..
            } => Some((self.subject, stated, declared)),
            Typed::Answered(_) => None,
        }
    }
}

/// What a value's written type names, as a match reads its scrutinee's.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: a family's `form` is its position among the collected data forms.
/// - executable: none — the coordinates hold no collection to check them
///   against.
///
/// # Adequacy
/// - hypothesis: L3 — as [`Lowerer::stated_data`].
/// - witness: `lower::native::tests::a_match_of_no_arms_switches_on_empty_data_and_on_a_path`
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Stated
{
    /// A path type, whose switch the checker decides.
    Path,
    /// A data family, bare or applied.
    Family
    {
        /// The family's declaration.
        constant: ConstantIndex,
        /// The family's position among the collected data forms.
        form: usize,
    },
}

/// One loop arm of a match, `loop => e`.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: `words` and `generator` name a loop the lowering collected.
/// - executable: none — the indices name collected words.
///
/// # Adequacy
/// - hypothesis: L3 — as [`Lowerer::loop_arms`].
/// - witness: `lower::native::tests::a_loop_arm_follows_the_constructors_branches`
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct LoopArm
{
    /// The words the loop is a letter of, by their position among the
    /// collected words.
    words: usize,
    /// The loop's position among its words' cells.
    generator: usize,
    /// The arm's body.
    body: NodeIndex,
    /// The arm's pattern, the loop's name.
    named: Placed,
}

/// The loop an arm's whole pattern names.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: `words` and `generator` name a loop the lowering collected.
/// - executable: none — the indices name collected words.
///
/// # Adequacy
/// - hypothesis: L3 — as [`Lowerer::loop_named`].
/// - witness: `lower::native::tests::a_loop_arm_follows_the_constructors_branches`
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct NamedLoop
{
    /// The words the loop is a letter of, by their position among the
    /// collected words.
    words: usize,
    /// The loop's position among its words' cells.
    generator: gandr_kernel_term::CellIndex,
}

/// What a pattern's name is to the modules enclosing it.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Declared
{
    /// Some enclosing module binds the name to a loop.
    Loop,
    /// None does: the name binds a pattern variable.
    Binder,
}

/// One pattern matrix the compiler has yet to reduce, and the tree node it
/// fills.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: one level per column, each row as wide.
/// - executable: none — the item holds no tree.
///
/// # Adequacy
/// - hypothesis: L3 — as [`Test`].
/// - witness: `lower::native::tests::nested_constructor_patterns_compile_to_nested_cases`
#[derive(Clone, Debug, Eq, PartialEq)]
struct Work
{
    /// The tree node the matrix compiles to.
    slot: TestAt,
    /// The tree binders above it.
    depth: Depth,
    /// The level each column scrutinises.
    levels: Vec<TreeLevel>,
    /// The rows.
    rows: Vec<Row>,
}

/// The patterns of one match, as the compiler reads them.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: a pattern's parts are minted after it, so a descending walk meets
///   every part before the pattern holding it.
/// - executable: none — the store is filled by the reader.
///
/// # Adequacy
/// - hypothesis: L3 — as [`Matcher`].
/// - witness: `lower::native::tests::a_match_keeps_its_patterns_beside_its_tree`
#[derive(Clone, Debug, Default, Eq, PartialEq)]
struct Written
{
    /// Each pattern, with its syntax.
    shapes: Vec<(Placed, Matcher)>,
    /// The field patterns of every constructor pattern, stretch by stretch.
    parts: Vec<PatternAt>,
    /// The spans inside a pattern that answer apart from its own: the name a
    /// constructor pattern applies, a word pattern's letter, a sum pattern's
    /// key, an or-pattern.
    spelled: Vec<(PatternAt, ByteSpan, PatternReading)>,
    /// Each wildcard a labelled pattern leaves for a field it does not
    /// write, with the field's label, and each place holding the rest of a
    /// dependent record, with the label of the field the rest starts at, in
    /// the order read.
    unwritten: Vec<(PatternAt, FieldLabel)>,
    /// Whether a sum pattern under no stated sum reads its index as a summand
    /// of the sum the case's arms settle: set where the patterns are a case's
    /// arms.
    positional: Positional,
    /// Each sum pattern read so under no stated sum, at the arity its index
    /// alone gives, with the site it was read at.
    unstated: Vec<(PatternAt, Site)>,
    /// Each cell and empty list a list pattern implies past its first cell,
    /// which stands at the list's own syntax and answers no span of its own.
    implied: Vec<PatternAt>,
}

/// The matcher every unwritten column entry reads as.
///
/// # Specification
/// trivial.
static WILD: Matcher = Matcher::Wild;

impl Written
{
    /// The pattern `row` holds in `column`; the wildcard for an entry no
    /// written pattern fills.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the stored pattern the column names, or the wildcard.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a catch-all row specialised at a constructor of two
    ///   fields tests neither field.
    /// - witness: `lower::native::tests::nested_constructor_patterns_compile_to_nested_cases`
    #[spec(ensures: |ret| row.columns.get(column.0).and_then(|&at| self.shapes.get(at.0)).map_or(*ret == Matcher::Wild, |held| *ret == held.1))]
    fn entry(
        &self,
        row: &Row,
        column: Column,
    ) -> &Matcher
    {
        row.columns
            .get(column.0)
            .and_then(|&at| self.shapes.get(at.0))
            .map_or(&WILD, |held| &held.1)
    }

    /// The refusal of the pattern `row` holds in `switch`'s column, of
    /// another kind than the first pattern the switch tests there.
    ///
    /// # Specification
    /// - requires: the pattern `row` holds in the column is of another kind
    ///   than the switch's first.
    /// - ensures: [`LoweringRefusal::MismatchedPattern`] at the bytes of that
    ///   pattern, naming the first's; at the first's own bytes for an entry no
    ///   written pattern fills.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a constructor of another data type and an integer
    ///   literal beside a constructor are each refused at their own arm.
    /// - witness: `lower::native::tests::a_pattern_of_another_type_is_refused_at_its_arm`
    #[spec(ensures: |ret| matches!(ret, LoweringRefusal::MismatchedPattern { first, .. } if first == switch.first))]
    fn mismatched<'source>(
        &self,
        row: &Row,
        switch: Switch,
    ) -> LoweringRefusal<'source>
    {
        let span = row
            .columns
            .get(switch.column.0)
            .and_then(|&at| self.shapes.get(at.0))
            .map_or(switch.first, |held| held.0.span);
        LoweringRefusal::MismatchedPattern {
            span,
            first: switch.first,
        }
    }
}

/// What the leftmost written pattern of a matrix's first row tests.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: one head per testing pattern shape.
/// - executable: none — the head holds no matrix.
///
/// # Adequacy
/// - hypothesis: L3 — as [`Test`].
/// - witness: `lower::native::tests::nested_constructor_patterns_compile_to_nested_cases`
#[derive(Clone, Debug, Eq, PartialEq)]
enum Head
{
    /// A hole: the row's match is undecided.
    Hole(HoleId),
    /// A constructor of the family whose generators are read from here.
    Data(Generators),
    /// A boolean.
    Boolean,
    /// This integer.
    Integer(Literal),
    /// A tuple of this many components, split dependently or not.
    Tuple(usize, Dependent),
    /// A record.
    Record,
    /// An injection into a sum of this many summands.
    Sum(usize),
    /// The empty native list or a cell.
    List,
}

/// Whether a queued pattern is the label tile a punned telescope entry binds.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct Punned(bool);

/// Whether a sum pattern under no stated sum may read its index as a summand
/// whose arity the case's arms settle together.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct Positional(bool);

/// Whether the places of a dependent record a pattern splits are written,
/// each with its type, or are the fields of the record a relation between
/// types abbreviates or a theory's models state, which no syntax writes.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Places
{
    /// The record is written, and each entry states its type.
    Written,
    /// The record is a relation's, or one nested in it: its fields' types are
    /// the relation's.
    Related(Layout),
    /// The record is a theory's models: its fields' types are the
    /// signature's.
    Modelled,
}

/// Whether a word's letter is a loop's inverse rather than the loop.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct Inverse(bool);

/// How many components a split binds, or how many summands a sum switch
/// cases on.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct Width(usize);

/// A pattern the reader has allocated and not yet read.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: the slot is the pattern's place in the match's store.
/// - executable: none — the record holds no store.
///
/// # Adequacy
/// - hypothesis: L3 — a sum pattern nested in a telescope pattern reads its
///   arity from the component type its scrutinee's type states.
/// - witness: `lower::native::tests::sum_patterns_case_on_the_stated_arity`
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Queued
{
    /// The pattern's syntax: a form, or the label tile a pun binds.
    at: Placed,
    /// The slot it fills.
    slot: PatternAt,
    /// The type its position states, when the source wrote one.
    stated: Maybe<NodeIndex, binder_type::Absent>,
    /// The record of a relation between types its position holds, when no
    /// syntax states it: a field of the record an equivalence abbreviates.
    related: Maybe<Layout, related::Absent>,
    /// Whether `at` is a punned label.
    punned: Punned,
}

/// The column a switch tests, and the bytes of the first pattern tested
/// there, which a row of another kind is refused against.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: the level is the one the column scrutinises.
/// - executable: none — the switch holds no matrix.
///
/// # Adequacy
/// - hypothesis: L3 — as [`Test`].
/// - witness: `lower::native::tests::patterns_outside_the_fragment_are_declined_by_name`
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Switch
{
    /// The column.
    column: Column,
    /// The tree level it scrutinises.
    level: TreeLevel,
    /// The bytes of the first pattern the switch tests in the column.
    first: ByteSpan,
}

/// A decision tree under construction: its nodes, and the matrices still to
/// reduce into them.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: every queued matrix names a pending node.
/// - executable: none — the pairing is maintained by [`Compiling::queue`].
///
/// # Adequacy
/// - hypothesis: L3 — as [`Test`].
/// - witness: `lower::native::tests::nested_constructor_patterns_compile_to_nested_cases`
#[derive(Clone, Debug, Default, Eq, PartialEq)]
struct Compiling
{
    /// The tree's nodes.
    tests: Vec<Test>,
    /// The matrices still to reduce.
    work: Vec<Work>,
}

impl Compiling
{
    /// Allocate a pending node and queue the matrix that fills it.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the new node's position, after every earlier node, and one
    ///   more queued matrix naming it.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a child's position follows its parent's.
    /// - witness: `lower::native::tests::nested_constructor_patterns_compile_to_nested_cases`
    #[spec(
        captures: before = (self.tests.len(), self.work.len()),
        ensures: |ret| ret == TestAt(before.0) && self.tests.len() == before.0.saturating_add(1) && self.work.len() == before.1.saturating_add(1),
    )]
    fn queue(
        &mut self,
        depth: Depth,
        levels: Vec<TreeLevel>,
        rows: Vec<Row>,
    ) -> TestAt
    {
        let slot = TestAt(self.tests.len());
        self.tests.push(Test::Pending);
        self.work.push(Work {
            slot,
            depth,
            levels,
            rows,
        });

        slot
    }

    /// Allocate a node the compiler fills now, with no matrix behind it.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the new node's position, after every earlier node, holding
    ///   `test`; no matrix queued.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a pruned branch's node follows its switch's.
    /// - witness: `lower::native::tests::a_constructor_no_row_admits_at_one_index_is_pruned`
    #[spec(
        captures: before = (self.tests.len(), self.work.len()),
        ensures: |ret| ret == TestAt(before.0) && self.tests.len() == before.0.saturating_add(1) && self.work.len() == before.1,
    )]
    fn place(
        &mut self,
        test: Test,
    ) -> TestAt
    {
        let slot = TestAt(self.tests.len());
        self.tests.push(test);
        slot
    }
}

/// `declared` with the binders it is read under replaced by `environment`,
/// the innermost first: the type a constructor's classifier reads where it
/// stands.
///
/// # Specification
/// - requires: `environment` holds one value per binder `declared` reads, the
///   innermost first.
/// - ensures: the substituted type, every node the substitution mints recorded
///   at `origin`; nothing when the substitution leaves no quoted type.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a slot's, a call parameter's, a field's and a stated
///   index's classifier, each over the arguments written before it.
/// - witness: `lower::native::tests::a_constructor_takes_its_slot_as_a_family_argument_421`
/// - witness: `lower::native::tests::a_constructor_argument_reads_the_arguments_before_it_1876`
/// - witness: `lower::native::tests::a_field_classifies_the_constructor_written_in_it_1171`
/// - witness: `lower::native::tests::a_constructor_at_a_family_s_index_takes_the_index_s_type_4027`
#[spec(ensures: |ret| matches!(ret, Maybe::Absent(_)) || matches!(ret, Maybe::Present(id) if sink.arena.value_type(id).is_some()))]
fn instantiated(
    declared: ValueTypeId,
    environment: &[ValueId],
    sink: &mut Sink<'_>,
    origin: Origin,
) -> Maybe<ValueTypeId, lowered::Absent>
{
    let mark = sink.arena.watermark();
    let code = sink.arena.value_quote(declared);
    let mut carried = Vec::new();
    let substituted = gandr_core_term::substitute_environment_traced(
        sink.arena,
        TermId::Value(code),
        environment,
        &mut carried,
    );
    exits::record_copies(sink, mark, &carried, origin);
    let TermId::Value(substituted) = substituted
    else {
        return Maybe::Absent(lowered::Absent::Unminted);
    };
    let Some(&Value::Quote(ty)) = sink.arena.value(substituted)
    else {
        return Maybe::Absent(lowered::Absent::Unminted);
    };

    Maybe::Present(ty)
}

impl<'source> Lowerer<'_, 'source>
{
    /// Seed every data declaration's types: each parameter's type under the
    /// parameters before it, each index classifier under the parameters and
    /// the indices before it, the universe at the outermost frame, each
    /// field's type under all the parameters and the fields before it in its
    /// constructor, and each index a constructor states, as a value, under the
    /// parameters and all its fields.
    ///
    /// # Specification
    /// - requires: the collection pass has run.
    /// - ensures: one frame per parameter, typed with its written type and
    ///   mentioned, so a type naming it counts it; one frame per index, bound
    ///   to its written name, typed and mentioned, or to none; one frame per
    ///   field but its constructor's last, and the last too where the
    ///   constructor states an index, bound to the field's written name or to
    ///   none; one seed per type and stated index the declarations write,
    ///   appended to `seeds`; each of them but the universe kept with the frame
    ///   it is read under, for the names a report or an editor spells its type
    ///   in; and each stated index handed the [`Classifier::Stated`] of its
    ///   place.
    /// - provides: the data half of [`Self::seed`].
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a two-parameter family whose field names its first
    ///   parameter lowers with the field scoped under both, and a field naming
    ///   the field before it reads that field's binder; `Cons`'s `S(n)` reads
    ///   its first field.
    /// - witness: `lower::native::tests::a_data_declaration_lowers_to_its_signature`
    /// - witness: `lower::native::tests::an_indexed_family_lowers_its_indices`
    /// - witness: `lower::native::tests::a_constructor_at_a_family_s_index_takes_the_index_s_type_4027`
    #[spec(
        captures: before = seeds.len(),
        ensures: seeds.len() >= before,
    )]
    pub(super) fn seed_data(
        &mut self,
        seeds: &mut Vec<(NodeIndex, Reading)>,
    )
    {
        let first = self.current.data;
        for (listed, form) in self.collected.data.iter().enumerate().skip(first) {
            let mut frame = Frame::Outermost;
            for parameter in &form.parameters {
                seeds.push((parameter.classifier.node, Reading::ValueType(frame)));
                self.data_frames.push((parameter.classifier.node, frame));
                let name = SurfaceName::from(self.text_at(parameter.named));
                let bound = self.scope.extend_typed(
                    frame,
                    name,
                    parameter.classifier.node,
                    Maybe::Present(parameter.named.span),
                );
                self.scope.mention(bound);
                frame = Frame::Inner(bound);
            }
            if let Maybe::Present(kind) = form.kind {
                seeds.push((kind.node, Reading::ValueType(Frame::Outermost)));
            }
            // Each index reads under the parameters and the indices before
            // it, a named one by its name; the generators read under the
            // parameters alone.
            let mut indexed = frame;
            for index in &form.indices {
                seeds.push((index.ty.node, Reading::ValueType(indexed)));
                self.data_frames.push((index.ty.node, indexed));
                let bound = match index.named {
                    Maybe::Present(named) => {
                        let name = SurfaceName::from(self.text_at(named));
                        let bound = self.scope.extend_typed(
                            indexed,
                            name,
                            index.ty.node,
                            Maybe::Present(named.span),
                        );
                        self.scope.mention(bound);
                        bound
                    },
                    Maybe::Absent(_) => self.scope.extend(
                        indexed,
                        SurfaceName::from(""),
                        Maybe::Absent(binder_site::Absent::Unwritten),
                    ),
                };
                indexed = Frame::Inner(bound);
            }
            for (tag, generator) in form.generators.iter().enumerate() {
                let last = generator.fields.len().checked_sub(1);
                let mut inner = frame;
                for (position, field) in generator.fields.iter().enumerate() {
                    seeds.push((field.ty.node, Reading::ValueType(inner)));
                    self.data_frames.push((field.ty.node, inner));
                    // The last field binds only for the indices the result
                    // states.
                    if Some(position) == last && generator.indices.is_empty() {
                        break;
                    }
                    let bound = match field.named {
                        Maybe::Present(named) => {
                            let name = SurfaceName::from(self.text_at(named));
                            let bound = self.scope.extend_typed(
                                inner,
                                name,
                                field.ty.node,
                                Maybe::Present(named.span),
                            );
                            self.scope.mention(bound);
                            bound
                        },
                        Maybe::Absent(_) => self.scope.extend(
                            inner,
                            SurfaceName::from(""),
                            Maybe::Absent(binder_site::Absent::Unwritten),
                        ),
                    };
                    inner = Frame::Inner(bound);
                }
                for (place, index) in generator.indices.iter().enumerate() {
                    seeds.push((index.node, Reading::Value(inner)));
                    self.data_frames.push((index.node, inner));
                    // A constructor written there is classified by the
                    // family's index type at its place.
                    let _first = self.inherited.insert(
                        index.node,
                        Classifier::Stated(StatedIndex {
                            form: listed,
                            generator: tag,
                            place,
                        }),
                    );
                }
            }
        }
    }

    /// The constructor `name`, written at `site`, names: one of a data family
    /// admitted strictly before the declaration `site` belongs to, declared
    /// in `site`'s own source or, when that declares none, in one source it
    /// imports unqualified. A data family's argument at a place the family
    /// declares a universe names no constructor: no constructor is a value of
    /// a universe, so the name there is a type's.
    ///
    /// # Specification
    /// - requires: `site` is the name's node or the form holding it.
    /// - ensures: the type-place absence when `site` is a data family's
    ///   argument at a parameter or index the family declares a universe;
    ///   otherwise the constructor entered under `name` in the site's source,
    ///   or else the one its unqualified imports answer, when its family's
    ///   admission position is strictly earlier than the site's declaration's;
    ///   otherwise the unnamed absence, two imports answering included.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a constructor of an earlier family resolves, a name
    ///   no family declares does not, an imported family's constructor resolves
    ///   in its importer, and a type sharing its constructor's name is read as
    ///   the type at a family's type place.
    /// - witness: `lower::native::tests::a_constructor_applies_to_its_fields`
    /// - witness: `tests::namespace::an_unqualified_import_answers_a_name_its_source_declares`
    /// - witness: `lower::native::tests::a_constructor_is_no_value_inside_its_own_family`
    /// - witness: `lower::native::tests::a_type_argument_names_the_type_its_constructor_shares_a_name_with_1855`
    #[spec(ensures: |ret| match ret {
        | Maybe::Present(found) => matches!(
            self.collected.owner_of(site.at.node),
            Maybe::Present(own) if found.family < own
        ),
        | Maybe::Absent(_) => true,
    })]
    pub(super) fn constructor_named(
        &mut self,
        site: Site,
        name: SurfaceName<'source>,
    ) -> Maybe<Constructor, constructed::Absent>
    {
        let Maybe::Present(own) = self.collected.owner_of(site.at.node)
        else {
            return Maybe::Absent(constructed::Absent::Unnamed);
        };
        // No constructor is a value of a universe, so an argument at a place
        // its data family declares one names a type.
        if let Some(&argued) = self.argued.get(&site.at.node)
            && let Some(form) = self.collected.data.get(argued.form)
            && let Some(classifier) = argued.place.checked_sub(form.parameters.len()).map_or_else(
                || {
                    form.parameters
                        .get(argued.place)
                        .map(|parameter| parameter.classifier)
                },
                |index| form.indices.get(index).map(|index| index.ty),
            )
            && self.tree.node(classifier.node).is_some_and(|node| {
                matches!(
                    shape_of(self.pbg, node),
                    Ok(Shape::Form {
                        former: Former::Universe,
                        ..
                    })
                )
            })
        {
            return Maybe::Absent(constructed::Absent::TypePlace);
        }
        let source = self.collected.unit.source_at(site.at.span.start());
        let (found, import) = match self.collected.constructors.get(&(source, name)) {
            Some(&found) => (found, None),
            None => match self.collected.imported_constructor(source, name) {
                Ok(Maybe::Present((found, import))) => (found, Some(import)),
                Ok(Maybe::Absent(_)) | Err(_) => {
                    return Maybe::Absent(constructed::Absent::Unnamed);
                },
            },
        };
        if found.family >= own {
            return Maybe::Absent(constructed::Absent::Unnamed);
        }
        if let Some(import) = import {
            self.collected.reach(import);
        }
        Maybe::Present(found)
    }

    /// The constructor `name` of the family `family` names, written
    /// qualified as `family.name` at `site`.
    ///
    /// The family is resolved as any global name is at `site`, and the
    /// constructor read from its own generators, so a constructor whose bare
    /// name the source gives another family's constructor is still named:
    /// `Theory.App` beside a source's own `App`.
    ///
    /// # Specification
    /// - requires: `site` is the qualified form or the form holding it.
    /// - ensures: the constructor of that name among the generators of the data
    ///   family or the `Theory` code `family` resolves to, or among the terms
    ///   of the theory it resolves to, `S.op` naming the operation `op`, when
    ///   its family's admission position is strictly earlier than the site's
    ///   declaration's; otherwise the unnamed absence.
    /// - fails: as [`Self::resolve_name`] at the family's name.
    /// - panics: none.
    ///
    /// # Errors
    /// The family name's resolution refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a qualified pattern of a family the source shadows a
    ///   constructor of, a qualified constructor value, and a theory's
    ///   operation applied and matched as a term, each lower to the family's
    ///   constructor.
    /// - witness: `lower::native::tests::a_qualified_constructor_names_its_family_s_constructor_2428`
    /// - witness: `tests::modules::models::a_theory_s_terms_are_its_operations_over_its_rules_4143`
    #[spec(ensures: |ret| !matches!(ret, Ok(Maybe::Present(found)) if !matches!(self.collected.owner_of(site.at.node), Maybe::Present(own) if found.family < own)))]
    pub(super) fn qualified_constructor(
        &mut self,
        site: Site,
        family: Placed,
        name: SurfaceName<'source>,
    ) -> Result<Maybe<Constructor, constructed::Absent>, LoweringRefusal<'source>>
    {
        let unnamed = Maybe::Absent(constructed::Absent::Unnamed);
        let Maybe::Present(own) = self.collected.owner_of(site.at.node)
        else {
            return Ok(unnamed);
        };
        // A tile has no owner of its own: the family is resolved from the
        // site's node, at the family name's bytes.
        let named = Site {
            at: Placed {
                node: site.at.node,
                span: family.span,
            },
            ..site
        };
        let family_name = SurfaceName::from(self.text_at(family));
        let Maybe::Present(Resolved::Declaration { constant, .. }) =
            self.resolve_name(named, Frame::Outermost, family_name)?
        else {
            return Ok(unnamed);
        };
        let slot_of = |slot: SlotIndex| {
            self.collected
                .slots
                .get(usize::from(slot))
                .is_some_and(|entry| entry.constant == constant)
        };
        let found = if let Some((position, form)) = self
            .collected
            .data
            .iter()
            .enumerate()
            .find(|&(_, form)| slot_of(form.slot))
        {
            form.generators
                .iter()
                .enumerate()
                .find(|&(_, generator)| SurfaceName::from(self.text_at(generator.named)) == name)
                .map(|(tag, generator)| Constructor {
                    family: form.slot,
                    form: Generators::Written(position),
                    tag,
                    arity: generator.fields.len(),
                    named: generator.named,
                })
        }
        else if let Maybe::Present(ref theory) = self.collected.theory
            && slot_of(theory.slot)
        {
            theory
                .arities
                .iter()
                .zip(THEORY_CONSTRUCTORS)
                .enumerate()
                .find(|&(_, (_, constructor))| SurfaceName::from(constructor) == name)
                .map(|(tag, (&arity, _))| Constructor {
                    family: theory.slot,
                    form: Generators::Presentation,
                    tag,
                    arity,
                    named: theory.named,
                })
        }
        else if let Some((position, terms)) = self
            .collected
            .terms
            .iter()
            .enumerate()
            .find(|&(_, terms)| slot_of(terms.theory))
        {
            terms
                .operations
                .iter()
                .zip(&terms.arities)
                .enumerate()
                .find(|&(_, (&named, _))| SurfaceName::from(self.text_at(named)) == name)
                .map(|(tag, (&named, &arity))| Constructor {
                    family: terms.slot,
                    form: Generators::Terms(position),
                    tag,
                    arity,
                    named,
                })
        }
        else {
            None
        };
        Ok(match found {
            Some(found) if found.family < own => Maybe::Present(found),
            Some(_) | None => unnamed,
        })
    }

    /// The constructor the selection `head`, written at `site`, names as
    /// `Family.Constructor`.
    ///
    /// # Specification
    /// - requires: `head` is the form at `site` or one of its operands.
    /// - ensures: as [`Self::qualified_constructor`] for a selection whose
    ///   target is a bare capitalised name, the unnamed absence where that
    ///   name's resolution refuses; the unnamed absence for any other form, so
    ///   a module's member, a record's field and a family's field keep their
    ///   own readings.
    /// - fails: [`LoweringRefusal::UnknownMold`] for a mold the grammar does
    ///   not hold.
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoweringRefusal::UnknownMold`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::qualified_constructor`]; a module's member
    ///   selected off a capitalised name still reads as the member.
    /// - witness: `lower::native::tests::a_qualified_constructor_names_its_family_s_constructor_2428`
    #[spec(ensures: |ret| ret.is_ok() || matches!(ret, Err(LoweringRefusal::UnknownMold { .. })))]
    pub(super) fn selected_constructor(
        &mut self,
        site: Site,
        head: Placed,
    ) -> Result<Maybe<Constructor, constructed::Absent>, LoweringRefusal<'source>>
    {
        let unnamed = Maybe::Absent(constructed::Absent::Unnamed);
        let Some((family, member)) = self.linked_selection(site, head)?
        else {
            return Ok(unnamed);
        };
        let Some(node) = self.tree.node(family.node)
        else {
            return Ok(unnamed);
        };
        let Shape::Form {
            former: Former::Constructor,
            ..
        } = shape_of(self.pbg, node)?
        else {
            return Ok(unnamed);
        };
        let name = SurfaceName::from(self.text_at(member));
        // A family name that does not resolve is the projection's to refuse.
        Ok(self
            .qualified_constructor(site, family, name)
            .unwrap_or(unnamed))
    }

    /// The constructor `head`, the head of a call written at `site`, names.
    ///
    /// # Specification
    /// - requires: `head` is the first operand of the call at `site`.
    /// - ensures: as [`Self::constructor_named`] for a capitalised name; as
    ///   [`Self::selected_constructor`] for a selection; the unnamed absence
    ///   for any other form.
    /// - fails: [`LoweringRefusal::UnknownMold`] for a mold the grammar does
    ///   not hold.
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoweringRefusal::UnknownMold`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a constructor head and a function head take their own
    ///   readings.
    /// - witness: `lower::native::tests::a_constructor_applies_to_its_fields`
    /// - witness: `lower::native::tests::a_qualified_constructor_names_its_family_s_constructor_2428`
    #[spec(ensures: |ret| ret.is_ok() || matches!(ret, Err(LoweringRefusal::UnknownMold { .. })))]
    pub(super) fn constructor_head(
        &mut self,
        site: Site,
        head: Placed,
    ) -> Result<Maybe<Constructor, constructed::Absent>, LoweringRefusal<'source>>
    {
        let Some(node) = self.tree.node(head.node)
        else {
            return Ok(Maybe::Absent(constructed::Absent::Unnamed));
        };
        match shape_of(self.pbg, node)? {
            Shape::Form {
                former: Former::Constructor,
                ..
            } => Ok(self.constructor_named(site, SurfaceName::from(self.text_at(head)))),
            Shape::Form {
                former: Former::Projection,
                ..
            } => self.selected_constructor(site, head),
            Shape::Root | Shape::Form { .. } | Shape::Repair(_) | Shape::Layout => {
                Ok(Maybe::Absent(constructed::Absent::Unnamed))
            },
        }
    }

    /// Classify `constructor` applied to the fields `fields` holds in the
    /// operand store, written at `site`.
    ///
    /// # Specification
    /// - requires: `fields` is a stretch of the operand store, each entry a
    ///   field the site was written with, left to right.
    /// - ensures: the constructor stands as a value, each field read as a value
    ///   under the site's frame. Its classifier is the annotation the site
    ///   stands under, or the signature of the definition it is; else, for a
    ///   family with parameters, the value type the answer of its position
    ///   returns — a tail's, or a `pure`'s or `return`'s operand's — else its
    ///   place in the data family application it is an argument of, the
    ///   constructor then awaiting that application's mint; else, written as an
    ///   argument of a call naming a declaration, the type the declaration
    ///   writes for the parameter at its place, under the parameters before it
    ///   replaced by the arguments written for them, the constructor then
    ///   awaiting the call's mint; else the one the constructor around it gives
    ///   the field it stands in, or the family's index type at its place where
    ///   it is an index a generator's result states; else, for a family
    ///   without, the one the lowering inserts. A field typed by the family
    ///   over its own parameters takes the constructor's classifier, and one
    ///   typed by a parameter the argument a written classifier gives it.
    /// - provides: constructor application, bare and called.
    /// - fails: yields the arity refusal for a field count other than the
    ///   constructor's; the wrong-sort refusal outside value position; the
    ///   unannotated refusal for a constructor of a family with parameters
    ///   whose position states no type, that stands at no data family's
    ///   argument place and at no index a generator's result states, and that
    ///   is passed at no parameter whose stated type names no entry of an
    ///   implicit telescope, and for one whose answer decodes a binder or a
    ///   constant no top-level definition writes a body for.
    /// - panics: none.
    ///
    /// # Errors
    /// The constructor's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — nullary, unary and three-field constructors, a wrong
    ///   field count and a parameterised family without its annotation, each
    ///   asserted as the exact plan's core node or refusal; a parameterised
    ///   family at a signed thunk's tail, under a `run` and as a definition,
    ///   its recursive field and its parameter field classified with it; and
    ///   one written as a data family's argument, classified by its place; one
    ///   passed to a parameter stating a closed type, classified by it; one
    ///   answering a definition's application, written as `= e` or as a
    ///   function tail, and one a declared constant's.
    /// - witness: `lower::native::tests::a_constructor_applies_to_its_fields`
    /// - witness: `lower::native::tests::a_parameterized_constructor_needs_its_classifier`
    /// - witness: `lower::native::tests::a_constructor_takes_its_classifier_from_the_type_it_answers_402`
    /// - witness: `lower::native::tests::a_constructor_takes_its_slot_as_a_family_argument_421`
    /// - witness: `lower::native::tests::a_constructor_argument_takes_its_parameter_s_type_1833`
    /// - witness: `lower::native::tests::a_constructor_answers_a_definition_s_application_2112`
    /// - witness: `lower::native::tests::a_constructor_answers_a_function_tail_s_application_3665`
    /// - witness: `lower::native::tests::a_constructor_at_a_family_s_index_takes_the_index_s_type_4027`
    #[spec(ensures: |ret| ret.is_err() || matches!(self.plans.get(site.at.node), Some(&Plan::Constructor(planned)) if planned.fields == fields))]
    pub(super) fn construct(
        &mut self,
        site: Site,
        constructor: Constructor,
        fields: Stretch,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let count = fields.end.saturating_sub(fields.start);
        if count != constructor.arity {
            return Err(site.out(FragmentBoundary::Arity(OperandCount::from(count))));
        }
        let frame = self.require(site, Produced::Value)?;
        // A family of neither parameters nor indices classifies its
        // constructors alone.
        let arguments = match constructor.form {
            Generators::Written(form) => self.collected.data.get(form).map_or(0_usize, |written| {
                written
                    .parameters
                    .len()
                    .saturating_add(written.indices.len())
            }),
            Generators::Presentation | Generators::Words(_) | Generators::Terms(_) => 0_usize,
        };
        // A constructor standing where a body ends is the value the body
        // returns, of the type the body answers.
        let answered = self
            .answers
            .get(&site.at.node)
            .filter(|_| self.exits.contains(&site.at.node));
        let classifier = match (
            self.classifiers.get(&site.at.node),
            answered,
            self.argued.get(&site.at.node),
            self.parameter_typed.get(&site.at.node),
            self.inherited.get(&site.at.node),
        ) {
            (Some(&written), ..) => Classifier::Written(written),
            (None, ..) if arguments == 0 => Classifier::Inserted,
            (None, Some(&answer), ..) => Classifier::Answered { answer, frame },
            (None, None, Some(&argued), ..) => {
                let _first = self.awaiting.insert(site.at.node);
                Classifier::Slot(argued)
            },
            (None, None, None, Some(&declared), _) => {
                // The parameter's type reads the arguments before it, which
                // the mint sweep reaches after it, so the call mints it.
                let _first = self.awaiting.insert(site.at.node);
                Classifier::Parameter(declared)
            },
            (None, None, None, None, Some(&inherited)) => {
                // A field's classifier reads the constructor around it, which
                // mints this one once that classifier and the fields before
                // it are; so does a call's parameter, handed down a field the
                // family types over its own parameters, which reads the
                // call's arguments.
                if let Classifier::Field(_) | Classifier::Parameter(_) = inherited {
                    let _first = self.awaiting.insert(site.at.node);
                }
                inherited
            },
            (None, None, None, None, None) => return Err(site.out(FragmentBoundary::Unannotated)),
        };
        // A result decoding a parameter or a constant with no body, written
        // as `= e` or as a function tail, states no type the constructor can
        // carry.
        if let Classifier::Answered { answer, .. } = classifier
            && answer.over == Over::Written
            && let Some(&(Plan::Decode(code, ..) | Plan::Unquote(code, ..))) =
                self.plans.get(answer.node)
            && let Maybe::Absent(_) = self.decoded_definition(code)
        {
            return Err(site.out(FragmentBoundary::Unannotated));
        }
        let family = self
            .collected
            .slots
            .get(usize::from(constructor.family))
            .map_or_else(|| ConstantIndex::from(0_usize), |slot| slot.constant);
        for (index, position) in (fields.start .. fields.end).enumerate() {
            if let Some(&field) = self.operands.get(position) {
                self.read(field, Reading::Value(frame));
                // Only a constructor written in the field, bare or applied,
                // reads the classifier the field gives.
                let constructed = self.tree.node(field).is_some_and(|node| {
                    matches!(
                        shape_of(self.pbg, node),
                        Ok(Shape::Form {
                            former: Former::Constructor | Former::Call,
                            ..
                        })
                    )
                });
                if constructed
                    && let Generators::Written(form) = constructor.form
                    && let Maybe::Present(inherited) = self.field_classifier(
                        FieldAt {
                            form,
                            tag: constructor.tag,
                            index,
                        },
                        classifier,
                        site.at.node,
                    )?
                {
                    let _first = self.inherited.insert(field, inherited);
                }
            }
        }
        self.plan(
            site,
            Plan::Constructor(Constructed {
                family,
                tag: ConstructorTag::from(constructor.tag),
                fields,
                classifier,
            }),
        );

        Ok(())
    }

    /// Record, for each argument of the call at `site`, the type the
    /// declaration its head names writes for the parameter at its place.
    ///
    /// # Specification
    /// - requires: `site` is a call read under `frame`, `head` its head and
    ///   `applied` its arguments in the operand store, every one the call
    ///   writes, the leading ones a descent leaves out of its application among
    ///   them.
    /// - ensures: when `head` is a bare name of a declaration written with a
    ///   parameter list and holding no refusal, or a descent `f[<]` into the
    ///   declaration whose own recursion `f` names, each argument at a
    ///   parameter written with a type maps to that type, the declaration and
    ///   the call's arguments in [`Lowerer::parameter_typed`], read by a
    ///   constructor written there as [`Classifier::Parameter`]; an argument
    ///   written as a thunk or a bare lambda is answered by that type as a
    ///   signed definition's is ([`Self::signed_answer`]), in
    ///   [`Lowerer::dependent_answers`] apart when the type names a parameter
    ///   before it (#3921); nothing changes for any other head, a binder's
    ///   name, a local recursion's descent or a refused declaration's among
    ///   them: a refused declaration's parameter types never lower.
    /// - fails: as [`Self::unwrapped`]; a name the head's own reading refuses
    ///   is refused there.
    /// - panics: none.
    ///
    /// # Errors
    /// The walk's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a list and a bare constructor passed to a function of
    ///   a closed parameter type, one passed where the type names the parameter
    ///   before it, and a local function's name, which classifies nothing; a
    ///   lambda passed in a thunk and bare for a parameter typed `Empty =>
    ///   Integer` matches no arm on its binder; a bare constructor passed to a
    ///   refused declaration is refused unannotated; a constructor passed to a
    ///   descent into a declaration's own recursion.
    /// - witness: `lower::native::tests::a_constructor_argument_takes_its_parameter_s_type_1833`
    /// - witness: `lower::native::tests::a_constructor_argument_reads_the_arguments_before_it_1876`
    /// - witness: `lower::native::tests::an_argument_lambda_s_binder_is_typed_by_its_parameter_1948`
    /// - witness: `lower::native::tests::a_refused_callee_classifies_no_argument_2126`
    /// - witness: `lower::native::tests::a_descent_call_s_constructor_argument_takes_its_parameter_s_type_2127`
    /// - witness: `lower::identity::tests::a_call_s_lambda_argument_reads_its_parameter_s_domain_3921`
    #[spec(
        captures: before = (self.parameter_typed.len(), self.thunked.len()),
        ensures: |ret| ret.is_err() || (self.parameter_typed.len() >= before.0 && self.thunked.len() >= before.1),
    )]
    pub(super) fn parameters_classify(
        &mut self,
        site: Site,
        frame: Frame,
        head: Placed,
        applied: Stretch,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let Some(slot) = self.called_slot(site, frame, head)?
        else {
            return Ok(());
        };
        let refused = self
            .collected
            .slots
            .get(usize::from(slot))
            .is_some_and(|declaration| declaration.refused().0);
        if refused {
            return Ok(());
        }
        let Some(parameters) = self.collected.parameters.get(&slot)
        else {
            return Ok(());
        };
        // The collection lists the explicit parameters alone: an operand the
        // lowering passes for an omitted entry pairs with none.
        let typed: Vec<(NodeIndex, Placed, bool)> = (applied.start .. applied.end)
            .filter(|position| {
                !self.instanced.contains_key(position)
                    && !self.nominated.contains_key(position)
                    && !self.components.contains_key(position)
                    && !self.kept_implicits.contains(position)
            })
            .zip(parameters)
            .filter_map(|(position, parameter)| match parameter.declared {
                Maybe::Present(declared) => {
                    Some((*self.operands.get(position)?, declared, parameter.dependent))
                },
                Maybe::Absent(_) => None,
            })
            .collect();
        for (argument, declared, dependent) in typed {
            let _first = self.parameter_typed.insert(argument, CalledAt {
                typed: declared,
                slot,
                applied,
            });
            let opened = self.tree.node(argument).is_some_and(|node| {
                matches!(
                    shape_of(self.pbg, node),
                    Ok(Shape::Form {
                        former: Former::Thunk | Former::Lambda,
                        ..
                    })
                )
            });
            if !opened {
                continue;
            }
            let Maybe::Present(written) = self.unwrapped(declared.node)?
            else {
                continue;
            };
            if let Some(answer) = self.signed_answer(&written)? {
                // A type naming the callee's parameters answers nothing where
                // the call stands; the lambda's binder alone reads it (#3921).
                let answers = if dependent {
                    &mut self.dependent_answers
                }
                else {
                    &mut self.thunked
                };
                let _first = answers.insert(argument, answer);
            }
        }
        Ok(())
    }

    /// The declaration the call at `site`, read under `frame`, calls through
    /// its head `head`: one its bare name resolves to, or the one whose own
    /// recursion a descent `f[<]` names.
    ///
    /// # Specification
    /// - requires: `site` is a call read under `frame` and `head` its head.
    /// - ensures: the slot of the declaration a bare-name head resolves to; for
    ///   an instantiation naming a recursion, the slot of the declaration
    ///   owning the call when that recursion's own name is the declaration's
    ///   name tile; none otherwise, a local recursion's descent and a binder's
    ///   name among them.
    /// - fails: as [`Self::instantiated_recursion`].
    /// - panics: none.
    ///
    /// # Errors
    /// The form's or the binder walk's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::parameters_classify`].
    /// - witness: `lower::native::tests::a_constructor_argument_takes_its_parameter_s_type_1833`
    /// - witness: `lower::native::tests::a_descent_call_s_constructor_argument_takes_its_parameter_s_type_2127`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |slot| slot.is_none_or(|slot| self.collected.slots.get(usize::from(slot)).is_some())))]
    fn called_slot(
        &mut self,
        site: Site,
        frame: Frame,
        head: Placed,
    ) -> Result<Option<SlotIndex>, LoweringRefusal<'source>>
    {
        let Some(node) = self.tree.node(head.node)
        else {
            return Ok(None);
        };
        match shape_of(self.pbg, node) {
            Ok(Shape::Form {
                former: Former::Name,
                ..
            }) => {
                let name = self.name_at(head);
                let Ok(Maybe::Present(Resolved::Declaration { constant, .. })) =
                    self.resolve_name(site, frame, name)
                else {
                    return Ok(None);
                };
                let slot = SlotIndex::from(usize::from(constant));
                Ok(self
                    .collected
                    .slots
                    .get(usize::from(slot))
                    .is_some()
                    .then_some(slot))
            },
            Ok(Shape::Form {
                former: Former::Instantiation,
                ..
            }) => {
                let Some(binder) = self.instantiated_recursion(frame, head)?
                else {
                    return Ok(None);
                };
                let Maybe::Present(own) = self.collected.owner_of(site.at.node)
                else {
                    return Ok(None);
                };
                let declared = self.collected.slots.get(usize::from(own));
                let recursion = self.recursions.get(&binder);
                Ok(declared
                    .zip(recursion)
                    .is_some_and(|(declared, recursion)| declared.named.node == recursion.named)
                    .then_some(own))
            },
            Ok(Shape::Form { .. } | Shape::Root | Shape::Repair(_) | Shape::Layout) | Err(_) => {
                Ok(None)
            },
        }
    }

    /// The result type the declaration a call names writes after its
    /// parameter list.
    ///
    /// # Specification
    /// - requires: `site` is the form `call` stands in, read under `frame`.
    /// - ensures: the operand written after `->` in the declaration form of the
    ///   slot the call's head names, as [`Self::called_slot`] reads it, when
    ///   `call` is a call, the declaration is a function written with a
    ///   parameter list in the source being lowered, refuses nothing and writes
    ///   a result; nothing otherwise, a declaration of another source among
    ///   them, since that source's own scope resolves its result's names.
    /// - provides: the type an observation off a call reads its entries from.
    /// - fails: as [`Self::called_slot`]; the refusals the tree's molds yield.
    /// - panics: none.
    ///
    /// # Errors
    /// The walk's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a call's stream observed by label, by position and in
    ///   an operand.
    /// - witness: `lower::arity::tests::an_observation_off_a_call_projects_the_run_result_1106`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |result| result.is_none_or(|result| result.node != call.node)))]
    pub(super) fn called_result(
        &mut self,
        site: Site,
        frame: Frame,
        call: Placed,
    ) -> Result<Option<Placed>, LoweringRefusal<'source>>
    {
        if !matches!(self.form_at(call)?, Some((_, Former::Call))) {
            return Ok(None);
        }
        let mut scratch = core::mem::take(&mut self.scratch);
        let read = read_pieces(self.pbg, self.tree, call.node, &mut scratch);
        let head = scratch.pieces.first().and_then(|piece| match *piece {
            Piece::Operand(head) => Some(head),
            Piece::Tile { .. } => None,
        });
        self.scratch = scratch;
        read?;
        let Some(head) = head
        else {
            return Ok(None);
        };
        let Some(slot) = self.called_slot(site, frame, head)?
        else {
            return Ok(None);
        };
        let Some(declared) = self.collected.slots.get(usize::from(slot))
        else {
            return Ok(None);
        };
        let Maybe::Present(Half {
            declaration: form,
            operand: Operand::Function,
            ..
        }) = declared.definition
        else {
            return Ok(None);
        };
        if declared.refused().0
            || self.source_of.get(usize::from(form.node)) != Some(&self.current.source)
        {
            return Ok(None);
        }
        let mut scratch = core::mem::take(&mut self.scratch);
        let read = read_pieces(self.pbg, self.tree, form.node, &mut scratch);
        // The parameter list closes at the form's first `)`: a parameter's
        // own parentheses stand inside its operand.
        let mut after = scratch
            .pieces
            .iter()
            .skip_while(|piece| {
                !matches!(**piece, Piece::Tile { label, .. } if label == TileName::PAREN_CLOSE)
            })
            .skip(1_usize);
        let result = match (after.next(), after.next()) {
            (Some(&Piece::Tile { label, .. }), Some(&Piece::Operand(result)))
                if label == TileName::ARROW =>
            {
                Some(result)
            },
            _ => None,
        };
        self.scratch = scratch;
        read?;

        Ok(result)
    }

    /// The classifier the field `at` of the constructor written at `around`
    /// gives a constructor written in it, from the constructor's own,
    /// `classifier`.
    ///
    /// # Specification
    /// - requires: `at.form` and `at.tag` name a generator the collection read.
    /// - ensures: while no field before it binds a parameter's name,
    ///   `classifier` itself when the field's written type, its parentheses
    ///   stripped, is the family applied to its own parameters in order, or the
    ///   family bare when it has none, and the argument a written classifier,
    ///   an application of the family, gives the parameter when the field's
    ///   type is that parameter; otherwise the field's declared type with the
    ///   family's parameters and the fields before it replaced, a
    ///   [`Classifier::Field`]; the unclassified absence when `at` names no
    ///   field.
    /// - provides: the classifier a constructor written in a field takes.
    /// - fails: [`LoweringRefusal::BudgetExceeded`] when the walk outruns the
    ///   allowance; the refusals the tree's molds yield.
    /// - panics: none.
    ///
    /// # Errors
    /// The walk's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a list's tail and head, written and answered; a field
    ///   typed by another family over a closed type, and over the family's
    ///   parameter.
    /// - witness: `lower::native::tests::a_constructor_takes_its_classifier_from_the_type_it_answers_402`
    /// - witness: `lower::native::tests::a_field_classifies_the_constructor_written_in_it_1171`
    #[spec(ensures: |ret| match ret {
        | Ok(Maybe::Present(found)) => found == classifier
            || matches!(found, Classifier::Written(_))
            || matches!(found, Classifier::Field(of) if of.around == around),
        | Ok(Maybe::Absent(_)) | Err(_) => true,
    })]
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            linear_search_in_loop,
            reason = "bounded: `named` holds one data declaration's parameter names"
        )
    )]
    fn field_classifier(
        &mut self,
        at: FieldAt,
        classifier: Classifier,
        around: NodeIndex,
    ) -> Result<Maybe<Classifier, inherited::Absent>, LoweringRefusal<'source>>
    {
        let unclassified = Maybe::Absent(inherited::Absent::Unclassified);
        let Some(data) = self.collected.data.get(at.form)
        else {
            return Ok(unclassified);
        };
        let Some(generator) = data.generators.get(at.tag)
        else {
            return Ok(unclassified);
        };
        let Some(field) = generator.fields.get(at.index)
        else {
            return Ok(unclassified);
        };
        let declared = field.ty.node;
        let substituted = Maybe::Present(Classifier::Field(FieldOf {
            around,
            declared,
            parameters: data.parameters.len(),
            index: at.index,
        }));
        let named: Vec<SurfaceName<'source>> = data
            .parameters
            .iter()
            .map(|parameter| self.name_at(parameter.named))
            .collect();
        // A field before it binding a parameter's name shadows the parameter,
        // so the spelling no longer says which the type names.
        let shadowed = generator.fields.iter().take(at.index).any(|earlier| {
            matches!(earlier.named, Maybe::Present(binder) if named.contains(&self.name_at(binder)))
        });
        if shadowed {
            return Ok(substituted);
        }
        let family = self
            .collected
            .slots
            .get(usize::from(data.slot))
            .map(|slot| slot.name);
        let Maybe::Present(typed) = self.unwrapped(declared)?
        else {
            return Ok(substituted);
        };
        let spelled = |lowerer: &Self, node: NodeIndex| {
            SurfaceName::from(
                lowerer
                    .tree
                    .fragment(node)
                    .unwrap_or_else(|| SourceFragment::from("")),
            )
        };
        let head = typed.keyword.map(|at| self.name_at(at));
        let own = spelled(self, typed.node);
        let uniform = if typed.former == Former::TypeApplication {
            head.is_some()
                && head == family
                && typed
                    .operands
                    .iter()
                    .map(|&node| spelled(self, node))
                    .eq(named.iter().copied())
        }
        else {
            typed.former == Former::TypeHead && named.is_empty() && Some(own) == family
        };
        if uniform {
            return Ok(Maybe::Present(classifier));
        }
        let (Some(parameter), Classifier::Written(written)) =
            (named.iter().position(|name| *name == own), classifier)
        else {
            return Ok(substituted);
        };
        let Maybe::Present(applied) = self.unwrapped(written)?
        else {
            return Ok(substituted);
        };
        Ok(match applied.operands.get(parameter) {
            Some(&argument) if applied.former == Former::TypeApplication => {
                Maybe::Present(Classifier::Written(argument))
            },
            Some(_) | None => substituted,
        })
    }

    /// Give each definition its signature as the type its constructors are
    /// checked against: a thunk's body the answer the signature states, and
    /// any other definition the signature itself. A definition no signature
    /// types whose whole value is an annotation `(e : T)` is signed by `T`.
    ///
    /// # Specification
    /// - requires: the collection has read every slot.
    /// - ensures: for each slot whose signature and definition are both written
    ///   types and terms: a signature `+U C`, its parentheses stripped, answers
    ///   the definition's thunk body with `C`, the alias `() => B` with `-F B`
    ///   and any other alias `(A1, …, An) => B` with the arrows it stands for,
    ///   each read under the outermost frame; any other signature classifies
    ///   the definition. A slot with no signature whose written definition is
    ///   `(e : T)` records `T` as the annotation's ascription and signs `e` by
    ///   `T` the same way.
    /// - provides: the expected type a constructor takes its classifier from
    ///   where the source states one only in the signature, and the binder
    ///   types and answers of the lambdas a thunk signed with an alias opens.
    /// - fails: as [`Self::unwrapped`].
    /// - panics: none.
    ///
    /// # Errors
    /// The walk's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a thunk signed `+U (-F T)` and `() => T`, and a
    ///   definition signed `T`, each over a parameterised family's constructor;
    ///   a lambda signed `A => B` and `(A, C) => B` lowering as under the
    ///   thunked arrow.
    /// - witness: `lower::native::tests::a_constructor_takes_its_classifier_from_the_type_it_answers_402`
    /// - witness: `lower::native::tests::a_lambda_under_a_value_function_alias_lowers_as_under_its_thunked_arrow_808`
    /// - witness: `lower::native::tests::an_annotated_definition_value_is_signed_by_its_annotation_1107`
    #[spec(
        captures: before = (self.inherited.len(), self.thunked.len()),
        ensures: |ret| ret.is_err() || (self.inherited.len() >= before.0 && self.thunked.len() >= before.1),
    )]
    pub(super) fn sign_definitions(&mut self) -> Result<(), LoweringRefusal<'source>>
    {
        let mut signed: Vec<(NodeIndex, NodeIndex)> = Vec::new();
        let mut unsigned: Vec<NodeIndex> = Vec::new();
        for slot in self.collected.slots.iter().skip(self.current.slots) {
            let Maybe::Present(Half {
                operand: Operand::Written(definition),
                ..
            }) = slot.definition
            else {
                continue;
            };
            if let Maybe::Present(Half {
                operand: Operand::Written(signature),
                ..
            }) = slot.signature
            {
                signed.push((definition.node, signature.node));
            }
            else if let Maybe::Absent(_) = slot.signature {
                unsigned.push(definition.node);
            }
        }
        for definition in unsigned {
            if let Some((value, classifier)) = self.annotation(definition)? {
                let _first = self.annotated_definitions.insert(definition, classifier);
                signed.push((value, classifier));
            }
        }
        for (definition, signature) in signed {
            let Maybe::Present(written) = self.unwrapped(signature)?
            else {
                continue;
            };
            if let Some(answer) = self.signed_answer(&written)? {
                let _first = self.thunked.insert(definition, answer);
            }
            else {
                let _first = self
                    .inherited
                    .insert(definition, Classifier::Written(signature));
            }
        }
        Ok(())
    }

    /// What the written type `written`, its parentheses stripped, answers a
    /// thunk's body or a bare lambda it types: `C` for `+U C`, `-F B` for
    /// `() => B` and the arrows any other value function space `(A1, …, An)
    /// => B` stands for, each read under the outermost frame.
    ///
    /// # Specification
    /// - ensures: the answer for a thunk type of one operand and for a value
    ///   function space; nothing for any other type.
    /// - fails: as [`Self::unwrapped`].
    /// - panics: none.
    ///
    /// # Errors
    /// The walk's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::sign_definitions`] and
    ///   [`Self::parameters_classify`].
    /// - witness: `lower::native::tests::a_lambda_under_a_value_function_alias_lowers_as_under_its_thunked_arrow_808`
    /// - witness: `lower::native::tests::an_argument_lambda_s_binder_is_typed_by_its_parameter_1948`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |answer| answer.is_none_or(|answer| answer.frame == Frame::Outermost)))]
    fn signed_answer(
        &mut self,
        written: &Unwrapped,
    ) -> Result<Option<Answer>, LoweringRefusal<'source>>
    {
        let thunked = matches!(written.former, Former::ThunkType | Former::ReturnerType)
            && written.keyword.is_some_and(|at| {
                type_former(self.name_at(at)) == Maybe::Present(TypeFormer::Thunk)
            });
        Ok(match *written.operands.as_slice() {
            [body] if thunked => Some(Answer {
                node: body,
                frame: Frame::Outermost,
                over: Over::Written,
                arm: Maybe::Absent(passed::Absent::Unpassed),
            }),
            [domain, codomain] if written.former == Former::ValueFunctionType => {
                match self.unwrapped(domain)? {
                    Maybe::Present(Unwrapped {
                        former: Former::ParenthesizedType,
                        ref operands,
                        ..
                    }) if operands.is_empty() => Some(Answer {
                        node: codomain,
                        frame: Frame::Outermost,
                        over: Over::Returning,
                        arm: Maybe::Absent(passed::Absent::Unpassed),
                    }),
                    Maybe::Present(_) | Maybe::Absent(_) => Some(Answer {
                        node: written.node,
                        frame: Frame::Outermost,
                        over: Over::Valued { taken: 0_usize },
                        arm: Maybe::Absent(passed::Absent::Unpassed),
                    }),
                }
            },
            _ => None,
        })
    }

    /// The value and the type of the annotation `(e : T)` that `node` writes.
    ///
    /// # Specification
    /// - requires: nothing; a node the tree does not hold writes no annotation.
    /// - ensures: `e` and `T` where `node` is a parenthesised expression of one
    ///   operand, a `:` and one more operand; none for any other node.
    /// - provides: the annotations a definition's whole value and a return's
    ///   whole operand are read by before they are classified.
    /// - fails: the refusals the tree's molds yield.
    /// - panics: none.
    ///
    /// # Errors
    /// The read's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an annotated definition value and an annotated
    ///   returned value each found, and a grouping beside them not.
    /// - witness: `lower::native::tests::an_annotated_definition_value_is_signed_by_its_annotation_1107`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |parts| parts.is_none_or(|(value, classifier)| value != node && classifier != node && value != classifier)))]
    pub(super) fn annotation(
        &mut self,
        node: NodeIndex,
    ) -> Result<Option<(NodeIndex, NodeIndex)>, LoweringRefusal<'source>>
    {
        let Some(tree_node) = self.tree.node(node)
        else {
            return Ok(None);
        };
        let Shape::Form {
            former: Former::Parenthesized,
            ..
        } = shape_of(self.pbg, tree_node)?
        else {
            return Ok(None);
        };
        let mut scratch = core::mem::take(&mut self.scratch);
        let read = read_pieces(self.pbg, self.tree, node, &mut scratch);
        let parts = match *scratch.pieces.as_slice() {
            [
                Piece::Tile { label: open, .. },
                Piece::Operand(value),
                Piece::Tile { label: colon, .. },
                Piece::Operand(classifier),
                Piece::Tile { label: close, .. },
            ] if open == TileName::PAREN_OPEN
                && colon == TileName::COLON
                && close == TileName::PAREN_CLOSE =>
            {
                Some((value.node, classifier.node))
            },
            _ => None,
        };
        self.scratch = scratch;
        read?;

        Ok(parts)
    }

    /// The form `node` writes once its parentheses are stripped: its former,
    /// the first tile it is written with and its operands.
    ///
    /// # Specification
    /// - requires: nothing; a node the tree does not hold has no form.
    /// - ensures: a parenthesised type around one operand read through to the
    ///   operand; the form's former, first tile and operands, left to right;
    ///   the unformed absence for a node that is no form.
    /// - provides: the syntactic reading a signature and a field type are read
    ///   by.
    /// - fails: [`LoweringRefusal::BudgetExceeded`] when the walk outruns the
    ///   allowance; the refusals the tree's molds yield.
    /// - panics: none.
    ///
    /// # Errors
    /// The walk's refusal.
    ///
    /// # Termination
    /// Every turn spends one unit of the lowerer's allowance and steps to the
    /// operand of the node it read, strictly deeper in a finite tree.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a parenthesised application and a bare head.
    /// - witness: `lower::native::tests::a_constructor_takes_its_classifier_from_the_type_it_answers_402`
    #[spec(captures: before = self.fuel.remaining, ensures: self.fuel.remaining <= before)]
    pub(super) fn unwrapped(
        &mut self,
        mut node: NodeIndex,
    ) -> Result<Maybe<Unwrapped, inherited::Absent>, LoweringRefusal<'source>>
    {
        loop {
            self.fuel.spend()?;
            let Some(tree_node) = self.tree.node(node)
            else {
                return Ok(Maybe::Absent(inherited::Absent::Unclassified));
            };
            let Shape::Form { former, .. } = shape_of(self.pbg, tree_node)?
            else {
                return Ok(Maybe::Absent(inherited::Absent::Unclassified));
            };
            let mut scratch = core::mem::take(&mut self.scratch);
            let read = read_pieces(self.pbg, self.tree, node, &mut scratch);
            let operands: Vec<NodeIndex> = scratch
                .pieces
                .iter()
                .filter_map(|piece| match *piece {
                    Piece::Operand(operand) => Some(operand.node),
                    Piece::Tile { .. } => None,
                })
                .collect();
            let keyword = scratch.pieces.iter().find_map(|piece| match *piece {
                Piece::Tile { at, .. } => Some(at),
                Piece::Operand(_) => None,
            });
            self.scratch = scratch;
            read?;
            if former == Former::ParenthesizedType
                && let [inner] = *operands.as_slice()
            {
                node = inner;
                continue;
            }
            return Ok(Maybe::Present(Unwrapped {
                node,
                former,
                keyword,
                operands,
            }));
        }
    }

    /// Classify the word `letter ∷ rest`, written at `site`.
    ///
    /// # Specification
    /// - requires: `letter` and `rest` are the cons's operands, in order.
    /// - ensures: the constructor of the words `letter` names, as
    ///   [`Self::written_letter`] reads it, applied to `rest`, as
    ///   [`Self::construct`] plans it; the letter, and the name inside an
    ///   inverse letter, recorded with its words so each answers at the path
    ///   type at their point.
    /// - fails: [`LoweringRefusal::UnresolvedName`] at a letter, or the name
    ///   inside an inverse letter, that nothing answers; the unadmitted refusal
    ///   at the cons for a left operand that is no loop and no loop's inverse;
    ///   [`Self::construct`]'s refusals.
    /// - panics: none.
    ///
    /// # Errors
    /// The cons's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a letter and an inverse cons onto a word, each letter
    ///   and the name inside the inverse labelled at the path type, a letter
    ///   naming nothing is unresolved, and a left operand that is no loop is
    ///   refused.
    /// - witness: `lower::native::tests::a_word_conses_its_letters_and_matches_them`
    /// - witness: `lower::native::tests::a_letter_naming_nothing_is_unresolved_1997`
    #[spec(ensures: |ret| ret.is_err() || matches!(self.plans.get(site.at.node), Some(&Plan::Constructor(_))))]
    pub(super) fn cons(
        &mut self,
        site: Site,
        letter: Placed,
        rest: Placed,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let Maybe::Present(constructor) = self.written_letter(site, letter)?
        else {
            return Err(site.out(FragmentBoundary::Unadmitted(Unbuilt::InfixForm)));
        };
        if let Generators::Words(words) = constructor.form {
            self.lettered.push((letter.span, words));
            if constructor.named.span != letter.span {
                self.lettered.push((constructor.named.span, words));
            }
        }
        let start = self.operands.len();
        self.operands.push(rest.node);
        let fields = Stretch {
            start,
            end: self.operands.len(),
        };
        self.construct(site, constructor, fields)
    }

    /// The letter a cons's left operand `at`, written under `site`, spells: a
    /// loop's name its letter, and `back(g)`, `g` a loop's name, its inverse.
    ///
    /// # Specification
    /// - requires: `at` is a cons's left operand.
    /// - ensures: as [`Self::loop_letter`], for the name `at` is or the one
    ///   `back` applies to; `back` is read by its spelling, whatever a
    ///   declaration of that name binds, since only a letter conses. The
    ///   unnamed absence for any other form.
    /// - fails: [`Self::loop_letter`]'s refusals;
    ///   [`LoweringRefusal::UnknownMold`].
    /// - panics: none.
    ///
    /// # Errors
    /// As stated.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::cons`].
    /// - witness: `lower::native::tests::a_word_conses_its_letters_and_matches_them`
    /// - witness: `lower::native::tests::only_back_inverts_a_letter`
    #[spec(ensures: |ret| match ret {
        Ok(Maybe::Present(constructor)) => constructor.arity == 1 && matches!(constructor.form, Generators::Words(_)),
        _ => true,
    })]
    fn written_letter(
        &mut self,
        site: Site,
        at: Placed,
    ) -> Result<Maybe<Constructor, constructed::Absent>, LoweringRefusal<'source>>
    {
        let unnamed = Ok(Maybe::Absent(constructed::Absent::Unnamed));
        let Some(node) = self.tree.node(at.node)
        else {
            return unnamed;
        };
        let (cell, inverse) = match shape_of(self.pbg, node)? {
            Shape::Form {
                former: Former::Name,
                ..
            } => (at, false),
            Shape::Form {
                former: Former::Call,
                ..
            } => {
                let mut pieces = core::mem::take(&mut self.scratch);
                let read = read_pieces(self.pbg, self.tree, at.node, &mut pieces);
                let mut operands = pieces.pieces.iter().filter_map(|piece| match *piece {
                    Piece::Operand(operand) => Some(operand),
                    Piece::Tile { .. } => None,
                });
                let written = (operands.next(), operands.next(), operands.next());
                self.scratch = pieces;
                read?;
                let (Some(head), Some(cell), None) = written
                else {
                    return unnamed;
                };
                if self.text_at(head).as_ref() != super::identity::BACK
                    || !matches!(self.form_at(cell)?, Some((_, Former::Name)))
                {
                    return unnamed;
                }
                (cell, true)
            },
            Shape::Form { .. } | Shape::Root | Shape::Repair(_) | Shape::Layout => {
                return unnamed;
            },
        };
        self.loop_letter(site, cell, Inverse(inverse))
    }

    /// The letter of the loop `cell` names, written under `site`, or its
    /// inverse when `inverse` holds.
    ///
    /// # Specification
    /// - requires: `cell` is a name's own node or tile inside the form at
    ///   `site`, which the name is resolved under: a name inside a letter is
    ///   owned by no declaration until the form around it is read.
    /// - ensures: when the name resolves to a loop's binding, the constructor
    ///   of the loop's words whose tag is the loop's letter, or its inverse,
    ///   with one field, the rest of the word; the unnamed absence for a name
    ///   that resolves to anything else.
    /// - fails: [`LoweringRefusal::UnresolvedName`] at the name when nothing
    ///   answers it, since only a declared loop is a letter; the name's
    ///   resolution refusals.
    /// - panics: none.
    ///
    /// # Errors
    /// As stated.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::cons`].
    /// - witness: `lower::native::tests::a_word_conses_its_letters_and_matches_them`
    /// - witness: `lower::native::tests::a_letter_naming_nothing_is_unresolved_1997`
    /// - witness: `tests::modules::a_forward_member_reference_is_refused_by_position`
    #[spec(ensures: |ret| match ret {
        Ok(Maybe::Present(constructor)) => constructor.arity == 1 && constructor.named == cell,
        _ => true,
    })]
    fn loop_letter(
        &mut self,
        site: Site,
        cell: Placed,
        inverse: Inverse,
    ) -> Result<Maybe<Constructor, constructed::Absent>, LoweringRefusal<'source>>
    {
        let named = Site {
            at: Placed {
                node: site.at.node,
                span: cell.span,
            },
            ..site
        };
        let name = self.name_at(cell);
        let resolved = self.resolve_name(named, site.reading.frame(), name)?;
        let Maybe::Present(super::Resolved::Declaration { constant, .. }) = resolved
        else {
            return match resolved {
                Maybe::Absent(_) => Err(LoweringRefusal::UnresolvedName {
                    span: cell.span,
                    name,
                }),
                Maybe::Present(_) => Ok(Maybe::Absent(constructed::Absent::Unnamed)),
            };
        };
        let Some(Maybe::Present(Half {
            operand: Operand::Loop { words, generator },
            ..
        })) = self
            .collected
            .slots
            .get(usize::from(constant))
            .map(|slot| slot.definition)
        else {
            return Ok(Maybe::Absent(constructed::Absent::Unnamed));
        };
        let Some(family) = self.collected.words.get(words).map(|written| written.slot)
        else {
            return Ok(Maybe::Absent(constructed::Absent::Unnamed));
        };
        let tag = if inverse.0 {
            gandr_core_term::FreeCells::inverse(gandr_core_term::CellIndex::from(generator))
        }
        else {
            gandr_core_term::FreeCells::letter(gandr_core_term::CellIndex::from(generator))
        };

        Ok(Maybe::Present(Constructor {
            family,
            form: Generators::Words(words),
            tag: usize::from(tag),
            arity: 1,
            named: cell,
        }))
    }

    /// The empty word `here(point)` is, when `point` spells the point a
    /// family's loops are at.
    ///
    /// # Specification
    /// - requires: `point` is the operand of a `here` call.
    /// - ensures: the empty word of the first words whose point `point` spells
    ///   as a closed term over their family's constructors, each written node
    ///   of the point recorded with the words so it answers at their family;
    ///   the unnamed absence when no words are at it, and `here(point)` stays
    ///   reflexivity.
    /// - fails: [`LoweringRefusal::UnknownMold`].
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoweringRefusal::UnknownMold`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — `here` at a looped point is the empty word, its point
    ///   labelled at the family, and at any other point reflexivity.
    /// - witness: `lower::native::tests::a_word_conses_its_letters_and_matches_them`
    #[spec(
        captures: before = self.pointed.len(),
        ensures: |ret| match ret {
            Ok(Maybe::Present(constructor)) => constructor.arity == 0 && constructor.tag == 0
                && matches!(constructor.form, Generators::Words(_)) && self.pointed.len() > before,
            _ => self.pointed.len() == before,
        },
    )]
    pub(super) fn looped_point(
        &mut self,
        point: Placed,
    ) -> Result<Maybe<Constructor, constructed::Absent>, LoweringRefusal<'source>>
    {
        let mut found = None;
        for (index, words) in self.collected.words.iter().enumerate() {
            let family = Generators::Written(words.family);
            let Some(declared) = self.collected.slots.get(usize::from(words.slot))
            else {
                continue;
            };
            let source = self.collected.unit.source_at(declared.named.span.start());
            let tag_of = |name: SourceFragment<'source>| {
                self.collected
                    .constructors
                    .get(&(source, SurfaceName::from(name)))
                    .filter(|constructor| constructor.form == family)
                    .map(|constructor| (constructor.tag, constructor.arity))
            };
            if let Maybe::Present(term) = closed_term(self.pbg, self.tree, point, &tag_of)?
                && term.nodes == words.point
            {
                found = Some((index, words.slot, term.written));
                break;
            }
        }
        let Some((index, family, written)) = found
        else {
            return Ok(Maybe::Absent(constructed::Absent::Unnamed));
        };
        self.pointed
            .extend(written.iter().map(|node| (node.span, index)));

        Ok(Maybe::Present(Constructor {
            family,
            form: Generators::Words(index),
            tag: 0,
            arity: 0,
            named: point,
        }))
    }

    /// Classify `(e : T)`, its `(` and `e` read, the cursor at its `:`.
    ///
    /// # Specification
    /// - requires: `run` is the parenthesised expression's first hole and
    ///   `cursor` stands at its `:`.
    /// - ensures: an annotation over a constructor standing as a value reads
    ///   `T` as a value type under the same frame, records it as the
    ///   constructor's classifier, and adopts the constructor, keeping no
    ///   ascription: `T` is already its classifier. An annotation over an
    ///   injection records `T` the same way, the injection reading its
    ///   summand's label among the sum `T` states, and, since an injection
    ///   keeps no type, is ascribed as any other value is. An annotation over
    ///   any other value is carried by the ascription its position already
    ///   makes where there is one: the whole value of a definition no signature
    ///   types, which `T` signs; the whole operand of a `return`; and a tail,
    ///   where a path through a body ends, a value there that takes the
    ///   `return` its polarity names, recorded with `T` for the mint to ascribe
    ///   that return at. Anywhere else it is planned as a value ascription of
    ///   the value at `T`: at a value position, at a subject's result or a
    ///   tested position, which take the `return` they insert, and at an
    ///   application's head, which forces it.
    /// - fails: a wrong-sort refusal at a statement, as for any value standing
    ///   there; the unadmitted annotation refusal at a position that reads a
    ///   type or nothing; the hole's and the tiles' own faults.
    /// - panics: none.
    ///
    /// # Errors
    /// The annotation's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an annotated parameterised constructor lowers over
    ///   the annotation's type, at a value position and at a tail; an annotated
    ///   name beside a definition's signature, inside a pair and at a head is
    ///   ascribed; an annotation at a statement is refused.
    /// - witness: `lower::native::tests::a_parameterized_constructor_needs_its_classifier`
    /// - witness: `lower::arity::tests::an_injection_takes_its_index_from_its_label`
    /// - witness: `lower::exits::tests::a_tail_without_an_exit_takes_the_one_its_polarity_names`
    /// - witness: `lower::native::tests::an_annotation_at_a_statement_is_of_the_wrong_sort`
    /// - witness: `lower::native::tests::an_annotated_definition_value_is_signed_by_its_annotation_1107`
    /// - witness: `lower::native::tests::an_annotated_return_is_ascribed_its_returner_1107`
    /// - witness: `lower::native::tests::an_annotation_no_form_carries_is_a_value_ascription_1543`
    #[spec(ensures: |ret| ret.is_err() || matches!(self.plans.get(site.at.node), Some(&(Plan::Transparent(_) | Plan::Ascribed(..)))))]
    pub(super) fn annotated(
        &mut self,
        site: Site,
        run: Run,
        mut cursor: Cursor<'_>,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let declined = site.folded(
            FormName::ANNOTATION,
            FragmentBoundary::Unadmitted(Unbuilt::Annotation),
        );
        let Run::One(inner) = run
        else {
            return Err(declined);
        };
        let (frame, tail) = match site.reading {
            Reading::Value(frame) => (frame, false),
            Reading::Computation(_) => (
                self.require(site, Produced::Value)?,
                self.exits.contains(&site.at.node),
            ),
            Reading::Head(_) => (self.require(site, Produced::Value)?, false),
            Reading::Unread
            | Reading::ValueType(_)
            | Reading::CompType(_)
            | Reading::Result(_)
            | Reading::Function => return Err(declined),
        };
        let signs = self.annotated_definitions.contains_key(&site.at.node);
        let returned = self.ascribed.contains_key(&site.at.node);
        let constructed = matches!(self.applied_constructor(site, inner)?, Maybe::Present(_));
        let carried = constructed || signs || returned || tail;
        if constructed {
            let _held = self.ascribed.remove(&site.at.node);
        }
        let _colon = cursor.tile(TileName::COLON);
        let classifier = site.one(cursor.operands())?;
        closed(site, &mut cursor, TileName::PAREN_CLOSE)?;
        exhausted(site, &cursor)?;
        self.read(classifier.node, Reading::ValueType(frame));
        if tail && !constructed {
            let _first = self.ascribed.insert(site.at.node, classifier.node);
        }
        self.read(inner.node, Reading::Value(frame));
        let _first = self.classifiers.insert(inner.node, classifier.node);
        if carried {
            self.plan(site, Plan::Transparent(inner.node));
        }
        else {
            self.plan(site, Plan::Ascribed(inner.node, classifier.node));
        }

        Ok(())
    }

    /// The constructor `inner`, written inside the parentheses at `site`,
    /// applies: a bare constructor, or a call whose head is one, in the
    /// spelling of either grammar.
    ///
    /// # Specification
    /// - requires: `inner` is the operand of the parenthesised form at `site`.
    /// - ensures: the constructor a constructor name or a call's head names, as
    ///   [`Self::constructor_head`] answers it; the constructor a type name or
    ///   a type application's head names, as [`Self::constructor_named`]
    ///   answers it, where the type grammar molds the parentheses; the unnamed
    ///   absence for any other form.
    /// - fails: [`LoweringRefusal::UnknownMold`].
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoweringRefusal::UnknownMold`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::annotated`].
    /// - witness: `lower::native::tests::a_parameterized_constructor_needs_its_classifier`
    /// - witness: `lower::native::tests::a_type_valued_calls_argument_takes_an_annotation_3633`
    #[spec(ensures: |ret| ret.is_ok() || matches!(ret, Err(LoweringRefusal::UnknownMold { .. })))]
    fn applied_constructor(
        &mut self,
        site: Site,
        inner: Placed,
    ) -> Result<Maybe<Constructor, constructed::Absent>, LoweringRefusal<'source>>
    {
        let bare = self.constructor_head(site, inner)?;
        if let Maybe::Present(_) = bare {
            return Ok(bare);
        }
        let Some(node) = self.tree.node(inner.node)
        else {
            return Ok(bare);
        };
        match shape_of(self.pbg, node)? {
            Shape::Form {
                former: Former::TypeHead,
                ..
            } => return Ok(self.constructor_named(site, self.name_at(inner))),
            Shape::Form {
                former: Former::Call | Former::TypeApplication,
                ..
            } => {},
            Shape::Root | Shape::Form { .. } | Shape::Repair(_) | Shape::Layout => return Ok(bare),
        }
        let mut scratch = core::mem::take(&mut self.scratch);
        let first = read_pieces(self.pbg, self.tree, inner.node, &mut scratch)
            .map(|()| scratch.pieces.first().copied());
        self.scratch = scratch;
        match first? {
            Some(Piece::Operand(head)) => self.constructor_head(site, head),
            Some(Piece::Tile { label, at }) if label == TileName::TYPE_IDENTIFIER => {
                Ok(self.constructor_named(site, self.name_at(at)))
            },
            Some(Piece::Tile { .. }) | None => Ok(bare),
        }
    }

    /// The number of parameters of the data family declared at `constant`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the parameter count of the data declaration whose slot takes
    ///   `constant`, and none for `Theory`; the undeclared absence for any
    ///   other declaration.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a family and a value declaration separate the hit
    ///   from the miss.
    /// - witness: `lower::native::tests::a_data_family_applies_to_its_parameters`
    /// - witness: `lower::native::tests::the_presentation_code_names_its_family_where_a_type_is_read`
    #[spec(ensures: |ret| matches!(ret, Maybe::Absent(_)) || self.collected.slots.get(usize::from(constant)).is_some())]
    pub(super) fn data_family(
        &self,
        constant: ConstantIndex,
    ) -> Maybe<OperandCount, family::Absent>
    {
        match self
            .collected
            .slots
            .get(usize::from(constant))
            .map(|slot| slot.definition)
        {
            Some(Maybe::Present(Half {
                operand: Operand::Data(form),
                ..
            })) => self.collected.data.get(form).map_or(
                Maybe::Absent(family::Absent::Undeclared),
                |written| {
                    Maybe::Present(OperandCount::from(
                        written
                            .parameters
                            .len()
                            .saturating_add(written.indices.len()),
                    ))
                },
            ),
            Some(Maybe::Present(Half {
                operand: Operand::Code,
                ..
            })) => Maybe::Present(OperandCount::from(0_usize)),
            _ => Maybe::Absent(family::Absent::Undeclared),
        }
    }

    /// Classify the data family at `constant`, of `arity` parameters,
    /// applied to the arguments `applied` holds in the operand store.
    ///
    /// # Specification
    /// - ensures: the family stands as a value type over its arguments, each
    ///   read as a value under the site's frame, standing inside the type as a
    ///   path type's endpoints do, and recorded at its place among the family's
    ///   parameters. Each argument is read as a type reads it wherever the
    ///   family stands, a body's quote included, so a call written there is the
    ///   value it returns (#3572).
    /// - fails: the arity refusal for an argument count other than `arity`; the
    ///   wrong-sort refusal where no value type is read or reached.
    /// - panics: none.
    ///
    /// # Errors
    /// The family's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a family over one and over two arguments, and over
    ///   too few, each asserted as the exact nominal type or refusal; a family
    ///   a body quotes reads each argument at its index in the body, and a call
    ///   among its arguments as the value it returns.
    /// - witness: `lower::native::tests::a_data_family_applies_to_its_parameters`
    /// - witness: `lower::tests::a_family_a_body_quotes_reads_its_parameters_at_their_indices_3553`
    /// - witness: `lower::tests::a_call_a_quoted_family_takes_is_the_value_it_returns_3572`
    #[spec(ensures: |ret| ret.is_err() || self.plans.get(site.at.node) == Some(&Plan::Data(constant, applied)))]
    pub(super) fn family(
        &mut self,
        site: Site,
        constant: ConstantIndex,
        arity: OperandCount,
        applied: Stretch,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let count = applied.end.saturating_sub(applied.start);
        if OperandCount::from(count) != arity {
            return Err(site.out(FragmentBoundary::Arity(OperandCount::from(count))));
        }
        let frame = self.require(site, Produced::ValueType)?;
        let form = self.collected.data.iter().position(|form| {
            self.collected
                .slots
                .get(usize::from(form.slot))
                .is_some_and(|slot| slot.constant == constant)
        });
        for (place, position) in (applied.start .. applied.end).enumerate() {
            if let Some(&argument) = self.operands.get(position) {
                if let Some(form) = form {
                    let _first = self.argued.insert(argument, Argued {
                        form,
                        place,
                        applied,
                    });
                }
                self.read(argument, Reading::Value(frame));
            }
        }
        // Each argument is a value the family's type reads: it counts in that
        // type's telescope, a body quote's where the family is quoted in a
        // body, as a path type's endpoints do. A type reads it wherever the
        // family stands, so a call written there is the value it returns, as
        // in a binder's type, and no run stands under the quote (#3572).
        let arguments = stretch(&self.operands, applied);
        self.in_type.extend(arguments.iter().copied());
        self.type_read.extend(arguments.iter().copied());
        self.plan(site, Plan::Data(constant, applied));

        Ok(())
    }

    /// Classify a theory's terms as a type, `Terms(S)`, its operand `theory`.
    ///
    /// # Specification
    /// - requires: `site` is a type application headed `Terms`, which nothing
    ///   the scope binds answers, written over `theory`.
    /// - ensures: the form stands as the value type of the terms the collection
    ///   took a slot for, for the theory the operand names, and is planned as
    ///   that family over no arguments; the operand is read as the theory's
    ///   name alone.
    /// - fails: yields the wrong-sort refusal where no value type is read; an
    ///   operand that is no capitalised name is out of the fragment at
    ///   [`Unbuilt::TermsType`]; the refusals [`Collected::presented_theory`]
    ///   yields at the operand; a theory [`term_generators`] refuses is out of
    ///   the fragment at the feature it names, at the whole type.
    /// - panics: none.
    ///
    /// # Errors
    /// The form's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a unital magma's terms, a two-sorted theory's, a
    ///   law-bearing theory's, and a name no theory answers.
    /// - witness: `tests::modules::models::a_theory_s_terms_are_its_operations_over_its_rules_4143`
    /// - witness: `tests::modules::models::the_terms_of_a_theory_outside_one_plain_sort_are_refused_4143`
    #[spec(ensures: |ret| ret.is_err() || matches!(self.plans.get(site.at.node), Some(&Plan::Data(..))))]
    pub(super) fn terms_type(
        &mut self,
        site: Site,
        theory: NodeIndex,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let outside = |at: Site| at.out(FragmentBoundary::Unadmitted(Unbuilt::TermsType));
        let Some(node) = self.tree.node(theory)
        else {
            return Err(outside(site));
        };
        let named = Placed::of(theory, node);
        let Shape::Form {
            former: Former::TypeHead | Former::Constructor,
            ..
        } = shape_of(self.pbg, node)?
        else {
            return Err(outside(Site { at: named, ..site }));
        };
        let (slot, presentation) =
            self.collected
                .presented_theory(named.span.start(), named.span, self.name_at(named))?;
        let Some(constant) = self
            .collected
            .terms
            .iter()
            .find(|terms| terms.theory == slot)
            .and_then(|terms| self.collected.slots.get(usize::from(terms.slot)))
            .map(|terms| terms.constant)
        else {
            let feature = term_generators(presentation)
                .err()
                .unwrap_or(Unbuilt::TermsType);
            return Err(site.out(FragmentBoundary::Unadmitted(feature)));
        };
        let none = Stretch {
            start: self.operands.len(),
            end: self.operands.len(),
        };
        self.family(site, constant, OperandCount::from(0_usize), none)
    }

    /// The data or codata family `head`, the head of a call written at
    /// `site`, names.
    ///
    /// # Specification
    /// - requires: `head` is the first operand of the call at `site`.
    /// - ensures: what the head's name resolves to when the head is a
    ///   capitalised name no constructor carries and the declaration it
    ///   resolves to is a data or a codata family; the undeclared absence for
    ///   any other head.
    /// - provides: the family a call applies where a value is read, so a type
    ///   written as a family's application is read as that type wherever it is
    ///   passed (#2512).
    /// - fails: the refusals the name's resolution yields.
    /// - panics: none.
    ///
    /// # Errors
    /// The resolution's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a data family applied as a type argument and as a
    ///   definition's body, a constructor and a function applied the same way
    ///   keep their own readings.
    /// - witness: `lower::native::tests::a_data_family_applied_where_a_value_is_read_is_quoted_2512`
    #[spec(
        ensures: |ret| match ret {
            | Ok(Maybe::Present(Resolved::Declaration { constant, .. })) => {
                matches!(self.data_family(constant), Maybe::Present(_))
                    || matches!(self.codata_family(constant), Maybe::Present(_))
            },
            | Ok(Maybe::Present(Resolved::Binder(_))) => false,
            | Ok(Maybe::Absent(_)) | Err(_) => true,
        },
    )]
    pub(super) fn family_head(
        &mut self,
        site: Site,
        head: Placed,
    ) -> Result<Maybe<Resolved, family::Absent>, LoweringRefusal<'source>>
    {
        let undeclared = Maybe::Absent(family::Absent::Undeclared);
        let Some(node) = self.tree.node(head.node)
        else {
            return Ok(undeclared);
        };
        let Shape::Form {
            former: Former::Constructor,
            ..
        } = shape_of(self.pbg, node)?
        else {
            return Ok(undeclared);
        };
        let name = self.name_at(head);
        if let Maybe::Present(_constructor) = self.constructor_named(site, name) {
            return Ok(undeclared);
        }
        let named = Site { at: head, ..site };
        let Maybe::Present(resolved) = self.resolve_name(named, site.reading.frame(), name)?
        else {
            return Ok(undeclared);
        };
        let Resolved::Declaration { constant, .. } = resolved
        else {
            return Ok(undeclared);
        };
        if matches!(self.data_family(constant), Maybe::Present(_))
            || matches!(self.codata_family(constant), Maybe::Present(_))
        {
            return Ok(Maybe::Present(resolved));
        }

        Ok(undeclared)
    }

    /// The number of parameters of the codata family declared at `constant`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the parameter count of the codata declaration whose slot
    ///   takes `constant`; the undeclared absence for any other declaration.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a codata family and a data family beside it separate
    ///   the hit from the miss.
    /// - witness: `description::tests::a_codata_declaration_lowers_to_its_signature`
    #[spec(ensures: |ret| matches!(ret, Maybe::Absent(_)) || self.collected.slots.get(usize::from(constant)).is_some())]
    pub(super) fn codata_family(
        &self,
        constant: ConstantIndex,
    ) -> Maybe<OperandCount, family::Absent>
    {
        let Some(slot) = self.collected.slots.get(usize::from(constant))
        else {
            return Maybe::Absent(family::Absent::Undeclared);
        };
        match self.collected.descriptions.get(&slot.introduced_by.node) {
            Maybe::Present(entry) if entry.description.polarity == DeclPolarity::Codata => {
                Maybe::Present(OperandCount::from(entry.parameters.len()))
            },
            Maybe::Present(_) | Maybe::Absent(_) => Maybe::Absent(family::Absent::Undeclared),
        }
    }

    /// Classify the codata family at `constant`, of `arity` parameters,
    /// applied to the arguments `applied` holds in the operand store.
    ///
    /// # Specification
    /// - ensures: the family stands as a computation type over its arguments,
    ///   each read as a value under the site's frame, standing inside the type
    ///   as a path type's endpoints do, and read as a type reads it wherever
    ///   the family stands, so a call written there is the value it returns.
    /// - fails: the arity refusal for an argument count other than `arity`; the
    ///   wrong-sort refusal where no computation type is read or reached.
    /// - panics: none.
    ///
    /// # Errors
    /// The family's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a codata family read as a function's answer lowers to
    ///   the nominal computation type over its argument; one a body quotes
    ///   reads its argument at its index in the body.
    /// - witness: `description::tests::a_codata_declaration_lowers_to_its_signature`
    /// - witness: `lower::tests::a_family_a_body_quotes_reads_its_parameters_at_their_indices_3553`
    #[spec(ensures: |ret| ret.is_err() || self.plans.get(site.at.node) == Some(&Plan::Codata(constant, applied)))]
    pub(super) fn codata_type(
        &mut self,
        site: Site,
        constant: ConstantIndex,
        arity: OperandCount,
        applied: Stretch,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let count = applied.end.saturating_sub(applied.start);
        if OperandCount::from(count) != arity {
            return Err(site.out(FragmentBoundary::Arity(OperandCount::from(count))));
        }
        let frame = self.require(site, Produced::CompType)?;
        for position in applied.start .. applied.end {
            if let Some(&argument) = self.operands.get(position) {
                self.read(argument, Reading::Value(frame));
            }
        }
        let arguments = stretch(&self.operands, applied);
        self.in_type.extend(arguments.iter().copied());
        self.type_read.extend(arguments.iter().copied());
        self.plan(site, Plan::Codata(constant, applied));

        Ok(())
    }

    /// Classify a match, `case e -> T? { p => c, … }`.
    ///
    /// # Specification
    /// - requires: `site` is a match in term position.
    /// - ensures: a match of no arms, `case e {}`, is planned as
    ///   [`Self::empty_case`] plans it: the data switch of no branches over a
    ///   scrutinee stated at a data type or a path type, and else the case of
    ///   no branches, the eliminator of the empty sum `Void`; otherwise the
    ///   match stands as a computation, its arms' patterns read and compiled to
    ///   a decision tree over the scrutinee, read as a value under the site's
    ///   frame; the written answer is read where a result is read and ascribes
    ///   the tree's root, which a data switch or a dependent split takes as its
    ///   motive instead, and else the answer the position states is taken; each
    ///   arm body is read as a computation under the case's frame, the tree's
    ///   anonymous binders and its own variables, answers what the match does,
    ///   passed with the constructor the arm reads a variable scrutinee at
    ///   ([`ArmReading`]), and takes the paths through the match's position; a
    ///   match on a recursive function's parameter records that parameter for
    ///   its arm bodies ([`Self::scrutinise`]).
    /// - provides: the reading of `case`.
    /// - fails: the wrong-sort refusal outside computation position; the view
    ///   form `case … with` by the view's name; a match of no arms as
    ///   [`Self::empty_case`] refuses it; a written answer on a match whose
    ///   arms continue a block as joining it; a pattern the fragment does not
    ///   read by its own name; a pattern of another kind than the first tested
    ///   at its place, a constructor of another data type among them, as
    ///   [`LoweringRefusal::MismatchedPattern`] at that pattern; a variable
    ///   bound twice in one pattern; a non-exhaustive match; a match whose tree
    ///   eliminates native data with no answer as unannotated; and the tiles'
    ///   and holes' own faults.
    /// - panics: none.
    ///
    /// # Errors
    /// The match's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the witnesses lower each pattern shape and refusal,
    ///   asserting the tree read back out of the arena or the exact refusal.
    /// - witness: `lower::native::tests::nested_constructor_patterns_compile_to_nested_cases`
    /// - witness: `lower::native::tests::a_non_exhaustive_match_is_refused`
    /// - witness: `lower::native::tests::a_match_in_an_arm_reads_the_answer_at_the_arm_s_constructor_2994`
    /// - witness: `lower::native::tests::a_match_without_an_answer_is_unannotated`
    /// - witness: `lower::native::tests::patterns_outside_the_fragment_are_declined_by_name`
    /// - witness: `lower::native::tests::a_match_of_no_arms_eliminates_the_empty_sum`
    /// - witness: `lower::exits::tests::a_match_continuing_its_block_answers_what_the_block_does`
    /// - witness: `lower::native::tests::an_or_pattern_settles_each_alternative`
    #[spec(ensures: |ret| ret.is_err() || matches!(self.plans.get(site.at.node), Some(&(Plan::Case(_) | Plan::EmptyCase(_)))))]
    pub(super) fn case(
        &mut self,
        site: Site,
        mut cursor: Cursor<'_>,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let frame = self.require(site, Produced::Computation)?;
        let _case = cursor.tile(TileName::CASE);
        let scrutinee = site.one(cursor.operands())?;
        if let Maybe::Present(with) = cursor.at(TileName::WITH) {
            return Err(LoweringRefusal::OutOfFragment {
                span: with.span,
                form: FormName::CASE_WITH_VIEW,
                sort: site.reading.sort(),
                boundary: FragmentBoundary::Unadmitted(Unbuilt::CaseView),
            });
        }
        let written = match cursor.tile(TileName::ARROW) {
            Maybe::Present(_) => Maybe::Present(site.one(cursor.operands())?),
            Maybe::Absent(_) => Maybe::Absent(answered::Absent::Unstated),
        };
        closed(site, &mut cursor, TileName::BRACE_OPEN)?;
        let mut arms: Vec<(Placed, Placed)> = Vec::new();
        while let Maybe::Absent(_) = cursor.tile(TileName::BRACE_CLOSE) {
            let _bar = cursor.tile(TileName::BAR);
            let pattern = site.one(cursor.operands())?;
            closed(site, &mut cursor, TileName::FAT_ARROW)?;
            let body = site.one(cursor.operands())?;
            arms.push((pattern, body));
            if let Maybe::Absent(_) = cursor.tile(TileName::COMMA) {
                closed(site, &mut cursor, TileName::BRACE_CLOSE)?;
                break;
            }
        }
        exhausted(site, &cursor)?;
        if arms.is_empty() {
            return self.empty_case(site, frame, scrutinee, written);
        }
        if self.joined.contains(&site.at.node)
            && let Maybe::Present(stated) = written
        {
            return Err(LoweringRefusal::OutOfFragment {
                span: stated.span,
                form: FormName::CASE,
                sort: site.reading.sort(),
                boundary: FragmentBoundary::JoinsBlock,
            });
        }
        // A loop's name as an arm's whole pattern names the loop's arm, never
        // a variable, and answers as the loop does; the other arms compile to
        // the tree.
        let mut looped = Vec::new();
        let mut constructed = Vec::with_capacity(arms.len());
        for &(pattern, body) in &arms {
            match self.loop_named(site, pattern)? {
                Maybe::Present(NamedLoop { words, generator }) => {
                    self.lettered.push((pattern.span, words));
                    looped.push(LoopArm {
                        words,
                        generator: usize::from(generator),
                        body: body.node,
                        named: pattern,
                    });
                },
                Maybe::Absent(_) => constructed.push((pattern, body)),
            }
        }
        let arms = constructed;
        let mut patterns = Written {
            positional: Positional(true),
            ..Written::default()
        };
        let mut rows = Vec::new();
        let mut variables: Vec<Vec<Placed>> = Vec::with_capacity(arms.len());
        let mut kept = CaseOrigin {
            written: site.at.node,
            scrutinee: scrutinee.node,
            scrutinised: Maybe::Absent(scrutinised::Absent::Unminted),
            patterns: Patterns::new(),
            arms: Vec::new(),
            spans: Vec::new(),
            labelled: Vec::new(),
        };
        let stated = self.scrutinee_type(frame, scrutinee)?;
        let mut roots = Vec::new();
        for (arm, &(pattern, body)) in arms.iter().enumerate() {
            let arm = ArmAt(arm);
            let alternatives = self.alternatives(pattern)?;
            let several = alternatives.len() > 1;
            let mut bound = Vec::new();
            for (place, alternative) in alternatives.into_iter().enumerate() {
                let mut named = Vec::new();
                let root = self.pattern(site, alternative, stated, &mut patterns, &mut named)?;
                if several && !named.is_empty() {
                    return Err(LoweringRefusal::OutOfFragment {
                        span: pattern.span,
                        form: FormName::OR_PATTERN,
                        sort: site.reading.sort(),
                        boundary: FragmentBoundary::Unadmitted(Unbuilt::OrPattern),
                    });
                }
                bound = named;
                if several && place == 0_usize {
                    patterns
                        .spelled
                        .push((root, pattern.span, PatternReading::Matched));
                }
                roots.push((arm, root, alternative.node, body.node));
                rows.push(Row {
                    columns: Vec::from([root]),
                    arm,
                    bindings: Vec::new(),
                    stuck: Maybe::Absent(stuck::Absent::Decided),
                });
            }
            variables.push(bound);
        }
        settle_unstated(&mut patterns, &roots)?;
        let tests = self.compile(site, &patterns, rows)?;
        let loops = self.loop_arms(site, &tests, looped)?;
        let eliminates = tests.iter().any(|test| {
            matches!(
                *test,
                Test::Data { .. }
                    | Test::Split {
                        dependent: Dependent(true),
                        ..
                    }
            )
        });
        let ascribed = match written {
            Maybe::Present(node) => Maybe::Present(Answer {
                node: node.node,
                frame,
                over: Over::Written,
                arm: Maybe::Absent(passed::Absent::Unpassed),
            }),
            Maybe::Absent(reason) => Maybe::Absent(reason),
        };
        let answer = match ascribed {
            Maybe::Present(written) => Maybe::Present(written),
            Maybe::Absent(reason) => self
                .answers
                .get(&site.at.node)
                .copied()
                .map_or(Maybe::Absent(reason), Maybe::Present),
        };
        if eliminates && matches!(answer, Maybe::Absent(_)) {
            return Err(site.out(FragmentBoundary::Unannotated));
        }
        Self::keep(&patterns, &roots, &mut kept);
        self.read(scrutinee.node, Reading::Value(frame));
        let bodies = arms
            .iter()
            .map(|&(_pattern, body)| body.node)
            .chain(loops.iter().map(|arm| arm.body));
        let enclosing = self.scrutinised.get(&site.at.node).copied();
        self.scrutinise(frame, scrutinee, enclosing, bodies)?;
        if let Maybe::Present(node) = written {
            self.read(node.node, Reading::Result(frame));
        }
        // Each arm passes the answer on with the constructor it reads the
        // scrutinee at, which a match in its body reads the answer under.
        let switched = match (answer, tests.first()) {
            (
                Maybe::Present(_),
                Some(&Test::Data {
                    level,
                    family: Maybe::Present(_),
                    ..
                }),
            ) if level == TreeLevel::default() => self.scrutinee_binder(frame, scrutinee)?,
            (Maybe::Present(_) | Maybe::Absent(_), Some(_) | None) => {
                Maybe::Absent(settled::Absent::Unswitched)
            },
        };
        let refinings = match switched {
            Maybe::Present(_) => refinings(&tests),
            Maybe::Absent(_) => Refinings::default(),
        };
        let mut binders = Vec::new();
        for (position, (&(_pattern, body), bound)) in arms.iter().zip(&variables).enumerate() {
            let mut inner = frame;
            binders.clear();
            for &binder in bound {
                let name = SurfaceName::from(self.text_at(binder));
                self.note_binder(binder, name)?;
                let site = Maybe::Present(binder.span);
                let id = match self.pattern_stated.get(&binder.node) {
                    Some(&stated) => self.scope.extend_typed(inner, name, stated, site),
                    None => self.scope.extend(inner, name, site),
                };
                if let Maybe::Present(_) = switched {
                    binders.push(id);
                }
                inner = Frame::Inner(id);
            }
            self.read(body.node, Reading::Computation(inner));
            if let Maybe::Present(stated) = answer {
                let settled = match switched {
                    Maybe::Present(binder) => {
                        arm_settled(&tests, &refinings, ArmAt(position), &binders, binder)
                    },
                    Maybe::Absent(reason) => Maybe::Absent(reason),
                };
                let at = ArmIndex(self.arms.len());
                self.arms.push(ArmReading {
                    settled,
                    outer: stated.arm,
                });
                let _first = self.answers.insert(body.node, Answer {
                    arm: Maybe::Present(at),
                    ..stated
                });
            }
            self.pass_paths(site.at.node, body.node);
        }
        // A loop arm reads the case's answer at its loop's point as a binder,
        // which the minted case replaces by that answer.
        for arm in &loops {
            let inner = Frame::Inner(self.scope.extend(
                frame,
                SurfaceName::from(""),
                Maybe::Absent(binder_site::Absent::Unwritten),
            ));
            self.read(arm.body, Reading::Computation(inner));
            if let Maybe::Present(stated) = answer {
                let _first = self.answers.insert(arm.body, Answer {
                    over: Over::Loop { arm: inner },
                    ..stated
                });
            }
            self.pass_paths(site.at.node, arm.body);
        }
        let index = CaseIndex(self.cases.len());
        self.cases.push(CaseForm {
            scrutinee: scrutinee.node,
            frame,
            answer,
            ascribed,
            bodies: arms.iter().map(|&(_pattern, body)| body.node).collect(),
            tests,
            loops,
            origin: kept,
            variables,
        });
        self.plan(site, Plan::Case(index));

        Ok(())
    }

    /// Classify a match of no arms, `case e -> T? {}`, over `scrutinee` under
    /// `frame`, with the answer `written` when one is written.
    ///
    /// # Specification
    /// - requires: `site` is a match of no arms in term position, read under
    ///   `frame`.
    /// - ensures: over a scrutinee [`Self::empty_switch`] reads a data switch
    ///   for, the match is planned as that switch with no branch, its answer
    ///   the written one and else the one its position states, the written
    ///   answer read where a result is read; over any other scrutinee it is
    ///   planned as the case of no branches, the eliminator of the empty sum
    ///   `Void`. The scrutinee is read as a value under `frame` either way.
    /// - provides: the empty match: a data type with no constructor, and a path
    ///   the checker decides has no inhabitant, are eliminated by their own
    ///   switch, exhaustive with no branch, at any answer.
    /// - fails: as [`Self::empty_switch`] refuses the scrutinee's type; a
    ///   written answer on the case of no branches, which checks at any type; a
    ///   data switch whose answer neither the match nor its position states, as
    ///   unannotated.
    /// - panics: none.
    ///
    /// # Errors
    /// The match's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a match of no arms over `Void`, over a data type with
    ///   no constructor, over a path and over a data type with a constructor
    ///   separate the empty sum's case, the data switch and the refusal.
    /// - witness: `lower::native::tests::a_match_of_no_arms_eliminates_the_empty_sum`
    /// - witness: `lower::native::tests::a_match_of_no_arms_switches_on_empty_data_and_on_a_path`
    #[spec(ensures: |ret| ret.is_err() || matches!(self.plans.get(site.at.node), Some(&(Plan::Case(_) | Plan::EmptyCase(_)))))]
    fn empty_case(
        &mut self,
        site: Site,
        frame: Frame,
        scrutinee: Placed,
        written: Maybe<Placed, answered::Absent>,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let stated = self.scrutinee_type(frame, scrutinee)?;
        let Maybe::Present(family) = self.empty_switch(site, frame, stated)?
        else {
            if let Maybe::Present(stated) = written {
                return Err(LoweringRefusal::OutOfFragment {
                    span: stated.span,
                    form: FormName::CASE,
                    sort: site.reading.sort(),
                    boundary: FragmentBoundary::Unadmitted(Unbuilt::EmptyCase),
                });
            }
            self.read(scrutinee.node, Reading::Value(frame));
            self.plan(site, Plan::EmptyCase(scrutinee.node));
            return Ok(());
        };
        let ascribed = match written {
            Maybe::Present(node) => Maybe::Present(Answer {
                node: node.node,
                frame,
                over: Over::Written,
                arm: Maybe::Absent(passed::Absent::Unpassed),
            }),
            Maybe::Absent(reason) => Maybe::Absent(reason),
        };
        let answer = match ascribed {
            Maybe::Present(written) => Maybe::Present(written),
            Maybe::Absent(reason) => self
                .answers
                .get(&site.at.node)
                .copied()
                .map_or(Maybe::Absent(reason), Maybe::Present),
        };
        if let Maybe::Absent(_) = answer {
            return Err(site.out(FragmentBoundary::Unannotated));
        }
        self.read(scrutinee.node, Reading::Value(frame));
        if let Maybe::Present(node) = written {
            self.read(node.node, Reading::Result(frame));
        }
        let index = CaseIndex(self.cases.len());
        self.cases.push(CaseForm {
            scrutinee: scrutinee.node,
            frame,
            answer,
            ascribed,
            bodies: Vec::new(),
            tests: Vec::from([Test::Data {
                level: TreeLevel::default(),
                depth: Depth::default(),
                family,
                eliminated: match family {
                    Maybe::Present(family) => Maybe::Present(family),
                    Maybe::Absent(_) => Maybe::Absent(eliminated::Absent::Armless),
                },
                equations: 0,
                branches: Vec::new(),
            }]),
            loops: Vec::new(),
            origin: CaseOrigin {
                written: site.at.node,
                scrutinee: scrutinee.node,
                scrutinised: Maybe::Absent(scrutinised::Absent::Unminted),
                patterns: Patterns::new(),
                arms: Vec::new(),
                spans: Vec::new(),
                labelled: Vec::new(),
            },
            variables: Vec::new(),
        });
        self.plan(site, Plan::Case(index));

        Ok(())
    }

    /// The family of the data switch a match of no arms eliminates its
    /// scrutinee by, the scrutinee stated at `stated`.
    ///
    /// # Specification
    /// - requires: `site` is a match of no arms under `frame`; `stated` is its
    ///   scrutinee's written type, as [`Self::scrutinee_type`] reads it.
    /// - ensures: read through parentheses, a path type answers a switch over
    ///   no bare family, whose emptiness the checker decides; a type head, bare
    ///   or applied, naming a data declaration with no constructor answers a
    ///   switch over that family, bare when it takes no parameter. Any other
    ///   stated type, the empty sum among them, answers
    ///   [`switched::Absent::Otherwise`], and an unstated one
    ///   [`switched::Absent::Untyped`].
    /// - fails: [`LoweringRefusal::NonExhaustiveMatch`] at the match for a head
    ///   naming a data declaration with a constructor, which no arm covers; the
    ///   head's own resolution refusals; the allowance, one step per form read.
    /// - panics: none.
    ///
    /// # Errors
    /// As `fails`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::empty_case`].
    /// - witness: `lower::native::tests::a_match_of_no_arms_switches_on_empty_data_and_on_a_path`
    #[spec(ensures: |ret| ret.is_ok() || matches!(ret, Err(LoweringRefusal::NonExhaustiveMatch { span }) if span == site.at.span) || !matches!(ret, Err(LoweringRefusal::NonExhaustiveMatch { .. })))]
    fn empty_switch(
        &mut self,
        site: Site,
        frame: Frame,
        stated: Maybe<NodeIndex, binder_type::Absent>,
    ) -> Result<Maybe<Maybe<ConstantIndex, bare::Absent>, switched::Absent>, LoweringRefusal<'source>>
    {
        let (constant, form) = match self.stated_data(frame, stated)? {
            Maybe::Present(Stated::Family { constant, form }) => (constant, form),
            Maybe::Present(Stated::Path) => {
                return Ok(Maybe::Present(Maybe::Absent(bare::Absent::Parameterised)));
            },
            Maybe::Absent(reason) => return Ok(Maybe::Absent(reason)),
        };
        let Some(written) = self.collected.data.get(form)
        else {
            return Ok(Maybe::Absent(switched::Absent::Otherwise));
        };
        if !written.generators.is_empty() {
            return Err(LoweringRefusal::NonExhaustiveMatch { span: site.at.span });
        }

        Ok(Maybe::Present(if written.parameters.is_empty() {
            Maybe::Present(constant)
        }
        else {
            Maybe::Absent(bare::Absent::Parameterised)
        }))
    }

    /// What the written type `stated` of a value read under `frame` names, as
    /// a match reads its scrutinee's: a path type, or a data family.
    ///
    /// # Specification
    /// - requires: `stated` is a written type, as [`Self::scrutinee_type`]
    ///   reads it.
    /// - ensures: read through parentheses, a path type answers
    ///   [`Stated::Path`]; a type head, bare or applied, naming a data
    ///   declaration answers that declaration and its position among the
    ///   collected data forms. Any other stated type answers
    ///   [`switched::Absent::Otherwise`], and an unstated one
    ///   [`switched::Absent::Untyped`].
    /// - fails: the head's own resolution refusals; the allowance, one step per
    ///   form read.
    /// - panics: none.
    ///
    /// # Errors
    /// As `fails`.
    ///
    /// # Termination
    /// Every round reads one form and descends only into the type its
    /// parentheses hold, a strict subtree, spending one step of the
    /// allowance.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::empty_case`] and [`Self::data_field`].
    /// - witness: `lower::native::tests::a_match_of_no_arms_switches_on_empty_data_and_on_a_path`
    /// - witness: `lower::native::tests::a_data_field_is_the_case_returning_it_1106`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |stated| match *stated {
        Maybe::Present(Stated::Family { form, .. }) => form < self.collected.data.len(),
        Maybe::Present(Stated::Path) | Maybe::Absent(_) => true,
    }))]
    fn stated_data(
        &mut self,
        frame: Frame,
        stated: Maybe<NodeIndex, binder_type::Absent>,
    ) -> Result<Maybe<Stated, switched::Absent>, LoweringRefusal<'source>>
    {
        let otherwise = Ok(Maybe::Absent(switched::Absent::Otherwise));
        let Maybe::Present(mut at) = stated
        else {
            return Ok(Maybe::Absent(switched::Absent::Untyped));
        };
        let mut scratch = core::mem::take(&mut self.scratch);
        let read = loop {
            if let Err(refusal) = self.fuel.spend() {
                break Err(refusal);
            }
            let Some(tree) = self.tree.node(at)
            else {
                break Ok(None);
            };
            let placed = Placed::of(at, tree);
            let former = match self.form_at(placed) {
                Ok(Some((_name, former))) => former,
                Ok(None) => break Ok(None),
                Err(refusal) => break Err(refusal),
            };
            if former == Former::PathType {
                break Ok(Some(Maybe::Absent(bare::Absent::Parameterised)));
            }
            if former == Former::TypeHead {
                break Ok(Some(Maybe::Present(placed)));
            }
            if former != Former::ParenthesizedType && former != Former::TypeApplication {
                break Ok(None);
            }
            if let Err(refusal) = read_pieces(self.pbg, self.tree, at, &mut scratch) {
                break Err(refusal);
            }
            if former == Former::TypeApplication {
                break Ok(scratch.pieces.first().and_then(|piece| match *piece {
                    Piece::Tile { at: head, .. } => Some(Maybe::Present(head)),
                    Piece::Operand(_) => None,
                }));
            }
            let mut operands = scratch.pieces.iter().filter_map(|piece| match *piece {
                Piece::Operand(inner) => Some(inner),
                Piece::Tile { .. } => None,
            });
            match (operands.next(), operands.next()) {
                (Some(inner), None) => at = inner.node,
                (Some(_) | None, _) => break Ok(None),
            }
        };
        self.scratch = scratch;
        let head = match read? {
            Some(Maybe::Present(head)) => head,
            Some(Maybe::Absent(_)) => return Ok(Maybe::Present(Stated::Path)),
            None => return otherwise,
        };
        let named = Site {
            at: head,
            name: FormName::IDENTIFIER,
            reading: Reading::Value(frame),
        };
        let name = self.name_at(head);
        let Maybe::Present(super::Resolved::Declaration { constant, .. }) =
            self.resolve_name(named, frame, name)?
        else {
            return otherwise;
        };
        let Some(Maybe::Present(Half {
            operand: Operand::Data(form),
            ..
        })) = self
            .collected
            .slots
            .get(usize::from(constant))
            .map(|slot| slot.definition)
        else {
            return otherwise;
        };
        if form >= self.collected.data.len() {
            return otherwise;
        }

        Ok(Maybe::Present(Stated::Family { constant, form }))
    }

    /// Classify a selection `e.l` as the field `l` of the data value `e` is:
    /// the case over `e` whose branch for each constructor returns that
    /// constructor's field `l`.
    ///
    /// # Specification
    /// - requires: `site` is a projection; `pieces` is its reading.
    /// - ensures: planned when the selection is one link off a name whose
    ///   written type, read as [`Self::stated_data`] reads a scrutinee's, is a
    ///   data family indexed by nothing: the name read as a value under the
    ///   form's frame, and per constructor its field count and the position of
    ///   its field named `l`. The type the projection returns is the answer its
    ///   position states when it states one, and otherwise the declared type of
    ///   the first constructor's field `l`, read at the arguments the written
    ///   type gives the family's parameters. Nothing is planned for any other
    ///   selection, so a record, a module path and an observation are read as
    ///   before.
    /// - fails: [`LoweringRefusal::PartialField`] at the member when a
    ///   constructor names no field `l`, naming the first such; the unannotated
    ///   refusal when the position states no answer and no field gives one: the
    ///   family declares no constructor, or the first constructor's field `l`
    ///   is typed by a field before it; the wrong-sort refusal where no
    ///   computation is read; the name's own resolution refusals.
    /// - panics: none.
    ///
    /// # Errors
    /// The selection's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a field of a family of one constructor, typed by its
    ///   position and by its declaration; a field every constructor of a sum
    ///   names at its own position; a field of a parameterised family read at
    ///   the written arguments; a field one constructor lacks; a field typed by
    ///   the field before it, with and without an answer.
    /// - witness: `lower::native::tests::a_data_field_is_the_case_returning_it_1106`
    /// - witness: `lower::native::tests::a_data_field_some_constructor_lacks_is_refused_1106`
    #[spec(ensures: |ret| !matches!(ret, Ok(arity::Planned(true))) || matches!(self.plans.get(site.at.node), Some(&Plan::Projected(_))))]
    pub(super) fn data_field(
        &mut self,
        site: Site,
        pieces: &Pieces,
    ) -> Result<arity::Planned, LoweringRefusal<'source>>
    {
        let unplanned = Ok(arity::Planned(false));
        let Ok((target, selected)) = Self::link(site, &pieces.pieces, site.at.span)
        else {
            return unplanned;
        };
        if !matches!(self.form_at(target)?, Some((_, Former::Name))) {
            return unplanned;
        }
        let frame = site.reading.frame();
        let written = self.scrutinee_type(frame, target)?;
        let Maybe::Present(stated) = written
        else {
            return unplanned;
        };
        let Maybe::Present(Stated::Family { constant, form }) = self.stated_data(frame, written)?
        else {
            return unplanned;
        };
        let Some(data) = self.collected.data.get(form)
        else {
            return unplanned;
        };
        if !data.indices.is_empty() {
            return unplanned;
        }
        let field = self.name_at(selected);
        let mut branches = Vec::with_capacity(data.generators.len());
        for generator in &data.generators {
            let Some(position) = generator.fields.iter().position(|written| {
                matches!(written.named, Maybe::Present(named) if self.name_at(named) == field)
            })
            else {
                return Err(LoweringRefusal::PartialField {
                    span: selected.span,
                    field,
                    constructor: self.name_at(generator.named),
                });
            };
            branches.push((generator.fields.len(), position));
        }
        let typed = if let Some(&answer) = self.answers.get(&site.at.node) {
            Typed::Answered(answer)
        }
        else {
            let (Some(generator), Some(&(_, position))) =
                (data.generators.first(), branches.first())
            else {
                return Err(site.out(FragmentBoundary::Unannotated));
            };
            let earlier: Vec<SurfaceName<'source>> = generator
                .fields
                .iter()
                .take(position)
                .filter_map(|before| match before.named {
                    Maybe::Present(named) => Some(self.name_at(named)),
                    Maybe::Absent(_) => None,
                })
                .collect();
            let Some(declared) = generator.fields.get(position).map(|at| at.ty.node)
            else {
                return Err(site.out(FragmentBoundary::Unannotated));
            };
            if self.spells_any(declared, &earlier) == Spelled(true) {
                return Err(site.out(FragmentBoundary::Unannotated));
            }
            Typed::Field {
                stated,
                declared,
                earlier: position,
                parameters: data.parameters.len(),
            }
        };
        let frame = self.require(site, Produced::Computation)?;
        self.read(target.node, Reading::Value(frame));
        let index = ProjectedIndex(self.projected.len());
        self.projected.push(Projected {
            subject: target.node,
            frame,
            family: constant,
            branches,
            typed,
        });
        self.plan(site, Plan::Projected(index));

        Ok(arity::Planned(true))
    }

    /// Whether some leaf of the syntax under `node` spells one of `names`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: spelled exactly when a node under `node`, `node` itself
    ///   included, has no child and covers the bytes of a name in `names`;
    ///   unspelled when `names` is empty.
    /// - provides: a conservative reading of whether a written type names a
    ///   binder: a name bound inside the type and spelled alike counts too.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — restating it walks the subtree again.
    ///
    /// # Termination
    /// Each round pops one node and pushes its children, which sit strictly
    /// above it in the tree's layout, so the walk visits each node of the
    /// finite subtree once.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a field typed by the field before it, and one typed
    ///   by a closed type, separate the two answers.
    /// - witness: `lower::native::tests::a_data_field_is_the_case_returning_it_1106`
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            linear_search_in_loop,
            reason = "bounded: `names` holds the fields before one constructor's field"
        )
    )]
    fn spells_any(
        &self,
        node: NodeIndex,
        names: &[SurfaceName<'source>],
    ) -> Spelled
    {
        if names.is_empty() {
            return Spelled(false);
        }
        let mut pending = Vec::from([node]);
        while let Some(at) = pending.pop() {
            let mut children = self.tree.children(at).peekable();
            if children.peek().is_none()
                && self.tree.fragment(at).is_some_and(|spelled| {
                    names.iter().any(|name| name.as_ref() == spelled.as_ref())
                })
            {
                return Spelled(true);
            }
            pending.extend(children);
        }
        Spelled(false)
    }

    /// The binder the scrutinee `scrutinee` of a match under `frame` reads,
    /// when it is a name the frame binds intuitionistically.
    ///
    /// # Specification
    /// - requires: `scrutinee` is a match's scrutinee, read under `frame`.
    /// - ensures: the binder [`crate::resolve::Scope::resolve`] finds for the
    ///   name in `frame` when that binder is intuitionistic; the unbound
    ///   absence for any other scrutinee.
    /// - provides: the variable a match's arms read at a constructor.
    /// - fails: the scrutinee's form and resolution refusals.
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoweringRefusal::UnknownMold`] and
    /// [`LoweringRefusal::BudgetExceeded`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a match on a parameter reads its binder, which each
    ///   of its arms reads at a constructor.
    /// - witness: `lower::native::tests::a_match_in_an_arm_reads_the_answer_at_the_arm_s_constructor_2994`
    #[spec(ensures: |ret| match ret {
        | Ok(Maybe::Present(binder)) => self.scope.zone(binder) == Zone::Intuitionistic,
        | Ok(Maybe::Absent(_)) | Err(_) => true,
    })]
    fn scrutinee_binder(
        &mut self,
        frame: Frame,
        scrutinee: Placed,
    ) -> Result<Maybe<ScopeId, settled::Absent>, LoweringRefusal<'source>>
    {
        if !matches!(self.form_at(scrutinee)?, Some((_, Former::Name))) {
            return Ok(Maybe::Absent(settled::Absent::Unbound));
        }
        let name = self.name_at(scrutinee);
        Ok(match self.scope.resolve(frame, name, &mut self.fuel)? {
            Maybe::Present(bound) if bound.zone == Zone::Intuitionistic => {
                Maybe::Present(bound.binder)
            },
            Maybe::Present(_) | Maybe::Absent(_) => Maybe::Absent(settled::Absent::Unbound),
        })
    }

    /// The arm `arm`, then each arm the answer was passed into before it, from
    /// the innermost out.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: `arm`'s reading first when it is stored, then each stored
    ///   reading's outer arm in turn while it stands before the one naming it.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Termination
    /// Each step moves to a position strictly before the last, so the walk
    /// ends within the store's length.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a match two arms deep reads the answer at both arms'
    ///   constructors.
    /// - witness: `lower::native::tests::a_match_in_an_arm_reads_the_answer_at_the_arm_s_constructor_2994`
    #[spec(ensures: |ret| ret.len() <= self.arms.len())]
    fn arms_outward(
        &self,
        arm: Maybe<ArmIndex, passed::Absent>,
    ) -> Vec<&ArmReading>
    {
        let mut chain = Vec::new();
        let mut next = arm;
        let mut bound = self.arms.len();
        while let Maybe::Present(ArmIndex(at)) = next
            && at < bound
            && let Some(reading) = self.arms.get(at)
        {
            chain.push(reading);
            bound = at;
            next = reading.outer;
        }
        chain
    }

    /// The alternatives of the arm pattern `pattern`: its or-pattern's
    /// operands in source order, flattened, or the pattern itself.
    ///
    /// # Specification
    /// - requires: `pattern` is an arm's pattern of the match at `site`.
    /// - ensures: at least one alternative, in source order.
    /// - fails: [`LoweringRefusal::UnknownMold`] and an or-pattern's repair.
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoweringRefusal::UnknownMold`] and [`LoweringRefusal::MalformedForm`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a three-way or-pattern keeps its alternatives in
    ///   order.
    /// - witness: `lower::native::tests::an_or_pattern_settles_each_alternative`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |alternatives| !alternatives.is_empty()))]
    fn alternatives(
        &mut self,
        pattern: Placed,
    ) -> Result<Vec<Placed>, LoweringRefusal<'source>>
    {
        let mut alternatives = Vec::new();
        let mut pending = Vec::from([pattern]);
        let mut pieces = Pieces::new();
        while let Some(next) = pending.pop() {
            self.fuel.spend()?;
            let Some(node) = self.tree.node(next.node)
            else {
                continue;
            };
            let Shape::Form { name, .. } = shape_of(self.pbg, node)?
            else {
                alternatives.push(next);
                continue;
            };
            if name != FormName::OR_PATTERN {
                alternatives.push(next);
                continue;
            }
            read_pieces(self.pbg, self.tree, next.node, &mut pieces)?;
            if let Maybe::Present(repaired) = pieces.repair {
                return Err(repaired.refusal(FormName::OR_PATTERN));
            }
            for piece in pieces.pieces.iter().rev() {
                if let Piece::Operand(alternative) = *piece {
                    pending.push(alternative);
                }
            }
        }
        if alternatives.is_empty() {
            alternatives.push(pattern);
        }

        Ok(alternatives)
    }

    /// The loop an arm's whole pattern names, when it is a name a loop binds.
    ///
    /// # Specification
    /// - requires: `pattern` is an arm's pattern of the match at `site`.
    /// - ensures: the position of the loop's words among the collected words
    ///   and the loop's position among its words' cells exactly when the
    ///   pattern is a name that resolves to a loop's binding; the unnamed
    ///   absence otherwise. A name no loop of the enclosing modules declares is
    ///   a binder and is never resolved, so a pattern variable spelled as a
    ///   later member or a recursive binder binds as it always has.
    /// - fails: the name's resolution refusals, for a name a loop declares, and
    ///   the tree's molds'.
    /// - panics: none.
    ///
    /// # Errors
    /// As `- fails:`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — `loop` names the circle's loop, and `x` binds.
    /// - witness: `lower::native::tests::a_loop_arm_follows_the_constructors_branches`
    #[spec(ensures: |ret| ret.as_ref().ok().is_none_or(|found| matches!(found, Maybe::Absent(_)) || !self.collected.words.is_empty()))]
    fn loop_named(
        &mut self,
        site: Site,
        pattern: Placed,
    ) -> Result<Maybe<NamedLoop, constructed::Absent>, LoweringRefusal<'source>>
    {
        if !matches!(self.form_at(pattern)?, Some((name, _)) if name == FormName::IDENTIFIER)
            || self.declares_a_loop(pattern, self.name_at(pattern))? == Declared::Binder
        {
            return Ok(Maybe::Absent(constructed::Absent::Unnamed));
        }
        Ok(match self.loop_letter(site, pattern, Inverse(false))? {
            Maybe::Present(Constructor {
                form: Generators::Words(words),
                tag,
                ..
            }) => gandr_core_term::FreeCells::generator(gandr_core_term::ConstructorTag::from(tag))
                .map_or(Maybe::Absent(constructed::Absent::Unnamed), |generator| {
                    Maybe::Present(NamedLoop { words, generator })
                }),
            Maybe::Present(_) => Maybe::Absent(constructed::Absent::Unnamed),
            Maybe::Absent(reason) => Maybe::Absent(reason),
        })
    }

    /// Whether a loop named `name` is declared in a module enclosing the
    /// declaration that owns `at`, read off the collected names without
    /// resolving: a source with no loop answers at once.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: [`Declared::Loop`] exactly when some module on the chain from
    ///   the owner's container out to the top level binds `name` to a loop's
    ///   slot.
    /// - fails: [`LoweringRefusal::BudgetExceeded`] when the walk out spends
    ///   the fuel.
    /// - panics: none.
    ///
    /// # Errors
    /// As `- fails:`.
    ///
    /// # Termination
    /// - reason: the `loop` steps out one module per iteration, each step
    ///   spending fuel, never recursing.
    /// - measure: the modules between the owner and the top level.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — `loop` names the circle's loop at the top level and
    ///   inside a module, while `kept` and `later` bind as pattern variables
    ///   beside a later member of the same name; a name read as a loop there
    ///   refuses a punned pattern.
    /// - witness: `lower::native::tests::a_loop_arm_follows_the_constructors_branches`
    #[spec(ensures: |ret| ret.as_ref().ok() != Some(&Declared::Loop) || !self.collected.words.is_empty())]
    fn declares_a_loop(
        &mut self,
        at: Placed,
        name: SurfaceName<'source>,
    ) -> Result<Declared, LoweringRefusal<'source>>
    {
        if self.collected.words.is_empty() {
            return Ok(Declared::Binder);
        }
        let Maybe::Present(own) = self.collected.owner_of(at.node)
        else {
            return Ok(Declared::Binder);
        };
        let mut container = self.collected.slots.get(usize::from(own)).map_or_else(
            || self.collected.top(at.span.start()),
            |slot| slot.container,
        );
        let is_loop = |target: SlotIndex| {
            matches!(
                self.collected
                    .slots
                    .get(usize::from(target))
                    .map(|slot| slot.definition),
                Some(Maybe::Present(Half {
                    operand: Operand::Loop { .. },
                    ..
                }))
            )
        };
        loop {
            self.fuel.spend()?;
            if let Some(&target) = self.collected.by_name.get(&(container, name))
                && is_loop(target)
            {
                return Ok(Declared::Loop);
            }
            let module = match container {
                crate::module::Container::Module(module) => module,
                crate::module::Container::TopLevel(source) => {
                    let Ok(Maybe::Present((target, import))) =
                        self.collected.imported_slot(source, name)
                    else {
                        return Ok(Declared::Binder);
                    };
                    if !is_loop(target) {
                        return Ok(Declared::Binder);
                    }
                    self.collected.reach(import);
                    return Ok(Declared::Loop);
                },
            };
            container = self
                .collected
                .structures
                .get(usize::from(module))
                .map_or_else(
                    || self.collected.top(at.span.start()),
                    |structure| structure.container,
                );
        }
    }

    /// The loop arms `written` of the match at `site`, in the order the loop
    /// branches of the tree `tests`' root follow its constructors' branches.
    ///
    /// # Specification
    /// - requires: `tests` is the match's compiled tree and `written` its loop
    ///   arms, in source order.
    /// - ensures: none for no loop arm; otherwise one arm per loop of the root
    ///   switch's sort, words by their position among the collected words and
    ///   loops in written order.
    /// - fails: [`LoweringRefusal::NonExhaustiveMatch`] when the root is no
    ///   switch on the scrutinee's constructors or a loop of its sort has no
    ///   arm; [`LoweringRefusal::DuplicateDefinition`] at a loop's second arm;
    ///   the wrong-sort refusal at an arm for a loop of another sort.
    /// - panics: none.
    ///
    /// # Errors
    /// As `- fails:`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the circle's loop arm follows its point's branch, and
    ///   a loop arm over a case with no loop arm owed is refused.
    /// - witness: `lower::native::tests::a_loop_arm_follows_the_constructors_branches`
    #[spec(captures: count = written.len(), ensures: |ret| ret.as_ref().map_or(true, |ordered| ordered.len() <= count))]
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            linear_search_in_loop,
            reason = "bounded: `owed` holds the loop arms one family's words declare"
        )
    )]
    fn loop_arms(
        &self,
        site: Site,
        tests: &[Test],
        written: Vec<LoopArm>,
    ) -> Result<Vec<LoopArm>, LoweringRefusal<'source>>
    {
        if written.is_empty() {
            return Ok(written);
        }
        let uncovered = LoweringRefusal::NonExhaustiveMatch { span: site.at.span };
        let Some(&Test::Data {
            level,
            family: Maybe::Present(family),
            ..
        }) = tests.first()
        else {
            return Err(uncovered);
        };
        if level != TreeLevel::default() {
            return Err(uncovered);
        }
        let mut owed = Vec::new();
        for (index, words) in self.collected.words.iter().enumerate() {
            let sort = self
                .collected
                .data
                .get(words.family)
                .and_then(|form| self.collected.slots.get(usize::from(form.slot)))
                .map(|slot| slot.constant);
            if sort == Some(family) {
                owed.extend((0 .. words.loops.len()).map(|generator| (index, generator)));
            }
        }
        if let Some(stray) = written
            .iter()
            .find(|arm| !owed.contains(&(arm.words, arm.generator)))
        {
            return Err(LoweringRefusal::OutOfFragment {
                span: stray.named.span,
                form: FormName::CASE,
                sort: site.reading.sort(),
                boundary: FragmentBoundary::WrongSort,
            });
        }
        let mut ordered = Vec::with_capacity(owed.len());
        for &(words, generator) in &owed {
            let mut matching = written
                .iter()
                .filter(|arm| arm.words == words && arm.generator == generator);
            let Some(&arm) = matching.next()
            else {
                return Err(uncovered);
            };
            if let Some(again) = matching.next() {
                return Err(LoweringRefusal::DuplicateDefinition {
                    span: again.named.span,
                    name: SurfaceName::from(self.text_at(again.named)),
                    first: arm.named.span,
                });
            }
            ordered.push(arm);
        }

        Ok(ordered)
    }

    /// Read the or-free pattern `root` of the match at `site` into
    /// `patterns`, numbering its variables into `named`; `stated` is the type
    /// the scrutinee's position states.
    ///
    /// # Specification
    /// - requires: `root` is an alternative of an arm of the match at `site`.
    /// - ensures: the root's position in `patterns`; every part after the
    ///   pattern holding it; each name bound once, numbered in source order.
    /// - fails: a pattern the fragment does not read, by its own name; a
    ///   constructor no earlier family declares, as unresolved; a constructor
    ///   applied to other than its arity; a sum pattern whose position states
    ///   no sum, as unannotated; a variable bound twice; a repair;
    ///   [`LoweringRefusal::WithoutK`] for `here`, reflexivity as a pattern.
    /// - panics: none.
    ///
    /// # Errors
    /// The pattern's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the match witnesses read every admitted shape and
    ///   decline the others.
    /// - witness: `lower::native::tests::patterns_outside_the_fragment_are_declined_by_name`
    /// - witness: `lower::native::tests::nested_constructor_patterns_compile_to_nested_cases`
    /// - witness: `lower::native::tests::telescope_patterns_split_and_project`
    /// - witness: `lower::identity::tests::matching_reflexivity_is_refused_as_k`
    #[spec(
        captures: before = patterns.shapes.len(),
        ensures: |ret| ret.as_ref().map_or(true, |&root| root == PatternAt(before) && patterns.shapes.len() > before),
    )]
    fn pattern(
        &mut self,
        site: Site,
        root: Placed,
        stated: Maybe<NodeIndex, binder_type::Absent>,
        patterns: &mut Written,
        named: &mut Vec<Placed>,
    ) -> Result<PatternAt, LoweringRefusal<'source>>
    {
        let first = PatternAt(patterns.shapes.len());
        patterns.shapes.push((root, Matcher::Wild));
        let mut work = Vec::from([Queued {
            at: root,
            slot: first,
            stated,
            related: Maybe::Absent(related::Absent::Otherwise),
            punned: Punned(false),
        }]);
        let mut pieces = Pieces::new();
        while let Some(queued) = work.pop() {
            self.fuel.spend()?;
            let shape = if queued.punned.0 {
                self.binder(queued.at, named)?
            }
            else {
                self.pattern_shape(site, queued, &mut pieces, patterns, named, &mut work)?
            };
            if let Some(held) = patterns.shapes.get_mut(queued.slot.0) {
                held.1 = shape;
            }
        }

        Ok(first)
    }

    /// The binder the name written at `at` makes, numbered into `named`.
    ///
    /// # Specification
    /// - requires: `at` is a pattern name or a punned label of one pattern.
    /// - ensures: the binder of the next arm variable.
    /// - fails: [`LoweringRefusal::DuplicateDefinition`] for a name already
    ///   bound in the pattern.
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoweringRefusal::DuplicateDefinition`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a name and a punned label each bind once.
    /// - witness: `lower::native::tests::telescope_patterns_split_and_project`
    #[spec(captures: before = named.len(), ensures: |ret| ret.is_err() || (named.len() == before.saturating_add(1) && matches!(ret, Ok(Matcher::Binder(variable)) if variable.0 == before)))]
    fn binder(
        &self,
        at: Placed,
        named: &mut Vec<Placed>,
    ) -> Result<Matcher, LoweringRefusal<'source>>
    {
        let spelled = self.text_at(at);
        if let Some(&earlier) = named
            .iter()
            .find(|&&binder| self.text_at(binder) == spelled)
        {
            return Err(LoweringRefusal::DuplicateDefinition {
                span: at.span,
                name: SurfaceName::from(spelled),
                first: earlier.span,
            });
        }
        named.push(at);

        Ok(Matcher::Binder(VariableAt(named.len().saturating_sub(1))))
    }

    /// The shape of the queued pattern, its field patterns allocated and
    /// queued on `work`.
    ///
    /// # Specification
    /// - requires: as [`Self::pattern`]; `pieces` is scratch.
    /// - ensures: as [`Self::pattern`], for one pattern; a telescope or tuple
    ///   pattern's components and a sum pattern's payload are queued with the
    ///   component's or summand's type the queued pattern's stated type writes,
    ///   when it writes one.
    /// - fails: as [`Self::pattern`].
    /// - panics: none.
    ///
    /// # Errors
    /// As [`Self::pattern`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::pattern`].
    /// - witness: `lower::native::tests::patterns_outside_the_fragment_are_declined_by_name`
    /// - witness: `lower::native::tests::telescope_patterns_split_and_project`
    /// - witness: `lower::native::tests::sum_patterns_case_on_the_stated_arity`
    #[spec(captures: before = patterns.shapes.len(), ensures: patterns.shapes.len() >= before)]
    fn pattern_shape(
        &mut self,
        site: Site,
        queued: Queued,
        pieces: &mut Pieces,
        patterns: &mut Written,
        named: &mut Vec<Placed>,
        work: &mut Vec<Queued>,
    ) -> Result<Matcher, LoweringRefusal<'source>>
    {
        let at = queued.at;
        let Some(node) = self.tree.node(at.node)
        else {
            return Ok(Matcher::Wild);
        };
        let name = match shape_of(self.pbg, node)? {
            Shape::Form { name, .. } => name,
            Shape::Repair(repair) => {
                return Err(LoweringRefusal::MalformedForm {
                    span: at.span,
                    form: FormName::CASE,
                    fault: FormFault::Repaired(repair),
                });
            },
            Shape::Root | Shape::Layout => return Ok(Matcher::Wild),
        };
        let here = Site {
            at,
            name,
            reading: site.reading,
        };
        if name == FormName::WILDCARD {
            return Ok(Matcher::Wild);
        }
        if name == FormName::HOLE {
            return Ok(Matcher::Hole(self.hole(at)?));
        }
        if name == FormName::UNIT {
            // `unit` is the empty product's pattern, `#{}` spelled as the
            // value it matches.
            return self.components(here, queued, &[], patterns, work);
        }
        if name == FormName::IDENTIFIER {
            if self.text_at(at).as_ref() == super::identity::HERE {
                return match self.collected.words.len() {
                    0_usize => Err(LoweringRefusal::WithoutK { span: at.span }),
                    1_usize => Ok(Matcher::Constructor {
                        form: Generators::Words(0),
                        tag: 0,
                        fields: allocated(patterns, work, &[]),
                    }),
                    _ => Err(here.out(FragmentBoundary::Unannotated)),
                };
            }
            // A loop's name in a pattern names the loop, never a variable; a
            // loop is matched only as an arm's whole pattern.
            if let Maybe::Present(_) = self.loop_named(site, at)? {
                return Err(here.out(FragmentBoundary::Unadmitted(Unbuilt::LoopPattern)));
            }
            if let Maybe::Present(stated) = queued.stated {
                let _first = self.pattern_stated.insert(at.node, stated);
            }
            return self.binder(at, named);
        }
        if name == FormName::NUMBER {
            return integer(here, self.text_at(at));
        }
        if name == FormName::BOOLEAN {
            return Ok(Matcher::Boolean(self.text_at(at).as_ref() == "true"));
        }
        if name == FormName::CONSTRUCTOR {
            let found = self.constructor_named(site, SurfaceName::from(self.text_at(at)));
            return self.constructor_pattern(here, at, found, &[], patterns, work);
        }
        read_pieces(self.pbg, self.tree, at.node, pieces)?;
        if let Maybe::Present(repaired) = pieces.repair {
            return Err(repaired.refusal(here.name));
        }
        if name == FormName::CONS_PATTERN {
            return self.cons_pattern(site, here, queued.slot, pieces, patterns, work);
        }
        if name == FormName::LIST_PATTERN {
            return self.list_pattern(here, queued, pieces, patterns, work);
        }
        if name == FormName::AS_PATTERN {
            let mut cursor = Cursor::new(&pieces.pieces, at.span);
            let inner = here.one(cursor.operands())?;
            closed(here, &mut cursor, TileName::AS)?;
            let Maybe::Present(alias) = cursor.tile(TileName::IDENTIFIER)
            else {
                return Err(here.fault(cursor.here(), FormFault::MisplacedTile));
            };
            exhausted(here, &cursor)?;
            let parts = allocated(patterns, work, &[
                Queued {
                    at: inner,
                    slot: UNWRITTEN,
                    ..queued
                },
                Queued {
                    at: alias,
                    slot: UNWRITTEN,
                    punned: Punned(true),
                    ..queued
                },
            ]);
            let part = |offset: usize| {
                patterns
                    .parts
                    .get(parts.start.saturating_add(offset))
                    .copied()
                    .unwrap_or(UNWRITTEN)
            };
            return Ok(Matcher::Alias {
                inner: part(0),
                alias: part(1),
            });
        }
        if name == FormName::LITERAL_PATTERN {
            return match pieces.pieces.first() {
                Some(&Piece::Tile { label, at: tile }) if label == TileName::NUMBER => {
                    integer(here, self.text_at(tile))
                },
                Some(&Piece::Tile { label, .. }) if label == TileName::TRUE => {
                    Ok(Matcher::Boolean(true))
                },
                Some(&Piece::Tile { label, .. }) if label == TileName::FALSE => {
                    Ok(Matcher::Boolean(false))
                },
                _ => Err(here.out(FragmentBoundary::Unadmitted(Unbuilt::LiteralPattern))),
            };
        }
        if name == FormName::CONSTRUCTOR_PATTERN {
            let mut cursor = Cursor::new(&pieces.pieces, at.span);
            let Maybe::Present(first) = cursor.tile(TileName::CONSTRUCTOR)
            else {
                return Err(here.fault(cursor.here(), FormFault::MisplacedTile));
            };
            // `Family.Constructor` names its family first, and `S.op` its
            // theory, whose terms the operation constructs.
            let (family, head) = match cursor.tile(TileName::DOT) {
                Maybe::Present(_) => {
                    let head = match cursor.tile(TileName::CONSTRUCTOR) {
                        Maybe::Present(head) => head,
                        Maybe::Absent(_) => match cursor.tile(TileName::IDENTIFIER) {
                            Maybe::Present(head) => head,
                            Maybe::Absent(_) => {
                                return Err(here.fault(cursor.here(), FormFault::MisplacedTile));
                            },
                        },
                    };
                    (Some(first), head)
                },
                Maybe::Absent(_) => (None, first),
            };
            let mut fields = Vec::new();
            if let Maybe::Present(_) = cursor.tile(TileName::PAREN_OPEN) {
                while let Maybe::Absent(_) = cursor.tile(TileName::PAREN_CLOSE) {
                    fields.push(here.one(cursor.operands())?);
                    if let Maybe::Absent(_) = cursor.tile(TileName::COMMA) {
                        closed(here, &mut cursor, TileName::PAREN_CLOSE)?;
                        break;
                    }
                }
            }
            exhausted(here, &cursor)?;
            let name = SurfaceName::from(self.text_at(head));
            let found = match family {
                Some(family) => self.qualified_constructor(site, family, name)?,
                None => self.constructor_named(site, name),
            };
            let shape = self.constructor_pattern(here, head, found, &fields, patterns, work)?;
            patterns
                .spelled
                .push((queued.slot, head.span, PatternReading::Constructor));
            return Ok(shape);
        }
        if name == FormName::TUPLE_PATTERN {
            let mut cursor = Cursor::new(&pieces.pieces, at.span);
            closed(here, &mut cursor, TileName::PAREN_OPEN)?;
            let entries = Self::tuple_entries(here, &mut cursor)?;
            return self.components(here, queued, &entries, patterns, work);
        }
        if name == FormName::TELESCOPE_PATTERN {
            let mut cursor = Cursor::new(&pieces.pieces, at.span);
            closed(here, &mut cursor, TileName::RECORD)?;
            let entries = self.pattern_entries(here, &mut cursor)?;
            return self.components(here, queued, &entries, patterns, work);
        }
        if name == FormName::LABELLED_SUM_PATTERN {
            let mut cursor = Cursor::new(&pieces.pieces, at.span);
            closed(here, &mut cursor, TileName::PLUS)?;
            closed(here, &mut cursor, TileName::BRACE_OPEN)?;
            let key = self.dotted(here, &mut cursor)?;
            closed(here, &mut cursor, TileName::EQUALS)?;
            let payload = here.one(cursor.operands())?;
            closed(here, &mut cursor, TileName::BRACE_CLOSE)?;
            exhausted(here, &cursor)?;
            return self.injected(here, queued, key, payload, patterns, work);
        }

        Err(here.out(FragmentBoundary::Unadmitted(super::unread_pattern(name))))
    }

    /// The shape of the constructor pattern at `here`, `found` the constructor
    /// resolved for the name spelled at `head`, its field patterns `fields`
    /// allocated and queued.
    ///
    /// # Specification
    /// - requires: `here` is a constructor pattern; `found` is the resolution
    ///   of the name at `head`, under the family written before it when one is.
    /// - ensures: the constructor, its fields a fresh stretch of the part
    ///   store, each field queued on `work` after its slot is allocated.
    /// - fails: the unresolved-name refusal when `found` is absent; the arity
    ///   refusal for other than its arity.
    /// - panics: none.
    ///
    /// # Errors
    /// The pattern's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::pattern`].
    /// - witness: `lower::native::tests::nested_constructor_patterns_compile_to_nested_cases`
    /// - witness: `lower::native::tests::a_qualified_constructor_names_its_family_s_constructor_2428`
    #[spec(captures: before = work.len(), ensures: |ret| ret.is_err() || work.len() == before.saturating_add(fields.len()))]
    fn constructor_pattern(
        &self,
        here: Site,
        head: Placed,
        found: Maybe<Constructor, constructed::Absent>,
        fields: &[Placed],
        patterns: &mut Written,
        work: &mut Vec<Queued>,
    ) -> Result<Matcher, LoweringRefusal<'source>>
    {
        let name = SurfaceName::from(self.text_at(head));
        let Maybe::Present(constructor) = found
        else {
            return Err(LoweringRefusal::UnresolvedName {
                span: head.span,
                name,
            });
        };
        if fields.len() != constructor.arity {
            return Err(here.out(FragmentBoundary::Arity(OperandCount::from(fields.len()))));
        }
        let queued: Vec<Queued> = fields
            .iter()
            .map(|&field| Queued {
                at: field,
                slot: UNWRITTEN,
                stated: Maybe::Absent(binder_type::Absent::Untyped),
                related: Maybe::Absent(related::Absent::Otherwise),
                punned: Punned(false),
            })
            .collect();

        Ok(Matcher::Constructor {
            form: constructor.form,
            tag: constructor.tag,
            fields: allocated(patterns, work, &queued),
        })
    }

    /// The shape of the word pattern `g ∷ p` or `back(g) ∷ p` at `here`, the
    /// pattern at `slot`, read from `pieces`, its rest pattern `p` allocated
    /// and queued.
    ///
    /// # Specification
    /// - requires: `here` is a cons pattern of the match at `site`, `slot` its
    ///   place in `patterns` and `pieces` its reading.
    /// - ensures: the constructor of the words of the loop `g` names whose tag
    ///   is its letter, or its inverse under `back`, as [`Self::loop_letter`]
    ///   reads it, its one field the rest queued on `work`; the letter `g`, and
    ///   the name `back` that inverts it, spelled at `slot` as a word of one
    ///   letter, so the parentheses around `g`, tiles of the pattern, answer
    ///   the pattern as a constructor pattern's do.
    /// - fails: the unadmitted refusal for a head other than `back` applied to
    ///   a name; the unresolved-name refusal for a name that is no loop; a tile
    ///   out of place.
    /// - panics: none.
    ///
    /// # Errors
    /// The pattern's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a letter and an inverse match their constructors, and
    ///   a name that is no loop is refused.
    /// - witness: `lower::native::tests::a_word_conses_its_letters_and_matches_them`
    /// - witness: `lower::native::tests::a_match_keeps_its_patterns_beside_its_tree`
    #[spec(captures: before = work.len(), ensures: |ret| ret.is_err() || work.len() == before.saturating_add(1))]
    fn cons_pattern(
        &mut self,
        site: Site,
        here: Site,
        slot: PatternAt,
        pieces: &Pieces,
        patterns: &mut Written,
        work: &mut Vec<Queued>,
    ) -> Result<Matcher, LoweringRefusal<'source>>
    {
        let mut cursor = Cursor::new(&pieces.pieces, here.at.span);
        let Maybe::Present(head) = cursor.tile(TileName::IDENTIFIER)
        else {
            return Err(here.fault(cursor.here(), FormFault::MisplacedTile));
        };
        let (cell, inverse) = if let Maybe::Present(_) = cursor.tile(TileName::PAREN_OPEN) {
            let Maybe::Present(cell) = cursor.tile(TileName::IDENTIFIER)
            else {
                return Err(here.fault(cursor.here(), FormFault::MisplacedTile));
            };
            let Maybe::Present(_) = cursor.tile(TileName::PAREN_CLOSE)
            else {
                return Err(here.fault(cursor.here(), FormFault::MisplacedTile));
            };
            if self.text_at(head).as_ref() != super::identity::BACK {
                return Err(here.out(FragmentBoundary::Unadmitted(Unbuilt::ConsPattern)));
            }
            patterns
                .spelled
                .push((slot, head.span, PatternReading::Matched));
            (cell, Inverse(true))
        }
        else {
            (head, Inverse(false))
        };
        patterns
            .spelled
            .push((slot, cell.span, PatternReading::Matched));
        closed(here, &mut cursor, TileName::CONS)?;
        let rest = here.one(cursor.operands())?;
        exhausted(here, &cursor)?;
        let Maybe::Present(constructor) = self.loop_letter(site, cell, inverse)?
        else {
            return Err(LoweringRefusal::UnresolvedName {
                span: cell.span,
                name: self.name_at(cell),
            });
        };
        let queued = [Queued {
            at: rest,
            slot: UNWRITTEN,
            stated: Maybe::Absent(binder_type::Absent::Untyped),
            related: Maybe::Absent(related::Absent::Otherwise),
            punned: Punned(false),
        }];

        Ok(Matcher::Constructor {
            form: constructor.form,
            tag: constructor.tag,
            fields: allocated(patterns, work, &queued),
        })
    }

    /// The shape of the list pattern `[p, …, q]` or `[p, …, q, ..r]` at
    /// `here`, the pattern `queued` holds, read from `pieces`: the cell of
    /// `p` over the rest of the list, each later cell and the closing empty
    /// list allocated in turn, every element and the rest queued in source
    /// order.
    ///
    /// # Specification
    /// - requires: `here` is a list pattern of a match, `pieces` its reading.
    /// - ensures: the empty list for `[]`; for `[..r]`, `r` queued into the
    ///   pattern's own slot and the wildcard it replaces; otherwise the cell of
    ///   the first element, whose tail is the cell of the next and so on, the
    ///   last tail the rest `r` or the empty list. Each element is queued at
    ///   the element type a stated `List(T)` writes and the rest at the list's
    ///   own stated type; every implied cell and empty list after the first
    ///   stands at the list's syntax and is recorded as implied.
    /// - fails: a tile out of place.
    /// - panics: none.
    ///
    /// # Errors
    /// The pattern's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the empty list, a list of two elements and a list
    ///   with a rest each compile to the list cases they write, read back out
    ///   of the arena.
    /// - witness: `lower::native::tests::list_patterns_case_on_the_native_list`
    #[spec(
        captures: before = work.len(),
        ensures: |ret| ret.as_ref().map_or(true, |shape| matches!(*shape, Matcher::Nil | Matcher::Cell { .. } | Matcher::Wild) && work.len() >= before),
    )]
    fn list_pattern(
        &mut self,
        here: Site,
        queued: Queued,
        pieces: &Pieces,
        patterns: &mut Written,
        work: &mut Vec<Queued>,
    ) -> Result<Matcher, LoweringRefusal<'source>>
    {
        let mut cursor = Cursor::new(&pieces.pieces, here.at.span);
        closed(here, &mut cursor, TileName::BRACKET_OPEN)?;
        let mut elements = Vec::new();
        let mut rest = None;
        loop {
            if let Maybe::Present(_) = cursor.tile(TileName::BRACKET_CLOSE) {
                break;
            }
            if let Maybe::Present(_) = cursor.tile(TileName::DOT_DOT) {
                rest = Some(here.one(cursor.operands())?);
                closed(here, &mut cursor, TileName::BRACKET_CLOSE)?;
                break;
            }
            elements.push(here.one(cursor.operands())?);
            if let Maybe::Absent(_) = cursor.tile(TileName::COMMA) {
                closed(here, &mut cursor, TileName::BRACKET_CLOSE)?;
                break;
            }
        }
        exhausted(here, &cursor)?;
        // The parse may read a closing `..p` as the rest pattern standing as
        // the last element; it is the list's rest all the same.
        if rest.is_none()
            && let Some(&last) = elements.last()
            && let Some(node) = self.tree.node(last.node)
            && let Shape::Form { name, .. } = shape_of(self.pbg, node)?
            && name == FormName::REST_PATTERN
        {
            let mut inner = Pieces::new();
            read_pieces(self.pbg, self.tree, last.node, &mut inner)?;
            if let Maybe::Present(repaired) = inner.repair {
                return Err(repaired.refusal(name));
            }
            let mut cursor = Cursor::new(&inner.pieces, last.span);
            closed(here, &mut cursor, TileName::DOT_DOT)?;
            rest = Some(here.one(cursor.operands())?);
            exhausted(here, &cursor)?;
            let _rest = elements.pop();
        }
        let element = self.listed(queued.stated)?;
        let mut pending = Vec::with_capacity(elements.len().saturating_add(1));
        let mut shape = Matcher::Nil;
        let mut cell = queued.slot;
        let last = elements.len().saturating_sub(1);
        for (index, &written) in elements.iter().enumerate() {
            // The head stands at its element; the tail at the rest when it is
            // the rest, and else at the list, a cell or empty list implied.
            let tail_at = match rest {
                Some(rest) if index == last => rest,
                Some(_) | None => here.at,
            };
            let start = patterns.parts.len();
            let head = PatternAt(patterns.shapes.len());
            patterns.shapes.push((written, Matcher::Wild));
            patterns.parts.push(head);
            let tail = PatternAt(patterns.shapes.len());
            patterns.shapes.push((tail_at, Matcher::Nil));
            patterns.parts.push(tail);
            pending.push(Queued {
                at: written,
                slot: head,
                stated: element,
                ..queued
            });
            let fields = Stretch {
                start,
                end: patterns.parts.len(),
            };
            if cell == queued.slot {
                shape = Matcher::Cell { fields };
            }
            else if let Some(held) = patterns.shapes.get_mut(cell.0) {
                held.1 = Matcher::Cell { fields };
            }
            cell = tail;
            if tail_at == here.at {
                patterns.implied.push(tail);
            }
        }
        if let Some(rest) = rest {
            pending.push(Queued {
                at: rest,
                slot: cell,
                ..queued
            });
            if cell == queued.slot {
                shape = Matcher::Wild;
            }
        }
        work.extend(pending.into_iter().rev());

        Ok(shape)
    }

    /// The element type the stated list type `stated` writes, `T` of
    /// `List(T)`.
    ///
    /// # Specification
    /// - requires: nothing beyond a well-formed tree.
    /// - ensures: the operand of a stated `List(T)`, its parentheses stripped;
    ///   untyped for any other stated type and for none.
    /// - fails: the walk's refusal reading the stated type.
    /// - panics: none.
    ///
    /// # Errors
    /// The walk's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::list_pattern`].
    /// - witness: `lower::native::tests::list_patterns_case_on_the_native_list`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |element| matches!(stated, Maybe::Present(_)) || matches!(*element, Maybe::Absent(_))))]
    fn listed(
        &mut self,
        stated: Maybe<NodeIndex, binder_type::Absent>,
    ) -> Result<Maybe<NodeIndex, binder_type::Absent>, LoweringRefusal<'source>>
    {
        let Maybe::Present(stated) = stated
        else {
            return Ok(stated);
        };
        if let Maybe::Present(typed) = self.unwrapped(stated)?
            && typed.former == Former::TypeApplication
            && typed.keyword.is_some_and(|head| {
                type_former(self.name_at(head)) == Maybe::Present(TypeFormer::List)
            })
            && let [element] = typed.operands[..]
        {
            return Ok(Maybe::Present(element));
        }

        Ok(Maybe::Absent(binder_type::Absent::Untyped))
    }

    /// The tuple or record shape of a telescope or tuple pattern's
    /// `entries`, each component queued with the type `queued` states for
    /// it.
    ///
    /// # Specification
    /// - requires: `entries` are the entries of the pattern `queued` holds at
    ///   `here`.
    /// - ensures: at a scrutinee written with a dependent record, labelled
    ///   entries and positional ones of its arity are its nested pairs, as
    ///   [`Self::dependent_components`] reads them; at one written as an
    ///   equivalence or a quasi-inverse, as [`Self::stated_relation`] reads it,
    ///   or at a record nested in one, so are those of the record it
    ///   abbreviates, and at one written `Model(T)` whose record nests pairs,
    ///   as [`Self::stated_bundle`] reads it, those of the record the signature
    ///   states, each component unstated; at one stated as a record of one or
    ///   more labelled entries, positional entries of its arity are its fields
    ///   in the order the record writes them; otherwise positional entries, in
    ///   index order, make a tuple and labelled ones a record of their labels;
    ///   each component queued with the positional type of the same place, or
    ///   the labelled type of the same label, of the telescope type `queued`
    ///   states, when it states one.
    /// - fails: the entries' arrangement refusals; the stated type's own
    ///   malformation; the unresolved-name refusal for a label the dependent
    ///   record lacks.
    /// - panics: none.
    ///
    /// # Errors
    /// The pattern's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — positional, reordered and labelled telescope
    ///   patterns, a tuple pattern, patterns at a dependent record, patterns at
    ///   a relation, and patterns at a theory's models.
    /// - witness: `lower::native::tests::telescope_patterns_split_and_project`
    /// - witness: `lower::native::tests::a_pattern_at_a_dependent_record_splits_it_under_its_motive`
    /// - witness: `lower::identity::tests::a_pattern_at_a_relation_splits_its_record`
    /// - witness: `tests::modules::models::a_pattern_at_a_model_type_splits_its_fields`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |shape| matches!(*shape, Matcher::Tuple { .. } | Matcher::Record { .. })))]
    fn components(
        &mut self,
        here: Site,
        queued: Queued,
        entries: &[arity::Entry<'source>],
        patterns: &mut Written,
        work: &mut Vec<Queued>,
    ) -> Result<Matcher, LoweringRefusal<'source>>
    {
        let Queued {
            stated, related, ..
        } = queued;
        let form = match stated {
            Maybe::Present(node) => {
                self.stated_form(here, node, Former::TelescopeType, arity::Thunked(false))?
            },
            Maybe::Absent(_) => Maybe::Absent(arity::stated_labels::Absent::Otherwise),
        };
        let arranged = arity::arrange(here, entries.to_vec())?;
        let links = match form {
            Maybe::Present((_, ref typed)) => self.dependent_links(typed)?,
            Maybe::Absent(reason) => Maybe::Absent(reason),
        };
        if let Maybe::Present((_, ref typed)) = form
            && let Maybe::Present(ref links) = links
            && match arranged {
                arity::Arranged::Positional(ref entries) => entries.len() == typed.len(),
                arity::Arranged::Labelled(_) => true,
            }
        {
            return Self::dependent_components(
                here,
                typed,
                links,
                arranged,
                Places::Written,
                patterns,
                work,
            );
        }
        let layout = match (related, stated, &form) {
            (Maybe::Present(layout), ..) => Maybe::Present(layout),
            (Maybe::Absent(_), Maybe::Present(node), &Maybe::Absent(_)) => {
                self.stated_relation(node)?
            },
            (Maybe::Absent(reason), ..) => Maybe::Absent(reason),
        };
        if let Maybe::Present(layout) = layout
            && match arranged {
                arity::Arranged::Positional(ref entries) => entries.len() == layout.fields().len(),
                arity::Arranged::Labelled(_) => true,
            }
        {
            let typed: Vec<arity::Entry<'source>> = layout
                .fields()
                .map(|field| arity::Entry {
                    key: arity::Key::Label(field, here.at),
                    held: arity::Held::Operand(here.at),
                })
                .collect();
            return Self::dependent_components(
                here,
                &typed,
                layout.links(),
                arranged,
                Places::Related(layout),
                patterns,
                work,
            );
        }
        if let Maybe::Present(node) = stated
            && let Maybe::Present((typed, links)) = self.stated_bundle(node, here.at)
            && match arranged {
                arity::Arranged::Positional(ref entries) => entries.len() == typed.len(),
                arity::Arranged::Labelled(_) => true,
            }
        {
            return Self::dependent_components(
                here,
                &typed,
                &links,
                arranged,
                Places::Modelled,
                patterns,
                work,
            );
        }
        let typed = form.map(|(_node, typed)| typed);
        let untyped = Maybe::Absent(binder_type::Absent::Untyped);
        let queue = |entry: &arity::Entry<'source>, stated| Queued {
            at: entry.held.at(),
            slot: UNWRITTEN,
            stated,
            related: Maybe::Absent(related::Absent::Otherwise),
            punned: Punned(matches!(entry.held, arity::Held::Punned(_))),
        };
        match arranged {
            arity::Arranged::Positional(entries) => {
                if let Maybe::Present(ref typed) = typed
                    && !entries.is_empty()
                    && typed.len() == entries.len()
                    && typed
                        .iter()
                        .all(|held| matches!(held.key, arity::Key::Label(..)))
                {
                    let mut labels = Vec::with_capacity(entries.len());
                    let mut queued = Vec::with_capacity(entries.len());
                    for (entry, component) in entries.iter().zip(typed) {
                        let arity::Key::Label(name, _) = component.key
                        else {
                            continue;
                        };
                        labels.push(FieldLabel::from(String::from(name.as_ref())));
                        queued.push(queue(entry, Maybe::Present(component.held.at().node)));
                    }
                    return Ok(Matcher::Record {
                        labels,
                        fields: allocated(patterns, work, &queued),
                    });
                }
                let queued: Vec<Queued> = match typed {
                    Maybe::Present(ref typed)
                        if typed.len() == entries.len()
                            && typed
                                .iter()
                                .all(|entry| matches!(entry.key, arity::Key::Positional)) =>
                    {
                        entries
                            .iter()
                            .zip(typed)
                            .map(|(entry, component)| {
                                queue(entry, Maybe::Present(component.held.at().node))
                            })
                            .collect()
                    },
                    Maybe::Present(_) | Maybe::Absent(_) => {
                        entries.iter().map(|entry| queue(entry, untyped)).collect()
                    },
                };
                Ok(Matcher::Tuple {
                    fields: allocated(patterns, work, &queued),
                    dependent: Dependent(false),
                })
            },
            arity::Arranged::Labelled(entries) => {
                let mut labels = Vec::with_capacity(entries.len());
                let mut queued = Vec::with_capacity(entries.len());
                for entry in &entries {
                    let arity::Key::Label(name, _) = entry.key
                    else {
                        continue;
                    };
                    let component = match typed {
                        | Maybe::Present(ref typed) => typed
                            .iter()
                            .find(|held| matches!(held.key, arity::Key::Label(label, _) if label == name))
                            .map_or(untyped, |held| Maybe::Present(held.held.at().node)),
                        | Maybe::Absent(_) => untyped,
                    };
                    labels.push(FieldLabel::from(String::from(name.as_ref())));
                    queued.push(queue(entry, component));
                }
                Ok(Matcher::Record {
                    labels,
                    fields: allocated(patterns, work, &queued),
                })
            },
        }
    }

    /// The nested pairs a pattern at a dependent record matches: its
    /// entries placed by the record's written order, the links nested to the
    /// right.
    ///
    /// # Specification
    /// - requires: `typed` are the entries of the dependent record the
    ///   scrutinee's position states, `links` whether each but the last binds
    ///   the ones after it, `arranged` the pattern's entries: positional ones
    ///   of the record's arity, or labelled ones, and `places` whether the
    ///   record's entries are written.
    /// - ensures: one tuple of two per link, the outermost returned and each
    ///   inner one a part after its parent: the link's entry, then the next
    ///   link or the last entry; a split of a link that binds is dependent; a
    ///   place no entry names is a wildcard, kept with its field's label when
    ///   the record labels it, and the rest a link nests is kept with the label
    ///   of the field it starts at; each written entry queued with its place's
    ///   written type, or unstated at a relation's or a model's record, in
    ///   written order.
    /// - fails: the unresolved-name refusal for a label the record lacks.
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoweringRefusal::UnresolvedName`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a positional and a labelled pattern at a dependent
    ///   record of two, a labelled one at a record of three naming two of its
    ///   labels, and patterns at a relation's record.
    /// - witness: `lower::native::tests::a_pattern_at_a_dependent_record_splits_it_under_its_motive`
    /// - witness: `lower::identity::tests::a_pattern_at_a_relation_splits_its_record`
    /// - witness: `lower::identity::tests::an_unwritten_field_is_named_by_its_label_670`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |shape| matches!(*shape, Matcher::Tuple { fields, .. } if fields.end.saturating_sub(fields.start) == 2_usize)))]
    fn dependent_components(
        here: Site,
        typed: &[arity::Entry<'source>],
        links: &[Dependent],
        arranged: arity::Arranged<'source>,
        places: Places,
        patterns: &mut Written,
        work: &mut Vec<Queued>,
    ) -> Result<Matcher, LoweringRefusal<'source>>
    {
        let mut placed: Vec<Option<(usize, arity::Entry<'source>)>> =
            alloc::vec![None; typed.len()];
        match arranged {
            arity::Arranged::Positional(entries) => {
                for (written, (slot, entry)) in placed.iter_mut().zip(entries).enumerate() {
                    *slot = Some((written, entry));
                }
            },
            arity::Arranged::Labelled(entries) => {
                for (written, entry) in entries.into_iter().enumerate() {
                    let arity::Key::Label(name, key) = entry.key
                    else {
                        continue;
                    };
                    let (arity::Place(place), _) = Self::labelled_in(typed, name, key)?;
                    if let Some(slot) = placed.get_mut(place) {
                        *slot = Some((written, entry));
                    }
                }
            },
        }
        let mut queued: Vec<(usize, Queued)> = Vec::with_capacity(typed.len());
        let mut part = |patterns: &mut Written, place: usize| -> PatternAt {
            let slot = PatternAt(patterns.shapes.len());
            let entry = placed.get(place).copied().flatten();
            patterns.shapes.push((
                entry.map_or(here.at, |(_, entry)| entry.held.at()),
                Matcher::Wild,
            ));
            if let Some((written, entry)) = entry {
                queued.push((written, Queued {
                    at: entry.held.at(),
                    slot,
                    stated: match (places, typed.get(place)) {
                        (Places::Written, Some(component)) => {
                            Maybe::Present(component.held.at().node)
                        },
                        (Places::Written, None) | (Places::Related(_) | Places::Modelled, _) => {
                            Maybe::Absent(binder_type::Absent::Untyped)
                        },
                    },
                    related: match places {
                        Places::Related(layout) => layout.inner(arity::Place(place)),
                        Places::Written | Places::Modelled => {
                            Maybe::Absent(related::Absent::Otherwise)
                        },
                    },
                    punned: Punned(matches!(entry.held, arity::Held::Punned(_))),
                }));
            }
            else if let Some(&arity::Entry {
                key: arity::Key::Label(label, _),
                ..
            }) = typed.get(place)
            {
                patterns
                    .unwritten
                    .push((slot, FieldLabel::from(String::from(label.as_ref()))));
            }
            slot
        };
        let mut outer = None;
        let mut pending: Option<PatternAt> = None;
        for (link, &dependent) in links.iter().enumerate() {
            let first = part(patterns, link);
            let second = if link.saturating_add(2) >= typed.len() {
                part(patterns, link.saturating_add(1))
            }
            else {
                // The rest of the record from the next field on: a binder the
                // pattern writes no name for, named by the label it starts at.
                let slot = PatternAt(patterns.shapes.len());
                patterns.shapes.push((here.at, Matcher::Wild));
                if let Some(&arity::Entry {
                    key: arity::Key::Label(label, _),
                    ..
                }) = typed.get(link.saturating_add(1))
                {
                    patterns
                        .unwritten
                        .push((slot, FieldLabel::from(String::from(label.as_ref()))));
                }
                slot
            };
            let start = patterns.parts.len();
            patterns.parts.extend([first, second]);
            let matcher = Matcher::Tuple {
                fields: Stretch {
                    start,
                    end: patterns.parts.len(),
                },
                dependent,
            };
            match pending {
                Some(slot) => {
                    if let Some(held) = patterns.shapes.get_mut(slot.0) {
                        held.1 = matcher;
                    }
                },
                None => outer = Some(matcher),
            }
            pending = Some(second);
        }
        queued.sort_by_key(|&(written, _)| core::cmp::Reverse(written));
        work.extend(queued.into_iter().map(|(_, each)| each));

        outer.ok_or_else(|| LoweringRefusal::OutOfFragment {
            span: here.at.span,
            form: here.name,
            sort: here.reading.sort(),
            boundary: FragmentBoundary::WrongSort,
        })
    }

    /// The injection shape of a sum pattern `+{ key = payload }` queued as
    /// `queued`, whose position states the type `queued.stated`.
    ///
    /// # Specification
    /// - requires: `key` and `payload` are the sum pattern's at `here`.
    /// - ensures: the injection into the summand the key's index names, or its
    ///   label names among the stated sum's entries, of as many summands as the
    ///   stated sum has; the payload queued with the summand's type, and the
    ///   key spelled at the payload, which it names. A position stating the
    ///   atom `Bool`, through parentheses, states the sum `+{Unit, Unit}` it
    ///   stands for, whose summands write no type to queue the payload with.
    ///   Where the position states no sum and `patterns` reads a case's arms,
    ///   an index names its summand of a sum one wider than it, recorded among
    ///   the unstated for the case to settle.
    /// - fails: the unannotated refusal where the position states no sum and
    ///   the pattern is not an index among a case's arms; a misplaced tile at
    ///   an index past the sum; the unresolved-name refusal for a label the sum
    ///   lacks.
    /// - panics: none.
    ///
    /// # Errors
    /// The pattern's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — labelled and indexed sum patterns under a stated sum,
    ///   nested in a telescope pattern, under `Bool`, with no stated sum, and
    ///   indexed with no stated sum among a case's arms.
    /// - witness: `lower::native::tests::sum_patterns_case_on_the_stated_arity`
    /// - witness: `lower::native::tests::a_sum_pattern_reads_bool_as_its_sum_815`
    /// - witness: `lower::native::tests::indexed_arms_settle_their_sum_1169`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |shape| matches!(*shape, Matcher::Injection { summand, arity, .. } if summand < arity)))]
    fn injected(
        &mut self,
        here: Site,
        queued: Queued,
        key: arity::Key<'source>,
        payload: Placed,
        patterns: &mut Written,
        work: &mut Vec<Queued>,
    ) -> Result<Matcher, LoweringRefusal<'source>>
    {
        let stated = queued.stated;
        let summands = match stated {
            Maybe::Present(node) => {
                self.stated_entries(here, node, Former::LabelledSumType, arity::Thunked(false))?
            },
            Maybe::Absent(_) => Maybe::Absent(arity::stated_labels::Absent::Otherwise),
        };
        let (summands, arity) = match summands {
            // `Bool` writes no summand, so its two are read off the atom.
            Maybe::Present(summands) if summands.is_empty() => (summands, 2_usize),
            Maybe::Present(summands) => {
                let arity = summands.len();
                (summands, arity)
            },
            Maybe::Absent(_) if self.stated_atom(stated)? == Some(TypeAtom::Boolean) => {
                (Vec::new(), 2_usize)
            },
            Maybe::Absent(_) => match key {
                arity::Key::Index(index, ..) if patterns.positional.0 => {
                    patterns.unstated.push((queued.slot, here));
                    (Vec::new(), index.saturating_add(1))
                },
                arity::Key::Index(..) | arity::Key::Label(..) | arity::Key::Positional => {
                    return Err(here.out(FragmentBoundary::Unannotated));
                },
            },
        };
        let (summand, held, keyed) = match key {
            arity::Key::Index(index, _, written) if index < arity => (
                index,
                summands.get(index).map(|entry| entry.held.at().node),
                written.span,
            ),
            arity::Key::Index(_, _, written) => {
                return Err(here.fault(written.span, FormFault::MisplacedTile));
            },
            arity::Key::Label(name, written) => {
                let (arity::Place(index), entry) = Self::labelled_in(&summands, name, written)?;
                (index, Some(entry.held.at().node), written.span)
            },
            arity::Key::Positional => {
                return Err(here.fault(payload.span, FormFault::MisplacedTile));
            },
        };
        let queued = [Queued {
            at: payload,
            slot: UNWRITTEN,
            stated: held.map_or(Maybe::Absent(binder_type::Absent::Untyped), Maybe::Present),
            related: Maybe::Absent(related::Absent::Otherwise),
            punned: Punned(false),
        }];
        let fields = allocated(patterns, work, &queued);
        let field = patterns
            .parts
            .get(fields.start)
            .copied()
            .unwrap_or(UNWRITTEN);
        patterns
            .spelled
            .push((field, keyed, PatternReading::Matched));

        Ok(Matcher::Injection {
            summand,
            arity,
            field,
        })
    }

    /// The type atom `stated` names, through parentheses.
    ///
    /// # Specification
    /// - requires: `stated` is a type's syntax node.
    /// - ensures: the atom when `stated` is present and plans, through
    ///   transparent nodes, as a type atom; or, not yet classified, as a
    ///   signature the sweep has not reached is, names an atom with no
    ///   constructor or outermost declaration of that name to shadow it;
    ///   nothing otherwise.
    /// - fails: the name's own resolution refusals.
    /// - panics: none.
    ///
    /// # Errors
    /// As [`Self::resolve_name`].
    ///
    /// # Termination
    /// Every turn steps to the operand of a transparent node, strictly deeper
    /// in a finite tree.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::injected`], a parameter's `Bool` and a
    ///   lambda's under a separate signature.
    /// - witness: `lower::native::tests::a_sum_pattern_reads_bool_as_its_sum_815`
    #[spec(ensures: |ret| !matches!(ret, Ok(Some(_))) || matches!(stated, Maybe::Present(_)))]
    fn stated_atom(
        &mut self,
        stated: Maybe<NodeIndex, binder_type::Absent>,
    ) -> Result<Option<TypeAtom>, LoweringRefusal<'source>>
    {
        let Maybe::Present(mut at) = stated
        else {
            return Ok(None);
        };
        while let Some(&Plan::Transparent(inner)) = self.plans.get(at) {
            at = inner;
        }
        match self.plans.get(at) {
            Some(&Plan::Atom(atom)) => return Ok(Some(atom)),
            Some(&Plan::Unplanned) | None => {},
            Some(_) => return Ok(None),
        }
        let Some(tree) = self.tree.node(at)
        else {
            return Ok(None);
        };
        let placed = Placed::of(at, tree);
        let Some((form, Former::Constructor | Former::TypeHead)) = self.form_at(placed)?
        else {
            return Ok(None);
        };
        let name = self.name_at(placed);
        let Maybe::Present(atom) = type_atom(name)
        else {
            return Ok(None);
        };
        let named = Site {
            at: placed,
            name: form,
            reading: Reading::ValueType(Frame::Outermost),
        };
        if let Maybe::Present(_) = self.constructor_named(named, name) {
            return Ok(None);
        }

        Ok(match self.resolve_name(named, Frame::Outermost, name)? {
            Maybe::Present(_) => None,
            Maybe::Absent(_) => Some(atom),
        })
    }

    /// Compile `rows` to a decision tree over the scrutinee at level zero.
    ///
    /// # Specification
    /// - requires: every row has one column, its arm's alternative.
    /// - ensures: the tree's nodes, its root first and every child after its
    ///   parent: a leaf where the first surviving row's columns all match
    ///   anything, a stuck node where its leftmost tested column is a hole or a
    ///   hole it passed decides it, and else a switch on that column.
    /// - fails: [`LoweringRefusal::NonExhaustiveMatch`] at the match where no
    ///   row survives; the wrong-sort refusal at a pattern whose kind its
    ///   column does not switch on; [`LoweringRefusal::BudgetExceeded`].
    /// - panics: none.
    ///
    /// # Errors
    /// The match's refusal.
    ///
    /// # Termination
    /// Every work item removes a column or a literal from the rows it hands
    /// on, or ends in a leaf, and the allowance is spent once per item and
    /// per row.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the witnesses compile a catch-all, an or-pattern, two
    ///   arms at one head, literal columns, holes and a missing constructor.
    /// - witness: `lower::native::tests::nested_constructor_patterns_compile_to_nested_cases`
    /// - witness: `lower::native::tests::a_non_exhaustive_match_is_refused`
    /// - witness: `lower::native::tests::literal_patterns_compare_and_branch`
    /// - witness: `lower::native::tests::a_pattern_hole_leaves_its_leaf_stuck`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |tests| !tests.is_empty() && tests.iter().all(|test| *test != Test::Pending)))]
    fn compile(
        &mut self,
        site: Site,
        patterns: &Written,
        rows: Vec<Row>,
    ) -> Result<Vec<Test>, LoweringRefusal<'source>>
    {
        let mut tree = Compiling::default();
        let _root = tree.queue(Depth::default(), Vec::from([TreeLevel::default()]), rows);
        while let Some(item) = tree.work.pop() {
            self.fuel.spend()?;
            let test = self.reduce(site, patterns, &item, &mut tree)?;
            if let Some(held) = tree.tests.get_mut(item.slot.0) {
                *held = test;
            }
        }

        Ok(tree.tests)
    }

    /// Reduce one matrix to the tree node it fills, queueing its children.
    ///
    /// # Specification
    /// - requires: as [`Self::compile`], for one item.
    /// - ensures: the item's node, its rows' as-patterns first settled where
    ///   they stand ([`peeled`]): a leaf or a stuck node when the first row
    ///   tests nothing, a stuck node when its leftmost tested pattern is a
    ///   hole, and else the switch on that pattern's column, its children
    ///   queued on `tree`.
    /// - fails: as [`Self::compile`].
    /// - panics: none.
    ///
    /// # Errors
    /// As [`Self::compile`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::compile`].
    /// - witness: `lower::native::tests::nested_constructor_patterns_compile_to_nested_cases`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |test| *test != Test::Pending))]
    fn reduce(
        &mut self,
        site: Site,
        patterns: &Written,
        item: &Work,
        tree: &mut Compiling,
    ) -> Result<Test, LoweringRefusal<'source>>
    {
        let settled = peeled(patterns, item);
        let item = settled.as_ref().unwrap_or(item);
        let Some(first) = item.rows.first()
        else {
            return Err(LoweringRefusal::NonExhaustiveMatch { span: site.at.span });
        };
        let tested = first
            .columns
            .iter()
            .enumerate()
            .find_map(|(column, &pattern)| {
                let &(written, ref shape) = patterns.shapes.get(pattern.0)?;
                let head = match *shape {
                    Matcher::Wild | Matcher::Binder(_) | Matcher::Alias { .. } => return None,
                    Matcher::Hole(hole) => Head::Hole(hole),
                    Matcher::Constructor { form, .. } => Head::Data(form),
                    Matcher::Boolean(_) => Head::Boolean,
                    Matcher::Integer(ref literal) => Head::Integer(literal.clone()),
                    Matcher::Tuple { fields, dependent } => {
                        Head::Tuple(fields.end.saturating_sub(fields.start), dependent)
                    },
                    Matcher::Record { .. } => Head::Record,
                    Matcher::Injection { arity, .. } => Head::Sum(arity),
                    Matcher::Nil | Matcher::Cell { .. } => Head::List,
                };
                Some((Column(column), written, head))
            });
        let Some((column, written, head)) = tested
        else {
            return Ok(leaf(patterns, first, &item.levels, item.depth));
        };
        let switch = Switch {
            column,
            level: item.levels.get(column.0).copied().unwrap_or_default(),
            first: written.span,
        };
        match head {
            Head::Hole(hole) => Ok(Test::Stuck(hole)),
            Head::Data(form) => self.switch_data(patterns, item, switch, form, tree),
            Head::Boolean => self.switch_boolean(patterns, item, switch, tree),
            Head::Integer(literal) => self.switch_integer(patterns, item, switch, literal, tree),
            Head::Tuple(arity, dependent) => {
                self.switch_tuple(patterns, item, switch, Width(arity), dependent, tree)
            },
            Head::Record => self.switch_record(patterns, item, switch, tree),
            Head::Sum(arity) => self.switch_sum(patterns, item, switch, Width(arity), tree),
            Head::List => self.switch_list(patterns, item, switch, tree),
        }
    }

    /// Switch on the native data value in `switch`'s column, a value of the
    /// data declaration at `form`: one child per constructor, its rows those
    /// that admit the constructor with its fields in the column's place.
    ///
    /// # Specification
    /// - requires: `switch`'s column holds a constructor of `form` in the
    ///   item's first row.
    /// - ensures: a data switch with one branch per constructor of `form`, in
    ///   tag order, each child queued under the constructor's fields.
    /// - fails: the switch's wrong-sort refusal for a row whose pattern in the
    ///   column is no constructor of `form`;
    ///   [`LoweringRefusal::BudgetExceeded`].
    /// - panics: none.
    ///
    /// # Errors
    /// As stated.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a catch-all row and a nested constructor each reach
    ///   the branch they admit.
    /// - witness: `lower::native::tests::nested_constructor_patterns_compile_to_nested_cases`
    /// - witness: `lower::native::tests::a_case_over_a_family_of_parameters_reads_its_answer_unabstracted`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |test| matches!(*test, Test::Data { .. })))]
    fn switch_data(
        &mut self,
        patterns: &Written,
        item: &Work,
        switch: Switch,
        form: Generators,
        tree: &mut Compiling,
    ) -> Result<Test, LoweringRefusal<'source>>
    {
        let arities: Vec<usize> = match form {
            Generators::Written(position) => self
                .collected
                .data
                .get(position)
                .map(|written| {
                    written
                        .generators
                        .iter()
                        .map(|generator| generator.fields.len())
                        .collect()
                })
                .unwrap_or_default(),
            Generators::Presentation => match self.collected.theory {
                Maybe::Present(ref theory) => theory.arities.clone(),
                Maybe::Absent(_) => Vec::new(),
            },
            Generators::Words(words) => {
                let loops = self
                    .collected
                    .words
                    .get(words)
                    .map_or(0_usize, |written| written.loops.len());
                let mut arities = Vec::from([0_usize]);
                arities.resize(loops.saturating_mul(2).saturating_add(1), 1_usize);
                arities
            },
            Generators::Terms(terms) => self
                .collected
                .terms
                .get(terms)
                .map(|written| written.arities.clone())
                .unwrap_or_default(),
        };
        let declared = match form {
            Generators::Written(position) => self
                .collected
                .data
                .get(position)
                .map(|written| (written.slot, written.parameters.is_empty())),
            // The presentation code's constructors need a written classifier,
            // so the switch reads it as a family of parameters would.
            Generators::Presentation => match self.collected.theory {
                Maybe::Present(ref theory) => Some((theory.slot, false)),
                Maybe::Absent(_) => None,
            },
            Generators::Words(words) => self
                .collected
                .words
                .get(words)
                .map(|written| (written.slot, true)),
            Generators::Terms(terms) => self
                .collected
                .terms
                .get(terms)
                .map(|written| (written.slot, true)),
        };
        let declared = declared.and_then(|(slot, bare)| {
            self.collected
                .slots
                .get(usize::from(slot))
                .map(|slot| (slot.constant, bare))
        });
        let family = match declared {
            Some((constant, true)) => Maybe::Present(constant),
            Some((_, false)) | None => Maybe::Absent(bare::Absent::Parameterised),
        };
        let eliminated = declared.map_or(
            Maybe::Absent(eliminated::Absent::Unslotted),
            |(constant, _)| Maybe::Present(constant),
        );
        // Each branch at an indexed family binds one equation per index past
        // its fields: the stated index's path to the scrutinee's.
        let equations = match form {
            Generators::Written(position) => self
                .collected
                .data
                .get(position)
                .map_or(0, |written| written.indices.len()),
            Generators::Presentation | Generators::Words(_) | Generators::Terms(_) => 0,
        };
        let mut branches = Vec::with_capacity(arities.len());
        let mut fresh: Vec<TreeLevel> = Vec::new();
        for (tag, &arity) in arities.iter().enumerate() {
            let mut specialised = Vec::new();
            for row in &item.rows {
                self.fuel.spend()?;
                let mut next = row.clone();
                let held = patterns.entry(row, switch.column);
                let replacement = match *held {
                    Matcher::Constructor {
                        form: other,
                        tag: written,
                        fields,
                    } => {
                        if other != form {
                            return Err(patterns.mismatched(row, switch));
                        }
                        if written != tag {
                            continue;
                        }
                        patterns
                            .parts
                            .get(fields.start .. fields.end)
                            .map(<[PatternAt]>::to_vec)
                            .unwrap_or_default()
                    },
                    Matcher::Wild | Matcher::Binder(_) | Matcher::Hole(_) => {
                        through(&mut next, held, switch.level);
                        alloc::vec![UNWRITTEN; arity]
                    },
                    Matcher::Boolean(_)
                    | Matcher::Integer(_)
                    | Matcher::Tuple { .. }
                    | Matcher::Record { .. }
                    | Matcher::Injection { .. }
                    | Matcher::Nil
                    | Matcher::Cell { .. }
                    | Matcher::Alias { .. } => return Err(patterns.mismatched(row, switch)),
                };
                next.columns = splice(&row.columns, switch.column, &replacement);
                specialised.push(next);
            }
            // A constructor no row admits at a family of one index is pruned:
            // its branch eliminates its one equation, which the checker admits
            // only when the constructor cannot stand at the scrutinee's index.
            if specialised.is_empty() && equations == 1 {
                branches.push((arity, tree.place(Test::Absurd)));
                continue;
            }
            fresh.clear();
            fresh.extend(
                (0 .. arity)
                    .map(|field| TreeLevel(item.depth.0.saturating_add(field).saturating_add(1))),
            );
            let child = tree.queue(
                Depth(item.depth.0.saturating_add(arity).saturating_add(equations)),
                splice(&item.levels, switch.column, &fresh),
                specialised,
            );
            branches.push((arity, child));
        }

        Ok(Test::Data {
            level: switch.level,
            depth: item.depth,
            family,
            eliminated,
            equations,
            branches,
        })
    }

    /// Switch on the boolean in `switch`'s column: `true` on the left.
    ///
    /// # Specification
    /// - requires: `switch`'s column holds a boolean in the item's first row.
    /// - ensures: a boolean switch whose children hold the rows admitting
    ///   `true` and `false`, the column removed, each under the case's one unit
    ///   binder.
    /// - fails: the switch's wrong-sort refusal for a row whose pattern in the
    ///   column is a constructor, an integer, a tuple, a record or an
    ///   injection; [`LoweringRefusal::BudgetExceeded`].
    /// - panics: none.
    ///
    /// # Errors
    /// As stated.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a `true` arm and a catch-all split into the two
    ///   sides.
    /// - witness: `lower::native::tests::literal_patterns_compare_and_branch`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |test| matches!(*test, Test::Boolean { .. })))]
    fn switch_boolean(
        &mut self,
        patterns: &Written,
        item: &Work,
        switch: Switch,
        tree: &mut Compiling,
    ) -> Result<Test, LoweringRefusal<'source>>
    {
        let mut left = Vec::new();
        let mut right = Vec::new();
        for row in &item.rows {
            self.fuel.spend()?;
            let held = patterns.entry(row, switch.column);
            let mut next = row.clone();
            next.columns = splice(&row.columns, switch.column, &[]);
            match *held {
                Matcher::Boolean(true) => left.push(next),
                Matcher::Boolean(false) => right.push(next),
                Matcher::Wild | Matcher::Binder(_) | Matcher::Hole(_) => {
                    through(&mut next, held, switch.level);
                    left.push(next.clone());
                    right.push(next);
                },
                Matcher::Constructor { .. }
                | Matcher::Integer(_)
                | Matcher::Tuple { .. }
                | Matcher::Record { .. }
                | Matcher::Injection { .. }
                | Matcher::Nil
                | Matcher::Cell { .. }
                | Matcher::Alias { .. } => return Err(patterns.mismatched(row, switch)),
            }
        }
        let without = splice(&item.levels, switch.column, &[]);
        let depth = Depth(item.depth.0.saturating_add(1));
        let no = tree.queue(depth, without.clone(), right);
        let yes = tree.queue(depth, without, left);

        Ok(Test::Boolean {
            level: switch.level,
            depth: item.depth,
            yes,
            no,
        })
    }

    /// Compare the integer in `switch`'s column with `literal`.
    ///
    /// # Specification
    /// - requires: `switch`'s column holds `literal` in the item's first row.
    /// - ensures: an integer test whose equal child holds the rows admitting
    ///   `literal`, the column removed, and whose other child holds the rows
    ///   admitting another integer, the column kept; both under the
    ///   comparison's binder and the case's unit binder.
    /// - fails: the switch's wrong-sort refusal for a row whose pattern in the
    ///   column is a constructor, a boolean, a tuple, a record or an injection;
    ///   [`LoweringRefusal::BudgetExceeded`].
    /// - panics: none.
    ///
    /// # Errors
    /// As stated.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — two literal arms and a catch-all compile to two
    ///   comparisons, and the catch-all reaches both other sides.
    /// - witness: `lower::native::tests::literal_patterns_compare_and_branch`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |test| matches!(*test, Test::Integer { .. })))]
    fn switch_integer(
        &mut self,
        patterns: &Written,
        item: &Work,
        switch: Switch,
        literal: Literal,
        tree: &mut Compiling,
    ) -> Result<Test, LoweringRefusal<'source>>
    {
        let mut equal = Vec::new();
        let mut other = Vec::new();
        for row in &item.rows {
            self.fuel.spend()?;
            let held = patterns.entry(row, switch.column);
            let mut matched = row.clone();
            matched.columns = splice(&row.columns, switch.column, &[]);
            match *held {
                Matcher::Integer(ref written) if *written == literal => equal.push(matched),
                Matcher::Integer(_) => other.push(row.clone()),
                Matcher::Wild | Matcher::Binder(_) | Matcher::Hole(_) => {
                    through(&mut matched, held, switch.level);
                    equal.push(matched);
                    other.push(row.clone());
                },
                Matcher::Constructor { .. }
                | Matcher::Boolean(_)
                | Matcher::Tuple { .. }
                | Matcher::Record { .. }
                | Matcher::Injection { .. }
                | Matcher::Nil
                | Matcher::Cell { .. }
                | Matcher::Alias { .. } => return Err(patterns.mismatched(row, switch)),
            }
        }
        let depth = Depth(item.depth.0.saturating_add(2));
        let no = tree.queue(depth, item.levels.clone(), other);
        let yes = tree.queue(depth, splice(&item.levels, switch.column, &[]), equal);

        Ok(Test::Integer {
            level: switch.level,
            depth: item.depth,
            literal,
            yes,
            no,
        })
    }

    /// Split the tuple in `switch`'s column into its `arity` components.
    ///
    /// # Specification
    /// - requires: `switch`'s column holds a tuple of `arity` components in the
    ///   item's first row, split dependently as `dependent` says.
    /// - ensures: a split, dependent as the column's tuple is, whose child
    ///   holds every row, the column replaced by the components a tuple pattern
    ///   writes or by wildcards for a pattern matching anything, under `arity`
    ///   more binders, component zero outermost; it keeps, for each component
    ///   some row's tuple leaves to a labelled wildcard, the first such label.
    /// - fails: the switch's wrong-sort refusal for a row whose pattern in the
    ///   column is a tuple of another arity or of another kind;
    ///   [`LoweringRefusal::BudgetExceeded`].
    /// - panics: none.
    ///
    /// # Errors
    /// As stated.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a positional telescope pattern of three binders, a
    ///   tuple pattern and a pattern at a dependent record each reach their arm
    ///   at the component's level.
    /// - witness: `lower::native::tests::telescope_patterns_split_and_project`
    /// - witness: `lower::native::tests::a_pattern_at_a_dependent_record_splits_it_under_its_motive`
    /// - witness: `lower::identity::tests::an_unwritten_field_is_named_by_its_label_670`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |test| matches!(*test, Test::Split { arity: held, dependent: split, .. } if held == width.0 && split == dependent)))]
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            linear_search_in_loop,
            reason = "bounded: the unwritten labels of one tuple pattern's components"
        )
    )]
    fn switch_tuple(
        &mut self,
        patterns: &Written,
        item: &Work,
        switch: Switch,
        width: Width,
        dependent: Dependent,
        tree: &mut Compiling,
    ) -> Result<Test, LoweringRefusal<'source>>
    {
        let Width(arity) = width;
        let mut specialised = Vec::with_capacity(item.rows.len());
        let mut unwritten: Vec<(usize, FieldLabel)> = Vec::new();
        for row in &item.rows {
            self.fuel.spend()?;
            let mut next = row.clone();
            let held = patterns.entry(row, switch.column);
            let replacement = match *held {
                Matcher::Tuple { fields, .. }
                    if fields.end.saturating_sub(fields.start) == arity =>
                {
                    let parts = patterns
                        .parts
                        .get(fields.start .. fields.end)
                        .map(<[PatternAt]>::to_vec)
                        .unwrap_or_default();
                    for (component, part) in parts.iter().enumerate() {
                        if let Some(&(_, ref label)) =
                            patterns.unwritten.iter().find(|&&(held, _)| held == *part)
                            && unwritten.iter().all(|&(named, _)| named != component)
                        {
                            unwritten.push((component, label.clone()));
                        }
                    }
                    parts
                },
                Matcher::Wild | Matcher::Binder(_) | Matcher::Hole(_) => {
                    through(&mut next, held, switch.level);
                    alloc::vec![UNWRITTEN; arity]
                },
                Matcher::Tuple { .. }
                | Matcher::Constructor { .. }
                | Matcher::Boolean(_)
                | Matcher::Integer(_)
                | Matcher::Record { .. }
                | Matcher::Injection { .. }
                | Matcher::Nil
                | Matcher::Cell { .. }
                | Matcher::Alias { .. } => return Err(patterns.mismatched(row, switch)),
            };
            next.columns = splice(&row.columns, switch.column, &replacement);
            specialised.push(next);
        }
        let child = tree.queue(
            Depth(item.depth.0.saturating_add(arity)),
            splice(&item.levels, switch.column, &fresh(item.depth, width)),
            specialised,
        );

        unwritten.sort_unstable_by_key(|&(component, _)| component);
        Ok(Test::Split {
            level: switch.level,
            depth: item.depth,
            arity,
            dependent,
            unwritten,
            child,
        })
    }

    /// Project the fields every row's record pattern in `switch`'s column
    /// names.
    ///
    /// # Specification
    /// - requires: `switch`'s column holds a record in the item's first row.
    /// - ensures: the projections of every label any row names, in label order,
    ///   whose child holds every row, the column replaced by the field each
    ///   label's pattern writes, a wildcard for a label the row does not name
    ///   or a pattern matching anything, under one more binder per label.
    /// - fails: the switch's wrong-sort refusal for a row whose pattern in the
    ///   column is of another kind; [`LoweringRefusal::BudgetExceeded`].
    /// - panics: none.
    ///
    /// # Errors
    /// As stated.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — two record arms naming different labels each reach
    ///   their arm with the fields they name.
    /// - witness: `lower::native::tests::telescope_patterns_split_and_project`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |test| matches!(*test, Test::Record { ref labels, .. } if labels.is_sorted())))]
    fn switch_record(
        &mut self,
        patterns: &Written,
        item: &Work,
        switch: Switch,
        tree: &mut Compiling,
    ) -> Result<Test, LoweringRefusal<'source>>
    {
        let mut named = BTreeSet::new();
        for row in &item.rows {
            match *patterns.entry(row, switch.column) {
                Matcher::Record { ref labels, .. } => named.extend(labels.iter().cloned()),
                Matcher::Wild | Matcher::Binder(_) | Matcher::Hole(_) => {},
                Matcher::Constructor { .. }
                | Matcher::Boolean(_)
                | Matcher::Integer(_)
                | Matcher::Tuple { .. }
                | Matcher::Injection { .. }
                | Matcher::Nil
                | Matcher::Cell { .. }
                | Matcher::Alias { .. } => return Err(patterns.mismatched(row, switch)),
            }
        }
        let labels: Vec<FieldLabel> = named.into_iter().collect();
        let mut specialised = Vec::with_capacity(item.rows.len());
        for row in &item.rows {
            self.fuel.spend()?;
            let mut next = row.clone();
            let held = patterns.entry(row, switch.column);
            let replacement: Vec<PatternAt> = match *held {
                Matcher::Record {
                    labels: ref written,
                    fields,
                } => {
                    let parts = patterns
                        .parts
                        .get(fields.start .. fields.end)
                        .unwrap_or_default();
                    labels
                        .iter()
                        .map(|label| {
                            written
                                .iter()
                                .zip(parts)
                                .find_map(|(each, &part)| (each == label).then_some(part))
                                .unwrap_or(UNWRITTEN)
                        })
                        .collect()
                },
                Matcher::Wild | Matcher::Binder(_) | Matcher::Hole(_) => {
                    through(&mut next, held, switch.level);
                    alloc::vec![UNWRITTEN; labels.len()]
                },
                Matcher::Constructor { .. }
                | Matcher::Boolean(_)
                | Matcher::Integer(_)
                | Matcher::Tuple { .. }
                | Matcher::Injection { .. }
                | Matcher::Nil
                | Matcher::Cell { .. }
                | Matcher::Alias { .. } => return Err(patterns.mismatched(row, switch)),
            };
            next.columns = splice(&row.columns, switch.column, &replacement);
            specialised.push(next);
        }
        let child = tree.queue(
            Depth(item.depth.0.saturating_add(labels.len())),
            splice(
                &item.levels,
                switch.column,
                &fresh(item.depth, Width(labels.len())),
            ),
            specialised,
        );

        Ok(Test::Record {
            level: switch.level,
            depth: item.depth,
            labels,
            child,
        })
    }

    /// Switch on the summand of the sum of `arity` summands in `switch`'s
    /// column.
    ///
    /// # Specification
    /// - requires: `switch`'s column holds an injection into a sum of `arity`
    ///   summands in the item's first row.
    /// - ensures: a sum switch with one child per summand, holding the rows
    ///   that admit it, the column replaced by the injection's payload or by a
    ///   wildcard for a pattern matching anything, under the payload's one
    ///   binder.
    /// - fails: the switch's wrong-sort refusal for a row whose pattern in the
    ///   column is an injection into a sum of another arity or of another kind;
    ///   [`LoweringRefusal::BudgetExceeded`].
    /// - panics: none.
    ///
    /// # Errors
    /// As stated.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a three-summand match with a catch-all reaches each
    ///   summand's arm, the catch-all filling the rest.
    /// - witness: `lower::native::tests::sum_patterns_case_on_the_stated_arity`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |test| matches!(*test, Test::Sum { ref branches, .. } if branches.len() == width.0)))]
    fn switch_sum(
        &mut self,
        patterns: &Written,
        item: &Work,
        switch: Switch,
        width: Width,
        tree: &mut Compiling,
    ) -> Result<Test, LoweringRefusal<'source>>
    {
        let Width(arity) = width;
        let mut branches = Vec::with_capacity(arity);
        for summand in 0 .. arity {
            let mut specialised = Vec::new();
            for row in &item.rows {
                self.fuel.spend()?;
                let mut next = row.clone();
                let held = patterns.entry(row, switch.column);
                let replacement = match *held {
                    Matcher::Injection {
                        summand: written,
                        arity: of,
                        field,
                    } => {
                        if of != arity {
                            return Err(patterns.mismatched(row, switch));
                        }
                        if written != summand {
                            continue;
                        }
                        field
                    },
                    Matcher::Wild | Matcher::Binder(_) | Matcher::Hole(_) => {
                        through(&mut next, held, switch.level);
                        UNWRITTEN
                    },
                    Matcher::Constructor { .. }
                    | Matcher::Boolean(_)
                    | Matcher::Integer(_)
                    | Matcher::Tuple { .. }
                    | Matcher::Record { .. }
                    | Matcher::Nil
                    | Matcher::Cell { .. }
                    | Matcher::Alias { .. } => return Err(patterns.mismatched(row, switch)),
                };
                next.columns = splice(&row.columns, switch.column, &[replacement]);
                specialised.push(next);
            }
            branches.push(tree.queue(
                Depth(item.depth.0.saturating_add(1)),
                splice(&item.levels, switch.column, &fresh(item.depth, Width(1))),
                specialised,
            ));
        }

        Ok(Test::Sum {
            level: switch.level,
            depth: item.depth,
            branches,
        })
    }

    /// Case on the native list in `switch`'s column: the empty list and a
    /// cell.
    ///
    /// # Specification
    /// - requires: `switch`'s column holds the empty list or a cell in the
    ///   item's first row.
    /// - ensures: a list case whose empty child holds the rows admitting the
    ///   empty list, the column removed, under no binder more; and whose cell
    ///   child holds the rows admitting a cell, the column replaced by the
    ///   cell's head and tail patterns, or by wildcards for a pattern matching
    ///   anything, under two binders more, the head outermost.
    /// - fails: the switch's wrong-sort refusal for a row whose pattern in the
    ///   column is no list pattern and matches not everything;
    ///   [`LoweringRefusal::BudgetExceeded`].
    /// - panics: none.
    ///
    /// # Errors
    /// As stated.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an empty arm, a cell arm and a catch-all reach the
    ///   sides they admit.
    /// - witness: `lower::native::tests::list_patterns_case_on_the_native_list`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |test| matches!(*test, Test::List { .. })))]
    fn switch_list(
        &mut self,
        patterns: &Written,
        item: &Work,
        switch: Switch,
        tree: &mut Compiling,
    ) -> Result<Test, LoweringRefusal<'source>>
    {
        let mut empty = Vec::new();
        let mut cells = Vec::new();
        for row in &item.rows {
            self.fuel.spend()?;
            let held = patterns.entry(row, switch.column);
            let mut next = row.clone();
            match *held {
                Matcher::Nil => {
                    next.columns = splice(&row.columns, switch.column, &[]);
                    empty.push(next);
                },
                Matcher::Cell { fields } => {
                    let parts = patterns
                        .parts
                        .get(fields.start .. fields.end)
                        .unwrap_or_default();
                    next.columns = splice(&row.columns, switch.column, parts);
                    cells.push(next);
                },
                Matcher::Wild | Matcher::Binder(_) | Matcher::Hole(_) => {
                    through(&mut next, held, switch.level);
                    let mut cell = next.clone();
                    next.columns = splice(&row.columns, switch.column, &[]);
                    cell.columns = splice(&row.columns, switch.column, &[UNWRITTEN; 2]);
                    empty.push(next);
                    cells.push(cell);
                },
                Matcher::Constructor { .. }
                | Matcher::Boolean(_)
                | Matcher::Integer(_)
                | Matcher::Tuple { .. }
                | Matcher::Record { .. }
                | Matcher::Injection { .. }
                | Matcher::Alias { .. } => return Err(patterns.mismatched(row, switch)),
            }
        }
        let cell = tree.queue(
            Depth(item.depth.0.saturating_add(2)),
            splice(&item.levels, switch.column, &fresh(item.depth, Width(2))),
            cells,
        );
        let nil = tree.queue(item.depth, splice(&item.levels, switch.column, &[]), empty);

        Ok(Test::List {
            level: switch.level,
            depth: item.depth,
            nil,
            cell,
        })
    }

    /// Mint `patterns` into `kept`'s core pattern table and record one arm
    /// alternative per entry of `roots`.
    ///
    /// # Specification
    /// - requires: every root of `roots` names a pattern of `patterns`.
    /// - ensures: each pattern minted after its parts, in the core's shapes: a
    ///   binder, a wildcard, a hole, a constructor over its fields, a literal,
    ///   a boolean as an injection over the unit, a tuple of no component as
    ///   the unit and of two as a pair, and an injection into a sum of two as
    ///   the injection on its side; any other tuple and a record as a
    ///   constructor of tag zero over its parts, any other injection as the
    ///   constructor tagged with its summand over its payload, and the empty
    ///   list and a cell as the constructors tagged zero and one over theirs,
    ///   which the core's coverage reads as outside its fragment; an as-pattern
    ///   as the pattern it names; one arm record per root, in order; each
    ///   pattern's own span but an implied list's, then each span `patterns`
    ///   spells inside one, recorded against the pattern minted for it.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a match over nested constructors, a binder, a hole
    ///   and an or-pattern keeps each alternative's shape; a pair pattern keeps
    ///   a pair and a two-summand injection its side.
    /// - witness: `lower::native::tests::a_match_keeps_its_patterns_beside_its_tree`
    /// - witness: `lower::native::tests::sum_patterns_case_on_the_stated_arity`
    /// - witness: `lower::native::tests::an_or_pattern_settles_each_alternative`
    /// - witness: `lower::native::tests::a_binary_injection_pattern_is_kept_at_its_side`
    #[spec(captures: before = kept.arms.len(), ensures: kept.arms.len() == before.saturating_add(roots.len()) && kept.spans.len() >= patterns.shapes.len().saturating_sub(patterns.implied.len()))]
    fn keep(
        patterns: &Written,
        roots: &[(ArmAt, PatternAt, NodeIndex, NodeIndex)],
        kept: &mut CaseOrigin,
    )
    {
        let mut minted: Vec<Option<PatternId>> =
            Vec::from_iter(patterns.shapes.iter().map(|_shape| None));
        for (position, &(_at, ref shape)) in patterns.shapes.iter().enumerate().rev() {
            let parts = |fields: Stretch| -> Vec<PatternId> {
                patterns
                    .parts
                    .get(fields.start .. fields.end)
                    .unwrap_or_default()
                    .iter()
                    .filter_map(|&part| minted.get(part.0).copied().flatten())
                    .collect()
            };
            if let Matcher::Alias { inner, .. } = *shape {
                let named = minted.get(inner.0).copied().flatten();
                if let Some(held) = minted.get_mut(position) {
                    *held = named;
                }
                continue;
            }
            let pattern = match *shape {
                Matcher::Alias { .. } | Matcher::Wild => Pattern::Wildcard,
                Matcher::Nil => Pattern::Constructor {
                    tag: ConstructorTag::from(0_usize),
                    fields: Vec::new(),
                },
                Matcher::Cell { fields } => Pattern::Constructor {
                    tag: ConstructorTag::from(1_usize),
                    fields: parts(fields),
                },
                Matcher::Binder(_) => Pattern::Binder,
                Matcher::Hole(hole) => Pattern::Hole(hole),
                Matcher::Integer(ref literal) => Pattern::Literal(literal.clone()),
                Matcher::Boolean(value) => {
                    let unit = kept.patterns.mint(Pattern::Unit);
                    Pattern::Injection(if value { Side::Left } else { Side::Right }, unit)
                },
                Matcher::Constructor { tag, fields, .. } => Pattern::Constructor {
                    tag: ConstructorTag::from(tag),
                    fields: parts(fields),
                },
                Matcher::Tuple { fields, .. } => match *parts(fields).as_slice() {
                    [] => Pattern::Unit,
                    [first, second] => Pattern::Pair(first, second),
                    ref several => Pattern::Constructor {
                        tag: ConstructorTag::from(0_usize),
                        fields: several.to_vec(),
                    },
                },
                Matcher::Record { fields, .. } => Pattern::Constructor {
                    tag: ConstructorTag::from(0_usize),
                    fields: parts(fields),
                },
                Matcher::Injection {
                    summand,
                    arity,
                    field,
                } => {
                    let body = minted.get(field.0).copied().flatten();
                    match (arity, summand, body) {
                        (2_usize, 0_usize, Some(body)) => Pattern::Injection(Side::Left, body),
                        (2_usize, 1_usize, Some(body)) => Pattern::Injection(Side::Right, body),
                        _ => Pattern::Constructor {
                            tag: ConstructorTag::from(summand),
                            fields: body.into_iter().collect(),
                        },
                    }
                },
            };
            let id = kept.patterns.mint(pattern);
            if let Matcher::Record { ref labels, .. } = *shape {
                kept.labelled.push((id, labels.clone()));
            }
            if let Some(held) = minted.get_mut(position) {
                *held = Some(id);
            }
        }
        for &(arm, root, written, body) in roots {
            if let Some(&Some(pattern)) = minted.get(root.0) {
                kept.arms.push(ArmOrigin {
                    arm: arm.0,
                    pattern,
                    written,
                    body,
                });
            }
        }
        let spelled = patterns
            .spelled
            .iter()
            .map(|&(slot, span, reading)| (slot.0, span, reading));
        let mut implied = alloc::vec![false; patterns.shapes.len()];
        for &at in &patterns.implied {
            if let Some(flag) = implied.get_mut(at.0) {
                *flag = true;
            }
        }
        let own = patterns
            .shapes
            .iter()
            .enumerate()
            .filter(|&(position, _)| !implied.get(position).copied().unwrap_or(false))
            .map(|(position, &(at, _))| (position, at.span, PatternReading::Matched));
        for (position, span, reading) in own.chain(spelled) {
            if let Some(&Some(pattern)) = minted.get(position) {
                kept.spans.push(PatternSpan {
                    pattern,
                    span,
                    reading,
                });
            }
        }
    }

    /// Mint every data declaration's signature, in source order, for those
    /// whose slot holds no refusal.
    ///
    /// # Specification
    /// - requires: the mint sweep has run.
    /// - ensures: each unrefused data declaration's signature over its minted
    ///   parameter types, index classifiers — the one at position `i` carried
    ///   past the `i` indices before it, which it does not name — field types,
    ///   stated indices and universe — `Type` at the fuss-free level when none
    ///   is written, its origin the declaration form — and the rules of its
    ///   presented reading ([`Self::presentation`]), pushed onto the module's
    ///   list, its index recorded by the declaration's position in the
    ///   collection's data list; an indexed declaration whose presented reading
    ///   writes a rule mints nothing and holds
    ///   [`LoweringRefusal::OutOfFragment`] at [`FragmentBoundary::Indexed`],
    ///   over the first such rule's two sides.
    /// - provides: the
    ///   [`DeclarationOutcome::Data`](crate::DeclarationOutcome::Data)
    ///   outcome's signature.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — two declarations, one with parameters and one without
    ///   a written universe, lower to their own signatures; a vector lowers its
    ///   length index and the length each constructor states; an indexed
    ///   family's constructor rule is declined, its operation rule kept.
    /// - witness: `lower::native::tests::a_data_declaration_lowers_to_its_signature`
    /// - witness: `lower::native::tests::an_indexed_family_lowers_its_indices`
    /// - witness: `lower::native::tests::an_indexed_family_presents_no_rule_2865`
    #[spec(captures: [data = self.data.len(), signed = self.signatures.len()], ensures: self.data.len() >= data && self.signatures.len() >= signed)]
    pub(super) fn mint_data(
        &mut self,
        sink: &mut Sink<'_>,
    )
    {
        for (position, form) in self
            .collected
            .data
            .iter()
            .enumerate()
            .skip(self.current.data)
        {
            let Some(slot) = self.collected.slots.get(usize::from(form.slot))
            else {
                continue;
            };
            let owned = matches!(slot.definition, Maybe::Present(Half { operand: Operand::Data(held), .. }) if held == position);
            if !owned || matches!(slot.refusal, Maybe::Present(_)) {
                continue;
            }
            let mut parameters = Vec::with_capacity(form.parameters.len());
            for parameter in &form.parameters {
                if let Maybe::Present(classifier) = self.value_type_at(parameter.classifier.node) {
                    parameters.push(classifier);
                }
            }
            let mut constructors = Vec::with_capacity(form.generators.len());
            for generator in &form.generators {
                let fields: Vec<ValueTypeId> = generator
                    .fields
                    .iter()
                    .filter_map(|field| match self.value_type_at(field.ty.node) {
                        Maybe::Present(id) => Some(id),
                        Maybe::Absent(_) => None,
                    })
                    .collect();
                constructors.push(fields);
            }
            // Each classifier is read under the parameters and the indices
            // before it already, as the signature's index telescope holds it.
            let indices: Vec<ValueTypeId> = form
                .indices
                .iter()
                .filter_map(|index| match self.value_type_at(index.ty.node) {
                    Maybe::Present(id) => Some(id),
                    Maybe::Absent(_) => None,
                })
                .collect();
            let results: Vec<Vec<ValueId>> = form
                .generators
                .iter()
                .map(|generator| {
                    generator
                        .indices
                        .iter()
                        .filter_map(|index| match self.value_at(index.node) {
                            Maybe::Present(id) => Some(id),
                            Maybe::Absent(_) => None,
                        })
                        .collect()
                })
                .collect();
            let complete = parameters.len() == form.parameters.len()
                && indices.len() == form.indices.len()
                && constructors
                    .iter()
                    .zip(&form.generators)
                    .all(|(fields, generator)| fields.len() == generator.fields.len())
                && results
                    .iter()
                    .zip(&form.generators)
                    .all(|(stated, generator)| stated.len() == generator.indices.len());
            let kind = match form.kind {
                Maybe::Present(written) => self.value_type_at(written.node),
                Maybe::Absent(_) => match self.origin_at(form.declaration.node) {
                    Maybe::Present(origin) => {
                        let id = sink.arena.value_type_universe(
                            Sort::Ground(GroundSort::Value),
                            Level::constant(super::Universe::FUSS_FREE.level),
                        );
                        sink.origins.record_value_type(id, origin);
                        Maybe::Present(id)
                    },
                    Maybe::Absent(reason) => Maybe::Absent(reason),
                },
            };
            let Maybe::Present(kind) = kind
            else {
                continue;
            };
            if !complete {
                continue;
            }
            let (presentation, written) = self.presentation(form);
            // An indexed family presents no rules: the checkers read a
            // presented type's rules over its terms at no index, so the family
            // is declined at its first rule.
            if let (false, Some(&span)) = (form.indices.is_empty(), written.first()) {
                let _first = self
                    .faults
                    .insert(form.slot, LoweringRefusal::OutOfFragment {
                        span,
                        form: FormName::RULE_MEMBER,
                        sort: FragmentSort::Declaration,
                        boundary: FragmentBoundary::Indexed,
                    });
                continue;
            }
            let index = DataIndex::from(self.data.len());
            let signature =
                DataSignature::new(parameters, constructors, kind).presented(presentation);
            let signature = if form.indices.is_empty() {
                signature
            }
            else {
                signature.indexed(indices, results)
            };
            self.data.push(Arc::new(signature));
            self.constructors.push(
                form.generators
                    .iter()
                    .map(|generator| String::from(<&str>::from(self.text_at(generator.named))))
                    .collect(),
            );
            let _first = self.signatures.insert(position, index);
        }
        self.mint_words(sink);
        self.mint_terms(sink);
    }

    /// Mint the words of every family's loops at their point, and each
    /// loop's binding, for the families [`Self::mint_data`] minted.
    ///
    /// # Specification
    /// - requires: the family signatures are minted.
    /// - ensures: per words entry over a minted family, a signature without
    ///   parameters at the family's universe whose constructors are the empty
    ///   word, then each loop's letter and its inverse, each a cons onto a
    ///   word, presented as the words of the loops at their point — the two
    ///   cancellations per loop the presentation mints — its index recorded by
    ///   the entry's position; each loop's binding the path type at the point
    ///   and the word of its one letter. Each letter a cons wrote, and each
    ///   loop's name where its cell declares it, is labelled at the path type,
    ///   and each node of a point an empty word or a cell's side wrote at the
    ///   family, since no core node holds them; the source's letters and empty
    ///   words over words an earlier source minted are labelled at the types
    ///   that source recorded.
    /// - provides: the
    ///   [`DeclarationOutcome::Data`](crate::DeclarationOutcome::Data) outcome
    ///   of a words slot and the completed outcome of a loop.
    /// - fails: never; words over a family that did not mint mint nothing.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a block with one loop mints its words with three
    ///   constructors and two rules, and binds the loop at its path type; a
    ///   word's letters and its empty word's point are labelled.
    /// - witness: `lower::native::tests::a_loop_mints_the_words_at_its_point`
    /// - witness: `lower::native::tests::a_word_conses_its_letters_and_matches_them`
    #[spec(captures: before = self.data.len(), ensures: self.data.len() >= before && self.worded.len() <= self.collected.words.len())]
    fn mint_words(
        &mut self,
        sink: &mut Sink<'_>,
    )
    {
        let mut spelled = Vec::new();
        let mut arities = Vec::new();
        for (index, words) in self
            .collected
            .words
            .iter()
            .enumerate()
            .skip(self.current.words)
        {
            let (Some(&minted), Some(form)) = (
                self.signatures.get(&words.family),
                self.collected.data.get(words.family),
            )
            else {
                continue;
            };
            let constant = |slot: SlotIndex| {
                self.collected
                    .slots
                    .get(usize::from(slot))
                    .map(|entry| entry.constant)
            };
            let (Some(family), Some(own), Some(kind), Maybe::Present(origin)) = (
                constant(form.slot),
                constant(words.slot),
                self.data
                    .get(usize::from(minted))
                    .map(|signature| signature.kind()),
                self.origin_at(form.declaration.node),
            )
            else {
                continue;
            };
            // The source writes the loops, never what their words mint: each
            // node is located at the declaration as an insertion, so no
            // reader takes it for a name written across the whole form.
            let origin = origin.inserted(Insertion::Words);
            let word = sink.arena.value_type_data(own, Vec::new());
            sink.origins.record_value_type(word, origin);
            let mut constructors =
                Vec::with_capacity(words.loops.len().saturating_mul(2).saturating_add(1));
            let mut names = Vec::with_capacity(constructors.capacity());
            constructors.push(Vec::new());
            names.push(String::from(super::identity::HERE));
            for &bound in &words.loops {
                let letter = self
                    .collected
                    .slots
                    .get(usize::from(bound))
                    .map_or("", |entry| entry.name.as_ref());
                constructors.extend([Vec::from([word]), Vec::from([word])]);
                names.extend([String::from(letter), alloc::format!("back({letter})")]);
            }
            let cells = words
                .loops
                .iter()
                .map(|_bound| {
                    gandr_core_term::FreeCell::new(words.point.clone(), words.point.clone())
                })
                .collect();
            let presentation = gandr_core_term::Presentation::words(
                gandr_core_term::FreeCells::new(family, cells),
            );
            let data = DataIndex::from(self.data.len());
            self.data.push(Arc::new(
                DataSignature::new(Vec::new(), constructors, kind).presented(presentation),
            ));
            self.constructors.push(names);
            let _first = self.worded.insert(index, data);
            let mark = sink.arena.watermark();
            let pointed_at = self.words_point(sink.arena, words);
            record_since(sink, mark, origin, Maybe::Absent(rooted::Absent::Unminted));
            let Maybe::Present((carrier, point)) = pointed_at
            else {
                continue;
            };
            let path = sink.arena.value_type_path(carrier, point, point);
            sink.origins.record_value_type(path, origin);
            let _first = self.word_types.insert(index, (path, carrier));
            let lettered = self
                .lettered
                .iter()
                .skip(self.current.lettered)
                .filter(|&&(_, at)| at == index)
                .map(|&(span, _)| (span, path));
            let pointed = self
                .pointed
                .iter()
                .skip(self.current.pointed)
                .filter(|&&(_, at)| at == index)
                .map(|&(span, _)| (span, carrier));
            let at_point = || form.cells.iter().filter(|cell| cell.point == words.point);
            // Each side of a loop spells the point: its nodes are minted apart
            // as the point's terms, each recorded once, written at its node.
            // A side's nodes stand in pre-order, the reverse of mint order.
            arities.clear();
            arities.extend(
                form.generators
                    .iter()
                    .map(|generator| gandr_kernel_term::FieldCount::from(generator.fields.len())),
            );
            for cell in at_point() {
                for side in cell.sides.chunks(words.point.len().max(1)) {
                    spelled.clear();
                    let _point =
                        spelled_point(sink.arena, carrier, (&words.point, &arities), &mut spelled);
                    for (&value, written) in spelled.iter().zip(side.iter().rev()) {
                        sink.origins
                            .record_value(value, Origin::new(written.node, written.span));
                    }
                }
            }
            let named = at_point().map(|cell| (cell.named.span, path));
            let sides =
                at_point().flat_map(|cell| cell.sides.iter().map(|side| (side.span, carrier)));
            for (span, ty) in lettered.chain(pointed).chain(named).chain(sides) {
                sink.origins.record_label(crate::origin::Label {
                    span,
                    labelled: crate::origin::Labelled::ValueType {
                        ty,
                        context: Vec::new(),
                    },
                });
            }
            let nil =
                sink.arena
                    .value_constructor(word, gandr_core_term::FreeCells::nil(), Vec::new());
            sink.origins.record_value(nil, origin);
            for (generator, &bound) in words.loops.iter().enumerate() {
                let letter = sink.arena.value_constructor(
                    word,
                    gandr_core_term::FreeCells::letter(gandr_core_term::CellIndex::from(generator)),
                    Vec::from([nil]),
                );
                sink.origins.record_value(letter, origin);
                let _first = self.looped.insert(bound, (path, letter));
            }
        }
        // A letter or an empty word this source writes over words an earlier
        // source minted is labelled at the types that source recorded.
        let earlier = |&&(span, at): &&(ByteSpan, usize)| {
            (at < self.current.words)
                .then(|| self.word_types.get(&at).map(|&types| (span, types)))?
        };
        let lettered = self
            .lettered
            .iter()
            .skip(self.current.lettered)
            .filter_map(|entry| earlier(&entry))
            .map(|(span, (path, _))| (span, path));
        let pointed = self
            .pointed
            .iter()
            .skip(self.current.pointed)
            .filter_map(|entry| earlier(&entry))
            .map(|(span, (_, carrier))| (span, carrier));
        for (span, ty) in lettered.chain(pointed) {
            sink.origins.record_label(crate::origin::Label {
                span,
                labelled: crate::origin::Labelled::ValueType {
                    ty,
                    context: Vec::new(),
                },
            });
        }
    }

    /// The carrier and the point of `words`: the family's type, and the closed
    /// term the point spells over it.
    ///
    /// # Specification
    /// - requires: `words` is an entry of the collection's words list.
    /// - ensures: the family's type without arguments, and the point as
    ///   [`spelled_point`] mints it over that type.
    /// - provides: the path type `Path(carrier, point, point)` a word at that
    ///   point stands at, for the words' own binding and for a derived
    ///   operation reading its path's type.
    /// - fails: the unminted absence for words over a family the collection
    ///   does not hold, or a point that spells nothing.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::mint_words`], and a derived operation over
    ///   a word.
    /// - witness: `lower::native::tests::a_loop_mints_the_words_at_its_point`
    /// - witness: `lower::identity::tests::a_derived_operation_synthesises_its_path_at_the_words`
    #[spec(ensures: |ret| match ret {
        | Maybe::Present((carrier, point)) => arena.value_type(carrier).is_some() && arena.value(point).is_some(),
        | Maybe::Absent(_) => true,
    })]
    pub(super) fn words_point(
        &self,
        arena: &mut CoreArena,
        words: &WordsForm,
    ) -> Maybe<(ValueTypeId, ValueId), lowered::Absent>
    {
        let Some(form) = self.collected.data.get(words.family)
        else {
            return Maybe::Absent(lowered::Absent::Unminted);
        };
        let Some(family) = self.collected.slots.get(usize::from(form.slot))
        else {
            return Maybe::Absent(lowered::Absent::Unminted);
        };
        let carrier = arena.value_type_data(family.constant, Vec::new());
        let arities: Vec<gandr_kernel_term::FieldCount> = form
            .generators
            .iter()
            .map(|generator| gandr_kernel_term::FieldCount::from(generator.fields.len()))
            .collect();
        let mut minted = Vec::new();
        spelled_point(arena, carrier, (&words.point, &arities), &mut minted)
            .map(|point| (carrier, point))
    }

    /// The words a constant is a word of: a loop's, or the words' own.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the entry of the collection's words list whose slot or one of
    ///   whose loops' slots `constant` is.
    /// - fails: [`worded::Absent::Unworded`] for any other constant.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the loop and the empty word read at their words, and
    ///   a function at none.
    /// - witness: `lower::identity::tests::a_derived_operation_synthesises_its_path_at_the_words`
    #[spec(ensures: |ret| matches!(ret, Maybe::Absent(_)) || matches!(
        self.collected.slots.get(usize::from(constant)).map(|slot| slot.definition),
        Some(Maybe::Present(Half { operand: Operand::Loop { .. } | Operand::Words(_), .. }))
    ))]
    pub(super) fn words_at(
        &self,
        constant: ConstantIndex,
    ) -> Maybe<&WordsForm, worded::Absent>
    {
        let Some(Maybe::Present(Half {
            operand: Operand::Loop { words, .. } | Operand::Words(words),
            ..
        })) = self
            .collected
            .slots
            .get(usize::from(constant))
            .map(|slot| slot.definition)
        else {
            return Maybe::Absent(worded::Absent::Unworded);
        };
        self.collected
            .words
            .get(words)
            .map_or(Maybe::Absent(worded::Absent::Unworded), Maybe::Present)
    }

    /// The rules a data declaration's presented reading writes over its own
    /// constructors, as the checkers read a presented type: each side in
    /// pre-order, a constructor by its tag and a variable by the order its
    /// first occurrence on the left takes; beside them, the bytes each rule's
    /// two sides cover.
    ///
    /// # Specification
    /// - requires: the description route has read the declaration's cells.
    /// - ensures: one rule per face of the presented reading, in rule order,
    ///   whose left side is headed by a constructor, whose two sides apply only
    ///   the declaration's own constructors and whose right side names only
    ///   variables the left binds; the empty presentation when the declaration
    ///   has no presented reading. A face applying an operation rewrites a
    ///   call, not the type's terms, and is left to its operation. The spans
    ///   are parallel to the rules.
    /// - provides: the rules [`DataSignature::presented`] carries to both
    ///   checkers, which validate them against the constructor table.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the circle's two cancellations lower to the rules
    ///   both checkers rewrite its words by, a family without rules lowers to
    ///   the free signature, and an indexed family's rule is declined where it
    ///   is written.
    /// - witness: `lower::native::tests::a_presented_family_lowers_its_rules`
    /// - witness: `lower::native::tests::an_indexed_family_presents_no_rule_2865`
    #[spec(ensures: |ret| ret.0.rules().len() == ret.1.len()
        && ret.1.len() <= match self.collected.descriptions.get(&form.declaration.node) {
            Maybe::Present(described) => described.description.rules.len(),
            Maybe::Absent(_) => 0,
        })]
    fn presentation(
        &self,
        form: &crate::module::DataForm,
    ) -> (gandr_core_term::Presentation, Vec<ByteSpan>)
    {
        let none = || (gandr_core_term::Presentation::default(), Vec::new());
        let Maybe::Present(described) = self.collected.descriptions.get(&form.declaration.node)
        else {
            return none();
        };
        let Some(cells) = self
            .collected
            .cells
            .declarations
            .iter()
            .find(|cells| cells.at.node == form.declaration.node)
        else {
            return none();
        };
        let Maybe::Present(ref presented) = cells.presented
        else {
            return none();
        };
        let names: Vec<SourceFragment<'source>> = form
            .generators
            .iter()
            .map(|generator| self.text_at(generator.named))
            .collect();
        let mut rules = Vec::new();
        let mut spans = Vec::new();
        let faces = if cells.oriented.is_empty() {
            described.description.rules.as_ref()
        }
        else {
            cells.oriented.as_slice()
        };
        let mut variables = Vec::new();
        for &(index, _cell) in &presented.faces {
            let (Some(face), Some(written)) = (
                faces.get(usize::from(index)),
                described.written.faces.get(usize::from(index)),
            )
            else {
                continue;
            };
            variables.clear();
            let (Maybe::Present(left), Maybe::Present(right), Some(from), Some(to)) = (
                rule_side(
                    &face.lhs,
                    &names,
                    &mut variables,
                    Binding::Binds,
                    Heads::Constructors,
                ),
                rule_side(
                    &face.rhs,
                    &names,
                    &mut variables,
                    Binding::Reads,
                    Heads::Constructors,
                ),
                written.left.nodes.first(),
                written.right.nodes.first(),
            )
            else {
                continue;
            };
            if matches!(
                left.first(),
                Some(gandr_core_term::RuleNode::Constructor(_))
            ) {
                rules.push(gandr_core_term::PresentedRule::new(left, right));
                spans.push(from.span.join(to.span));
            }
        }
        (gandr_core_term::Presentation::new(rules), spans)
    }

    /// Mint the terms of every theory a terms type of the source asks for.
    ///
    /// # Specification
    /// - requires: the theories' descriptions and cells are read.
    /// - ensures: per terms entry of the source, a signature without parameters
    ///   at the fuss-free value universe whose constructors are the theory's
    ///   operations in its presentation's order, each taking its inputs as
    ///   terms and named `S.op`, presented by the rules [`Self::term_rules`]
    ///   reads, its index recorded by the entry's position; a fault at the
    ///   entry's slot in its place when the rules do not read. Every node is
    ///   located at the type that asked for the terms, as an insertion.
    /// - provides: the
    ///   [`DeclarationOutcome::Data`](crate::DeclarationOutcome::Data) outcome
    ///   of a terms slot.
    /// - fails: never; an entry whose slot or type has no origin mints nothing.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a unital magma mints its terms with a nullary and a
    ///   binary constructor and its two unit rules.
    /// - witness: `tests::modules::models::a_theory_s_terms_are_its_operations_over_its_rules_4143`
    #[spec(captures: before = self.data.len(), ensures: self.data.len() >= before && self.termed.len() <= self.collected.terms.len())]
    fn mint_terms(
        &mut self,
        sink: &mut Sink<'_>,
    )
    {
        for (index, terms) in self
            .collected
            .terms
            .iter()
            .enumerate()
            .skip(self.current.terms)
        {
            let (Some(own), Some(theory)) = (
                self.collected.slots.get(usize::from(terms.slot)),
                self.collected.slots.get(usize::from(terms.theory)),
            )
            else {
                continue;
            };
            let Maybe::Present(origin) = self.origin_at(own.introduced_by.node)
            else {
                continue;
            };
            let rules = match self.term_rules(terms) {
                Ok(rules) => rules,
                Err(refusal) => {
                    let _first = self.faults.insert(terms.slot, refusal);
                    continue;
                },
            };
            // The source writes the type, never the terms' signature: each
            // node is located at the type as an insertion.
            let origin = origin.inserted(Insertion::Terms);
            let term = sink.arena.value_type_data(own.constant, Vec::new());
            sink.origins.record_value_type(term, origin);
            let kind = sink.arena.value_type_universe(
                Sort::Ground(GroundSort::Value),
                Level::constant(super::Universe::FUSS_FREE.level),
            );
            sink.origins.record_value_type(kind, origin);
            let constructors = terms
                .arities
                .iter()
                .map(|&arity| alloc::vec![term; arity])
                .collect();
            let data = DataIndex::from(self.data.len());
            self.data.push(Arc::new(
                DataSignature::new(Vec::new(), constructors, kind).presented(rules),
            ));
            self.constructors.push(
                terms
                    .operations
                    .iter()
                    .map(|&named| alloc::format!("{}.{}", theory.name, self.text_at(named)))
                    .collect(),
            );
            let _first = self.termed.insert(index, data);
        }
    }

    /// The rules of the theory `terms` are the terms of, read over the terms'
    /// constructors, as the checkers read a presented type.
    ///
    /// # Specification
    /// - requires: the description route has read the theory's cells.
    /// - ensures: one rule per rule of the theory, in rule order, oriented as
    ///   its block orients it: each side in pre-order, an operation by the tag
    ///   of its constructor and a variable by the order its first occurrence on
    ///   the left takes; the empty presentation for a theory the collection
    ///   holds no description of.
    /// - provides: the rules [`DataSignature::presented`] carries to both
    ///   checkers, which validate them against the constructor table: a rule no
    ///   presented type rewrites by is refused there, at the terms.
    /// - fails: [`LoweringRefusal::OutOfFragment`] at [`Unbuilt::TermsType`],
    ///   over the rule's two sides, for a rule a side of which applies what is
    ///   no operation of the theory or reads a variable its left side does not
    ///   bind.
    /// - panics: none.
    ///
    /// # Errors
    /// As the fails clause.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a unital magma's two unit rules lower to rules over
    ///   its terms, and a monoid's associativity reaches the checker, which
    ///   refuses it.
    /// - witness: `tests::modules::models::a_theory_s_terms_are_its_operations_over_its_rules_4143`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |rules| rules.rules().len() <= match self.collected.slots.get(usize::from(terms.theory)).map(|slot| self.collected.descriptions.get(&slot.introduced_by.node)) {
        Some(Maybe::Present(described)) => described.description.rules.len(),
        _ => 0,
    }))]
    fn term_rules(
        &self,
        terms: &TermsForm,
    ) -> Result<gandr_core_term::Presentation, LoweringRefusal<'source>>
    {
        let Some(block) = self
            .collected
            .slots
            .get(usize::from(terms.theory))
            .map(|slot| slot.introduced_by.node)
        else {
            return Ok(gandr_core_term::Presentation::default());
        };
        let Maybe::Present(described) = self.collected.descriptions.get(&block)
        else {
            return Ok(gandr_core_term::Presentation::default());
        };
        let faces = match self
            .collected
            .cells
            .declarations
            .iter()
            .find(|cells| cells.at.node == block)
        {
            Some(cells) if !cells.oriented.is_empty() => cells.oriented.as_slice(),
            Some(_) | None => described.description.rules.as_ref(),
        };
        let names: Vec<SourceFragment<'source>> = terms
            .operations
            .iter()
            .map(|&named| self.text_at(named))
            .collect();
        let mut rules = Vec::with_capacity(faces.len());
        let mut variables = Vec::new();
        for (face, written) in faces.iter().zip(&described.written.faces) {
            variables.clear();
            let (Maybe::Present(left), Maybe::Present(right)) = (
                rule_side(
                    &face.lhs,
                    &names,
                    &mut variables,
                    Binding::Binds,
                    Heads::Operations,
                ),
                rule_side(
                    &face.rhs,
                    &names,
                    &mut variables,
                    Binding::Reads,
                    Heads::Operations,
                ),
            )
            else {
                let span = match (written.left.nodes.first(), written.right.nodes.first()) {
                    (Some(from), Some(to)) => from.span.join(to.span),
                    _ => described.at.span,
                };
                return Err(LoweringRefusal::OutOfFragment {
                    span,
                    form: FormName::RULE_MEMBER,
                    sort: FragmentSort::Declaration,
                    boundary: FragmentBoundary::Unadmitted(Unbuilt::TermsType),
                });
            };
            rules.push(gandr_core_term::PresentedRule::new(left, right));
        }

        Ok(gandr_core_term::Presentation::new(rules))
    }

    /// Mint the nominal type of the family at `constant` over the arguments
    /// `arguments` names in the operand store.
    ///
    /// # Specification
    /// - requires: every argument is already minted or absent.
    /// - ensures: the family over its arguments, left to right, with the
    ///   written origin; nothing when an argument did not lower.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::family`].
    /// - witness: `lower::native::tests::a_data_family_applies_to_its_parameters`
    #[spec(ensures: |ret| matches!(ret, Maybe::Absent(_) | Maybe::Present(Lowered::ValueType(_))))]
    pub(super) fn mint_family(
        &self,
        constant: ConstantIndex,
        arguments: Stretch,
        sink: &mut Sink<'_>,
        origin: Origin,
    ) -> Maybe<Lowered, lowered::Absent>
    {
        let mut passed = Vec::with_capacity(arguments.end.saturating_sub(arguments.start));
        for position in arguments.start .. arguments.end {
            let Some(&argument) = self.operands.get(position)
            else {
                return Maybe::Absent(lowered::Absent::Unminted);
            };
            match self.value_at(argument) {
                Maybe::Present(value) => passed.push(value),
                Maybe::Absent(reason) => return Maybe::Absent(reason),
            }
        }
        let id = sink.arena.value_type_data(constant, passed);
        sink.origins.record_value_type(id, origin);

        Maybe::Present(Lowered::ValueType(id))
    }

    /// Mint the nominal computation type of the codata family at `constant`
    /// over the arguments `arguments` names in the operand store.
    ///
    /// # Specification
    /// - requires: every argument is already minted or absent.
    /// - ensures: the family over its arguments, left to right, with the
    ///   written origin; nothing when an argument did not lower.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::codata_type`].
    /// - witness: `description::tests::a_codata_declaration_lowers_to_its_signature`
    #[spec(ensures: |ret| matches!(ret, Maybe::Absent(_) | Maybe::Present(Lowered::CompType(_))))]
    pub(super) fn mint_codata(
        &self,
        constant: ConstantIndex,
        arguments: Stretch,
        sink: &mut Sink<'_>,
        origin: Origin,
    ) -> Maybe<Lowered, lowered::Absent>
    {
        let mut passed = Vec::with_capacity(arguments.end.saturating_sub(arguments.start));
        for position in arguments.start .. arguments.end {
            let Some(&argument) = self.operands.get(position)
            else {
                return Maybe::Absent(lowered::Absent::Unminted);
            };
            match self.value_at(argument) {
                Maybe::Present(value) => passed.push(value),
                Maybe::Absent(reason) => return Maybe::Absent(reason),
            }
        }
        let id = sink.arena.comp_type_codata(constant, passed);
        sink.origins.record_comp_type(id, origin);

        Maybe::Present(Lowered::CompType(id))
    }

    /// Mint a constructor over its fields and its classifier.
    ///
    /// # Specification
    /// - requires: every field, the annotation's type and the answer's are
    ///   already minted or absent; for a slot, the family's parameter type and
    ///   every argument before the constructor's are too.
    /// - ensures: the constructor value over its fields, its classifier the
    ///   annotation's type — or the type a family's argument quotes — carried
    ///   into the term's binders; the value type the answer's returner returns
    ///   carried from the answer's frame to the constructor's; for a slot, the
    ///   family's parameter at the constructor's place with the parameters
    ///   before it replaced by the arguments written for them; or the family
    ///   over no arguments; the classifier's origin inserted and the written
    ///   origin on the value; a classifier of another family than the
    ///   constructor's own gives way to that family, over the classifier's
    ///   arguments when it has as many as the family takes and over none
    ///   otherwise, and the constructor so classified stands ascribed the
    ///   classifier, so the checker meets the type the source wrote for it
    ///   rather than the namesake constructor of another family of one shape;
    ///   nothing when a field, the annotation, the answer or a slot's type or
    ///   argument did not lower, or the answer is no returner.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::construct`].
    /// - witness: `lower::native::tests::a_constructor_applies_to_its_fields`
    /// - witness: `lower::native::tests::a_constructor_takes_its_slot_as_a_family_argument_421`
    /// - witness: `lower::native::tests::a_constructor_keeps_its_family_under_another_s_classifier_2075`
    #[spec(ensures: |ret| matches!(ret, Maybe::Absent(_) | Maybe::Present(Lowered::Value(_))))]
    pub(super) fn mint_constructor(
        &self,
        constructed: Constructed,
        sink: &mut Sink<'_>,
        origin: Origin,
    ) -> Maybe<Lowered, lowered::Absent>
    {
        let mut fields = Vec::new();
        for position in constructed.fields.start .. constructed.fields.end {
            let Some(&field) = self.operands.get(position)
            else {
                return Maybe::Absent(lowered::Absent::Unminted);
            };
            match self.value_at(field) {
                Maybe::Present(value) => fields.push(value),
                Maybe::Absent(reason) => return Maybe::Absent(reason),
            }
        }
        let written =
            match self.classifier_type(constructed.classifier, constructed.family, sink, origin) {
                Maybe::Present(id) => id,
                Maybe::Absent(reason) => return Maybe::Absent(reason),
            };
        // A constructor's tag counts within its own family: under a classifier
        // of another family it would name that family's constructor of the
        // same place.
        let own = match sink.arena.value_type(written) {
            Some(&gandr_core_term::ValueType::Data {
                declaration,
                ref arguments,
            }) if declaration != constructed.family => {
                let takes = match self.data_family(constructed.family) {
                    Maybe::Present(count) => usize::from(count),
                    Maybe::Absent(_) => 0_usize,
                };
                let carried = if arguments.len() == takes {
                    arguments.clone()
                }
                else {
                    Vec::new()
                };
                let id = sink.arena.value_type_data(constructed.family, carried);
                sink.origins
                    .record_value_type(id, origin.inserted(Insertion::Classifier));
                Some(id)
            },
            _ => None,
        };
        let Some(classifier) = own
        else {
            let id = sink
                .arena
                .value_constructor(written, constructed.tag, fields);
            return Maybe::Present(sink.value(id, origin));
        };
        let id = sink
            .arena
            .value_constructor(classifier, constructed.tag, fields);
        sink.origins.record_value(id, origin);
        let ascribed = sink.arena.value_ascribe(id, written);

        Maybe::Present(sink.value(ascribed, origin))
    }

    /// The value type `classifier` names for a constructor of the family
    /// `family`, minted in the term context of the constructor's frame.
    ///
    /// # Specification
    /// - requires: as [`Self::mint_constructor`]; for a field's classifier, the
    ///   field's declared type, the constructor it belongs to, that
    ///   constructor's classifier and its fields before the field are minted or
    ///   absent.
    /// - ensures: the annotation's type — or the type a family's argument
    ///   quotes — carried into the term's binders, or kept at the signature's
    ///   when the constructor stands inside a signature type, whose terms count
    ///   only the frames that bind there; the value type the answer's returner
    ///   returns carried from the answer's frame to the constructor's; for a
    ///   slot, the family's parameter at the constructor's place with the
    ///   parameters before it replaced by the arguments written for them; for a
    ///   declaration's parameter, its written type with the parameters before
    ///   it replaced by the call's arguments for them; for a field, its
    ///   declared type with the family's parameters replaced by the arguments
    ///   of its constructor's classifier and the fields before it by the values
    ///   written for them; for a stated index, the family's index type at its
    ///   place with the earlier indices replaced by those the generator states
    ///   and the parameters by the generator's own; or the family over no
    ///   arguments; every node minted recorded at the classifier's inserted
    ///   origin; nothing when a type or a value it reads did not lower, or the
    ///   answer is no returner.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::construct`].
    /// - witness: `lower::native::tests::a_constructor_applies_to_its_fields`
    /// - witness: `lower::native::tests::a_constructor_takes_its_slot_as_a_family_argument_421`
    /// - witness: `lower::native::tests::a_field_classifies_the_constructor_written_in_it_1171`
    /// - witness: `lower::native::tests::an_annotation_inside_a_signature_type_counts_its_binders_there_3744`
    /// - witness: `lower::native::tests::a_constructor_at_a_family_s_index_takes_the_index_s_type_4027`
    #[spec(ensures: |ret| matches!(ret, Maybe::Absent(_)) || matches!(ret, Maybe::Present(id) if sink.arena.value_type(id).is_some()))]
    fn classifier_type(
        &self,
        classifier: Classifier,
        family: ConstantIndex,
        sink: &mut Sink<'_>,
        origin: Origin,
    ) -> Maybe<ValueTypeId, lowered::Absent>
    {
        let classified = origin.inserted(Insertion::Classifier);
        // A field's classifier reads the classifier of the constructor around
        // it: follow those out to the first that is no field's, the
        // constructor that owns it.
        let (mut classifier, mut family) = (classifier, family);
        let mut owner = origin.node();
        let mut fields = Vec::new();
        while let Classifier::Field(field) = classifier {
            let Some(&Plan::Constructor(outer)) = self.plans.get(field.around)
            else {
                return Maybe::Absent(lowered::Absent::Unminted);
            };
            fields.push(field);
            owner = field.around;
            (classifier, family) = (outer.classifier, outer.family);
        }
        let outermost = match classifier {
            Classifier::Written(written) => {
                // A type written as a family's argument is read as its code;
                // the classifier is the type it quotes.
                let quoted = if let Maybe::Present(code) = self.value_at(written)
                    && let Some(&gandr_core_term::Value::Quote(quoted)) = sink.arena.value(code)
                {
                    Some(quoted)
                }
                else {
                    None
                };
                let id = match (self.value_type_at(written), quoted) {
                    (Maybe::Present(id), _) => id,
                    (Maybe::Absent(_), Some(quoted)) => quoted,
                    (Maybe::Absent(_), None) => return Maybe::Absent(lowered::Absent::Unminted),
                };
                // A constructor inside a signature type counts its fields in
                // the signature's telescope: its annotation stays there too.
                if self.in_type.contains(&owner) && !self.in_quote.contains(&owner) {
                    id
                }
                else {
                    let frame = self.reading(written).frame();
                    self.relocate_value_type(id, frame, Telescope::Signature, sink, classified)
                }
            },
            Classifier::Slot(argued) => match self.slot_type(argued, sink, classified) {
                Maybe::Present(id) => id,
                Maybe::Absent(reason) => return Maybe::Absent(reason),
            },
            Classifier::Stated(stated) => match self.stated_index_type(stated, sink, classified) {
                Maybe::Present(id) => id,
                Maybe::Absent(reason) => return Maybe::Absent(reason),
            },
            Classifier::Parameter(declared) => {
                match self.called_parameter_type(declared, sink, classified) {
                    Maybe::Present(id) => id,
                    Maybe::Absent(reason) => return Maybe::Absent(reason),
                }
            },
            Classifier::Answered { answer, frame } => {
                let mark = sink.arena.watermark();
                let written = self.answered_type(answer, sink);
                let Maybe::Present(written) = written
                else {
                    return Maybe::Absent(lowered::Absent::Unminted);
                };
                let written = self.unfolded(written, sink);
                let gap = self
                    .scope
                    .telescope_binders(frame)
                    .count()
                    .saturating_sub(self.scope.telescope_binders(answer.frame).count());
                let lift = Binders::from(u32::try_from(gap).unwrap_or(u32::MAX));
                let mut copies = Vec::new();
                let carried = self.relocate(
                    sink.arena,
                    written,
                    answer.frame,
                    Telescope::Signature,
                    lift,
                    Some(&mut copies),
                );
                record_copied_since(
                    sink,
                    mark,
                    origin.inserted(Insertion::Classifier),
                    Maybe::Absent(rooted::Absent::Classifier),
                    &copies,
                );
                let Some(&CompType::Returner { result, .. }) = sink.arena.comp_type(carried)
                else {
                    return Maybe::Absent(lowered::Absent::OtherSort);
                };
                result
            },
            Classifier::Inserted => {
                let id = sink.arena.value_type_data(family, Vec::new());
                sink.origins.record_value_type(id, classified);
                id
            },
            // The loop above leaves no field's classifier.
            Classifier::Field(_) => return Maybe::Absent(lowered::Absent::Unminted),
        };
        let mut ty = outermost;
        for field in fields.into_iter().rev() {
            ty = match self.field_type(field, ty, sink, origin) {
                Maybe::Present(id) => id,
                Maybe::Absent(reason) => return Maybe::Absent(reason),
            };
        }

        Maybe::Present(ty)
    }

    /// The type `field` gives a constructor written in it, given `applied`,
    /// the classifier of the constructor the field belongs to.
    ///
    /// # Specification
    /// - requires: the field's declared type and the constructor's fields
    ///   before it are minted or absent; `applied` is minted in the
    ///   constructor's frame.
    /// - ensures: the field's declared type with the family's parameters
    ///   replaced by `applied`'s arguments and the fields before it by the
    ///   values the constructor is written with, every node the substitution
    ///   mints recorded at the classifier's inserted origin; nothing when the
    ///   field's constructor plans no constructor, `applied` is no application
    ///   of a family to at least the family's parameters, or a type or a value
    ///   it reads did not lower.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a list written in a field typed `List(Integer)`, in
    ///   one typed `List(a)` of a family applied to `Integer`, and in one
    ///   naming the field before it.
    /// - witness: `lower::native::tests::a_field_classifies_the_constructor_written_in_it_1171`
    #[spec(ensures: |ret| matches!(ret, Maybe::Absent(_)) || matches!(ret, Maybe::Present(id) if sink.arena.value_type(id).is_some()))]
    fn field_type(
        &self,
        field: FieldOf,
        applied: ValueTypeId,
        sink: &mut Sink<'_>,
        origin: Origin,
    ) -> Maybe<ValueTypeId, lowered::Absent>
    {
        let unminted = Maybe::Absent(lowered::Absent::Unminted);
        let Some(&Plan::Constructor(outer)) = self.plans.get(field.around)
        else {
            return unminted;
        };
        let Some(&gandr_core_term::ValueType::Data { ref arguments, .. }) =
            sink.arena.value_type(applied)
        else {
            return unminted;
        };
        let mut environment: Vec<ValueId> =
            arguments.iter().take(field.parameters).copied().collect();
        if environment.len() != field.parameters {
            return unminted;
        }
        for position in outer.fields.start .. outer.fields.start.saturating_add(field.index) {
            let Some(&written) = self.operands.get(position)
            else {
                return unminted;
            };
            match self.value_at(written) {
                Maybe::Present(value) => environment.push(value),
                Maybe::Absent(reason) => return Maybe::Absent(reason),
            }
        }
        let declared = match self.value_type_at(field.declared) {
            Maybe::Present(declared) => declared,
            Maybe::Absent(reason) => return Maybe::Absent(reason),
        };
        // The innermost binder is the last field before this one.
        environment.reverse();
        instantiated(
            declared,
            &environment,
            sink,
            origin.inserted(Insertion::Classifier),
        )
    }

    /// The type a data family's application gives the argument at `argued`'s
    /// place.
    ///
    /// # Specification
    /// - requires: the family's parameter and index types and the arguments
    ///   before the place are minted or absent.
    /// - ensures: the family's parameter, or index, at the place, read under
    ///   the parameters and indices before it, with each of those replaced by
    ///   the argument written for it, every node the substitution mints
    ///   recorded at `origin`; nothing when the classifier or an argument did
    ///   not lower.
    /// - provides: the classifier of a constructor written as a family's
    ///   argument (#421).
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — `Inl(a)` written for the third parameter `s :
    ///   SumOb(l, r)` of a family applied to `Integer` and `String` is
    ///   classified `SumOb(Integer, String)`; `S(Z)` written for a vector's
    ///   length is classified `Nat`.
    /// - witness: `lower::native::tests::a_constructor_takes_its_slot_as_a_family_argument_421`
    /// - witness: `lower::native::tests::an_indexed_family_lowers_its_indices`
    #[spec(ensures: |ret| matches!(ret, Maybe::Absent(_)) || matches!(ret, Maybe::Present(id) if sink.arena.value_type(id).is_some()))]
    fn slot_type(
        &self,
        argued: Argued,
        sink: &mut Sink<'_>,
        origin: Origin,
    ) -> Maybe<ValueTypeId, lowered::Absent>
    {
        let Some(form) = self.collected.data.get(argued.form)
        else {
            return Maybe::Absent(lowered::Absent::Unminted);
        };
        // An index reads under the parameters and the indices before it.
        let parameters = form.parameters.len();
        let classifier = argued.place.checked_sub(parameters).map_or_else(
            || {
                form.parameters
                    .get(argued.place)
                    .map(|parameter| parameter.classifier)
            },
            |index| form.indices.get(index).map(|index| index.ty),
        );
        let Some(classifier) = classifier
        else {
            return Maybe::Absent(lowered::Absent::Unminted);
        };
        let declared = match self.value_type_at(classifier.node) {
            Maybe::Present(declared) => declared,
            Maybe::Absent(reason) => return Maybe::Absent(reason),
        };
        let bound = argued.place;
        let mut environment = Vec::with_capacity(bound);
        for &argument in stretch(&self.operands, argued.applied).iter().take(bound) {
            match self.value_at(argument) {
                Maybe::Present(value) => environment.push(value),
                Maybe::Absent(reason) => return Maybe::Absent(reason),
            }
        }
        // The innermost parameter is the last before the place.
        environment.reverse();
        instantiated(declared, &environment, sink, origin)
    }

    /// The type a generator's result gives the index it states at `stated`'s
    /// place.
    ///
    /// # Specification
    /// - requires: the family's index types and the indices the generator
    ///   states before the place are minted or absent.
    /// - ensures: the family's index at the place, read under the family's
    ///   parameters and the indices before it, with each earlier index replaced
    ///   by the index the generator states for it and each parameter by the
    ///   generator's own, read past its fields; every node the substitution
    ///   mints recorded at `origin`; nothing when the index type or an earlier
    ///   stated index did not lower.
    /// - provides: the classifier of a constructor written as an index a
    ///   generator's result states (#4027).
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — `FZ(Zero)` stated for an index of type
    ///   `Fin(Succ(Zero))` is classified so, and `FZ(n)` stated after `n` for
    ///   an index of type `Fin(Succ(m))` reads the `n` stated before it.
    /// - witness: `lower::native::tests::a_constructor_at_a_family_s_index_takes_the_index_s_type_4027`
    #[spec(ensures: |ret| matches!(ret, Maybe::Absent(_)) || matches!(ret, Maybe::Present(id) if sink.arena.value_type(id).is_some()))]
    fn stated_index_type(
        &self,
        stated: StatedIndex,
        sink: &mut Sink<'_>,
        origin: Origin,
    ) -> Maybe<ValueTypeId, lowered::Absent>
    {
        let unminted = Maybe::Absent(lowered::Absent::Unminted);
        let Some(form) = self.collected.data.get(stated.form)
        else {
            return unminted;
        };
        let (Some(generator), Some(index)) = (
            form.generators.get(stated.generator),
            form.indices.get(stated.place),
        )
        else {
            return unminted;
        };
        let declared = match self.value_type_at(index.ty.node) {
            Maybe::Present(declared) => declared,
            Maybe::Absent(reason) => return Maybe::Absent(reason),
        };
        let parameters = form.parameters.len();
        let mut environment = Vec::with_capacity(parameters.saturating_add(stated.place));
        for earlier in generator.indices.iter().take(stated.place) {
            match self.value_at(earlier.node) {
                Maybe::Present(value) => environment.push(value),
                Maybe::Absent(reason) => return Maybe::Absent(reason),
            }
        }
        // The innermost binder is the last index stated before the place.
        environment.reverse();
        // The parameters stand past the generator's fields, each of which
        // binds where the result states an index; the last is innermost.
        let fields = generator.fields.len();
        for parameter in 0 .. parameters {
            let Ok(at) = u32::try_from(fields.saturating_add(parameter))
            else {
                return unminted;
            };
            let variable = sink
                .arena
                .value_variable(Zone::Intuitionistic, DeBruijnIndex::from(at));
            sink.origins.record_value(variable, origin);
            environment.push(variable);
        }
        instantiated(declared, &environment, sink, origin)
    }

    /// The type a declaration's parameter gives the argument a call writes for
    /// it.
    ///
    /// # Specification
    /// - requires: the parameter's type and the call's arguments are minted or
    ///   absent.
    /// - ensures: the parameter's written type, read under the declaration's
    ///   parameters before it, with each of those it names replaced by the
    ///   argument the call writes for it, every node the substitution mints
    ///   recorded at `origin`; the written type itself when it names none;
    ///   nothing when it names a binder no argument stands for — a linear one,
    ///   or one the declaration's parentheses do not bind — or a type or an
    ///   argument it reads did not lower.
    /// - provides: the classifier of a constructor written as a call's argument
    ///   (#1833, #1876).
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a list passed for `xs : List(Integer)` is classified
    ///   as written, and one passed for `xs : List(a)` after `Integer` for `a :
    ///   Type` is classified `List(Integer)`, a recursive declaration's own
    ///   binder standing between the two.
    /// - witness: `lower::native::tests::a_constructor_argument_takes_its_parameter_s_type_1833`
    /// - witness: `lower::native::tests::a_constructor_argument_reads_the_arguments_before_it_1876`
    #[spec(ensures: |ret| matches!(ret, Maybe::Absent(_)) || matches!(ret, Maybe::Present(id) if sink.arena.value_type(id).is_some()))]
    fn called_parameter_type(
        &self,
        declared: CalledAt,
        sink: &mut Sink<'_>,
        origin: Origin,
    ) -> Maybe<ValueTypeId, lowered::Absent>
    {
        let (written, environment) =
            match self.called_environment(declared, declared.typed.node, sink) {
                Maybe::Present(read) => read,
                Maybe::Absent(reason) => return Maybe::Absent(reason),
            };
        if environment.is_empty() {
            return Maybe::Present(written);
        }
        instantiated(written, &environment, sink, origin)
    }

    /// The type written at `written`, read under the parameters before the
    /// one `declared` names, beside the arguments the call writes for the
    /// parameters it names: what [`Self::called_parameter_type`] substitutes.
    ///
    /// # Specification
    /// - requires: `written` is read under the frame `declared`'s type is read
    ///   under; the type and the call's arguments are minted or absent.
    /// - ensures: the written type, and an environment, innermost first, that
    ///   holds the argument the call writes for each parameter the type names,
    ///   and any one of them for a binder between them it does not name; empty
    ///   when the type names none.
    /// - fails: the type's own absence; the unminted absence when it names a
    ///   binder no argument stands for — a linear one, or one the declaration's
    ///   parentheses do not bind; an argument's own absence.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::called_parameter_type`], and a lambda's
    ///   binder at a parameter's domain.
    /// - witness: `lower::native::tests::a_constructor_argument_reads_the_arguments_before_it_1876`
    /// - witness: `lower::identity::tests::a_call_s_lambda_argument_reads_its_parameter_s_domain_3921`
    #[spec(ensures: |ret| matches!(ret, Maybe::Absent(_)) || matches!(ret, Maybe::Present((id, _)) if sink.arena.value_type(id).is_some()))]
    pub(super) fn called_environment(
        &self,
        declared: CalledAt,
        written: NodeIndex,
        sink: &Sink<'_>,
    ) -> Maybe<(ValueTypeId, Vec<ValueId>), lowered::Absent>
    {
        let unminted = Maybe::Absent(lowered::Absent::Unminted);
        let written = match self.value_type_at(written) {
            Maybe::Present(read) => read,
            Maybe::Absent(reason) => return Maybe::Absent(reason),
        };
        let Some(support) = sink.arena.value_type_support(written)
        else {
            return unminted;
        };
        if support.indices(Zone::Linear).next().is_some() {
            return unminted;
        }
        let Some(parameters) = self.collected.parameters.get(&declared.slot)
        else {
            return unminted;
        };
        // The binders the type counts its indices by, innermost first: the
        // parameters before it its signature names, and whatever else binds
        // there, a recursive declaration's own binder among them.
        let bound: Vec<ScopeId> = self
            .scope
            .chain(self.reading(declared.typed.node).frame())
            .filter(|&binder| {
                self.scope.zone(binder) != Zone::Linear
                    && bool::from(self.scope.binds(binder, Telescope::Signature))
            })
            .collect();
        let applied = stretch(&self.operands, declared.applied);
        // Each parameter's argument, by the bytes its binder is written at.
        let arguments: BTreeMap<ByteSpan, NodeIndex> = parameters
            .iter()
            .zip(applied)
            .map(|(parameter, &argument)| (parameter.binder.span, argument))
            .collect();
        let mut environment: Vec<Option<ValueId>> = Vec::new();
        for index in support.indices(Zone::Intuitionistic) {
            let Ok(at) = usize::try_from(u32::from(index))
            else {
                return unminted;
            };
            let Some(&binder) = bound.get(at)
            else {
                return unminted;
            };
            let Maybe::Present(site) = self.scope.site(binder)
            else {
                return unminted;
            };
            let Some(&argument) = arguments.get(&site)
            else {
                return unminted;
            };
            let value = match self.value_at(argument) {
                Maybe::Present(value) => value,
                Maybe::Absent(reason) => return Maybe::Absent(reason),
            };
            if environment.len() <= at {
                environment.resize(at.saturating_add(1), None);
            }
            if let Some(entry) = environment.get_mut(at) {
                *entry = Some(value);
            }
        }
        // A binder between the named ones that the type does not name takes
        // any value: no index reaches it.
        let Some(&filler) = environment.iter().flatten().next()
        else {
            return Maybe::Present((written, Vec::new()));
        };
        let environment: Vec<ValueId> = environment
            .into_iter()
            .map(|entry| entry.unwrap_or(filler))
            .collect();

        Maybe::Present((written, environment))
    }

    /// `ty`, a value type read under `frame` in `telescope`, carried into the
    /// term context of the same frame.
    ///
    /// # Specification
    /// - requires: `ty` is minted under `frame`, counting only the frames that
    ///   bind in `telescope`.
    /// - ensures: as [`Self::carry_value_type`] to `frame` itself.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a closed annotation is carried unchanged, and one
    ///   under a match's binders keeps each of its nodes at its bytes.
    /// - witness: `lower::native::tests::a_parameterized_constructor_needs_its_classifier`
    /// - witness: `lower::native::tests::a_relocated_annotation_keeps_its_bytes`
    #[spec(ensures: |ret| sink.arena.value_type(ret).is_some() || ret == ty)]
    pub(super) fn relocate_value_type(
        &self,
        ty: ValueTypeId,
        frame: Frame,
        telescope: Telescope,
        sink: &mut Sink<'_>,
        origin: Origin,
    ) -> ValueTypeId
    {
        self.carry_value_type(ty, frame, telescope, frame, sink, origin)
    }

    /// `ty`, a value type read under `from` in `telescope`, carried into the
    /// term context of `to`, a frame whose chain passes through `from`.
    ///
    /// # Specification
    /// - requires: `ty` is minted under `from`, counting only the frames that
    ///   bind in `telescope`; `from` is `to` or a frame of `to`'s chain.
    /// - ensures: `ty` itself when every frame of `from`'s chain binds and `to`
    ///   is `from`; otherwise `ty` with a binder inserted for each frame of
    ///   `from`'s chain that does not bind, then every free index raised by the
    ///   intuitionistic frames `to`'s chain has past `from`, each node the
    ///   rewrite copies recorded at the origin of the node it copies and every
    ///   other node it mints with `origin`.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a closed annotation is carried unchanged; a type a
    ///   scope fixes to a parameter is read at the scope and at an exercise
    ///   under it.
    /// - witness: `lower::native::tests::a_relocated_annotation_keeps_its_bytes`
    /// - witness: `lower::capability::tests::a_scope_fixing_a_sort_to_a_parameter_reads_it_where_it_is_used_2881`
    #[spec(ensures: |ret| sink.arena.value_type(ret).is_some() || ret == ty)]
    pub(super) fn carry_value_type(
        &self,
        ty: ValueTypeId,
        from: Frame,
        telescope: Telescope,
        to: Frame,
        sink: &mut Sink<'_>,
        origin: Origin,
    ) -> ValueTypeId
    {
        let gap = self
            .scope
            .telescope_binders(to)
            .count()
            .saturating_sub(self.scope.telescope_binders(from).count());
        let lift = Binders::from(u32::try_from(gap).unwrap_or(u32::MAX));
        if lift == Binders::NONE && self.scope.binders_in(from, telescope).all(|binds| binds) {
            return ty;
        }
        let mark = sink.arena.watermark();
        let wrapped = sink.arena.comp_type_returner(ty);
        let mut copies = Vec::new();
        let carried = self.relocate(
            sink.arena,
            wrapped,
            from,
            telescope,
            lift,
            Some(&mut copies),
        );
        let result = match sink.arena.comp_type(carried) {
            Some(&CompType::Returner { result: inner, .. }) => inner,
            _ => ty,
        };
        record_copied_since(
            sink,
            mark,
            origin,
            Maybe::Absent(rooted::Absent::Classifier),
            &copies,
        );

        result
    }

    /// `ty`, a value type read under `from` in `telescope`, carried under
    /// `to` in the same telescope, a frame whose chain passes through `from`.
    ///
    /// # Specification
    /// - requires: `ty` is minted under `from`, counting only the frames that
    ///   bind in `telescope`; `from` is `to` or a frame of `to`'s chain.
    /// - ensures: `ty` itself when no frame between `from` and `to` binds in
    ///   `telescope`; otherwise `ty` with every free index raised by the frames
    ///   between that bind, each node the shift copies recorded at the origin
    ///   of the node it copies and every other node it mints with `origin`.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a typed parameter of a lambda inside a type, under a
    ///   parameter the type does not name, binds its argument at its written
    ///   type.
    /// - witness: `lower::identity::tests::an_annotation_inside_a_type_reads_in_the_type_s_telescope_3801`
    #[spec(ensures: |ret| sink.arena.value_type(ret).is_some() || ret == ty)]
    pub(super) fn lift_value_type(
        &self,
        ty: ValueTypeId,
        from: Frame,
        telescope: Telescope,
        to: Frame,
        sink: &mut Sink<'_>,
        origin: Origin,
    ) -> ValueTypeId
    {
        let bound = |frame| {
            self.scope
                .binders_in(frame, telescope)
                .filter(|&binds| binds)
                .count()
        };
        let gap = bound(to).saturating_sub(bound(from));
        let lift = Binders::from(u32::try_from(gap).unwrap_or(u32::MAX));
        if lift == Binders::NONE {
            return ty;
        }
        let mark = sink.arena.watermark();
        let mut copies = Vec::new();
        let lifted = gandr_core_term::shift_value_type(sink.arena, ty, lift)
            .settle_traced(sink.arena, &mut copies);
        record_copied_since(
            sink,
            mark,
            origin,
            Maybe::Absent(rooted::Absent::Classifier),
            &copies,
        );

        lifted
    }

    /// `ty`, a computation type read under `frame` in `telescope`, carried
    /// into the term context of the same frame.
    ///
    /// # Specification
    /// - requires: `ty` is minted under `frame`, counting only the frames that
    ///   bind in `telescope`.
    /// - ensures: as [`Self::relocate_value_type`], for a computation type.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a computation type quoted in a body past an
    ///   unmentioned parameter reads its binders in the term's context.
    /// - witness: `lower::tests::a_quote_in_a_body_reads_past_an_unmentioned_parameter`
    #[spec(ensures: |ret| sink.arena.comp_type(ret).is_some() || ret == ty)]
    pub(super) fn relocate_comp_type(
        &self,
        ty: CompTypeId,
        frame: Frame,
        telescope: Telescope,
        sink: &mut Sink<'_>,
        origin: Origin,
    ) -> CompTypeId
    {
        if self.scope.binders_in(frame, telescope).all(|binds| binds) {
            return ty;
        }
        let mark = sink.arena.watermark();
        let mut copies = Vec::new();
        let carried = self.relocate(
            sink.arena,
            ty,
            frame,
            telescope,
            Binders::default(),
            Some(&mut copies),
        );
        record_copied_since(
            sink,
            mark,
            origin,
            Maybe::Absent(rooted::Absent::Classifier),
            &copies,
        );

        carried
    }

    /// The computation type `answer` states, read under its own frame: the
    /// written computation type, the returner over a written value type the
    /// position returns, or the arrows an alias stands for past the domains
    /// taken.
    ///
    /// # Specification
    /// - requires: the answer's node is already minted or absent.
    /// - ensures: the node's computation type for a written answer and a loop
    ///   arm's, a returner newly minted over the node's value type for a
    ///   returning one, and for a valued one the computation type the alias's
    ///   thunk holds, its first `taken` arrows peeled; each with every stage a
    ///   quantified signature placed erased, since a body's types are plain;
    ///   the node's absence when it did not lower, and the other-sort absence
    ///   for an alias holding fewer arrows.
    /// - provides: the one reading every consumer of an answer mints it by.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Termination
    /// The peeling loop runs `taken` times.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a function result and a thunk signed `() => T`, each
    ///   answering a constructor's classifier, and a match under a lambda
    ///   signed `A => B` answering `-F B`.
    /// - witness: `lower::native::tests::a_constructor_takes_its_classifier_from_the_type_it_answers_402`
    /// - witness: `lower::native::tests::a_lambda_under_a_value_function_alias_lowers_as_under_its_thunked_arrow_808`
    /// - witness: `lower::staged::tests::a_case_under_a_staged_result_answers_plainly`
    #[spec(ensures: |ret| matches!(ret, Maybe::Absent(_)) || matches!(ret, Maybe::Present(id) if sink.arena.comp_type(id).is_some()))]
    pub(super) fn answered_type(
        &self,
        answer: Answer,
        sink: &mut Sink<'_>,
    ) -> Maybe<CompTypeId, lowered::Absent>
    {
        let answered = match answer.over {
            Over::Written | Over::Loop { .. } => self.comp_type_at(answer.node),
            Over::Returning => match self.value_type_at(answer.node) {
                Maybe::Present(result) => Maybe::Present(sink.arena.comp_type_returner(result)),
                Maybe::Absent(reason) => Maybe::Absent(reason),
            },
            Over::Valued { taken } => {
                let alias = match self.value_type_at(answer.node) {
                    Maybe::Present(alias) => alias,
                    Maybe::Absent(reason) => return Maybe::Absent(reason),
                };
                let Some(&gandr_core_term::ValueType::Thunk(mut held)) =
                    sink.arena.value_type(alias)
                else {
                    return Maybe::Absent(lowered::Absent::OtherSort);
                };
                for _taken in 0 .. taken {
                    let Some(&CompType::Arrow { codomain, .. }) = sink.arena.comp_type(held)
                    else {
                        return Maybe::Absent(lowered::Absent::OtherSort);
                    };
                    held = codomain;
                }
                Maybe::Present(held)
            },
        };
        match answered {
            Maybe::Present(written) if !self.stage_marks.is_empty() => {
                match gandr_core_term::staged::unstaged(sink.arena, Part::Computation(written)) {
                    Some(Part::Computation(plain)) => Maybe::Present(plain),
                    Some(Part::Value(_)) | None => Maybe::Absent(lowered::Absent::OtherSort),
                }
            },
            Maybe::Present(_) | Maybe::Absent(_) => answered,
        }
    }

    /// `ty` read through each top-level definition whose application it
    /// decodes: the decode of the definition's body applied to the same
    /// arguments, reduced as [`gandr_core_term::decoded_comp_reading`] reduces
    /// it, again while the reduct decodes another such application.
    ///
    /// # Specification
    /// - requires: each definition body the chain reaches is minted or absent;
    ///   [`Self::unfolded_definitions`] names them to the mint sweep.
    /// - ensures: the first type of the chain that decodes no definition with a
    ///   minted body, or whose decode does not reduce; `ty` itself when it
    ///   decodes none. The nodes the reading makes are minted in the arena.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Termination
    /// Each turn unfolds one definition, and the turns number at most the
    /// slots; the inner walk descends an application spine to its head.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a constructor returned against `opt(Integer)` with
    ///   `opt` a static abstraction over a returner, against `opt(A)` at a type
    ///   parameter, and against a definition that unfolds to `opt`.
    /// - witness: `lower::native::tests::a_constructor_answers_a_definition_s_application_2112`
    #[spec(ensures: |ret| ret == ty || sink.arena.comp_type(ret).is_some())]
    fn unfolded(
        &self,
        ty: CompTypeId,
        sink: &mut Sink<'_>,
    ) -> CompTypeId
    {
        let mut read = ty;
        let mut arguments = Vec::new();
        for _definition in 0 .. self.collected.slots.len() {
            let Some(&CompType::Element { code, ref target }) = sink.arena.comp_type(read)
            else {
                break;
            };
            let target = target.clone();
            arguments.clear();
            let mut head = code;
            while let Some(&Value::StaticApplication(applied, argument)) = sink.arena.value(head) {
                arguments.push(argument);
                head = applied;
            }
            let Some(&Value::Constant(constant)) = sink.arena.value(head)
            else {
                break;
            };
            let Maybe::Present(body) = self.definition_body(constant)
            else {
                break;
            };
            let mut applied = body;
            for &argument in arguments.iter().rev() {
                applied = sink.arena.value_static_application(applied, argument);
            }
            let decoded = sink.arena.comp_type_element(applied, target);
            let reduced = gandr_core_term::decoded_comp_reading(sink.arena, decoded);
            if reduced == decoded {
                break;
            }
            read = reduced;
        }

        read
    }

    /// Add to `into` the body of each top-level definition the type at `from`
    /// decodes an application of, then of each definition that body applies in
    /// turn, so the mint sweep reaches them before a constructor
    /// [`Self::unfolded`] classifies by them.
    ///
    /// # Specification
    /// - ensures: `into` gains each such body; nothing for a type that decodes
    ///   no definition's application.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the minting order is the claim; the witness
    ///   observes the constructor it lets mint.
    ///
    /// # Termination
    /// Each turn steps into a static abstraction's body or onto a body not yet
    /// added, and the turns number at most the plans.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::unfolded`].
    /// - witness: `lower::native::tests::a_constructor_answers_a_definition_s_application_2112`
    pub(super) fn unfolded_definitions(
        &self,
        from: NodeIndex,
        into: &mut BTreeSet<NodeIndex>,
    )
    {
        let mut at = from;
        for _step in 0 .. usize::from(self.plans.count()) {
            let code = match self.plans.get(at) {
                Some(&Plan::StaticLambda(body)) => {
                    at = body;
                    continue;
                },
                Some(&(Plan::Decode(code, ..) | Plan::StaticApplication(code, _))) => code,
                Some(_) | None => return,
            };
            let Maybe::Present(body) = self.decoded_definition(code)
            else {
                return;
            };
            if !into.insert(body) {
                return;
            }
            at = body;
        }
    }

    /// The node of the body of the top-level definition `code` names; a
    /// binder names none.
    ///
    /// # Specification
    /// trivial.
    fn decoded_definition(
        &self,
        code: Code,
    ) -> Maybe<NodeIndex, unfolding::Absent>
    {
        match code {
            Code::Constant(constant) => self.definition_written(constant),
            Code::Bound { .. } => Maybe::Absent(unfolding::Absent::Opaque),
        }
    }

    /// The node of the body a top-level definition of `constant` writes: the
    /// one form of `= e ;`, or the declaration form of a function tail
    /// `(params) -> T { … }`, which the tail lowers at (#3665).
    ///
    /// # Specification
    /// trivial.
    fn definition_written(
        &self,
        constant: ConstantIndex,
    ) -> Maybe<NodeIndex, unfolding::Absent>
    {
        if let Some(slot) = self.collected.slots.get(usize::from(constant))
            && slot.constant == constant
            && let Container::TopLevel(_) = slot.container
            && let Maybe::Absent(_) = slot.refusal
        {
            match slot.definition {
                Maybe::Present(Half {
                    operand: Operand::Written(body),
                    ..
                }) => return Maybe::Present(body.node),
                Maybe::Present(Half {
                    declaration,
                    operand: Operand::Function,
                    ..
                }) => return Maybe::Present(declaration.node),
                Maybe::Present(_) | Maybe::Absent(_) => {},
            }
        }

        Maybe::Absent(unfolding::Absent::Opaque)
    }

    /// The value the body of a top-level definition of `constant` lowered to.
    ///
    /// # Specification
    /// trivial.
    fn definition_body(
        &self,
        constant: ConstantIndex,
    ) -> Maybe<ValueId, unfolding::Absent>
    {
        match self.definition_written(constant) {
            Maybe::Present(node) => match self.value_at(node) {
                Maybe::Present(body) => Maybe::Present(body),
                Maybe::Absent(_) => Maybe::Absent(unfolding::Absent::Unlowered),
            },
            Maybe::Absent(reason) => Maybe::Absent(reason),
        }
    }

    /// `ty`, a computation type read under `from` in `telescope`, carried
    /// into the term context of `from` and then under `lift` more binders,
    /// each node it rewrote reported into `copies` when given.
    ///
    /// # Specification
    /// - requires: `ty` is minted under `from`, counting only the frames that
    ///   bind in `telescope`.
    /// - ensures: a binder inserted at each frame of `from`'s chain that does
    ///   not bind in `telescope`, then every free index raised by `lift`;
    ///   `copies`, when given, gains each node a shift rewrote beside its
    ///   source.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a function result and a written answer become the
    ///   motive of a nested tree; a dependent transport's motive answers where
    ///   its endpoints are written.
    /// - witness: `lower::native::tests::a_match_takes_its_answer_from_the_function_result`
    /// - witness: `lower::identity::tests::a_dependent_transport_lowers_to_its_telescope`
    #[spec(ensures: |ret| arena.comp_type(ret).is_some() || ret == ty)]
    pub(super) fn relocate(
        &self,
        arena: &mut CoreArena,
        ty: CompTypeId,
        from: Frame,
        telescope: Telescope,
        lift: Binders,
        mut copies: Option<&mut Vec<Carried>>,
    ) -> CompTypeId
    {
        let mut shift =
            |arena: &mut CoreArena, subject: CompTypeId, scope: Binders, amount: Binders| {
                let shifted = gandr_core_term::shift_comp_type_under(arena, subject, scope, amount);
                match copies.as_deref_mut() {
                    Some(copies) => shifted.settle_traced(arena, copies),
                    None => shifted.settle(arena),
                }
            };
        let mut carried = ty;
        for (position, binds) in self.scope.binders_in(from, telescope).enumerate() {
            if !binds {
                let scope = Binders::from(u32::try_from(position).unwrap_or(u32::MAX));
                carried = shift(arena, carried, scope, Binders::ONE);
            }
        }
        shift(arena, carried, Binders::NONE, lift)
    }

    /// Mint the field read off a data value at `projected`: the data case over
    /// the value whose branch for each constructor returns its field.
    ///
    /// # Specification
    /// - requires: the subject, and the answer or the stated type and the
    ///   field's declared type the projection is typed by, are already minted
    ///   or absent.
    /// - ensures: a data case over the subject's value whose motive returns the
    ///   projection's type under one binder more, reading none of it, and whose
    ///   branch for each constructor binds its fields and returns the one read;
    ///   the type is the answer carried from its frame to the projection's, or
    ///   the field's declared type lowered out from under the fields before it
    ///   with the family's parameters replaced by the arguments of the
    ///   subject's stated type carried to the projection's frame. The case
    ///   carries the written origin and records the family it eliminates; every
    ///   other node minted the inserted match origin, a copy that of the node
    ///   it copies. Nothing when a node it reads did not lower, the stated type
    ///   is no application of a family to at least its parameters, or the
    ///   field's type names a field before it.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::data_field`].
    /// - witness: `lower::native::tests::a_data_field_is_the_case_returning_it_1106`
    #[spec(ensures: |ret| matches!(ret, Maybe::Absent(_)) || matches!(ret, Maybe::Present(Lowered::Computation(id)) if matches!(sink.arena.computation(id), Some(gandr_core_term::Computation::DataCase { .. }))))]
    pub(super) fn mint_projected(
        &self,
        projected: ProjectedIndex,
        sink: &mut Sink<'_>,
        origin: Origin,
    ) -> Maybe<Lowered, lowered::Absent>
    {
        let unminted = Maybe::Absent(lowered::Absent::Unminted);
        let Some(form) = self.projected.get(projected.0)
        else {
            return unminted;
        };
        let Maybe::Present(scrutinee) = self.value_at(form.subject)
        else {
            return unminted;
        };
        let lift = |from: Frame| {
            let gap = self
                .scope
                .telescope_binders(form.frame)
                .count()
                .saturating_sub(self.scope.telescope_binders(from).count());
            Binders::from(u32::try_from(gap).unwrap_or(u32::MAX))
        };
        let mark = sink.arena.watermark();
        let mut copies = Vec::new();
        let answered = match form.typed {
            Typed::Answered(answer) => {
                let Maybe::Present(written) = self.answered_type(answer, sink)
                else {
                    return unminted;
                };
                self.relocate(
                    sink.arena,
                    written,
                    answer.frame,
                    Telescope::Signature,
                    lift(answer.frame),
                    Some(&mut copies),
                )
            },
            Typed::Field {
                stated,
                declared,
                earlier,
                parameters,
            } => {
                let (Maybe::Present(applied), Maybe::Present(declared)) =
                    (self.value_type_at(stated), self.value_type_at(declared))
                else {
                    return unminted;
                };
                let at = self.reading(stated).frame();
                let wrapped = sink.arena.comp_type_returner(applied);
                let carried = self.relocate(
                    sink.arena,
                    wrapped,
                    at,
                    Telescope::Signature,
                    lift(at),
                    Some(&mut copies),
                );
                let Some(&CompType::Returner {
                    result: applied, ..
                }) = sink.arena.comp_type(carried)
                else {
                    return unminted;
                };
                let Some(&gandr_core_term::ValueType::Data { ref arguments, .. }) =
                    sink.arena.value_type(applied)
                else {
                    return unminted;
                };
                let mut environment: Vec<ValueId> =
                    arguments.iter().take(parameters).copied().collect();
                if environment.len() != parameters {
                    return unminted;
                }
                // The innermost binder is the last parameter.
                environment.reverse();
                let past = Binders::from(u32::try_from(earlier).unwrap_or(u32::MAX));
                let Maybe::Present(lowered) =
                    gandr_core_term::strengthen_value_type(sink.arena, declared, past)
                else {
                    return unminted;
                };
                let declared = lowered.settle(sink.arena);
                let code = sink.arena.value_quote(declared);
                let substituted = gandr_core_term::substitute_environment_traced(
                    sink.arena,
                    TermId::Value(code),
                    &environment,
                    &mut copies,
                );
                let TermId::Value(substituted) = substituted
                else {
                    return unminted;
                };
                let Some(&Value::Quote(ty)) = sink.arena.value(substituted)
                else {
                    return unminted;
                };
                sink.arena.comp_type_returner(ty)
            },
        };
        let motive =
            gandr_core_term::shift_comp_type(sink.arena, answered, Binders::ONE).settle(sink.arena);
        let mut branches = Vec::with_capacity(form.branches.len());
        let mut arities = Vec::with_capacity(form.branches.len());
        for &(arity, position) in &form.branches {
            let read = variable(
                sink.arena,
                Depth(arity.saturating_sub(position).saturating_sub(1)),
            );
            let mut branch = sink.arena.computation_return(read);
            for _field in 0 .. arity {
                branch = sink.arena.computation_lambda(branch);
            }
            branches.push(branch);
            arities.push(gandr_kernel_term::FieldCount::from(arity));
        }
        let case = sink
            .arena
            .computation_data_case(scrutinee, motive, branches, arities);
        sink.origins.record_elimination(case, form.family);
        record_copied_since(
            sink,
            mark,
            origin.inserted(Insertion::Match),
            Maybe::Present((case, origin)),
            &copies,
        );

        Maybe::Present(Lowered::Computation(case))
    }

    /// What each term variable of `frame` reads as at the arm `arm` and every
    /// arm the answer was passed into before it: the scrutinee of each
    /// settled one its constructor over what the arm reads its fields at, the
    /// outermost arm read first.
    ///
    /// # Specification
    /// - requires: the arms `arm` chains stand on `frame`'s chain.
    /// - ensures: one value per term binder of `frame`, index for index, when
    ///   some arm on the chain is settled and `frame` reads its scrutinee and
    ///   every variable its reading names intuitionistically: each variable
    ///   read through every such arm from the outermost in, an arm reading its
    ///   scrutinee's variable as [`Self::built_value`] builds its reading and
    ///   every other variable as itself. The unsettled absence otherwise, every
    ///   variable reading itself.
    /// - provides: the substitution an arm's leaf makes in the arm's body, made
    ///   where a match in that body stands, so the match reads its answer and
    ///   its own leaves read their bodies under it before its own refinement.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a match in an arm, on the arm's field, answers at the
    ///   arm's constructor over each of its own constructors, and its branches
    ///   read the outer scrutinee there too.
    /// - witness: `lower::native::tests::a_match_in_an_arm_reads_the_answer_at_the_arm_s_constructor_2994`
    /// - witness: `lower::native::tests::an_arm_variable_at_a_switched_field_reads_its_constructor_3008`
    #[spec(ensures: |ret| match ret {
        | Maybe::Present(ref read) => read.len() == self.scope.telescope_binders(frame).count(),
        | Maybe::Absent(_) => true,
    })]
    fn arm_readings(
        &self,
        arm: Maybe<ArmIndex, passed::Absent>,
        frame: Frame,
        arena: &mut CoreArena,
    ) -> Maybe<Vec<ValueId>, passed::Absent>
    {
        let context = self.scope.telescope_binders(frame).count();
        let mut readings: Option<Vec<ValueId>> = None;
        for reading in self.arms_outward(arm).into_iter().rev() {
            let Maybe::Present(ref settled) = reading.settled
            else {
                continue;
            };
            let Some(held) = self.term_depth(frame, settled.scrutinee)
            else {
                continue;
            };
            let Some(value) = self.built_value(frame, &settled.read, arena)
            else {
                continue;
            };
            let step: Vec<ValueId> = (0 .. context)
                .map(|position| {
                    if position == held.0 {
                        value
                    }
                    else {
                        variable(arena, Depth(position))
                    }
                })
                .collect();
            match readings {
                None => readings = Some(step),
                Some(ref mut read) => {
                    for entry in read.iter_mut() {
                        if let TermId::Value(stepped) = gandr_core_term::substitute_environment(
                            arena,
                            TermId::Value(*entry),
                            &step,
                        ) {
                            *entry = stepped;
                        }
                    }
                },
            }
        }
        readings.map_or(Maybe::Absent(passed::Absent::Unsettled), Maybe::Present)
    }

    /// The value the prefix-ordered `read` spells under `frame`: an arm
    /// variable's binder as its variable, a constructor over the values its
    /// fields spell.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the value, when `read` spells exactly one term and `frame`
    ///   reads every binder it names intuitionistically; none otherwise.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::arm_readings`].
    /// - witness: `lower::native::tests::a_match_in_an_arm_reads_the_answer_at_the_arm_s_constructor_2994`
    /// - witness: `lower::native::tests::an_arm_variable_at_a_switched_field_reads_its_constructor_3008`
    #[spec(ensures: |ret| ret.is_none_or(|value| arena.value(value).is_some()))]
    fn built_value(
        &self,
        frame: Frame,
        read: &[Built],
        arena: &mut CoreArena,
    ) -> Option<ValueId>
    {
        let mut values: Vec<ValueId> = Vec::with_capacity(read.len());
        for &node in read.iter().rev() {
            match node {
                Built::Bound(binder) => {
                    let index = self.term_depth(frame, binder)?;
                    values.push(variable(arena, index));
                },
                Built::Constructed { family, tag, arity } => {
                    let from = values.len().checked_sub(arity)?;
                    let fields = values.drain(from ..).rev().collect();
                    values.push(constructed(arena, family, tag, fields));
                },
            }
        }
        match *values.as_slice() {
            [value] => Some(value),
            _ => None,
        }
    }

    /// The term index the intuitionistic binder `binder` has from `frame`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the index [`crate::resolve::Scope::bindings`] gives `binder`
    ///   from `frame` when the binder is intuitionistic and on the chain; none
    ///   otherwise.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::arm_readings`].
    /// - witness: `lower::native::tests::a_match_in_an_arm_reads_the_answer_at_the_arm_s_constructor_2994`
    #[spec(ensures: |ret| ret.is_none_or(|_| self.scope.zone(binder) == Zone::Intuitionistic))]
    fn term_depth(
        &self,
        frame: Frame,
        binder: ScopeId,
    ) -> Option<Depth>
    {
        self.scope.bindings(frame).find_map(|(_, bound)| {
            (bound.binder == binder && bound.zone == Zone::Intuitionistic)
                .then(|| Depth(usize::try_from(u32::from(bound.index)).unwrap_or(usize::MAX)))
        })
    }

    /// Mint the match at `case`: its scrutinee bound once over its decision
    /// tree.
    ///
    /// # Specification
    /// - requires: the scrutinee, every arm body and the answer are already
    ///   minted or absent.
    /// - ensures: the tree, every node minted descending: a data case over the
    ///   scrutinised level with the motive [`tracked_motives`] reads from the
    ///   answer, each branch a lambda per field and then one per index
    ///   equation, a pruned branch the case of no branches on its equation; a
    ///   sum case for a boolean; an integer comparison bound and cased on; a
    ///   hole for a stuck node; and a leaf as its arm's body with each variable
    ///   replaced by what [`level_read`] reads the level that settled it at and
    ///   the case's context carried under the tree's binders, the scrutinee's
    ///   variable read as [`level_read`] reads level zero where the root
    ///   refines it. An answer passed into arms is read with each variable of
    ///   the case's frame as [`Self::arm_readings`] reads it, and each leaf
    ///   reads its body's variables so before its own refinement. Level zero is
    ///   the scrutinee itself, carried under the binders above its use, so no
    ///   binding of it is minted. The root carries the written origin, a leaf's
    ///   copy of its arm's body the origin of what it copies, every other node
    ///   the inserted match origin, and the arms are recorded beside the root
    ///   with the scrutinee's value; a match whose first arm matches anything
    ///   is that arm's body. A match that writes its answer has its root
    ///   ascribed it, an integer test's case under the comparison's binder, but
    ///   for a data case and a dependent split, whose motive is that answer.
    ///   Nothing when the scrutinee, a reached body or a needed answer did not
    ///   lower.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the witnesses read each tree back out of the arena.
    /// - witness: `lower::native::tests::nested_constructor_patterns_compile_to_nested_cases`
    /// - witness: `lower::native::tests::literal_patterns_compare_and_branch`
    /// - witness: `lower::native::tests::an_arm_variable_at_a_switched_field_reads_its_constructor_3008`
    /// - witness: `lower::native::tests::a_pattern_hole_leaves_its_leaf_stuck`
    /// - witness: `lower::native::tests::a_match_keeps_its_patterns_beside_its_tree`
    /// - witness: `lower::native::tests::a_written_answer_ascribes_the_match_2089`
    /// - witness: `lower::native::tests::a_match_in_an_arm_reads_the_answer_at_the_arm_s_constructor_2994`
    #[spec(ensures: |ret| matches!(ret, Maybe::Absent(_) | Maybe::Present(Lowered::Computation(_))))]
    pub(super) fn mint_case(
        &self,
        case: CaseIndex,
        sink: &mut Sink<'_>,
        origin: Origin,
    ) -> Maybe<Lowered, lowered::Absent>
    {
        let Some(form) = self.cases.get(case.0)
        else {
            return Maybe::Absent(lowered::Absent::Unminted);
        };
        let Maybe::Present(scrutinee) = self.value_at(form.scrutinee)
        else {
            return Maybe::Absent(lowered::Absent::Unminted);
        };
        let mut bodies = Vec::with_capacity(form.bodies.len());
        for &body in &form.bodies {
            bodies.push(self.computation_at(body));
        }
        let mark = sink.arena.watermark();
        // What each variable of the match's frame reads as at the arms its
        // answer was passed into.
        let armed = match form.answer {
            Maybe::Present(answer) => self.arm_readings(answer.arm, form.frame, sink.arena),
            Maybe::Absent(_) => Maybe::Absent(passed::Absent::Unpassed),
        };
        let motive = match form.answer {
            Maybe::Present(answer) => match self.answered_type(answer, sink) {
                Maybe::Present(written) => {
                    let gap = Depth(
                        self.scope
                            .telescope_binders(form.frame)
                            .count()
                            .saturating_sub(self.scope.telescope_binders(answer.frame).count()),
                    );
                    let base = self.relocate(
                        sink.arena,
                        written,
                        answer.frame,
                        Telescope::Signature,
                        Binders::default(),
                        None,
                    );
                    Maybe::Present(match armed {
                        Maybe::Present(ref read) => {
                            let carried = gandr_core_term::shift_comp_type(
                                sink.arena,
                                base,
                                Binders::from(u32::try_from(gap.0).unwrap_or(u32::MAX)),
                            )
                            .settle(sink.arena);
                            let refined = match environment_substituted(sink.arena, carried, read) {
                                Maybe::Present(refined) => refined,
                                Maybe::Absent(_) => carried,
                            };
                            (refined, Depth::default())
                        },
                        Maybe::Absent(_) => (base, gap),
                    })
                },
                Maybe::Absent(reason) => Maybe::Absent(reason),
            },
            Maybe::Absent(_) => Maybe::Absent(lowered::Absent::Unminted),
        };
        // The answer written on the match is its root's type: the motive's
        // base, read where the match stands.
        let ascription = match (form.ascribed, motive) {
            (Maybe::Present(_), Maybe::Present((base, _gap))) => Maybe::Present(base),
            (Maybe::Present(_), Maybe::Absent(reason)) => return Maybe::Absent(reason),
            (Maybe::Absent(_), _) => Maybe::Absent(lowered::Absent::Unminted),
        };
        let scrutinised = Scrutinised {
            scrutinee,
            outer: Depth(self.scope.telescope_binders(form.frame).count()),
        };
        let tracked = match motive {
            Maybe::Present((base, gap))
                if form.tests.iter().any(|test| {
                    matches!(
                        *test,
                        Test::Data { .. }
                            | Test::Split {
                                dependent: Dependent(true),
                                ..
                            }
                    )
                }) =>
            {
                tracked_motives(&form.tests, base, gap, scrutinised, sink.arena)
            },
            Maybe::Present(_) | Maybe::Absent(_) => Vec::new(),
        };
        let refinings = refinings(&form.tests);
        let dependent = dependents(&form.tests, &tracked, sink.arena);
        let readings = Readings {
            refinings: &refinings,
            dependent: &dependent,
            held: held_variable(scrutinised, sink.arena),
        };
        let mut minted: Vec<Maybe<ComputationId, lowered::Absent>> = Vec::from_iter(
            form.tests
                .iter()
                .map(|_test| Maybe::Absent(lowered::Absent::Unminted)),
        );
        let mut copies = Vec::new();
        for (position, test) in form.tests.iter().enumerate().rev() {
            let read = tracked
                .get(position)
                .copied()
                .unwrap_or(Maybe::Absent(lowered::Absent::Unminted));
            let at = refinings
                .under
                .get(position)
                .copied()
                .unwrap_or(Maybe::Absent(refined::Absent::Unswitched));
            let answered = if position == 0_usize {
                ascription
            }
            else {
                Maybe::Absent(lowered::Absent::Unminted)
            };
            let id = mint_test(
                test,
                (scrutinised, readings),
                (&bodies, match armed {
                    Maybe::Present(ref read) => read,
                    Maybe::Absent(_) => &[],
                }),
                &minted,
                (read, at, answered),
                sink,
                &mut copies,
            );
            if let Some(held) = minted.get_mut(position) {
                *held = id;
            }
        }
        self.name_fields(form, &minted, sink);
        let inserted = origin.inserted(Insertion::Match);
        let minted_root = match minted.first() {
            Some(&Maybe::Present(root)) if form.loops.is_empty() => Maybe::Present(root),
            Some(&Maybe::Present(root)) => self.with_loops(form, root, sink, &mut copies),
            Some(&Maybe::Absent(_)) | None => Maybe::Absent(lowered::Absent::Unminted),
        };
        let Maybe::Present(root) = minted_root
        else {
            record_copied_since(
                sink,
                mark,
                inserted,
                Maybe::Absent(rooted::Absent::Unminted),
                &copies,
            );
            return Maybe::Absent(lowered::Absent::Unminted);
        };
        if sink.arena.computations_since(mark).all(|id| id != root) {
            record_copied_since(
                sink,
                mark,
                inserted,
                Maybe::Absent(rooted::Absent::Adopted),
                &copies,
            );
            return Maybe::Present(Lowered::Computation(root));
        }
        record_copied_since(
            sink,
            mark,
            inserted,
            Maybe::Present((root, origin)),
            &copies,
        );
        let mut kept = form.origin.clone();
        kept.scrutinised = Maybe::Present(scrutinee);
        sink.origins.record_case(root, kept);

        Maybe::Present(Lowered::Computation(root))
    }

    /// Records, for each field binder a data switch of `form`'s tree opens
    /// and each component binder a split opens, the arm variable every arm
    /// reached through it binds there, when they agree on its name.
    ///
    /// # Specification
    /// - requires: `minted` holds the tree's nodes as [`mint_test`] minted
    ///   them, position for position.
    /// - ensures: each lambda a minted data switch's branch opens for its field
    ///   `f` under `d` tree binders is recorded as written at the arm variable
    ///   that the leaves under that branch settle at level `d + f + 1`, when at
    ///   least one leaf settles a variable there and every one that does writes
    ///   the same name; each component `c` of a minted split under `d` tree
    ///   binders likewise, at the variable the leaves under the split settle at
    ///   level `d + c + 1`, or else at the label of the field a labelled
    ///   pattern leaves unwritten there, or of the field the rest of a
    ///   dependent record held there starts at; any other binder keeps no name.
    /// - provides: the source's name for a pattern variable, which a type
    ///   printed inside an arm reads its field binder by, whether or not the
    ///   arm uses it.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the origins it records live in the sink's table,
    ///   which a predicate over the lowerer cannot read.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a field a single arm names, and one two arms name
    ///   alike, each answer under the written name; a relation's record split
    ///   names a component its arm never uses, and one a label pattern omits; a
    ///   dependent record's rest is named by the label it starts at.
    /// - witness: `lower::native::tests::a_pattern_variable_names_its_field_binder`
    /// - witness: `lower::identity::tests::a_relation_split_names_each_written_component_665`
    /// - witness: `lower::identity::tests::an_unwritten_field_is_named_by_its_label_670`
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            linear_search_in_loop,
            reason = "bounded: `unwritten` holds the components one split leaves unwritten"
        )
    )]
    fn name_fields(
        &self,
        form: &CaseForm,
        minted: &[Maybe<ComputationId, lowered::Absent>],
        sink: &mut Sink<'_>,
    )
    {
        for (test, &held) in form.tests.iter().zip(minted) {
            let Maybe::Present(switch) = held
            else {
                continue;
            };
            let (depth, branches) = match *test {
                Test::Data {
                    depth,
                    ref branches,
                    ..
                } => (depth, branches),
                Test::Split {
                    depth,
                    arity,
                    child,
                    ref unwritten,
                    ..
                } => {
                    for component in 0 .. arity {
                        let level = TreeLevel(depth.0.saturating_add(component).saturating_add(1));
                        let name = if let Some(origin) = self.field_name(form, child, level) {
                            ComponentName::Written(origin)
                        }
                        else {
                            let Some(&(_, ref label)) =
                                unwritten.iter().find(|&&(held, _)| held == component)
                            else {
                                continue;
                            };
                            ComponentName::Labelled(label.clone())
                        };
                        sink.origins
                            .place_component(switch, SplitComponent::from(component), name);
                    }
                    continue;
                },
                Test::Pending
                | Test::Stuck(_)
                | Test::Absurd
                | Test::Leaf { .. }
                | Test::Boolean { .. }
                | Test::Integer { .. }
                | Test::Record { .. }
                | Test::Sum { .. }
                | Test::List { .. } => continue,
            };
            let Some(&gandr_core_term::Computation::DataCase {
                branches: ref lowered,
                ..
            }) = sink.arena.computation(switch)
            else {
                continue;
            };
            for (&(arity, at), &branch) in branches.iter().zip(lowered) {
                let mut lambda = branch;
                for field in 0 .. arity {
                    let level = TreeLevel(depth.0.saturating_add(field).saturating_add(1));
                    if let Some(origin) = self.field_name(form, at, level) {
                        sink.origins.place_binder(lambda, origin);
                    }
                    let Some(&gandr_core_term::Computation::Lambda(body)) =
                        sink.arena.computation(lambda)
                    else {
                        break;
                    };
                    lambda = body;
                }
            }
        }
    }

    /// The origin of the arm variable every leaf under `at` settles at
    /// `level`, when at least one does and all write one name.
    ///
    /// # Specification
    /// - requires: `at` is a node of `form`'s tree.
    /// - ensures: the first such variable's origin when the leaves under `at`
    ///   that settle a variable at `level` all write the same name; none when
    ///   no leaf does, two write different names, or the variable has no
    ///   origin.
    /// - provides: the name [`Self::name_fields`] records.
    /// - fails: never.
    /// - panics: none.
    /// - intension: one pass over the subtree on an explicit stack.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::name_fields`].
    /// - witness: `lower::native::tests::a_pattern_variable_names_its_field_binder`
    #[spec(ensures: |ret| ret.is_none() || form.tests.get(at.0).is_some())]
    fn field_name(
        &self,
        form: &CaseForm,
        at: TestAt,
        level: TreeLevel,
    ) -> Option<Origin>
    {
        let mut named: Option<Placed> = None;
        let mut pending = Vec::from([at]);
        while let Some(TestAt(position)) = pending.pop() {
            match form.tests.get(position) {
                Some(&Test::Leaf {
                    arm, ref bindings, ..
                }) => {
                    let variables = form.variables.get(arm.0).map_or(&[][..], Vec::as_slice);
                    for (&settled, &variable) in bindings.iter().zip(variables) {
                        if settled != level {
                            continue;
                        }
                        match named {
                            Some(first) if self.text_at(first) != self.text_at(variable) => {
                                return None;
                            },
                            Some(_) => {},
                            None => named = Some(variable),
                        }
                    }
                },
                Some(&Test::Data { ref branches, .. }) => {
                    pending.extend(branches.iter().map(|&(_arity, child)| child));
                },
                Some(&Test::Sum { ref branches, .. }) => pending.extend(branches.iter().copied()),
                Some(&Test::List { nil, cell, .. }) => pending.extend([nil, cell]),
                Some(&(Test::Boolean { yes, no, .. } | Test::Integer { yes, no, .. })) => {
                    pending.extend([yes, no]);
                },
                Some(&(Test::Split { child, .. } | Test::Record { child, .. })) => {
                    pending.push(child);
                },
                Some(&(Test::Pending | Test::Stuck(_) | Test::Absurd)) | None => {},
            }
        }
        let variable = named?;
        match self.origin_at(variable.node) {
            Maybe::Present(origin) => Some(origin),
            Maybe::Absent(_) => None,
        }
    }

    /// The root data case `root` of the match `form` with a loop branch per
    /// loop arm after its constructors' branches.
    ///
    /// # Specification
    /// - requires: `root` is the minted root of `form`'s tree, and `form`
    ///   carries loop arms.
    /// - ensures: the data case over the root's scrutinee and motive whose
    ///   branches are the root's, then each loop arm's body in `form`'s order
    ///   with the binder its arm reads replaced by `b`, the root's answer at
    ///   the arm's loop's point over the root's branches as
    ///   [`gandr_core_term::identity::answer_at`] reads it, which the checker
    ///   reads alike; every node the replacement rewrote reported in `copies`
    ///   beside its original. The unminted absence when the root is no data
    ///   case, a body did not lower or a point does not spell.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the circle's loop arm follows its point's branch and
    ///   reads `Base`, the value that branch returns, for its answer.
    /// - witness: `lower::native::tests::a_loop_arm_follows_the_constructors_branches`
    #[spec(ensures: |ret| matches!(ret, Maybe::Absent(_)) || matches!(ret, Maybe::Present(id) if matches!(sink.arena.computation(id), Some(gandr_core_term::Computation::DataCase { .. }))))]
    fn with_loops(
        &self,
        form: &CaseForm,
        root: ComputationId,
        sink: &mut Sink<'_>,
        copies: &mut Vec<Carried>,
    ) -> Maybe<ComputationId, lowered::Absent>
    {
        let unminted = Maybe::Absent(lowered::Absent::Unminted);
        // A presented type is never indexed, so its case takes no equation.
        let Some(&gandr_core_term::Computation::DataCase {
            scrutinee,
            motive,
            ref branches,
            arities: ref constructors,
            ..
        }) = sink.arena.computation(root)
        else {
            return unminted;
        };
        let (branches, constructors) = (branches.clone(), constructors.clone());
        let mut all = branches.clone();
        let mut rewritten = Vec::new();
        for arm in &form.loops {
            let Maybe::Present(body) = self.computation_at(arm.body)
            else {
                return unminted;
            };
            let Some((carrier, point, arities)) =
                self.collected.words.get(arm.words).and_then(|words| {
                    let data = self.collected.data.get(words.family)?;
                    let family = self.collected.slots.get(usize::from(data.slot))?.constant;
                    let arities: Vec<gandr_kernel_term::FieldCount> = data
                        .generators
                        .iter()
                        .map(|generator| {
                            gandr_kernel_term::FieldCount::from(generator.fields.len())
                        })
                        .collect();
                    Some((family, &words.point, arities))
                })
            else {
                return unminted;
            };
            let classifier = sink.arena.value_type_data(carrier, Vec::new());
            let Maybe::Present(at) =
                spelled_point(sink.arena, classifier, (point, &arities), &mut Vec::new())
            else {
                return unminted;
            };
            let carried = gandr_core_term::identity::answer_at(
                sink.arena,
                at,
                motive,
                &branches,
                &constructors,
            );
            rewritten.clear();
            let instantiated = gandr_core_term::instantiate_computation_traced(
                sink.arena,
                body,
                carried,
                &mut rewritten,
            );
            exits::mark_copies(sink, &rewritten);
            copies.extend_from_slice(&rewritten);
            all.push(instantiated);
        }
        let extended = sink
            .arena
            .computation_data_case(scrutinee, motive, all, constructors);
        if let Maybe::Present(family) = sink.origins.elimination(root) {
            sink.origins.record_elimination(extended, family);
        }
        Maybe::Present(extended)
    }
}

/// What every node of one match's tree reads: the scrutinee, and how many
/// term binders the case's frame holds.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: the scrutinee is minted under the case's frame.
/// - executable: none — the record holds no scope to count against.
///
/// # Adequacy
/// - hypothesis: L3 — a leaf under a function's parameters reads them past the
///   tree's binders.
/// - witness: `lower::native::tests::nested_constructor_patterns_compile_to_nested_cases`
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Scrutinised
{
    /// The scrutinee, under the case's frame.
    scrutinee: ValueId,
    /// The term binders of the case's frame.
    outer: Depth,
}

quenchant_shape::reason_enum! {
    /// Why a leaf of a match's tree reads a level as itself.
    pub mod refined {
        /// No switch above the leaf refines the level to a constructor.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// No data switch over a bare family above the node scrutinises
            /// the level.
            Unswitched,
            /// The scrutinee is no variable of the case's frame.
            Unbound,
            /// The switch's motive does not read its scrutinee.
            Independent,
        }
    }
}

/// A branch of a data switch over a bare family, which the nodes below it
/// stand under.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: `switch` is the switch's position in its tree, `level` the level
///   it scrutinises under `depth` tree binders, `family` the bare family that
///   classifies its constructors, and `tag` and `arity` the branch's
///   constructor and field count, whose fields are the levels `depth + 1` to
///   `depth + arity`; `outer` is the branch the switch itself stands under.
/// - executable: none — the record holds no tree to check its branch against.
///
/// # Adequacy
/// - hypothesis: L3 — a leaf under a dependent switch reads the switched level
///   at its branch's constructor, and one under an independent switch reads it
///   as itself.
/// - witness: `lower::native::tests::a_case_over_a_variable_answers_its_motive_at_each_constructor`
/// - witness: `lower::native::tests::an_arm_variable_at_a_switched_field_reads_its_constructor_3008`
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Refining
{
    /// The switch's position in its tree.
    switch: TestAt,
    /// The level the switch scrutinises.
    level: TreeLevel,
    /// The tree binders above the switch.
    depth: Depth,
    /// The family the bare family type names.
    family: ConstantIndex,
    /// The branch's constructor.
    tag: ConstructorTag,
    /// The constructor's field count.
    arity: usize,
    /// The branch the switch stands under.
    outer: Maybe<RefiningAt, refined::Absent>,
}

/// A branch of a match's data switches, by its position in the tree's
/// [`Refinings`].
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct RefiningAt(usize);

/// The branches of a match's data switches over bare families, and the
/// innermost one each node of the tree stands under.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: `under` holds one entry per node of the tree; each entry, and
///   each branch's `outer`, names a branch of `branches` or none.
/// - executable: none — the record holds no tree to check its entries against.
///
/// # Adequacy
/// - hypothesis: L3 — as [`Refining`].
/// - witness: `lower::native::tests::an_arm_variable_at_a_switched_field_reads_its_constructor_3008`
/// - witness: `lower::native::tests::a_match_in_an_arm_reads_the_answer_at_the_arm_s_constructor_2994`
#[derive(Clone, Debug, Default, Eq, PartialEq)]
struct Refinings
{
    /// Every branch of every such switch, each after the branch above it.
    branches: Vec<Refining>,
    /// The innermost branch above each node.
    under: Vec<Maybe<RefiningAt, refined::Absent>>,
}

impl Refinings
{
    /// The branch a node below `under` stands under whose switch scrutinises
    /// `level`.
    ///
    /// # Specification
    /// - requires: `under` is an entry of [`Self::under`] or a branch's
    ///   `outer`.
    /// - ensures: the innermost branch on the chain from `under` out whose
    ///   switch scrutinises `level`; the unswitched absence when none does.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Termination
    /// Each step moves to a branch stored strictly before the last, so the
    /// walk ends within the store's length.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Refining`].
    /// - witness: `lower::native::tests::an_arm_variable_at_a_switched_field_reads_its_constructor_3008`
    #[spec(ensures: |ret| match ret {
        | Maybe::Present(branch) => branch.level == level,
        | Maybe::Absent(_) => true,
    })]
    fn switched(
        &self,
        under: Maybe<RefiningAt, refined::Absent>,
        level: TreeLevel,
    ) -> Maybe<&Refining, refined::Absent>
    {
        let mut at = under;
        let mut bound = self.branches.len();
        while let Maybe::Present(RefiningAt(position)) = at {
            let Some(branch) = self.branches.get(position).filter(|_| position < bound)
            else {
                break;
            };
            if branch.level == level {
                return Maybe::Present(branch);
            }
            bound = position;
            at = branch.outer;
        }
        Maybe::Absent(refined::Absent::Unswitched)
    }
}

/// What a match's leaves read its tree's levels and its scrutinee's variable
/// at.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: `dependent` holds one entry per node of the tree, whether its
///   motive reads its binder; `held` is the scrutinee's index in the case's
///   frame, when it is a variable of it.
/// - executable: none — the record holds no tree to check its entries against.
///
/// # Adequacy
/// - hypothesis: L3 — as [`Refining`].
/// - witness: `lower::native::tests::a_case_over_a_variable_answers_its_motive_at_each_constructor`
/// - witness: `lower::native::tests::an_arm_variable_at_a_switched_field_reads_its_constructor_3008`
#[derive(Clone, Copy, Debug)]
struct Readings<'tree>
{
    /// The tree's switches' branches.
    refinings: &'tree Refinings,
    /// Whether each node's motive reads its binder.
    dependent: &'tree [Dependent],
    /// The scrutinee's index in the case's frame.
    held: Maybe<Depth, refined::Absent>,
}

/// The motive of every data case and dependent split of a tree, read from the
/// root down.
///
/// # Specification
/// - requires: `tests` is a compiled tree, every child after its parent; `base`
///   is the answer in the term context of its own frame, `gap` the binders the
///   case's frame adds to it.
/// - ensures: one entry per node. The root answers `base` under `gap` more
///   binders; a data case's motive over a bare family and a dependent split's
///   motive is its answer with its scrutinee abstracted, as [`abstracted`]
///   reads it, and a data case's motive over any other family is its answer
///   under one binder more, reading none of it, since [`Readings::refines`]
///   finds no branch of it for a leaf to read (#616). A data case's branches
///   answer its motive at the constructor over their fields when the motive
///   reads its binder and the bare family classifies the constructor, and its
///   answer under their fields otherwise, past their index equations either
///   way; a pruned branch's case of no branches answers that answer under one
///   binder more, reading none of it; a dependent split's child answers its
///   motive at the pair of its two components; every other node passes its
///   answer to its children under the binders it opens. Nodes other than data
///   cases, pruned branches and dependent splits answer nothing.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a split whose answer names its scrutinee reads it back at
///   the pair of its components, and one whose answer does not keeps it; a data
///   case whose answer names its scrutinee reads it back at each constructor.
/// - witness: `lower::native::tests::a_pattern_at_a_dependent_record_splits_it_under_its_motive`
/// - witness: `lower::native::tests::a_case_over_a_variable_answers_its_motive_at_each_constructor`
#[spec(ensures: |ret| ret.len() == tests.len())]
fn tracked_motives(
    tests: &[Test],
    base: CompTypeId,
    gap: Depth,
    scrutinised: Scrutinised,
    arena: &mut CoreArena,
) -> Vec<Maybe<CompTypeId, lowered::Absent>>
{
    let binders = |count: usize| Binders::from(u32::try_from(count).unwrap_or(u32::MAX));
    let mut expected: Vec<Option<CompTypeId>> = alloc::vec![None; tests.len()];
    let mut motives = alloc::vec![Maybe::Absent(lowered::Absent::Unminted); tests.len()];
    if let Some(root) = expected.first_mut() {
        *root = Some(gandr_core_term::shift_comp_type(arena, base, binders(gap.0)).settle(arena));
    }
    for (position, test) in tests.iter().enumerate() {
        let Some(here) = expected.get(position).copied().flatten()
        else {
            continue;
        };
        let mut answers: Vec<(TestAt, CompTypeId)> = Vec::new();
        let mut under = |arena: &mut CoreArena, at: TestAt, count: usize| {
            answers.push((
                at,
                gandr_core_term::shift_comp_type(arena, here, binders(count)).settle(arena),
            ));
        };
        match *test {
            Test::Pending | Test::Stuck(_) | Test::Leaf { .. } => {},
            // The case of no branches on the equation answers the branch's
            // own answer, reading none of its binder.
            Test::Absurd => {
                if let Some(slot) = motives.get_mut(position) {
                    *slot = Maybe::Present(
                        gandr_core_term::shift_comp_type(arena, here, Binders::ONE).settle(arena),
                    );
                }
            },
            Test::Data {
                level,
                depth,
                family,
                equations,
                ref branches,
                ..
            } => {
                let motive = match family {
                    Maybe::Present(_) => {
                        let scrutinee = level_value(arena, scrutinised, depth, level);
                        let context = Depth(scrutinised.outer.0.saturating_add(depth.0));
                        abstracted(arena, here, scrutinee, context)
                    },
                    Maybe::Absent(_) => {
                        gandr_core_term::shift_comp_type(arena, here, Binders::ONE).settle(arena)
                    },
                };
                if let Some(slot) = motives.get_mut(position) {
                    *slot = Maybe::Present(motive);
                }
                let reads = matches!(
                    gandr_core_term::strengthen_comp_type(arena, motive),
                    Maybe::Absent(_)
                );
                for (tag, &(arity, at)) in branches.iter().enumerate() {
                    let answer = match family {
                        Maybe::Present(family) if reads => {
                            let lifted = gandr_core_term::shift_comp_type_under(
                                arena,
                                motive,
                                Binders::ONE,
                                binders(arity),
                            )
                            .settle(arena);
                            let fields = (0 .. arity)
                                .rev()
                                .map(|field| variable(arena, Depth(field)))
                                .collect();
                            let at_constructor =
                                constructed(arena, family, ConstructorTag::from(tag), fields);
                            gandr_core_term::instantiate_comp_type(arena, lifted, at_constructor)
                        },
                        Maybe::Present(_) | Maybe::Absent(_) => {
                            gandr_core_term::shift_comp_type(arena, here, binders(arity))
                                .settle(arena)
                        },
                    };
                    // The child stands past the branch's equations too.
                    let answer = if equations == 0 {
                        answer
                    }
                    else {
                        gandr_core_term::shift_comp_type(arena, answer, binders(equations))
                            .settle(arena)
                    };
                    answers.push((at, answer));
                }
            },
            Test::Boolean { yes, no, .. } => {
                under(arena, yes, 1_usize);
                under(arena, no, 1_usize);
            },
            Test::Integer { yes, no, .. } => {
                under(arena, yes, 2_usize);
                under(arena, no, 2_usize);
            },
            Test::Split {
                arity,
                dependent: Dependent(false),
                child,
                ..
            } => under(arena, child, arity),
            Test::Split {
                level,
                depth,
                dependent: Dependent(true),
                child,
                ..
            } => {
                let scrutinee = level_value(arena, scrutinised, depth, level);
                let context = Depth(scrutinised.outer.0.saturating_add(depth.0));
                let motive = abstracted(arena, here, scrutinee, context);
                if let Some(slot) = motives.get_mut(position) {
                    *slot = Maybe::Present(motive);
                }
                let lifted = gandr_core_term::shift_comp_type_under(
                    arena,
                    motive,
                    Binders::ONE,
                    binders(2_usize),
                )
                .settle(arena);
                let first = variable(arena, Depth(1_usize));
                let second = variable(arena, Depth::default());
                let pair = arena.value_tuple(&[first, second]);
                answers.push((
                    child,
                    gandr_core_term::instantiate_comp_type(arena, lifted, pair),
                ));
            },
            Test::Record {
                ref labels, child, ..
            } => under(arena, child, labels.len()),
            Test::List { nil, cell, .. } => {
                under(arena, nil, 0_usize);
                under(arena, cell, 2_usize);
            },
            Test::Sum { ref branches, .. } => {
                for &at in branches {
                    under(arena, at, 1_usize);
                }
            },
        }
        for (at, answer) in answers {
            if let Some(slot) = expected.get_mut(at.0) {
                *slot = Some(answer);
            }
        }
    }

    motives
}

/// The branches of `tests`' data switches over bare families, and the
/// innermost one each node stands under.
///
/// # Specification
/// - requires: `tests` is a compiled tree, every child after its parent.
/// - ensures: one branch per branch of each data switch whose family is bare,
///   each stored after the branch its switch stands under; each node below such
///   a branch, under no deeper one, stands under it; the root, and every node
///   under no such branch, stands under none.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a leaf under a nested switch reads both switched levels
///   at their constructors, and an arm's leaves name the constructors the arm
///   reads its scrutinee at.
/// - witness: `lower::native::tests::an_arm_variable_at_a_switched_field_reads_its_constructor_3008`
/// - witness: `lower::native::tests::a_match_in_an_arm_reads_the_answer_at_the_arm_s_constructor_2994`
#[spec(ensures: |ret| ret.under.len() == tests.len())]
fn refinings(tests: &[Test]) -> Refinings
{
    let mut refinings = Refinings {
        branches: Vec::new(),
        under: alloc::vec![Maybe::Absent(refined::Absent::Unswitched); tests.len()],
    };
    let stand = |under: &mut [Maybe<RefiningAt, refined::Absent>], at: TestAt, branch| {
        if let Some(slot) = under.get_mut(at.0) {
            *slot = branch;
        }
    };
    for (position, test) in tests.iter().enumerate() {
        let above = refinings
            .under
            .get(position)
            .copied()
            .unwrap_or(Maybe::Absent(refined::Absent::Unswitched));
        match *test {
            Test::Pending | Test::Stuck(_) | Test::Absurd | Test::Leaf { .. } => {},
            Test::Data {
                level,
                depth,
                family: Maybe::Present(family),
                ref branches,
                ..
            } => {
                for (tag, &(arity, at)) in branches.iter().enumerate() {
                    let here = RefiningAt(refinings.branches.len());
                    refinings.branches.push(Refining {
                        switch: TestAt(position),
                        level,
                        depth,
                        family,
                        tag: ConstructorTag::from(tag),
                        arity,
                        outer: above,
                    });
                    stand(&mut refinings.under, at, Maybe::Present(here));
                }
            },
            Test::Data {
                family: Maybe::Absent(_),
                ref branches,
                ..
            } => {
                for &(_arity, at) in branches {
                    stand(&mut refinings.under, at, above);
                }
            },
            Test::Boolean { yes, no, .. } | Test::Integer { yes, no, .. } => {
                stand(&mut refinings.under, yes, above);
                stand(&mut refinings.under, no, above);
            },
            Test::Split { child, .. } | Test::Record { child, .. } => {
                stand(&mut refinings.under, child, above);
            },
            Test::List { nil, cell, .. } => {
                stand(&mut refinings.under, nil, above);
                stand(&mut refinings.under, cell, above);
            },
            Test::Sum { ref branches, .. } => {
                for &at in branches {
                    stand(&mut refinings.under, at, above);
                }
            },
        }
    }

    refinings
}

/// Whether the motive [`tracked_motives`] read for each data switch over a
/// bare family reads its binder.
///
/// # Specification
/// - requires: `tracked` holds the motive [`tracked_motives`] read for each
///   node of `tests`, or nothing.
/// - ensures: one entry per node of `tests`, dependent exactly when the node is
///   a data switch over a bare family whose motive is tracked and does not
///   strengthen past its binder.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a root whose answer names its scrutinee refines each
///   branch's leaves, and one whose answer does not refines none.
/// - witness: `lower::native::tests::a_case_over_a_variable_answers_its_motive_at_each_constructor`
/// - witness: `lower::native::tests::an_arm_variable_at_a_switched_field_reads_its_constructor_3008`
#[spec(ensures: |ret| ret.len() == tests.len())]
fn dependents(
    tests: &[Test],
    tracked: &[Maybe<CompTypeId, lowered::Absent>],
    arena: &mut CoreArena,
) -> Vec<Dependent>
{
    tests
        .iter()
        .enumerate()
        .map(|(position, test)| {
            let (
                &Test::Data {
                    family: Maybe::Present(_),
                    ..
                },
                Some(&Maybe::Present(motive)),
            ) = (test, tracked.get(position))
            else {
                return Dependent(false);
            };
            Dependent(matches!(
                gandr_core_term::strengthen_comp_type(arena, motive),
                Maybe::Absent(_)
            ))
        })
        .collect()
}

/// The scrutinee's index in the case's frame, when it is an intuitionistic
/// variable of the frame.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the index of the intuitionistic variable the scrutinee is, when
///   it is below the frame's term binders; the unbound absence otherwise.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a case over a parameter reads it at each constructor.
/// - witness: `lower::native::tests::a_case_over_a_variable_answers_its_motive_at_each_constructor`
#[spec(ensures: |ret| match ret {
    | Maybe::Present(held) => held < scrutinised.outer,
    | Maybe::Absent(_) => true,
})]
fn held_variable(
    scrutinised: Scrutinised,
    arena: &CoreArena,
) -> Maybe<Depth, refined::Absent>
{
    match arena.value(scrutinised.scrutinee) {
        Some(&Value::Variable {
            zone: Zone::Intuitionistic,
            index,
        }) => match usize::try_from(u32::from(index)) {
            Ok(held) if held < scrutinised.outer.0 => Maybe::Present(Depth(held)),
            Ok(_) | Err(_) => Maybe::Absent(refined::Absent::Unbound),
        },
        _ => Maybe::Absent(refined::Absent::Unbound),
    }
}

impl<'tree> Readings<'tree>
{
    /// The branch above a node below `under` that refines `level`: the
    /// innermost whose switch scrutinises it, when that switch's motive reads
    /// its binder.
    ///
    /// # Specification
    /// - requires: as [`Refinings::switched`].
    /// - ensures: the branch [`Refinings::switched`] finds, when its switch is
    ///   dependent; the independent absence when it is not, and the unswitched
    ///   absence when there is none.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Refining`].
    /// - witness: `lower::native::tests::a_case_over_a_variable_answers_its_motive_at_each_constructor`
    /// - witness: `lower::native::tests::an_arm_variable_at_a_switched_field_reads_its_constructor_3008`
    #[spec(ensures: |ret| match ret {
        | Maybe::Present(branch) => branch.level == level,
        | Maybe::Absent(_) => true,
    })]
    fn refines(
        &self,
        under: Maybe<RefiningAt, refined::Absent>,
        level: TreeLevel,
    ) -> Maybe<&'tree Refining, refined::Absent>
    {
        match self.refinings.switched(under, level) {
            Maybe::Present(branch)
                if self
                    .dependent
                    .get(branch.switch.0)
                    .is_some_and(|&Dependent(reads)| reads) =>
            {
                Maybe::Present(branch)
            },
            Maybe::Present(_) => Maybe::Absent(refined::Absent::Independent),
            Maybe::Absent(reason) => Maybe::Absent(reason),
        }
    }
}

/// The levels a reading reaches from `start`, in prefix order, each with the
/// branch `branch` finds for it: a level whose branch's switch stands above a
/// binder past the level is followed by that branch's fields, each read so in
/// turn; any other level ends its path.
///
/// # Specification
/// - requires: nothing.
/// - ensures: `start` first; after each level whose branch is present at a
///   depth at least the level, the levels of that branch's fields, the first
///   field first; every level paired with what `branch` finds for it.
/// - fails: never.
/// - panics: none.
/// - executable: none — the specification facade wraps the body in a closure,
///   which cannot return the opaque iterator; [`level_read`] and [`arm_read`]
///   state what their readings of it ensure.
///
/// # Termination
/// Each level the walk reaches is a field of the branch refining the level
/// before it, past that level; the levels a chain's branches refine are
/// distinct and their fields disjoint, so the walk reads each branch on the
/// chain at most once.
///
/// # Adequacy
/// - hypothesis: L3 — as [`level_read`] and [`arm_read`].
/// - witness: `lower::native::tests::an_arm_variable_at_a_switched_field_reads_its_constructor_3008`
/// - witness: `lower::native::tests::a_case_over_a_variable_answers_its_motive_at_each_constructor`
/// - witness: `lower::native::tests::a_match_in_an_arm_reads_the_answer_at_the_arm_s_constructor_2994`
fn levels<'tree>(
    start: TreeLevel,
    mut branch: impl FnMut(TreeLevel) -> Maybe<&'tree Refining, refined::Absent>,
) -> impl Iterator<Item = (TreeLevel, Maybe<&'tree Refining, refined::Absent>)>
{
    let mut pending = alloc::vec![start];
    core::iter::from_fn(move || {
        let at = pending.pop()?;
        let found = branch(at);
        if let Maybe::Present(refining) = found
            && refining.depth.0 >= at.0
        {
            pending.extend(
                (0 .. refining.arity).rev().map(|field| {
                    TreeLevel(refining.depth.0.saturating_add(field).saturating_add(1))
                }),
            );
        }
        Some((at, found))
    })
}

/// The value a leaf under `depth` tree binders, below the branch `under`,
/// reads the level `level` at.
///
/// # Specification
/// - requires: `level` is at most `depth`; `under` is the leaf's entry of the
///   readings' [`Refinings::under`].
/// - ensures: the constructor of the branch [`Readings::refines`] finds for
///   `level`, over what the leaf reads each of its fields at, read so in turn;
///   the level's [`level_value`] when none refines it, or when the branch's
///   switch stands above no binder past the level.
/// - fails: never.
/// - panics: none.
///
/// # Termination
/// As [`levels`], whose walk it reads.
///
/// # Adequacy
/// - hypothesis: L3 — an arm variable at a field a nested switch matched reads
///   that switch's constructor, and the scrutinee's variable reads every
///   switched level beneath it so.
/// - witness: `lower::native::tests::an_arm_variable_at_a_switched_field_reads_its_constructor_3008`
/// - witness: `lower::native::tests::a_case_over_a_variable_answers_its_motive_at_each_constructor`
#[spec(ensures: |ret| arena.value(ret).is_some())]
fn level_read(
    arena: &mut CoreArena,
    (scrutinised, readings): (Scrutinised, Readings<'_>),
    under: Maybe<RefiningAt, refined::Absent>,
    depth: Depth,
    level: TreeLevel,
) -> ValueId
{
    if !matches!(readings.refines(under, level), Maybe::Present(branch) if branch.depth.0 >= level.0)
    {
        return level_value(arena, scrutinised, depth, level);
    }
    let order: Vec<(TreeLevel, Maybe<&Refining, refined::Absent>)> =
        levels(level, |at| readings.refines(under, at)).collect();
    let mut values: Vec<ValueId> = Vec::with_capacity(order.len());
    for &(at, branch) in order.iter().rev() {
        let value = match branch {
            Maybe::Present(branch) if branch.depth.0 >= at.0 => {
                let from = values.len().saturating_sub(branch.arity);
                let fields = values.drain(from ..).rev().collect();
                constructed(arena, branch.family, branch.tag, fields)
            },
            Maybe::Present(_) | Maybe::Absent(_) => level_value(arena, scrutinised, depth, at),
        };
        values.push(value);
    }
    values
        .pop()
        .unwrap_or_else(|| level_value(arena, scrutinised, depth, level))
}

/// What the arm `arm` of a match on the variable `scrutinee` binds reads
/// that variable at, over the binders `variables` of the arm's variables.
///
/// # Specification
/// - requires: `refinings` is [`refinings`] of `tests`; `variables` holds the
///   binders of the arm's variables, in variable order.
/// - ensures: settled when the arm has a leaf and every leaf of it reads the
///   scrutinee alike, as [`arm_read`] reads it, at a constructor. Unnamed
///   otherwise.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — an arm naming its constructor's field settles, one whose
///   nested pattern switches the field settles at the nested constructor, and
///   one leaving a field to a wildcard leaves it unnamed.
/// - witness: `lower::native::tests::a_match_in_an_arm_reads_the_answer_at_the_arm_s_constructor_2994`
/// - witness: `lower::native::tests::an_arm_leaving_a_field_unnamed_passes_the_answer_as_written_2994`
/// - witness: `lower::native::tests::an_arm_variable_at_a_switched_field_reads_its_constructor_3008`
#[spec(ensures: |ret| match ret {
    | Maybe::Present(ref settled) => {
        settled.scrutinee == scrutinee
            && matches!(settled.read.first(), Some(&Built::Constructed { .. }))
    },
    | Maybe::Absent(_) => true,
})]
fn arm_settled(
    tests: &[Test],
    refinings: &Refinings,
    arm: ArmAt,
    variables: &[ScopeId],
    scrutinee: ScopeId,
) -> Maybe<Settled, settled::Absent>
{
    let unnamed = Maybe::Absent(settled::Absent::Unnamed);
    let mut found: Option<Vec<Built>> = None;
    for (test, &under) in tests.iter().zip(&refinings.under) {
        let Test::Leaf {
            arm: reached,
            depth,
            ref bindings,
        } = *test
        else {
            continue;
        };
        if reached != arm {
            continue;
        }
        let Maybe::Present(read) = arm_read(refinings, under, depth, (bindings, variables))
        else {
            return unnamed;
        };
        if !matches!(read.first(), Some(&Built::Constructed { .. })) {
            return unnamed;
        }
        match found {
            Some(ref first) if *first != read => return unnamed,
            Some(_) => {},
            None => found = Some(read),
        }
    }
    found.map_or(unnamed, |read| Maybe::Present(Settled { scrutinee, read }))
}

/// What a leaf under `depth` tree binders, below the branch `under`,
/// settling the arm variables `variables` at the levels `bindings`, reads the
/// scrutinee at as its arm passes it on, in prefix order.
///
/// # Specification
/// - requires: `bindings` and `variables` are the leaf's levels and its arm's
///   binders, in variable order, each level at most `depth`.
/// - ensures: each level read as the constructor of the innermost branch above
///   the leaf whose switch scrutinises it, followed by what the leaf reads each
///   field at; else as the binder of the first variable settled at it. Unnamed
///   when some level the reading reaches is neither, or a branch's switch
///   stands above no binder past the level it scrutinises.
/// - fails: never.
/// - panics: none.
///
/// # Termination
/// As [`levels`], whose walk it reads.
///
/// # Adequacy
/// - hypothesis: L3 — as [`arm_settled`].
/// - witness: `lower::native::tests::a_match_in_an_arm_reads_the_answer_at_the_arm_s_constructor_2994`
/// - witness: `lower::native::tests::an_arm_variable_at_a_switched_field_reads_its_constructor_3008`
#[spec(ensures: |ret| match ret {
    | Maybe::Present(ref read) => !read.is_empty(),
    | Maybe::Absent(_) => true,
})]
fn arm_read(
    refinings: &Refinings,
    under: Maybe<RefiningAt, refined::Absent>,
    depth: Depth,
    (bindings, variables): (&[TreeLevel], &[ScopeId]),
) -> Maybe<Vec<Built>, settled::Absent>
{
    let unnamed = Maybe::Absent(settled::Absent::Unnamed);
    let mut named: Vec<Option<ScopeId>> = alloc::vec![None; depth.0.saturating_add(1)];
    for (&level, &binder) in bindings.iter().zip(variables) {
        if let Some(slot) = named.get_mut(level.0) {
            let _first = slot.get_or_insert(binder);
        }
    }
    let mut read = Vec::new();
    for (at, branch) in levels(TreeLevel::default(), |at| refinings.switched(under, at)) {
        match branch {
            Maybe::Present(branch) if branch.depth.0 >= at.0 => {
                read.push(Built::Constructed {
                    family: branch.family,
                    tag: branch.tag,
                    arity: branch.arity,
                });
            },
            Maybe::Present(_) => return unnamed,
            Maybe::Absent(_) => {
                let Some(&Some(binder)) = named.get(at.0)
                else {
                    return unnamed;
                };
                read.push(Built::Bound(binder));
            },
        }
    }
    Maybe::Present(read)
}

/// The constructor `tag` of the parameterless family `family` over `fields`.
///
/// # Specification
/// trivial.
pub(super) fn constructed(
    arena: &mut CoreArena,
    family: ConstantIndex,
    tag: ConstructorTag,
    fields: Vec<ValueId>,
) -> ValueId
{
    let classifier = arena.value_type_data(family, Vec::new());
    arena.value_constructor(classifier, tag, fields)
}

/// The closed constructor term the prefix-ordered `point` spells over
/// `carrier`, whose constructors take `arities` fields, every value it mints
/// reported to `minted` in mint order.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the term whose prefix reading is `point`'s constructor nodes,
///   each a constructor of `carrier` over the terms after it; the unminted
///   absence for an empty point.
/// - fails: never.
/// - panics: none.
///
/// # Termination
/// - reason: one `for` over the point's nodes, not recursion.
/// - measure: the nodes left.
///
/// # Adequacy
/// - hypothesis: L3 — the circle's point is `Base`, the loop arm's case at it
///   and the words' path type alike.
/// - witness: `lower::native::tests::a_loop_arm_follows_the_constructors_branches`
#[spec(captures: before = minted.len(), ensures: |ret| minted.len() >= before && matches!(ret, Maybe::Absent(_)) == (minted.len() == before))]
fn spelled_point(
    arena: &mut CoreArena,
    carrier: ValueTypeId,
    (point, arities): (
        &[gandr_core_term::RuleNode],
        &[gandr_kernel_term::FieldCount],
    ),
    minted: &mut Vec<ValueId>,
) -> Maybe<ValueId, lowered::Absent>
{
    let mut built = Vec::new();
    for node in point.iter().rev() {
        let gandr_core_term::RuleNode::Constructor(tag) = *node
        else {
            continue;
        };
        let arity = arities
            .get(usize::from(tag))
            .copied()
            .map_or(0_usize, usize::from);
        let fields: Vec<ValueId> = built
            .drain(built.len().saturating_sub(arity) ..)
            .rev()
            .collect();
        let value = arena.value_constructor(carrier, tag, fields);
        minted.push(value);
        built.push(value);
    }
    built
        .last()
        .copied()
        .map_or(Maybe::Absent(lowered::Absent::Unminted), Maybe::Present)
}

/// `ty`, read under `context` binders, with the value `scrutinee` abstracted
/// as one binder more: the motive a dependent split reads.
///
/// # Specification
/// - requires: `ty` and `scrutinee` are read under `context` binders.
/// - ensures: for an intuitionistic variable `context` binders hold, `ty` under
///   one binder more with that variable read as the new binder and every other
///   index read one further out; for any other scrutinee, `ty` under one binder
///   more, reading none of it.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — an answer naming the scrutinee parameter abstracts it,
///   and one naming another parameter keeps it.
/// - witness: `lower::native::tests::a_pattern_at_a_dependent_record_splits_it_under_its_motive`
#[spec(ensures: |ret| arena.comp_type(ret).is_some())]
fn abstracted(
    arena: &mut CoreArena,
    ty: CompTypeId,
    scrutinee: ValueId,
    context: Depth,
) -> CompTypeId
{
    let held = match arena.value(scrutinee) {
        Some(&Value::Variable {
            zone: Zone::Intuitionistic,
            index,
        }) => usize::try_from(u32::from(index)).unwrap_or(usize::MAX),
        _ => usize::MAX,
    };
    if held >= context.0 {
        return gandr_core_term::shift_comp_type(arena, ty, Binders::ONE).settle(arena);
    }
    let environment: Vec<ValueId> = (0 .. context.0)
        .map(|position| {
            if position == held {
                variable(arena, Depth::default())
            }
            else {
                variable(arena, Depth(position.saturating_add(1)))
            }
        })
        .collect();
    match environment_substituted(arena, ty, &environment) {
        Maybe::Present(motive) => motive,
        Maybe::Absent(_) => gandr_core_term::shift_comp_type(arena, ty, Binders::ONE).settle(arena),
    }
}

/// `ty` with each index `i` below `environment`'s length read as its entry
/// `i`.
///
/// # Specification
/// - requires: `ty` is read under `environment.len()` binders, and every entry
///   under the context the result is read in.
/// - ensures: the substituted type, read back out of its quotation; absent when
///   the substitution yields no quoted type.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a split's answer abstracts its scrutinee, and an arm's
///   answer reads its scrutinee at the arm's constructor.
/// - witness: `lower::native::tests::a_pattern_at_a_dependent_record_splits_it_under_its_motive`
/// - witness: `lower::native::tests::a_match_in_an_arm_reads_the_answer_at_the_arm_s_constructor_2994`
#[spec(ensures: |ret| matches!(ret, Maybe::Absent(_)) || matches!(ret, Maybe::Present(read) if arena.comp_type(read).is_some()))]
fn environment_substituted(
    arena: &mut CoreArena,
    ty: CompTypeId,
    environment: &[ValueId],
) -> Maybe<CompTypeId, lowered::Absent>
{
    let quoted = arena.value_quote_computation(ty);
    match gandr_core_term::substitute_environment(arena, TermId::Value(quoted), environment) {
        TermId::Value(substituted) => match arena.value(substituted) {
            Some(&Value::QuoteComputation(read)) => Maybe::Present(read),
            _ => Maybe::Absent(lowered::Absent::Unminted),
        },
        TermId::Computation(_) => Maybe::Absent(lowered::Absent::Unminted),
    }
}

/// Mint one node of a match's tree over its already minted children.
///
/// # Specification
/// - requires: every child of `test` is minted in `minted` or absent; `read` is
///   the motive [`tracked_motives`] read for this node, `under` the branch
///   [`refinings`] stands it under, `readings` the tree's, and `answered` the
///   answer the match writes, read where the node stands, for its root; `armed`
///   is empty or holds, per term binder of the case's frame, the value
///   [`Lowerer::arm_readings`] reads it as.
/// - ensures: as [`Lowerer::mint_case`], for one node; a data case and a
///   dependent split read the read motive; a leaf reads each arm variable as
///   [`level_read`] reads the level that settled it, and, under a refining
///   root, the scrutinee's variable as [`level_read`] reads level zero; a leaf
///   reads each variable of the case's frame as its entry of a nonempty
///   `armed`, read so; any other node ascribed `answered`, an integer test's
///   case under its comparison's binder; nothing when a child, the arm's body
///   or a needed motive is absent. A leaf's copy of an exit or of a bind whose
///   rest is distributed is recorded as its original is, and every copy a leaf
///   makes is reported in `copies` beside its original.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — as [`Lowerer::mint_case`].
/// - witness: `lower::native::tests::nested_constructor_patterns_compile_to_nested_cases`
/// - witness: `lower::native::tests::a_pattern_at_a_dependent_record_splits_it_under_its_motive`
/// - witness: `lower::native::tests::a_case_over_a_variable_answers_its_motive_at_each_constructor`
/// - witness: `lower::native::tests::a_match_in_an_arm_reads_the_answer_at_the_arm_s_constructor_2994`
/// - witness: `lower::native::tests::an_arm_variable_at_a_switched_field_reads_its_constructor_3008`
#[spec(ensures: |ret| matches!(ret, Maybe::Absent(_)) || matches!(ret, Maybe::Present(id) if sink.arena.computation(id).is_some()))]
fn mint_test(
    test: &Test,
    (scrutinised, readings): (Scrutinised, Readings<'_>),
    (bodies, armed): (&[Maybe<ComputationId, lowered::Absent>], &[ValueId]),
    minted: &[Maybe<ComputationId, lowered::Absent>],
    (read, under, answered): (
        Maybe<CompTypeId, lowered::Absent>,
        Maybe<RefiningAt, refined::Absent>,
        Maybe<CompTypeId, lowered::Absent>,
    ),
    sink: &mut Sink<'_>,
    copies: &mut Vec<Carried>,
) -> Maybe<ComputationId, lowered::Absent>
{
    let child = |at: TestAt| {
        minted
            .get(at.0)
            .copied()
            .unwrap_or(Maybe::Absent(lowered::Absent::Unminted))
    };
    match *test {
        Test::Pending => Maybe::Absent(lowered::Absent::Unminted),
        Test::Stuck(hole) => {
            let hole = sink.arena.computation_hole(hole);
            Maybe::Present(answered_at(sink, hole, answered))
        },
        Test::Absurd => {
            let Maybe::Present(motive) = read
            else {
                return Maybe::Absent(lowered::Absent::Unminted);
            };
            let equation = variable(sink.arena, Depth::default());
            Maybe::Present(sink.arena.computation_data_case(
                equation,
                motive,
                Vec::new(),
                Vec::new(),
            ))
        },
        Test::Leaf {
            arm,
            depth,
            ref bindings,
        } => {
            let Some(&Maybe::Present(body)) = bodies.get(arm.0)
            else {
                return Maybe::Absent(lowered::Absent::Unminted);
            };
            let armed = armed_for(sink.arena, body, Depth(bindings.len()), armed);
            let held = match (readings.held, readings.refines(under, TreeLevel::default())) {
                (Maybe::Present(held), Maybe::Present(_)) => Maybe::Present(held),
                (Maybe::Present(_), Maybe::Absent(reason)) | (Maybe::Absent(reason), _) => {
                    Maybe::Absent(reason)
                },
            };
            if depth == Depth::default()
                && bindings.is_empty()
                && matches!(held, Maybe::Absent(_))
                && armed.is_empty()
            {
                return Maybe::Present(answered_at(sink, body, answered));
            }
            let mut environment =
                Vec::with_capacity(bindings.len().saturating_add(scrutinised.outer.0));
            for &level in bindings.iter().rev() {
                environment.push(level_read(
                    sink.arena,
                    (scrutinised, readings),
                    under,
                    depth,
                    level,
                ));
            }
            for outer in 0 .. scrutinised.outer.0 {
                let read = match held {
                    Maybe::Present(Depth(held)) if held == outer => level_read(
                        sink.arena,
                        (scrutinised, readings),
                        under,
                        depth,
                        TreeLevel::default(),
                    ),
                    Maybe::Present(_) | Maybe::Absent(_) => {
                        variable(sink.arena, Depth(outer.saturating_add(depth.0)))
                    },
                };
                environment.push(read);
            }
            // The arms the answer was passed into read the frame's variables
            // first, the leaf's own reading of them after.
            if !armed.is_empty() {
                let reads = environment.split_off(bindings.len());
                for &reading in armed {
                    match gandr_core_term::substitute_environment(
                        sink.arena,
                        TermId::Value(reading),
                        &reads,
                    ) {
                        TermId::Value(read) => environment.push(read),
                        TermId::Computation(_) => return Maybe::Absent(lowered::Absent::Unminted),
                    }
                }
            }
            let mut carried = Vec::new();
            match gandr_core_term::substitute_environment_traced(
                sink.arena,
                TermId::Computation(body),
                &environment,
                &mut carried,
            ) {
                TermId::Computation(substituted) => {
                    exits::mark_copies(sink, &carried);
                    copies.extend_from_slice(&carried);
                    Maybe::Present(answered_at(sink, substituted, answered))
                },
                TermId::Value(_) => Maybe::Absent(lowered::Absent::Unminted),
            }
        },
        Test::Data {
            level,
            depth,
            eliminated,
            equations,
            ref branches,
            ..
        } => {
            let Maybe::Present(motive) = read
            else {
                return Maybe::Absent(lowered::Absent::Unminted);
            };
            let mut lowered_branches = Vec::with_capacity(branches.len());
            let mut arities = Vec::with_capacity(branches.len());
            for &(arity, at) in branches {
                arities.push(gandr_kernel_term::FieldCount::from(arity));
                let Maybe::Present(mut branch) = child(at)
                else {
                    return Maybe::Absent(lowered::Absent::Unminted);
                };
                for _binder in 0 .. arity.saturating_add(equations) {
                    branch = sink.arena.computation_lambda(branch);
                }
                lowered_branches.push(branch);
            }
            let scrutinee = level_value(sink.arena, scrutinised, depth, level);
            let case = sink.arena.computation_data_case_with_equations(
                scrutinee,
                motive,
                (lowered_branches, arities),
                gandr_kernel_term::EquationCount::from(equations),
            );
            if let Maybe::Present(family) = eliminated {
                sink.origins.record_elimination(case, family);
            }
            Maybe::Present(case)
        },
        Test::Boolean {
            level,
            depth,
            yes,
            no,
        } => match (child(yes), child(no)) {
            (Maybe::Present(left), Maybe::Present(right)) => {
                let scrutinee = level_value(sink.arena, scrutinised, depth, level);
                let case = sink.arena.computation_case(scrutinee, &[left, right]);
                Maybe::Present(answered_at(sink, case, answered))
            },
            _ => Maybe::Absent(lowered::Absent::Unminted),
        },
        Test::Integer {
            level,
            depth,
            ref literal,
            yes,
            no,
        } => {
            let (Maybe::Present(left), Maybe::Present(right)) = (child(yes), child(no))
            else {
                return Maybe::Absent(lowered::Absent::Unminted);
            };
            // The integer primitive by its name, `int.eq`: `==` is the
            // prelude's equality through a model, which a printed test
            // would read back as.
            let Some(&equal) = PRELUDE
                .iter()
                .find(|primitive| primitive.name().as_ref() == "int.eq")
            else {
                return Maybe::Absent(lowered::Absent::Unminted);
            };
            let scrutinee = level_value(sink.arena, scrutinised, depth, level);
            let compared = sink.arena.value_literal(literal.clone());
            let test = sink
                .arena
                .computation_primitive(equal, Arguments::Binary([scrutinee, compared]));
            let answer = variable(sink.arena, Depth::default());
            let branched = sink.arena.computation_case(answer, &[left, right]);
            // The case stands under the comparison's binder.
            let answered = match answered {
                Maybe::Present(ty) => Maybe::Present(
                    gandr_core_term::shift_comp_type(sink.arena, ty, Binders::ONE)
                        .settle(sink.arena),
                ),
                Maybe::Absent(reason) => Maybe::Absent(reason),
            };
            let branched = answered_at(sink, branched, answered);
            Maybe::Present(sink.arena.computation_bind(test, branched))
        },
        Test::Split {
            level,
            depth,
            arity,
            dependent,
            child: at,
            ..
        } => {
            let Maybe::Present(body) = child(at)
            else {
                return Maybe::Absent(lowered::Absent::Unminted);
            };
            let scrutinee = level_value(sink.arena, scrutinised, depth, level);
            if dependent.0 {
                let Maybe::Present(read) = read
                else {
                    return Maybe::Absent(lowered::Absent::Unminted);
                };
                return Maybe::Present(sink.arena.computation_dependent_split(
                    scrutinee,
                    ComponentCount::from(arity),
                    read,
                    body,
                ));
            }
            let split = sink
                .arena
                .computation_split(scrutinee, ComponentCount::from(arity), body);
            Maybe::Present(answered_at(sink, split, answered))
        },
        Test::Record {
            level,
            depth,
            ref labels,
            child: at,
        } => {
            let Maybe::Present(mut body) = child(at)
            else {
                return Maybe::Absent(lowered::Absent::Unminted);
            };
            for (offset, label) in labels.iter().enumerate().rev() {
                let under = Depth(depth.0.saturating_add(offset));
                let record = level_value(sink.arena, scrutinised, under, level);
                let projected = sink
                    .arena
                    .computation_record_projection(record, label.clone());
                body = sink.arena.computation_bind(projected, body);
            }
            Maybe::Present(answered_at(sink, body, answered))
        },
        Test::Sum {
            level,
            depth,
            ref branches,
        } => {
            let mut lowered_branches = Vec::with_capacity(branches.len());
            for &at in branches {
                let Maybe::Present(branch) = child(at)
                else {
                    return Maybe::Absent(lowered::Absent::Unminted);
                };
                lowered_branches.push(branch);
            }
            let scrutinee = level_value(sink.arena, scrutinised, depth, level);
            let case = sink.arena.computation_case(scrutinee, &lowered_branches);
            Maybe::Present(answered_at(sink, case, answered))
        },
        Test::List {
            level,
            depth,
            nil,
            cell,
        } => match (child(nil), child(cell)) {
            (Maybe::Present(empty), Maybe::Present(cons)) => {
                let scrutinee = level_value(sink.arena, scrutinised, depth, level);
                let case = sink.arena.computation_list_case(scrutinee, empty, cons);
                Maybe::Present(answered_at(sink, case, answered))
            },
            _ => Maybe::Absent(lowered::Absent::Unminted),
        },
    }
}

/// `armed` when the arm body `body`, read under `bound` arm variables past
/// the case's frame, reads a variable of the frame that `armed` reads as
/// other than itself; nothing otherwise.
///
/// # Specification
/// - requires: `armed` is empty or holds one value per term binder of the
///   case's frame, as [`Lowerer::arm_readings`] reads them.
/// - ensures: `armed` exactly when an intuitionistic index `j` the body's
///   support selects is at least `bound` and `armed`'s entry `j - bound` is no
///   variable at its own index; empty otherwise.
/// - provides: a leaf that copies its body for the arm readings only where they
///   change it, so a body they leave alone keeps its nodes and their origins.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a match in an arm whose branches name the outer scrutinee
///   reads it at the arm's constructor, and a scrutinee in an arm whose leaf
///   body the readings leave alone keeps its label.
/// - witness: `lower::native::tests::a_match_in_an_arm_reads_the_answer_at_the_arm_s_constructor_2994`
/// - witness: `lower::exits::tests::a_use_a_local_end_replaces_keeps_its_bytes`
#[spec(ensures: |ret| ret.is_empty() || ret.len() == armed.len())]
fn armed_for<'armed>(
    arena: &CoreArena,
    body: ComputationId,
    bound: Depth,
    armed: &'armed [ValueId],
) -> &'armed [ValueId]
{
    let Some(support) = arena.computation_support(body)
    else {
        return &[];
    };
    let changes = support.indices(Zone::Intuitionistic).any(|read| {
        let Some(outer) = usize::try_from(u32::from(read))
            .ok()
            .and_then(|at| at.checked_sub(bound.0))
        else {
            return false;
        };
        armed.get(outer).is_some_and(|&reading| {
            !matches!(
                arena.value(reading),
                Some(&Value::Variable { zone: Zone::Intuitionistic, index })
                    if usize::try_from(u32::from(index)).ok() == Some(outer)
            )
        })
    });
    if changes { armed } else { &[] }
}

/// `id`, a match's root, ascribed `answered` when the match writes its
/// answer, and `id` itself otherwise.
///
/// # Specification
/// - requires: `answered` is read where `id` stands.
/// - ensures: the ascription of `id` to `answered` when present, else `id`.
/// - provides: the one ascription a written answer gives a match's root.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — as [`Lowerer::mint_case`].
/// - witness: `lower::native::tests::a_written_answer_ascribes_the_match_2089`
#[spec(ensures: |ret| match answered {
    | Maybe::Present(ty) => matches!(sink.arena.computation(ret), Some(&Computation::Ascribe { body, ty: written }) if body == id && written == ty),
    | Maybe::Absent(_) => ret == id,
})]
fn answered_at(
    sink: &mut Sink<'_>,
    id: ComputationId,
    answered: Maybe<CompTypeId, lowered::Absent>,
) -> ComputationId
{
    match answered {
        Maybe::Present(ty) => sink.arena.computation_ascribe(id, ty),
        Maybe::Absent(_) => id,
    }
}

/// The value tree level `level` names under `depth` tree binders: the
/// scrutinee carried under them for level zero, and else the binder that
/// introduced the level.
///
/// # Specification
/// - requires: `level` is at most `depth`.
/// - ensures: the scrutinee itself at depth zero; its shift by `depth`
///   otherwise; the variable `depth - level` for a binder's level.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a nested switch reads its field and a leaf its binder.
/// - witness: `lower::native::tests::nested_constructor_patterns_compile_to_nested_cases`
#[spec(ensures: |ret| arena.value(ret).is_some())]
fn level_value(
    arena: &mut CoreArena,
    scrutinised: Scrutinised,
    depth: Depth,
    level: TreeLevel,
) -> ValueId
{
    if level == TreeLevel::default() {
        if depth == Depth::default() {
            return scrutinised.scrutinee;
        }
        let lift = u32::try_from(depth.0).unwrap_or(u32::MAX);
        return gandr_core_term::shift_value(arena, scrutinised.scrutinee, Binders::from(lift))
            .settle(arena);
    }

    variable(arena, Depth(depth.0.saturating_sub(level.0)))
}

/// The intuitionistic variable `index` binders out.
///
/// # Specification
/// trivial.
fn variable(
    arena: &mut CoreArena,
    index: Depth,
) -> ValueId
{
    arena.value_variable(
        Zone::Intuitionistic,
        DeBruijnIndex::from(u32::try_from(index.0).unwrap_or(u32::MAX)),
    )
}

/// The integer pattern `text` spells, written at `here`.
///
/// # Specification
/// - requires: `text` is a number's lexeme.
/// - ensures: the canonical integer the lexeme denotes.
/// - fails: the malformed-literal refusal for a lexeme that is not decimal
///   digits.
/// - panics: none.
///
/// # Errors
/// [`LoweringRefusal::MalformedLiteral`].
///
/// # Adequacy
/// - hypothesis: L3 — a literal column compares against the written integer.
/// - witness: `lower::native::tests::literal_patterns_compare_and_branch`
#[spec(ensures: |ret| matches!(ret, Ok(Matcher::Integer(_)) | Err(LoweringRefusal::MalformedLiteral { .. })))]
fn integer<'source>(
    here: Site,
    text: gandr_surface_syntax::SourceFragment<'_>,
) -> Result<Matcher, LoweringRefusal<'source>>
{
    match parse_literal(Former::Number, text) {
        Maybe::Present(literal) => Ok(Matcher::Integer(literal)),
        Maybe::Absent(_) => Err(LoweringRefusal::MalformedLiteral {
            span: here.at.span,
            form: here.name,
        }),
    }
}

/// The node a matrix whose first row tests nothing reduces to: the hole it
/// matched through, or its arm with every variable at the level that settled
/// it.
///
/// # Specification
/// - requires: no column of `first` holds a pattern that tests.
/// - ensures: a stuck node on the first hole `first` passed; else a leaf of its
///   arm under `depth` binders, one level per arm variable in variable order,
///   the variables its binders in the remaining columns settle included.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a binder in the scrutinee's column and one in a field
///   each reach the arm body at their own level.
/// - witness: `lower::native::tests::nested_constructor_patterns_compile_to_nested_cases`
/// - witness: `lower::native::tests::a_pattern_hole_leaves_its_leaf_stuck`
#[spec(ensures: |ret| match first.stuck {
    | Maybe::Present(hole) => ret == Test::Stuck(hole),
    | Maybe::Absent(_) => matches!(ret, Test::Leaf { arm, depth: under, .. } if arm == first.arm && under == depth),
})]
fn leaf(
    patterns: &Written,
    first: &Row,
    levels: &[TreeLevel],
    depth: Depth,
) -> Test
{
    if let Maybe::Present(hole) = first.stuck {
        return Test::Stuck(hole);
    }
    let mut bindings = first.bindings.clone();
    for (&level, &pattern) in levels.iter().zip(&first.columns) {
        if let Some(&(_, Matcher::Binder(variable))) = patterns.shapes.get(pattern.0) {
            bindings.push((variable, level));
        }
    }
    bindings.sort_unstable();

    Test::Leaf {
        arm: first.arm,
        depth,
        bindings: bindings
            .into_iter()
            .map(|(_variable, level)| level)
            .collect(),
    }
}

/// `item` with every as-pattern its rows hold settled where it stands: the
/// alias's binder bound at the column's level and the column holding the
/// pattern it names, until none is left; none when no row holds one.
///
/// # Specification
/// - requires: `item`'s rows are as wide as its levels.
/// - ensures: `None` when no column of any row holds an as-pattern; else the
///   item with each such column replaced by the pattern it names and one more
///   binding per alias at that column's level.
/// - fails: never.
/// - panics: none.
/// - intension: each alias names a pattern minted after it, so the peeling of
///   one column ends.
///
/// # Adequacy
/// - hypothesis: L3 — an as-pattern over a cell binds the whole list beside the
///   cell's head and tail.
/// - witness: `lower::native::tests::list_patterns_case_on_the_native_list`
#[spec(ensures: |ret| ret.as_ref().is_none_or(|work| work.rows.len() == item.rows.len()))]
fn peeled(
    patterns: &Written,
    item: &Work,
) -> Option<Work>
{
    let alias = |at: PatternAt| match patterns.shapes.get(at.0) {
        Some(&(_, Matcher::Alias { inner, alias })) => Some((inner, alias)),
        _ => None,
    };
    if !item
        .rows
        .iter()
        .any(|row| row.columns.iter().any(|&at| alias(at).is_some()))
    {
        return None;
    }
    let mut work = item.clone();
    for row in &mut work.rows {
        for (column, &level) in row.columns.iter_mut().zip(&item.levels) {
            while let Some((inner, named)) = alias(*column) {
                if let Some(&(_, Matcher::Binder(variable))) = patterns.shapes.get(named.0) {
                    row.bindings.push((variable, level));
                }
                *column = inner;
            }
        }
    }

    Some(work)
}

/// Settle `held`, a pattern that matches anything, at `level` for `row`: a
/// binder binds its variable there, and a hole is the one the row passed
/// unless it passed an earlier one.
///
/// # Specification
/// - requires: `held` is the row's pattern in the column at `level`.
/// - ensures: one more binding for a binder; the hole recorded for a hole when
///   none was; nothing else changes.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a binder and a hole each settle at a constructor's
///   column.
/// - witness: `lower::native::tests::a_pattern_hole_leaves_its_leaf_stuck`
#[spec(
    captures: before = (row.bindings.len(), row.stuck),
    ensures: row.bindings.len() == before.0.saturating_add(usize::from(matches!(*held, Matcher::Binder(_))))
        && if let Matcher::Hole(hole) = *held && matches!(before.1, Maybe::Absent(_)) {
            row.stuck == Maybe::Present(hole)
        } else {
            row.stuck == before.1
        },
)]
fn through(
    row: &mut Row,
    held: &Matcher,
    level: TreeLevel,
)
{
    match *held {
        Matcher::Binder(variable) => row.bindings.push((variable, level)),
        Matcher::Hole(hole) => {
            if let Maybe::Absent(_) = row.stuck {
                row.stuck = Maybe::Present(hole);
            }
        },
        Matcher::Wild
        | Matcher::Constructor { .. }
        | Matcher::Boolean(_)
        | Matcher::Integer(_)
        | Matcher::Tuple { .. }
        | Matcher::Record { .. }
        | Matcher::Injection { .. }
        | Matcher::Nil
        | Matcher::Cell { .. }
        | Matcher::Alias { .. } => {},
    }
}

/// `columns` with the entry at `column` replaced by `replacement`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the entries before `column`, then `replacement`, then the entries
///   after it; `columns` and then `replacement` when `column` is past the end.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a constructor's fields take its column's place.
/// - witness: `lower::native::tests::nested_constructor_patterns_compile_to_nested_cases`
#[spec(ensures: |ret| ret.len() == columns.len().saturating_sub(usize::from(column.0 < columns.len())).saturating_add(replacement.len()))]
fn splice<Entry>(
    columns: &[Entry],
    column: Column,
    replacement: &[Entry],
) -> Vec<Entry>
where
    Entry: Copy,
{
    let mut spliced = Vec::with_capacity(columns.len().saturating_add(replacement.len()));
    spliced.extend(columns.iter().take(column.0).copied());
    spliced.extend_from_slice(replacement);
    spliced.extend(columns.iter().skip(column.0.saturating_add(1)).copied());

    spliced
}

/// The levels `width` fresh binders under `depth` tree binders introduce,
/// outermost first.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the levels `depth + 1` through `depth + width`, in order.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a split's components and a record's fields each reach
///   their arm at their own level.
/// - witness: `lower::native::tests::telescope_patterns_split_and_project`
#[spec(ensures: |ret| ret.len() == width.0 && ret.iter().enumerate().all(|(offset, level)| level.0 == depth.0.saturating_add(offset).saturating_add(1)))]
fn fresh(
    depth: Depth,
    width: Width,
) -> Vec<TreeLevel>
{
    (0 .. width.0)
        .map(|offset| TreeLevel(depth.0.saturating_add(offset).saturating_add(1)))
        .collect()
}

/// Allocate a slot in `patterns` for each of `queued`, as a fresh stretch
/// of the part store, and queue each on `work` to be read into its slot.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the stretch of the new parts, one per queued pattern in order,
///   each queued on `work` with its slot, the first popped first.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a constructor's, a tuple's and an injection's parts are
///   each read into their own slot.
/// - witness: `lower::native::tests::nested_constructor_patterns_compile_to_nested_cases`
/// - witness: `lower::native::tests::telescope_patterns_split_and_project`
#[spec(
    captures: before = (patterns.parts.len(), work.len()),
    ensures: |ret| ret.start == before.0 && ret.end == before.0.saturating_add(queued.len()) && work.len() == before.1.saturating_add(queued.len()),
)]
fn allocated(
    patterns: &mut Written,
    work: &mut Vec<Queued>,
    queued: &[Queued],
) -> Stretch
{
    let start = patterns.parts.len();
    for each in queued {
        let slot = PatternAt(patterns.shapes.len());
        patterns.shapes.push((each.at, Matcher::Wild));
        patterns.parts.push(slot);
    }
    let end = patterns.parts.len();
    for (offset, &each) in queued.iter().enumerate().rev() {
        if let Some(&slot) = patterns.parts.get(start.saturating_add(offset)) {
            work.push(Queued { slot, ..each });
        }
    }

    Stretch { start, end }
}

/// Settle the sum a case's sum patterns inject into where no sum is stated:
/// arms whose roots are indices under no stated sum, covering the summands
/// `.0` to `.n-1` between them, inject into a sum of `n` summands.
///
/// # Specification
/// - requires: `roots` holds each arm's root pattern in `patterns`, the
///   patterns of a case's arms.
/// - ensures: every sum pattern read under no stated sum injects into a sum one
///   wider than the greatest index among them, when each is an arm's root,
///   every root is one, and their indices cover every summand below the
///   greatest; nothing changes when none was read.
/// - fails: the unannotated refusal, at the first such pattern, otherwise.
/// - panics: none.
/// - executable: none — the settled arity is the width the switch the case
///   compiles next takes from the arms, whose branch count its own predicate
///   checks.
///
/// # Errors
/// The unannotated refusal.
///
/// # Adequacy
/// - hypothesis: L3 — two and three indexed arms settle their sum; an arm that
///   matches anything, a summand no arm writes and an index nested in a tuple
///   are refused.
/// - witness: `lower::native::tests::indexed_arms_settle_their_sum_1169`
fn settle_unstated<'source>(
    patterns: &mut Written,
    roots: &[(ArmAt, PatternAt, NodeIndex, NodeIndex)],
) -> Result<(), LoweringRefusal<'source>>
{
    let Some(&(_, first)) = patterns.unstated.first()
    else {
        return Ok(());
    };
    let refused = || first.out(FragmentBoundary::Unannotated);
    let unstated: BTreeSet<PatternAt> = patterns.unstated.iter().map(|&(slot, _)| slot).collect();
    let rooted: BTreeSet<PatternAt> = roots.iter().map(|&(_, root, ..)| root).collect();
    if unstated != rooted {
        return Err(refused());
    }
    let mut covered: Vec<bool> = Vec::new();
    for root in rooted {
        let Some(&(_, Matcher::Injection { summand, .. })) = patterns.shapes.get(root.0)
        else {
            return Err(refused());
        };
        if covered.len() <= summand {
            covered.resize(summand.saturating_add(1), false);
        }
        if let Some(seen) = covered.get_mut(summand) {
            *seen = true;
        }
    }
    if !covered.iter().all(|&seen| seen) {
        return Err(refused());
    }
    let width = covered.len();
    for &(slot, _) in &patterns.unstated {
        if let Some(&mut (_, Matcher::Injection { ref mut arity, .. })) =
            patterns.shapes.get_mut(slot.0)
        {
            *arity = width;
        }
    }
    Ok(())
}

/// Record `origin` for every node minted since `mark`, and the root's own
/// origin for the root.
///
/// # Specification
/// - requires: nothing has been recorded for a node minted since `mark`.
/// - ensures: every node minted since `mark` carries `origin`, in ascending
///   order in each family, except the root, which carries its own.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — every node of a compiled tree has an origin.
/// - witness: `lower::native::tests::a_match_keeps_its_patterns_beside_its_tree`
#[spec(ensures: sink.arena.values_since(mark).all(|id| sink.origins.value(id) == Maybe::Present(origin))
    && sink.arena.computations_since(mark).all(|id| match root {
        | Maybe::Present((held, written)) if held == id => sink.origins.computation(id) == Maybe::Present(written),
        | _ => sink.origins.computation(id) == Maybe::Present(origin),
    }))]
pub(super) fn record_since(
    sink: &mut Sink<'_>,
    mark: gandr_core_term::ArenaWatermark,
    origin: Origin,
    root: Maybe<(ComputationId, Origin), rooted::Absent>,
)
{
    record_copied_since(sink, mark, origin, root, &[]);
}

/// Record, for every copy a match's leaves made of a written variable, the
/// binder the variable was written against.
///
/// A leaf places an arm's body under the binders its tests opened, so each
/// written use in the body stands in the tree as the copy the substitution
/// minted for it. The copy keeps the use's binder, which is what names the
/// binders a split opens for its components: a type the copy's judgement
/// spells, a dependent split's answer at its components say, reads them by
/// the names the arm wrote. A pattern variable that binds the whole scrutinee
/// stands for the scrutinee's own node, which the leaf did not mint; that
/// node keeps the binding it was written with.
///
/// A rewrite can copy a copy: an arm that writes a call inside another form
/// reports the use's first copy as the source of a second. The copies are
/// recorded in ascending order and each source is read as the loop reaches
/// it, so the second copy finds the binder its source took earlier in the
/// same pass; reading every source before recording any left it unbound.
///
/// # Specification
/// - requires: `carried` is what the rewrites since `floor` reported, and no
///   variable the origin table records a binding for was minted after it.
/// - ensures: every value minted after `floor` that `carried` maps a recorded
///   use to holds that use's binder, recorded once, in ascending order of the
///   copies; a value from before `floor` keeps what it held.
/// - provides: what keeps a match leaf's copy of a use naming its binder.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a leaf's copy of an arm returning its two pattern
///   variables swapped names each at the variable that binds it, and a variable
///   binding the whole scrutinee leaves the scrutinee bound at its parameter; a
///   copy left without its binding, bound at the other component, or a
///   scrutinee rebound at the pattern fails the witness. A copy the same
///   rewrite made of a copy names the use's binder too; reading every source
///   before recording any leaves it unbound and fails the second witness.
/// - witness: `lower::native::tests::a_leaf_copy_keeps_each_use_naming_its_pattern_variable`
/// - witness: `lower::native::tests::a_leaf_copy_of_a_copy_keeps_the_use_naming_its_binder_451`
#[spec(
    requires: sink.arena.values_since(floor).next().is_none_or(|first| {
        sink.origins.bindings().last().is_none_or(|&(held, _)| held < first)
    }),
    ensures: carried.iter().all(|pair| match *pair {
        Carried::Value(held, written) => sink.arena.values_since(floor).next().is_none_or(|first| written < first)
            || matches!(sink.origins.binding(held), Maybe::Absent(_))
            || matches!(sink.origins.binding(written), Maybe::Present(_)),
        Carried::Computation(..) | Carried::ValueType(..) | Carried::CompType(..) => true,
    }),
)]
fn carry_bindings(
    sink: &mut Sink<'_>,
    carried: &[Carried],
    floor: gandr_core_term::ArenaWatermark,
)
{
    let Some(first) = sink.arena.values_since(floor).next()
    else {
        return;
    };
    let mut copies: Vec<(ValueId, ValueId)> = carried
        .iter()
        .filter_map(|pair| match *pair {
            Carried::Value(held, written) if first <= written => Some((written, held)),
            Carried::Value(..)
            | Carried::Computation(..)
            | Carried::ValueType(..)
            | Carried::CompType(..) => None,
        })
        .collect();
    copies.sort_by_key(|&(written, _)| written);
    let mut recorded = None;
    for (written, held) in copies {
        if recorded == Some(written) {
            continue;
        }
        if let Maybe::Present(binder) = sink.origins.binding(held) {
            sink.origins.record_binding(written, binder);
            recorded = Some(written);
        }
    }
}

/// [`record_since`], each node `carried` reports as a copy at the origin of
/// the node it was copied from, and each copy of a written use at the use's
/// binder.
///
/// # Specification
/// - requires: nothing has been recorded for a node minted since `mark`, and
///   `carried` reports the rewrites that minted the copies among them.
/// - ensures: every node minted since `mark` carries an origin, in ascending
///   order in each family: the root its own; a node `carried` reports as a copy
///   the origin of the node it was copied from, a copy of a match's root that
///   match's record too; every other node `origin`. Each written variable the
///   rewrite replaced by a node answering elsewhere is labelled with it, and a
///   copy of a written use holds the use's binder, as [`carry_bindings`]
///   states.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — every node of a compiled tree has an origin, and a leaf's
///   copy of its arm's body answers at the body's bytes.
/// - witness: `lower::native::tests::a_match_keeps_its_patterns_beside_its_tree`
/// - witness: `lower::native::tests::a_leaf_keeps_its_arm_body_written`
/// - witness: `lower::exits::tests::a_use_a_local_end_replaces_keeps_its_bytes`
/// - witness: `lower::native::tests::a_leaf_copy_keeps_each_use_naming_its_pattern_variable`
#[spec(ensures: sink.arena.values_since(mark).all(|id| matches!(sink.origins.value(id), Maybe::Present(_)))
    && sink.arena.computations_since(mark).all(|id| match root {
        | Maybe::Present((held, written)) if held == id => sink.origins.computation(id) == Maybe::Present(written),
        | _ => matches!(sink.origins.computation(id), Maybe::Present(_)),
    }))]
fn record_copied_since(
    sink: &mut Sink<'_>,
    mark: gandr_core_term::ArenaWatermark,
    origin: Origin,
    root: Maybe<(ComputationId, Origin), rooted::Absent>,
    carried: &[Carried],
)
{
    let sources = gandr_core_term::Sources::of(carried);
    for id in sink.arena.values_since(mark) {
        let recorded = exits::value_origin(sink, &sources, id, origin);
        sink.origins.record_value(id, recorded);
    }
    for id in sink.arena.computations_since(mark) {
        match root {
            Maybe::Present((held, written)) if held == id => {
                sink.origins.record_computation(id, written);
            },
            Maybe::Present(_) | Maybe::Absent(_) => {
                let recorded = exits::computation_origin(sink, &sources, id, origin);
                sink.origins.record_computation(id, recorded);
                exits::keep_case(sink, &sources, id);
            },
        }
    }
    for id in sink.arena.value_types_since(mark) {
        let recorded = exits::value_type_origin(sink, &sources, id, origin);
        sink.origins.record_value_type(id, recorded);
    }
    for id in sink.arena.comp_types_since(mark) {
        let recorded = exits::comp_type_origin(sink, &sources, id, origin);
        sink.origins.record_comp_type(id, recorded);
    }
    exits::label_replaced(sink, carried);
    carry_bindings(sink, carried, mark);
}

impl<'source> Lowerer<'_, 'source>
{
    /// Classify an instantiation, `f[<]`: the head of a recursive call
    /// claiming structural descent, the self reference a value passes on, or
    /// a function's implicits supplied where no call applies it.
    ///
    /// # Specification
    /// - requires: `site` is an instantiation in term position.
    /// - ensures: an instantiation whose one resident is `<` and whose head is
    ///   a name the frame of a recursive function's fixpoint binds stands as
    ///   the variable the frame binds, the fixpoint's own thunk, read inside a
    ///   type at its index in the type's telescope as [`Self::resolved_term`]
    ///   reads any binder there, makes the function's fixpoint claim descent
    ///   and checks the position [`Self::claim`] reads; heading a call, the
    ///   call passes each of the function's parameters before the staged one as
    ///   itself, labelled with its parameter's written type, and one argument
    ///   for the staged one and each after it. Inside a joint fixpoint
    ///   ([`Joint`]) a head naming a sibling member stands as the function's
    ///   own fixpoint binder, and either head's call injects its argument at
    ///   the called member's summand. The head's name, its marker aside, keeps
    ///   what it names: the fixpoint binder, or the sibling member's
    ///   declaration. A call whose one resident is `>` and which is the whole
    ///   arm of a copattern block stands as the same variable, passes its
    ///   arguments as a descent call does, and claims nothing: the fixpoint
    ///   stays partial. An instantiation whose residents supply a function's
    ///   implicits by name is planned as [`Self::supplied_value`] plans it; one
    ///   whose head names a held slot and whose bracket holds one number is the
    ///   element there, as [`Self::element`] plans it.
    /// - provides: the head of a recursive call, and the self reference a value
    ///   position passes on.
    /// - fails: the reserved refusal for any other resident, a termination
    ///   claim the grammar reserves, marking the resident under a named head
    ///   and the whole instantiation under any other head (#3811); the
    ///   unguarded-corecursion refusal for a `>` call that is not the whole arm
    ///   of a copattern block; the foreign-claim refusal for an instantiation
    ///   whose head names a function other than a recursive one in scope; the
    ///   unresolved-name refusal, at the head, for a head that names nothing;
    ///   the unadmitted refusal for a call through a joint member that stages a
    ///   parameter after its first, for a joint member's claim standing
    ///   unapplied, whose thunk is the joint's at the sum of the block's
    ///   domains, and for a `>` claim standing unapplied or naming a joint
    ///   member; the arity refusal, at the call, for a call passing other than
    ///   one argument per parameter; the non-uniform refusal, at the argument,
    ///   for a parameter before the staged one passed as anything but itself,
    ///   and at the call for a joint member over leading parameters; the
    ///   several-parameters refusal [`Self::claim`] raises; the wrong-sort
    ///   refusal outside a head or value position; and the allowance refusal
    ///   from the binder walk.
    /// - panics: none.
    ///
    /// # Errors
    /// The instantiation's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a descent call over one parameter, over a uniform
    ///   leading one and over a varying later one, a call through a joint
    ///   member over a later one, a claim standing unapplied and a productive
    ///   call as a copattern arm lower to their variable, and a descent call
    ///   under a lambda a body's quoted family holds to it at its index in the
    ///   body; a productive call elsewhere, combined claims, a claim on a
    ///   function that is not recursive, a wrong argument count and a varied
    ///   leading parameter each refuse by their own boundary, and a resident
    ///   that is no claim under a head that is no name marks the whole
    ///   instantiation.
    /// - witness: `lower::native::tests::a_recursive_function_closes_a_fixpoint_over_its_staged_parameter`
    /// - witness: `lower::native::tests::a_recursive_call_passes_its_leading_parameters_unchanged`
    /// - witness: `lower::native::tests::an_unapplied_claim_lowers_to_the_self_binder`
    /// - witness: `lower::native::tests::a_productive_call_is_the_whole_arm_of_a_copattern_block`
    /// - witness: `lower::native::tests::a_mutual_blocks_recursive_functions_share_one_fixpoint`
    /// - witness: `lower::native::tests::a_mutual_block_member_takes_a_parameter_after_its_staged_one_3722`
    /// - witness: `lower::tests::a_self_call_a_body_quotes_reads_its_fixpoint_at_its_index_3562`
    /// - witness: `lower::native::tests::a_reserved_claim_under_a_head_that_is_no_name_marks_the_whole_instantiation_3811`
    #[spec(ensures: |ret| ret.is_err() || matches!(self.plans.get(site.at.node), Some(&(Plan::Variable(..) | Plan::StaticApplication(Code::Bound { .. }, _) | Plan::Application(..) | Plan::Access(_)))))]
    pub(super) fn instantiation(
        &mut self,
        site: Site,
        mut cursor: Cursor<'_>,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        if let Some(&place) = self.view_places.get(&site.at.node) {
            return self.view_place(site, cursor, place);
        }
        if let Maybe::Present(lent) = self.lent_head(site)? {
            return self.element(site, cursor, lent);
        }
        if self.supplied_value(site)? == arity::Planned(true) {
            return Ok(());
        }
        let frame = self.require(site, Produced::Value)?;
        let head = site.one(cursor.operands())?;
        closed(site, &mut cursor, TileName::BRACKET_OPEN)?;
        let resident = site.one(cursor.operands())?;
        if let Maybe::Present(_) = cursor.at(TileName::COMMA) {
            return Err(site.out(FragmentBoundary::Reserved(Unbuilt::RecursiveClaim)));
        }
        closed(site, &mut cursor, TileName::BRACKET_CLOSE)?;
        exhausted(site, &cursor)?;
        let mut scratch = core::mem::take(&mut self.scratch);
        let read = read_pieces(self.pbg, self.tree, resident.node, &mut scratch);
        let claim = match *scratch.pieces.as_slice() {
            [Piece::Tile { label, .. }] if label == TileName::LESS_THAN => Some(Claim::Descent),
            [Piece::Tile { label, .. }] if label == TileName::GREATER_THAN => {
                Some(Claim::Productive)
            },
            _ => None,
        };
        self.scratch = scratch;
        read?;
        let named = self.tree.node(head.node).is_some_and(|node| {
            matches!(
                shape_of(self.pbg, node),
                Ok(Shape::Form {
                    former: Former::Name,
                    ..
                })
            )
        });
        let Some(claim) = claim
        else {
            // A resident that is no claim is the mistake under a name a claim
            // could stand on; under any other head the instantiation is (#3811).
            let marked = if named {
                Site {
                    at: resident,
                    ..site
                }
            }
            else {
                site
            };
            return Err(marked.out(FragmentBoundary::Reserved(Unbuilt::RecursiveClaim)));
        };
        if !named {
            return Err(site.out(FragmentBoundary::Unadmitted(Unbuilt::RecursiveClaim)));
        }
        let name = self.name_at(head);
        let descent = self.descents.get(&site.at.node).copied();
        let joint = match self.collected.owner_of(site.at.node) {
            Maybe::Present(owner) => self.joint(owner),
            Maybe::Absent(_) => Joint::alone(),
        };
        let resolved = self.scope.resolve(frame, name, &mut self.fuel)?;
        // A sibling of the joint answers by the function's own fixpoint
        // binder: the joint fixpoint is the function's own, read at the
        // sibling's summand. The head's name, without its marker, keeps what
        // it calls: the function's own binder, or the sibling's declaration.
        let (bound, summand) = match resolved {
            Maybe::Present(bound) if self.recursions.contains_key(&bound.binder) => {
                self.resolved(head.span, Resolved::Binder(bound));
                (bound, joint.summand())
            },
            Maybe::Present(_) => return Err(site.out(FragmentBoundary::ForeignClaim)),
            Maybe::Absent(_) => {
                let (Maybe::Present((owner, _)), Maybe::Present(called)) =
                    (joint.own, joint.member(&self.collected, name))
                else {
                    return Err(self.foreign_claim(site, frame, head, name)?);
                };
                if let Some(constant) = joint
                    .members
                    .get(usize::from(called))
                    .and_then(|&member| self.collected.slots.get(usize::from(member)))
                    .map(|slot| slot.constant)
                {
                    let declared = Maybe::Absent(binder_type::Absent::Untyped);
                    self.resolved(head.span, Resolved::Declaration { constant, declared });
                }
                let Some(own) = self
                    .collected
                    .slots
                    .get(usize::from(owner))
                    .map(|slot| slot.name)
                else {
                    return Err(site.out(FragmentBoundary::Unadmitted(Unbuilt::RecursiveClaim)));
                };
                let Maybe::Present(bound) = self.scope.resolve(frame, own, &mut self.fuel)?
                else {
                    return Err(site.out(FragmentBoundary::Unadmitted(Unbuilt::RecursiveClaim)));
                };
                (bound, Maybe::Present(called))
            },
        };
        let Some(&recursion) = self.recursions.get(&bound.binder)
        else {
            return Err(site.out(FragmentBoundary::Unadmitted(Unbuilt::RecursiveClaim)));
        };
        if claim == Claim::Productive {
            // A productive self-call is the whole arm of a copattern block,
            // so each observation yields before the function runs again. It
            // claims nothing of termination: the fixpoint stays partial and
            // unfolds only under an observation of its result.
            let Some(descent) = descent
            else {
                return Err(site.out(FragmentBoundary::Unadmitted(Unbuilt::RecursiveClaim)));
            };
            if !self.cocased.contains(&descent.call.at.node) {
                return Err(LoweringRefusal::UnguardedCorecursion {
                    span: site.at.span,
                    name,
                });
            }
            if let Maybe::Present(_) = summand {
                return Err(site.out(FragmentBoundary::Unadmitted(Unbuilt::RecursiveClaim)));
            }
            self.uniform_descent(frame, recursion, descent.call, descent.arguments)?;
            let head = self.resolved_term(site, frame, Resolved::Binder(bound))?;
            self.plan(site, head);
            return Ok(());
        }
        // The position first: a claim under a match on another parameter
        // reads its arguments against the wrong split.
        self.claim(site, bound.binder)?;
        match (descent, summand) {
            (Some(descent), Maybe::Present(summand)) => {
                // The joint fixpoint takes the injection of the descended value
                // first, then the parameters after it: no member passes a
                // leading parameter, so each stages its first.
                if !stretch(&self.parameters, recursion.uniform).is_empty() {
                    return Err(descent.call.out(FragmentBoundary::NonUniform));
                }
                if recursion.staged != ParameterAt(0) {
                    return Err(descent
                        .call
                        .out(FragmentBoundary::Unadmitted(Unbuilt::RecursiveClaim)));
                }
                let _previous = self.injected.insert(site.at.node, summand);
                self.uniform_descent(frame, recursion, descent.call, descent.arguments)?;
            },
            (Some(descent), Maybe::Absent(_)) => {
                self.uniform_descent(frame, recursion, descent.call, descent.arguments)?;
            },
            // Unapplied, a joint member's claim would be the joint's thunk, at
            // the sum of the block's domains rather than the member's own.
            (None, Maybe::Present(_)) => {
                return Err(site.out(FragmentBoundary::Unadmitted(Unbuilt::RecursiveClaim)));
            },
            (None, Maybe::Absent(_)) => {},
        }
        if let Some(held) = self.recursions.get_mut(&bound.binder) {
            held.claimed = Claimed(true);
        }
        let head = self.resolved_term(site, frame, Resolved::Binder(bound))?;
        self.plan(site, head);

        Ok(())
    }

    /// The refusal of a descent claim whose head, `name` at `head`, is no
    /// recursive function the claim is read in.
    ///
    /// # Specification
    /// - requires: `site` is an instantiation read in `frame`, headed by `name`
    ///   at `head`, which no joint block member answers.
    /// - ensures: the foreign-claim refusal at `site` when `name` resolves to a
    ///   binder, a declaration or a builtin primitive; the unresolved-name
    ///   refusal at `head` when it resolves to nothing.
    /// - provides: the refusal [`Self::instantiation`] raises for a claim on
    ///   another function.
    /// - fails: the refusals name resolution raises before an answer: an
    ///   unmarked self reference, a forward member reference, the allowance.
    /// - panics: none.
    ///
    /// # Errors
    /// The refusals of [`Self::resolve_name`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a claim on an earlier declaration and on a name
    ///   nothing declares, each asserted as its exact refusal.
    /// - witness: `lower::native::tests::a_descent_claim_names_its_own_function_873`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |refusal| {
        matches!(*refusal, LoweringRefusal::OutOfFragment { boundary: FragmentBoundary::ForeignClaim, .. })
            || matches!(*refusal, LoweringRefusal::UnresolvedName { span, name: refused } if span == head.span && refused == name)
    }))]
    fn foreign_claim(
        &mut self,
        site: Site,
        frame: Frame,
        head: Placed,
        name: SurfaceName<'source>,
    ) -> Result<LoweringRefusal<'source>, LoweringRefusal<'source>>
    {
        let named = Site { at: head, ..site };
        if let Maybe::Present(_) = self.resolve_name(named, frame, name)? {
            return Ok(site.out(FragmentBoundary::ForeignClaim));
        }
        let path = NamePath::from(Vec::from([Segment::from(name.as_ref())]));
        if let PathResolution::Complete(Recognized::BuiltinPrimitive { .. }) =
            self.recognition.resolve_path(&path)
        {
            return Ok(site.out(FragmentBoundary::ForeignClaim));
        }
        Ok(LoweringRefusal::UnresolvedName {
            span: head.span,
            name,
        })
    }

    /// The joint fixpoint the declaration at `owner` is read in.
    ///
    /// # Specification
    /// - requires: the module is collected.
    /// - ensures: the `def rec` declarations of the mutual block holding
    ///   `owner`, in block order, with `owner`'s summand, when the block
    ///   declares at least two and `owner` is one; otherwise no joint.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Joint`].
    /// - witness: `lower::native::tests::a_mutual_blocks_recursive_functions_share_one_fixpoint`
    #[spec(ensures: |ret| match ret.own {
        Maybe::Present((own, summand)) => own == owner && ret.members.len() >= 2 && ret.members.get(usize::from(summand)) == Some(&owner),
        Maybe::Absent(_) => ret.members.is_empty(),
    })]
    pub(super) fn joint(
        &self,
        owner: SlotIndex,
    ) -> Joint
    {
        let Some(block) = self
            .collected
            .blocks
            .iter()
            .find(|block| (block.first .. block.end).contains(&owner))
        else {
            return Joint::alone();
        };
        let members: Vec<SlotIndex> = self
            .collected
            .recursive
            .range(block.first .. block.end)
            .copied()
            .collect();
        match members.iter().position(|&member| member == owner) {
            Some(at) if members.len() >= 2 => Joint {
                members,
                own: Maybe::Present((owner, Summand::from(at))),
            },
            Some(_) | None => Joint::alone(),
        }
    }

    /// Check the arguments `arguments` a descent call `call` on `recursion`
    /// passes, read under `frame`.
    ///
    /// # Specification
    /// - requires: `arguments` is a stretch of the operand store.
    /// - ensures: one argument per parameter of the recursive function, each
    ///   before the staged one the parameter itself, which the call erases and
    ///   which is labelled with its parameter's written type.
    /// - provides: the check a descent call's claim makes, in a body and in the
    ///   type a decoder's arm returns.
    /// - fails: the arity refusal, at the call, for a call passing other than
    ///   one argument per parameter; the non-uniform refusal, at the argument,
    ///   for a parameter before the staged one passed as anything but itself;
    ///   the allowance refusal from the binder walk.
    /// - panics: none.
    ///
    /// # Errors
    /// The call's refusal.
    ///
    /// # Termination
    /// The loop runs once per leading parameter, a finite stretch.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::instantiation`], whose descent calls
    ///   observe each refusal.
    /// - witness: `lower::native::tests::a_recursive_call_passes_its_leading_parameters_unchanged`
    /// - witness: `lower::native::tests::a_productive_call_is_the_whole_arm_of_a_copattern_block`
    #[spec(ensures: |ret| ret.is_err() || stretch(&self.operands, arguments).len() == stretch(&self.parameters, recursion.parameters).len())]
    fn uniform_descent(
        &mut self,
        frame: Frame,
        recursion: Recursion,
        call: Site,
        arguments: Stretch,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let uniform = stretch(&self.parameters, recursion.uniform);
        let first = arguments.start;
        let arguments = stretch(&self.operands, arguments);
        if arguments.len() != stretch(&self.parameters, recursion.parameters).len() {
            return Err(call.out(FragmentBoundary::Arity(OperandCount::from(arguments.len()))));
        }
        let mut passed_names = Vec::with_capacity(uniform.len());
        for (at, (parameter, &argument)) in uniform.iter().zip(arguments).enumerate() {
            // An implicit the call omits is the function's own.
            if self.kept_implicits.contains(&first.saturating_add(at)) {
                continue;
            }
            let Some(node) = self.tree.node(argument)
            else {
                return Err(call.out(FragmentBoundary::NonUniform));
            };
            let passed = Placed::of(argument, node);
            let unchanged = match shape_of(self.pbg, node)? {
                Shape::Form {
                    former: Former::Name,
                    ..
                } => {
                    let written = self.name_at(passed);
                    match self.scope.resolve(frame, written, &mut self.fuel)? {
                        Maybe::Present(found) if found.binder == parameter.frame => Some(found),
                        Maybe::Present(_) | Maybe::Absent(_) => None,
                    }
                },
                Shape::Root | Shape::Form { .. } | Shape::Repair(_) | Shape::Layout => None,
            };
            let Some(found) = unchanged
            else {
                let varied = Site { at: passed, ..call };
                return Err(varied.out(FragmentBoundary::NonUniform));
            };
            // The call erases the argument, so no origin records its name: keep
            // the use beside the others the lowering resolved.
            passed_names.push((passed.span, found));
            // The argument is the parameter itself, which the fixpoint binds
            // outside the call: it answers at the parameter's written type.
            if let Maybe::Present(declared) = parameter.declared
                && let Reading::ValueType(read) = self.reading(declared)
            {
                self.labels.push(LabelSite {
                    written: passed.span,
                    held: declared,
                    read: LabelRead::ValueType(read),
                });
            }
        }
        for (span, found) in passed_names {
            self.resolved(span, Resolved::Binder(found));
        }

        Ok(())
    }

    /// Whether the parameter type written at `ty`, read under `frame` before
    /// the parameters bind, is a decode: a declaration's application, or the
    /// declaration bare, whose definition is a body rather than a family. A
    /// decode carries no stage: one code decodes values of every size,
    /// so a recursion stages the code, never the value it decodes.
    ///
    /// # Specification
    /// - requires: `site` is the function's declaration form.
    /// - ensures: `Decoded(true)` exactly when `ty` is a type application or a
    ///   bare type name whose head resolves ([`Self::resolve_name`]) to a
    ///   declaration defined as `= e` or as a function tail; `Decoded(false)`
    ///   for a family, a binder, an unresolved head and every other form.
    /// - fails: as [`Self::resolve_name`].
    /// - panics: none.
    /// - executable: none — the answer is a resolution, which a clause repeats
    ///   only by spending the lowering's fuel again.
    ///
    /// # Errors
    /// The resolution's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::staged_by_body`].
    /// - witness: `lower::native::tests::a_claim_under_a_match_on_a_decode_stages_the_code_3680`
    pub(super) fn decodes(
        &mut self,
        site: Site,
        frame: Frame,
        ty: NodeIndex,
    ) -> Result<Decoded, LoweringRefusal<'source>>
    {
        let Some(node) = self.tree.node(ty)
        else {
            return Ok(Decoded(false));
        };
        if !matches!(shape_of(self.pbg, node)?, Shape::Form {
            former: Former::TypeApplication | Former::TypeHead,
            ..
        }) {
            return Ok(Decoded(false));
        }
        let mut scratch = core::mem::take(&mut self.scratch);
        let read = read_pieces(self.pbg, self.tree, ty, &mut scratch);
        let head = scratch.pieces.iter().find_map(|piece| match *piece {
            Piece::Tile { label, at }
                if label == TileName::TYPE_IDENTIFIER || label == TileName::TYPE_VARIABLE =>
            {
                Some(at)
            },
            Piece::Tile { .. } | Piece::Operand(_) => None,
        });
        self.scratch = scratch;
        read?;
        let Some(head) = head
        else {
            return Ok(Decoded(false));
        };
        let name = self.name_at(head);
        // The head is resolved as the type's own node, which the function
        // declaring the parameter owns.
        let placed = Placed::of(ty, node);
        let resolved = self.resolve_name(Site { at: placed, ..site }, frame, name)?;
        let Maybe::Present(super::Resolved::Declaration { constant, .. }) = resolved
        else {
            return Ok(Decoded(false));
        };
        Ok(Decoded(
            self.collected
                .slots
                .get(usize::from(constant))
                .is_some_and(|slot| {
                    matches!(
                        slot.definition,
                        Maybe::Present(Half {
                            operand: Operand::Written(_) | Operand::Function,
                            ..
                        })
                    )
                }),
        ))
    }

    /// The position a recursive function named `own` stages, read off its
    /// body before the body is classified: the parameter the innermost match
    /// above the body's first claim scrutinises, written bare; the first
    /// parameter when that claim is productive; and the last parameter where
    /// no match on a parameter stands above it or the body claims nothing. In
    /// a joint, a claim through a sibling member is a claim of the function's
    /// own, since it runs the one fixpoint.
    ///
    /// **Choice.** The position is read off the body, where the match that
    /// takes the staged parameter apart already says it. **Alternatives.** A
    /// position written on the claim, a second spelling of what the match
    /// says; a search for the decreasing argument, which duplicates the
    /// checkers' judgment. **Reversal.** Descent on several parameters at
    /// once — lexicographic or measured — is the sized rung's, and replaces
    /// the one position by a measure.
    ///
    /// # Specification
    /// - requires: `parameters` are the function's parameter names in order,
    ///   `decoded` marks each whose type is a decode ([`Self::decodes`]),
    ///   `roots` the syntax the function writes after its parameter list, in
    ///   source order, and `joint` the joint the function is read in.
    /// - ensures: `staged` is the position, in `0 .. parameters.len()`, of the
    ///   parameter the innermost match above the first claim in source order —
    ///   an instantiation of `own` or of a member of `joint`, or a descent
    ///   `own[<](…)` written where a type is read — scrutinises, a scrutinee
    ///   written as a bare name equal to that parameter's, passing over each
    ///   match whose parameter that call writes back bare in its own place — it
    ///   consumes that one alongside the one it descends on — and each match
    ///   inside another whose parameter `decoded` marks — a decode carries no
    ///   stage, so the claim descends on the code outside it — unless every
    ///   such match is passed over; the first position when that instantiation
    ///   claims productivity (`>`), so every call may vary every parameter; the
    ///   last position otherwise. `kept` is the longest run of parameters
    ///   before `staged`, from the first, that every call of `own` under
    ///   `roots` writes back bare in its own place ([`Self::kept_before`]). The
    ///   classification sweep checks every claim against `staged`
    ///   ([`Self::claim`]) and every kept argument against its parameter
    ///   ([`Self::uniform_descent`]), so a name a binder between the match and
    ///   the parameter shadows is refused there.
    /// - provides: where the function binds its own name: after the kept
    ///   parameters, the ones from `kept` to `staged` its fixpoint's leading
    ///   binders.
    /// - fails: a fault reading a form's pieces or shape.
    /// - panics: none.
    ///
    /// # Errors
    /// The form fault.
    ///
    /// # Termination
    /// - reason: the `while let` loop over a stack of syntax nodes, each pushed
    ///   once by its parent in the finite tree, not recursion.
    /// - measure: the nodes under `roots` not yet popped.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — claims under a match on the first parameter, under
    ///   nested matches on one parameter's fields and under no match on a
    ///   parameter each stage their own position; an accumulator before the
    ///   staged parameter that the calls change is not kept; a productive call
    ///   stages the first parameter; a joint member whose one claim is through
    ///   a sibling stages the parameter that claim's match takes apart; a claim
    ///   under a match on a parameter typed by a decode, inside a match on the
    ///   code, stages the code.
    /// - witness: `lower::native::tests::a_definition_descends_on_the_parameter_its_cases_scrutinise`
    /// - witness: `lower::native::tests::a_definition_without_a_case_on_a_parameter_stages_its_last`
    /// - witness: `lower::native::tests::a_varying_parameter_before_the_staged_one_is_a_leading_binder_626`
    /// - witness: `lower::native::tests::a_productive_call_is_the_whole_arm_of_a_copattern_block`
    /// - witness: `lower::native::tests::a_claim_under_a_match_on_another_parameter_descends_on_the_staged_one_2135`
    /// - witness: `lower::native::tests::a_descent_inside_a_record_type_stages_its_match_s_parameter_3087`
    /// - witness: `lower::native::tests::a_mutual_block_member_takes_a_parameter_after_its_staged_one_3722`
    /// - witness: `lower::native::tests::a_claim_under_a_match_on_a_decode_stages_the_code_3680`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |staging| staging.kept <= staging.staged && staging.staged.0 < parameters.len().max(1)))]
    pub(super) fn staged_by_body(
        &mut self,
        own: SurfaceName<'source>,
        joint: &Joint,
        parameters: &[SurfaceName<'source>],
        decoded: &[Decoded],
        roots: &[NodeIndex],
    ) -> Result<Staging, LoweringRefusal<'source>>
    {
        let mut scratch = core::mem::take(&mut self.scratch);
        let found = self.first_claim(own, joint, (parameters, decoded), roots, &mut scratch);
        let staged = match found {
            Ok(found) => found.unwrap_or_else(|| ParameterAt(parameters.len().saturating_sub(1))),
            Err(refusal) => {
                self.scratch = scratch;
                return Err(refusal);
            },
        };
        let kept = self.kept_before(own, parameters, roots, staged, &mut scratch);
        self.scratch = scratch;
        Ok(Staging {
            kept: kept?,
            staged,
        })
    }

    /// The name `operand` writes, when it is a bare name form; `None` for an
    /// operand the tree lacks or another form.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// The form fault.
    fn bare_name(
        &self,
        operand: Placed,
    ) -> Result<Option<SurfaceName<'source>>, LoweringRefusal<'source>>
    {
        let Some(node) = self.tree.node(operand.node)
        else {
            return Ok(None);
        };
        Ok(matches!(shape_of(self.pbg, node)?, Shape::Form {
            former: Former::Name,
            ..
        })
        .then(|| self.name_at(operand)))
    }

    /// How many parameters, from the first and before `staged`, every call of
    /// `own` under `roots` writes back bare in its own place.
    ///
    /// # Specification
    /// - requires: as [`Self::staged_by_body`]; `scratch` is free for reading
    ///   pieces.
    /// - ensures: the largest `k <= staged` such that every call form headed by
    ///   an instantiation of `own`, and every descent of `own` written where a
    ///   type is read, writes, at each position below `k`, a bare name equal to
    ///   the parameter at that position; `staged` when no call stands under
    ///   `roots`.
    /// - fails: as [`Self::staged_by_body`].
    /// - panics: none.
    ///
    /// # Errors
    /// The form fault.
    ///
    /// # Termination
    /// - reason: as [`Self::staged_by_body`].
    /// - measure: the nodes under `roots` not yet popped.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::staged_by_body`].
    /// - witness: `lower::native::tests::a_varying_parameter_before_the_staged_one_is_a_leading_binder_626`
    /// - witness: `lower::native::tests::a_recursive_call_passes_its_leading_parameters_unchanged`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |kept| *kept <= staged))]
    fn kept_before(
        &self,
        own: SurfaceName<'source>,
        parameters: &[SurfaceName<'source>],
        roots: &[NodeIndex],
        staged: ParameterAt,
        scratch: &mut Pieces,
    ) -> Result<ParameterAt, LoweringRefusal<'source>>
    {
        let mut kept = staged.0;
        // How many of `arguments`, from the first and at most `kept`, name
        // their own parameter bare.
        let passed =
            |arguments: &[Placed], kept: usize| -> Result<usize, LoweringRefusal<'source>> {
                let mut passed = 0_usize;
                for (&argument, &parameter) in arguments.iter().zip(parameters).take(kept) {
                    if self.bare_name(argument)? != Some(parameter) {
                        break;
                    }
                    passed = passed.saturating_add(1);
                }
                Ok(passed)
            };
        let mut pending: Vec<NodeIndex> = roots.iter().rev().copied().collect();
        let mut operands: Vec<Placed> = Vec::new();
        while let Some(at) = pending.pop() {
            if kept == 0 {
                break;
            }
            let Some(node) = self.tree.node(at)
            else {
                continue;
            };
            let former = match shape_of(self.pbg, node)? {
                Shape::Form { former, .. } => Some(former),
                Shape::Root | Shape::Repair(_) | Shape::Layout => None,
            };
            read_pieces(self.pbg, self.tree, at, scratch)?;
            operands.clear();
            operands.extend(scratch.pieces.iter().filter_map(|piece| match *piece {
                Piece::Operand(operand) => Some(operand),
                Piece::Tile { .. } => None,
            }));
            if former == Some(Former::TypeApplication)
                && self.descends_in_type(own, &scratch.pieces).0
            {
                kept = kept.min(passed(&operands, kept)?);
            }
            if former == Some(Former::Call)
                && let Some((&head, arguments)) = operands.split_first()
                && self.tree.node(head.node).is_some_and(|node| {
                    matches!(
                        shape_of(self.pbg, node),
                        Ok(Shape::Form {
                            former: Former::Instantiation,
                            ..
                        })
                    )
                })
            {
                read_pieces(self.pbg, self.tree, head.node, scratch)?;
                let instantiated = scratch.pieces.iter().find_map(|piece| match *piece {
                    Piece::Operand(operand) => Some(operand),
                    Piece::Tile { .. } => None,
                });
                if let Some(instantiated) = instantiated
                    && self.bare_name(instantiated)? == Some(own)
                {
                    kept = kept.min(passed(arguments, kept)?);
                }
            }
            pending.extend(operands.iter().rev().map(|operand| operand.node));
        }

        Ok(ParameterAt(kept))
    }

    /// The position the match above the first claim of `own`, or of a member
    /// of `joint`, under `roots` scrutinises, by [`Self::staged_by_body`]'s
    /// rule.
    ///
    /// # Specification
    /// - requires: as [`Self::staged_by_body`]; `scratch` is free for reading
    ///   pieces.
    /// - ensures: `Some` of the scrutinised parameter's position — the
    ///   innermost match's whose parameter the call does not write back bare
    ///   and `decoded` does not mark with a match outside it, the innermost's
    ///   when it passes over every one — of the first position when the
    ///   instantiation's claim is `>`, or of the last position where no match
    ///   on a parameter stands above the first claim; `None` when no
    ///   instantiation of `own` or of a member of `joint`, and no descent of
    ///   `own` written where a type is read, stands under `roots`.
    /// - fails: as [`Self::staged_by_body`].
    /// - panics: none.
    ///
    /// # Errors
    /// The form fault.
    ///
    /// # Termination
    /// - reason: as [`Self::staged_by_body`].
    /// - measure: the nodes under `roots` not yet popped.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::staged_by_body`].
    /// - witness: `lower::native::tests::a_definition_descends_on_the_parameter_its_cases_scrutinise`
    /// - witness: `lower::native::tests::a_claim_under_a_match_on_another_parameter_descends_on_the_staged_one_2135`
    /// - witness: `lower::native::tests::a_descent_inside_a_record_type_stages_its_match_s_parameter_3087`
    /// - witness: `lower::native::tests::a_mutual_block_member_takes_a_parameter_after_its_staged_one_3722`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |found| found.is_none_or(|position| position.0 < parameters.len().max(1))))]
    fn first_claim(
        &self,
        own: SurfaceName<'source>,
        joint: &Joint,
        (parameters, decoded): (&[SurfaceName<'source>], &[Decoded]),
        roots: &[NodeIndex],
        scratch: &mut Pieces,
    ) -> Result<Option<ParameterAt>, LoweringRefusal<'source>>
    {
        let last = ParameterAt(parameters.len().saturating_sub(1));
        // A parameter's position, when `operand` names it bare.
        let named = |operand: Placed| -> Result<Option<ParameterAt>, LoweringRefusal<'source>> {
            Ok(self.bare_name(operand)?.and_then(|written| {
                parameters
                    .iter()
                    .position(|&parameter| parameter == written)
                    .map(ParameterAt)
            }))
        };
        // Whether `operand` names, bare, `own` or a member of the joint, each
        // a head the one fixpoint answers.
        let named_claimed = |operand: Placed| -> Result<bool, LoweringRefusal<'source>> {
            Ok(self.bare_name(operand)?.is_some_and(|written| {
                written == own
                    || matches!(joint.member(&self.collected, written), Maybe::Present(_))
            }))
        };
        // The match a claim with `arguments` descends on, from the innermost
        // `link` outward: past each match whose parameter the claim writes
        // back bare in its own place, and each whose parameter is typed by a
        // decode with a match outside it, none when it passes over every one.
        let descended = |mut link: Option<usize>,
                         arguments: &[Placed],
                         links: &[(ParameterAt, Option<usize>)]|
         -> Result<Option<usize>, LoweringRefusal<'source>> {
            while let Some(&(position, outer)) = link.and_then(|at| links.get(at)) {
                let unchanged = match arguments.get(position.0) {
                    Some(&argument) => named(argument)? == Some(position),
                    None => false,
                };
                let decode = outer.is_some() && decoded.get(position.0).is_some_and(|mark| mark.0);
                if !unchanged && !decode {
                    break;
                }
                link = outer;
            }
            Ok(link)
        };
        // The matches on parameters above a node, innermost first: each link
        // a position and the link of the match enclosing it.
        let mut links: Vec<(ParameterAt, Option<usize>)> = Vec::new();
        let mut written: Vec<Placed> = Vec::new();
        let mut pending: Vec<(NodeIndex, Option<usize>)> =
            roots.iter().rev().map(|&root| (root, None)).collect();
        while let Some((at, scrutinised)) = pending.pop() {
            let Some(node) = self.tree.node(at)
            else {
                continue;
            };
            let former = match shape_of(self.pbg, node)? {
                Shape::Form { former, .. } => Some(former),
                Shape::Root | Shape::Repair(_) | Shape::Layout => None,
            };
            read_pieces(self.pbg, self.tree, at, scratch)?;
            let pieces = &scratch.pieces;
            let operands = pieces.iter().filter_map(|piece| match *piece {
                Piece::Operand(operand) => Some(operand),
                Piece::Tile { .. } => None,
            });
            // A descent written where a type is read, `own[<](…)`, is a claim
            // whose arguments are the application's own operands.
            if former == Some(Former::TypeApplication) && self.descends_in_type(own, pieces).0 {
                written.clear();
                written.extend(operands);
                let link = descended(scrutinised, &written, &links)?.or(scrutinised);
                let innermost = link
                    .and_then(|at| links.get(at))
                    .map(|&(position, _)| position);
                return Ok(Some(innermost.unwrap_or(last)));
            }
            if former == Some(Former::Instantiation)
                && let Some(head) = operands.clone().next()
                && named_claimed(head)?
            {
                // A productive claim varies every parameter: each call is a
                // fresh observation's answer, so nothing stays fixed.
                if let Some(resident) = operands.clone().nth(1) {
                    read_pieces(self.pbg, self.tree, resident.node, scratch)?;
                    if matches!(scratch.pieces.as_slice(), &[Piece::Tile { label, .. }] if label == TileName::GREATER_THAN)
                    {
                        return Ok(Some(ParameterAt(0)));
                    }
                }
                let innermost = scrutinised
                    .and_then(|link| links.get(link))
                    .map(|&(position, _)| position);
                return Ok(Some(innermost.unwrap_or(last)));
            }
            // A call of `own`, or of a joint member, descends on the innermost
            // matched parameter it does not pass back unchanged: a match on a
            // parameter the call writes back bare, inside one on the parameter
            // it takes apart, consumes the one alongside the other.
            let mut chosen = scrutinised;
            if former == Some(Former::Call) && scrutinised.is_some() {
                written.clear();
                written.extend(operands);
                if let Some((&head, arguments)) = written.split_first()
                    && self.tree.node(head.node).is_some_and(|node| {
                        matches!(
                            shape_of(self.pbg, node),
                            Ok(Shape::Form {
                                former: Former::Instantiation,
                                ..
                            })
                        )
                    })
                {
                    read_pieces(self.pbg, self.tree, head.node, scratch)?;
                    let instantiated = scratch.pieces.iter().find_map(|piece| match *piece {
                        Piece::Operand(operand) => Some(operand),
                        Piece::Tile { .. } => None,
                    });
                    if let Some(instantiated) = instantiated
                        && named_claimed(instantiated)?
                    {
                        chosen = descended(scrutinised, arguments, &links)?.or(scrutinised);
                    }
                    read_pieces(self.pbg, self.tree, at, scratch)?;
                }
            }
            let pieces = &scratch.pieces;
            let operands = pieces.iter().filter_map(|piece| match *piece {
                Piece::Operand(operand) => Some(operand),
                Piece::Tile { .. } => None,
            });
            // A match on a parameter hands its position to its arm bodies,
            // the operands its `=>` tiles introduce; every other child keeps
            // the enclosing one.
            let arms = match (former, operands.clone().next()) {
                (Some(Former::Case), Some(scrutinee)) => named(scrutinee)?.map(|position| {
                    links.push((position, scrutinised));
                    links.len().saturating_sub(1)
                }),
                _ => None,
            };
            let mut children = Vec::new();
            let mut after_arrow = false;
            for piece in pieces {
                match *piece {
                    Piece::Tile { label, .. } => after_arrow = label == TileName::FAT_ARROW,
                    Piece::Operand(operand) => {
                        let inherited = match arms {
                            Some(link) if after_arrow => Some(link),
                            Some(_) | None => chosen,
                        };
                        children.push((operand.node, inherited));
                        after_arrow = false;
                    },
                }
            }
            pending.extend(children.into_iter().rev());
        }

        Ok(None)
    }

    /// Whether `pieces`, a type application's, write a descent of `own` where a
    /// type is read, `own[<](…)`, as [`Self::staged_unquote`] reads one.
    ///
    /// # Specification
    /// - ensures: `true` exactly when the pieces open with a type identifier or
    ///   a type variable spelling `own`, followed by `[`.
    /// - panics: none.
    /// - executable: none — the spelling is read off the tree the pieces
    ///   locate, which the answer does not carry.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a descent inside a quoted record type's field stages
    ///   the parameter its match takes apart, as a bare one does.
    /// - witness: `lower::native::tests::a_descent_inside_a_record_type_stages_its_match_s_parameter_3087`
    fn descends_in_type(
        &self,
        own: SurfaceName<'source>,
        pieces: &[Piece],
    ) -> TypeDescent
    {
        TypeDescent(
            matches!(*pieces, [Piece::Tile { label, at }, Piece::Tile { label: open, .. }, ..]
            if (label == TileName::TYPE_IDENTIFIER || label == TileName::TYPE_VARIABLE)
                && open == TileName::BRACKET_OPEN
                && self.name_at(at) == own),
        )
    }

    /// How many parameters a recursive call headed by the instantiation
    /// `head`, read under `frame`, passes unchanged: those before the staged
    /// one of the recursive function its head names.
    ///
    /// # Specification
    /// - requires: `head` is an instantiation form.
    /// - ensures: the count of the named recursive function's parameters before
    ///   its staged one when the head's name resolves to the frame binding a
    ///   recursive function's own name; zero otherwise, where the claim
    ///   ([`Self::instantiation`]) refuses or the call is a joint sibling's,
    ///   whose members take no leading parameter.
    /// - provides: the arguments a descent call leaves out of its application.
    /// - fails: a fault reading the head's pieces or shape; the allowance
    ///   refusal from the binder walk.
    /// - panics: none.
    ///
    /// # Errors
    /// The form's or the binder walk's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a call over a uniform leading parameter applies its
    ///   later arguments alone.
    /// - witness: `lower::native::tests::a_recursive_function_closes_a_fixpoint_over_its_staged_parameter`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |leading| leading.0 <= self.parameters.len()))]
    pub(super) fn leading_parameters(
        &mut self,
        frame: Frame,
        head: Placed,
    ) -> Result<ParameterAt, LoweringRefusal<'source>>
    {
        Ok(ParameterAt(
            self.instantiated_recursion(frame, head)?
                .and_then(|binder| self.recursions.get(&binder))
                .map_or(0, |recursion| {
                    stretch(&self.parameters, recursion.uniform).len()
                }),
        ))
    }

    /// Lay out a recursive call headed by the instantiation `head` in its
    /// function's merged telescope's order, passing each entry it omits: an
    /// implicit and an instance, as the call's arguments `written` give the
    /// explicit ones.
    ///
    /// # Specification
    /// - requires: `head` is an instantiation form read under `frame`;
    ///   `written` is the call's arguments, the last the operand store holds.
    /// - ensures: when the head names the recursive function `site` stands in,
    ///   and `written` holds one argument per explicit parameter of its merged
    ///   telescope, the operands from `written.start` are one per parameter in
    ///   the telescope's order: each explicit one the next written argument; an
    ///   implicit before the fixpoint the function's own, kept in
    ///   [`Lowerer::kept_implicits`] and left out of the application; one past
    ///   it a hole the call nominates ([`Self::nominate`]), a model implicit
    ///   one per component ([`Self::pass_model`]); an instance the one of its
    ///   interface in scope ([`Self::resolved_instance`]). Otherwise nothing
    ///   changes, and the claim's arity check reads the call
    ///   ([`Self::uniform_descent`]).
    /// - fails: [`Self::resolved_instance`]'s, [`Self::nominate`]'s and
    ///   [`Self::pass_model`]'s refusals; the head's, as
    ///   [`Self::instantiated_recursion`].
    /// - panics: none.
    ///
    /// # Errors
    /// As `- fails:`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a descent under a row that labels a theory's instance
    ///   passes the function's own instance; a descent under an implicit
    ///   telescope passes the function's own implicit before its staged
    ///   parameter.
    /// - witness: `lower::native::tests::a_recursion_under_an_instance_row_binds_its_own_name_3699`
    /// - witness: `lower::native::tests::a_recursion_under_an_implicit_telescope_descends_on_its_matched_parameter_3828`
    #[spec(
        captures: before = self.operands.len(),
        ensures: |ret| ret.is_err() || self.operands.len() >= before,
    )]
    pub(super) fn omitted_entries(
        &mut self,
        site: Site,
        frame: Frame,
        head: Placed,
        written: Stretch,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let Some(binder) = self.instantiated_recursion(frame, head)?
        else {
            return Ok(());
        };
        let Some(recursion) = self.recursions.get(&binder).copied()
        else {
            return Ok(());
        };
        let Maybe::Present(owner) = self.collected.owner_of(site.at.node)
        else {
            return Ok(());
        };
        let Some(function) = self
            .collected
            .slots
            .get(usize::from(owner))
            .filter(|slot| slot.named.node == recursion.named)
            .map(|slot| slot.name)
        else {
            return Ok(());
        };
        let Some(Ok(entries)) = self.collected.plicities.get(&owner).cloned()
        else {
            return Ok(());
        };
        let explicit = entries
            .iter()
            .filter(|entry| entry.plicity == crate::module::Plicity::Explicit)
            .count();
        if written.end.saturating_sub(written.start) != explicit || explicit == entries.len() {
            return Ok(());
        }
        // The parameters before the fixpoint, which the call leaves out of
        // its application.
        let kept = stretch(&self.parameters, recursion.uniform).len();
        let arguments = self.operands.split_off(written.start);
        let mut arguments = arguments.into_iter();
        let mut place = 0_usize;
        for entry in entries {
            if let Some((_, slot)) = self.implicit_slot(site, entry)? {
                let width = slot.components().len();
                if place < kept {
                    for _component in 0 .. width {
                        let _fresh = self.kept_implicits.insert(self.operands.len());
                        self.operands.push(site.at.node);
                    }
                }
                else {
                    self.pass_model(site, frame, (function, entry.name), &slot, None)?;
                }
                place = place.saturating_add(width);
                continue;
            }
            match entry.plicity {
                crate::module::Plicity::Explicit => {
                    if let Some(argument) = arguments.next() {
                        self.operands.push(argument);
                    }
                },
                crate::module::Plicity::Implicit if place < kept => {
                    let _fresh = self.kept_implicits.insert(self.operands.len());
                    self.operands.push(site.at.node);
                },
                crate::module::Plicity::Implicit => {
                    let hole = self.nominate(super::implicit::Nomination::Omitted {
                        function,
                        implicit: entry.name,
                    })?;
                    let _first = self.nominated.insert(self.operands.len(), hole);
                    self.operands.push(site.at.node);
                },
                crate::module::Plicity::Instance => {
                    let index = self.resolved_instance(site, frame, function, entry)?;
                    let _first = self.instanced.insert(self.operands.len(), index);
                    self.operands.push(site.at.node);
                },
            }
            place = place.saturating_add(1);
        }

        Ok(())
    }

    /// The frame binding the recursive function's own name the instantiation
    /// `head`, read under `frame`, names.
    ///
    /// # Specification
    /// - requires: `head` is an instantiation form.
    /// - ensures: the binder the head's bare name resolves to under `frame`
    ///   when it keys a recursion; none for a head naming anything else.
    /// - fails: a fault reading the head's pieces or shape; the allowance
    ///   refusal from the binder walk.
    /// - panics: none.
    ///
    /// # Errors
    /// The form's or the binder walk's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::leading_parameters`] and
    ///   [`Self::parameters_classify`].
    /// - witness: `lower::native::tests::a_recursive_function_closes_a_fixpoint_over_its_staged_parameter`
    /// - witness: `lower::native::tests::a_descent_call_s_constructor_argument_takes_its_parameter_s_type_2127`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |binder| binder.is_none_or(|binder| self.recursions.contains_key(&binder))))]
    fn instantiated_recursion(
        &mut self,
        frame: Frame,
        head: Placed,
    ) -> Result<Option<ScopeId>, LoweringRefusal<'source>>
    {
        let mut scratch = core::mem::take(&mut self.scratch);
        let read = read_pieces(self.pbg, self.tree, head.node, &mut scratch);
        let named = scratch.pieces.iter().find_map(|piece| match *piece {
            Piece::Operand(operand) => Some(operand),
            Piece::Tile { .. } => None,
        });
        self.scratch = scratch;
        read?;
        let Some(named) = named
        else {
            return Ok(None);
        };
        let Some(name) = self.bare_name(named)?
        else {
            return Ok(None);
        };
        Ok(match self.scope.resolve(frame, name, &mut self.fuel)? {
            Maybe::Present(bound) if self.recursions.contains_key(&bound.binder) => {
                Some(bound.binder)
            },
            Maybe::Present(_) | Maybe::Absent(_) => None,
        })
    }

    /// Check the position the claim at `site` descends on against the one the
    /// recursive function whose own name the frame `recursion` binds stages.
    ///
    /// # Specification
    /// - requires: `recursion` binds a recursive function's own name.
    /// - ensures: `Ok` when the parameter recorded for `site` by
    ///   [`Self::scrutinise`] for this function — the staged one when any match
    ///   above `site` takes it apart, the innermost match's otherwise — or its
    ///   last parameter where no match is, is the staged one
    ///   ([`Self::staged_by_body`]).
    /// - provides: the one-position rule every claim of one function keeps.
    /// - fails: [`LoweringRefusal::DescentOnSeveralParameters`] at `site`,
    ///   naming the staged parameter and the claimed one, when they differ.
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoweringRefusal::DescentOnSeveralParameters`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — claims under cases on one parameter are admitted and
    ///   claims under cases on two are refused, naming both.
    /// - witness: `lower::native::tests::claims_under_cases_on_two_parameters_are_refused_by_name`
    /// - witness: `lower::native::tests::a_rebuilt_argument_descends_on_the_same_position`
    /// - witness: `lower::native::tests::a_claim_under_a_match_on_another_parameter_descends_on_the_staged_one_2135`
    #[spec(ensures: |ret| ret.is_ok() || matches!(ret, Err(LoweringRefusal::DescentOnSeveralParameters { .. })))]
    fn claim(
        &self,
        site: Site,
        recursion: ScopeId,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let Some(held) = self.recursions.get(&recursion)
        else {
            return Ok(());
        };
        let parameters = stretch(&self.parameters, held.parameters);
        let staged = held.staged;
        let claimed = match self.scrutinised.get(&site.at.node) {
            Some(scrutiny) if scrutiny.recursion == recursion => scrutiny.position,
            Some(_) | None => ParameterAt(parameters.len().saturating_sub(1)),
        };
        if claimed == staged {
            return Ok(());
        }
        let named = |at: ParameterAt| {
            parameters
                .get(at.0)
                .and_then(|parameter| {
                    self.tree
                        .node(parameter.binder)
                        .map(|node| self.name_at(Placed::of(parameter.binder, node)))
                })
                .unwrap_or_else(|| SurfaceName::from(""))
        };
        Err(LoweringRefusal::DescentOnSeveralParameters {
            span: site.at.span,
            staged: named(staged),
            claimed: named(claimed),
        })
    }

    /// Record that each arm body in `bodies` stands under a match on
    /// `scrutinee`, read under `frame`, when it names a recursive function's
    /// parameter; `enclosing` is the record the match itself stands under.
    ///
    /// # Specification
    /// - requires: `bodies` are the match's arm bodies, not yet visited by the
    ///   classification sweep.
    /// - ensures: when `scrutinee` is a name written bare that resolves to a
    ///   recursive function's parameter, every body records that function and
    ///   that parameter's position, replacing what an enclosing match recorded,
    ///   unless `enclosing` records the parameter that same function stages:
    ///   then every body keeps it, so a call under a match on another parameter
    ///   still descends on the staged one; otherwise nothing changes, so a
    ///   match on anything else leaves the enclosing match's record in force.
    /// - provides: the scrutiny the sweep hands down to every node under an
    ///   arm, which [`Self::claim`] reads.
    /// - fails: the allowance refusal from the binder walk; a fault reading the
    ///   scrutinee's shape.
    /// - panics: none.
    ///
    /// # Errors
    /// The binder walk's or the form's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::claim`].
    /// - witness: `lower::native::tests::claims_under_cases_on_two_parameters_are_refused_by_name`
    /// - witness: `lower::native::tests::a_rebuilt_argument_descends_on_the_same_position`
    /// - witness: `lower::native::tests::a_claim_under_a_match_on_another_parameter_descends_on_the_staged_one_2135`
    #[spec(
        captures: before = self.scrutinised.len(),
        ensures: |ret| ret.is_err() || self.scrutinised.len() >= before,
    )]
    pub(super) fn scrutinise(
        &mut self,
        frame: Frame,
        scrutinee: Placed,
        enclosing: Option<Scrutiny>,
        bodies: impl IntoIterator<Item = NodeIndex>,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        if self.staged_parameters.is_empty() {
            return Ok(());
        }
        let Some(written) = self.bare_name(scrutinee)?
        else {
            return Ok(());
        };
        let Maybe::Present(found) = self.scope.resolve(frame, written, &mut self.fuel)?
        else {
            return Ok(());
        };
        let Some(&scrutiny) = self.staged_parameters.get(&found.binder)
        else {
            return Ok(());
        };
        let staged = enclosing.filter(|outer| {
            outer.recursion == scrutiny.recursion
                && self
                    .recursions
                    .get(&outer.recursion)
                    .is_some_and(|held| held.staged == outer.position)
        });
        let recorded = staged.unwrap_or(scrutiny);
        for body in bodies {
            let _previous = self.scrutinised.insert(body, recorded);
        }

        Ok(())
    }

    /// Classify a decoder's own recursion written in the type one of its arms
    /// returns, `el[<](a)`: the decode of the code the descent call returns.
    ///
    /// # Specification
    /// - requires: `site` is a type application in type position whose head,
    ///   named `name` at `head`, is followed by `[`; `cursor` stands past it.
    /// - ensures: the descent `[<]` on a name the frame of a recursive
    ///   function's fixpoint binds, applied to one argument per parameter with
    ///   each before the staged one passed as itself, stands as the unquote of
    ///   that fixpoint called on the staged argument and every one after it,
    ///   each read as a value, at the universe the position reads, and makes
    ///   the fixpoint claim descent once [`Self::claim`] admits its position;
    ///   the fixpoint's binder is recorded as mentioned.
    /// - provides: the written spelling of an inductive-recursive decode, `(x :
    ///   el[<](a)) -> -F el[<](b(x))`, whose codomain decodes a code the arm
    ///   cannot compute before its binder.
    /// - fails: the misplaced-tile fault for a bracket holding other than `<`;
    ///   the unadmitted refusal for a head naming no recursive function in
    ///   scope; the refusals [`Self::uniform_descent`] and [`Self::claim`]
    ///   raise; the wrong-sort refusal where no type is read.
    /// - panics: none.
    ///
    /// # Errors
    /// The application's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a decoder's arm returning a function type whose
    ///   domain and codomain each decode a descent call, read back as the exact
    ///   unquotes, and a descent on a name no fixpoint binds, refused as
    ///   unadmitted.
    /// - witness: `lower::native::tests::a_decoders_descent_in_its_returned_type_unquotes_the_fixpoint`
    #[spec(ensures: |ret| ret.is_err() || matches!(self.plans.get(site.at.node), Some(&Plan::Unquote(Code::Bound { .. }, ..))))]
    pub(super) fn staged_unquote(
        &mut self,
        site: Site,
        name: SurfaceName<'source>,
        mut cursor: Cursor<'_>,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        closed(site, &mut cursor, TileName::LESS_THAN)?;
        closed(site, &mut cursor, TileName::BRACKET_CLOSE)?;
        let start = self.operands.len();
        arguments(site, &mut cursor, &mut self.operands)?;
        let written = Stretch {
            start,
            end: self.operands.len(),
        };
        self.staged_descent(site, name, written)
    }

    /// Classify a descent `name[<](…)` standing where a type is read, its
    /// arguments `written` in the operand store: the unquote of the call of the
    /// recursive function `name`'s fixpoint, as [`Self::staged_unquote`] plans
    /// the type application and [`Self::typed_call`] the call the expression
    /// grammar molds inside a quoted type (#3681).
    ///
    /// # Specification
    /// - requires: `site` stands where a type is read; `written` is the
    ///   arguments the descent is written with, the last the store holds.
    /// - ensures: as [`Self::staged_unquote`], past its tiles.
    /// - fails: as [`Self::staged_unquote`], past its tiles.
    /// - panics: none.
    ///
    /// # Errors
    /// The descent's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::staged_unquote`], and a descent the
    ///   expression grammar molds at a quoted path carrier.
    /// - witness: `lower::native::tests::a_decoders_descent_in_its_returned_type_unquotes_the_fixpoint`
    /// - witness: `lower::tests::a_descent_at_a_quoted_path_carrier_unquotes_as_in_a_type_3681`
    #[spec(ensures: |ret| ret.is_err() || matches!(self.plans.get(site.at.node), Some(&Plan::Unquote(Code::Bound { .. }, ..))))]
    pub(super) fn staged_descent(
        &mut self,
        site: Site,
        name: SurfaceName<'source>,
        written: Stretch,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let from = site.reading.frame();
        let Maybe::Present(bound) = self.scope.resolve(from, name, &mut self.fuel)?
        else {
            return Err(site.out(FragmentBoundary::Unadmitted(Unbuilt::RecursiveClaim)));
        };
        let Some(&recursion) = self.recursions.get(&bound.binder)
        else {
            return Err(site.out(FragmentBoundary::Unadmitted(Unbuilt::RecursiveClaim)));
        };
        self.claim(site, bound.binder)?;
        self.uniform_descent(from, recursion, site, written)?;
        if let Some(held) = self.recursions.get_mut(&bound.binder) {
            held.claimed = Claimed(true);
        }
        let leading = stretch(&self.parameters, recursion.uniform).len();
        let applied = Stretch {
            start: written.start.saturating_add(leading).min(written.end),
            end: written.end,
        };
        let universe = site.reading.positional_universe();
        let produced = match universe.sort {
            GroundSort::Value => Produced::ValueType,
            GroundSort::Computation => Produced::CompType,
        };
        let frame = self.require(site, produced)?;
        let telescope = self.name_in_type(site.at.node, bound.binder);
        for position in applied.start .. applied.end {
            if let Some(&argument) = self.operands.get(position) {
                self.read(argument, Reading::Value(frame));
            }
        }
        let code = Code::Bound {
            from,
            binder: bound.binder,
            telescope,
        };
        self.plan(site, Plan::Unquote(code, applied, universe));

        Ok(())
    }

    /// The evidence the fixpoint of `function` carries, when it recurses.
    ///
    /// # Specification
    /// - requires: the classification is complete, so every claim is recorded.
    /// - ensures: for a recursive tail one of whose calls claims descent,
    ///   structural descent when the fixpoint stages its first binder, and
    ///   descent staged at the fixpoint's binder `staged - kept` when leading
    ///   binders stand before it; partial evidence for a recursive tail none of
    ///   whose calls claims it, and the plain absence for a tail that does not
    ///   recurse.
    /// - provides: the claim [`Self::mint_function`] closes the fixpoint with.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a recursive function with a descent call, one with no
    ///   call and one whose calls change a parameter before the staged one each
    ///   carry their own evidence.
    /// - witness: `lower::native::tests::a_recursive_function_closes_a_fixpoint_over_its_staged_parameter`
    /// - witness: `lower::native::tests::a_varying_parameter_before_the_staged_one_is_a_leading_binder_626`
    #[spec(ensures: |ret| match function.recursion {
        | Maybe::Present(frame) => ret == Maybe::Present(match self.recursions.get(&frame) {
            Some(held) if held.claimed.0 => match held.staged.0.saturating_sub(stretch(&self.parameters, held.uniform).len()) {
                0 => FixpointEvidence::StructuralDescent,
                position => FixpointEvidence::Staged { position: StagedPosition::from(position) },
            },
            Some(_) | None => FixpointEvidence::Partial,
        }),
        | Maybe::Absent(reason) => ret == Maybe::Absent(reason),
    })]
    pub(super) fn evidence(
        &self,
        function: &Function,
    ) -> Maybe<FixpointEvidence, recursion::Absent>
    {
        match function.recursion {
            Maybe::Present(frame) => Maybe::Present(match self.recursions.get(&frame) {
                Some(held) if held.claimed.0 => {
                    let kept = stretch(&self.parameters, held.uniform).len();
                    match held.staged.0.saturating_sub(kept) {
                        0 => FixpointEvidence::StructuralDescent,
                        position => FixpointEvidence::Staged {
                            position: StagedPosition::from(position),
                        },
                    }
                },
                Some(_) | None => FixpointEvidence::Partial,
            }),
            Maybe::Absent(reason) => Maybe::Absent(reason),
        }
    }

    /// Join each mutual block's recursive functions into one fixpoint over the
    /// sum of their domains, each member that fixpoint at its own summand.
    ///
    /// **Choice.** The core has one fixpoint former, and the kernel stages a
    /// fixpoint over a sum of a block's families at the block's one stage, so
    /// mutual recursion is the joint fixpoint `fix f. λ y. case y { … }` over
    /// `A₀ + … + Aₙ`, a member `λ x. f (injᵢ x)` and a descent through a
    /// sibling `f (inj_j v) c₁ … cₘ`. A member's parameters after its staged
    /// one stay the lambdas of its branch, so the case stands directly under
    /// the staged lambda and no branch is re-indexed past them.
    /// **Alternatives.** A mutual fixpoint former, a new kernel node the
    /// record declines; a tuple of fixpoints, which no stage relates.
    /// **Reversal.** A member over leading parameters, or at a dependent
    /// type, joins once the joint reads a telescope rather than one domain.
    ///
    /// # Specification
    /// - requires: the mint sweep has run.
    /// - ensures: in a mutual block of at least two `def rec` declarations,
    ///   each staging its first parameter and lowered to `thunk (fix. λ. bᵢ)`
    ///   at `+U (Aᵢ -> C)`, `bᵢ` the lambdas of the later parameters over the
    ///   body and `C` the arrow over their types, every member's body is `thunk
    ///   (λ x. ((fix. λ y. case y { b₀↑ | … | bₙ↑ }) : Σᵢ Aᵢ -> C) (injᵢ x))`,
    ///   each `bᵢ` raised past the case's binder and its copies at the origins
    ///   of what they copy, every other node the fixpoint's insertion; the
    ///   fixpoint claims descent when a member's did. A block with a member
    ///   that did not lower so is unchanged.
    /// - provides: mutual recursion between a block's functions as the one
    ///   fixpoint the core has.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — each member's body shape is a term in the sink's
    ///   arena, which a clause would walk member by member; the witness reads
    ///   the shapes back.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Joint`].
    /// - witness: `lower::native::tests::a_mutual_block_member_takes_a_parameter_after_its_staged_one_3722`
    /// - witness: `lower::native::tests::a_mutual_blocks_recursive_functions_share_one_fixpoint`
    pub(super) fn mint_joints(
        &mut self,
        sink: &mut Sink<'_>,
    )
    {
        let mut joined = Vec::new();
        for index in self.current.blocks .. self.collected.blocks.len() {
            let Some(&block) = self.collected.blocks.get(index)
            else {
                continue;
            };
            let members = self.collected.recursive.range(block.first .. block.end);
            let count = members.clone().count();
            if count < 2 {
                continue;
            }
            joined.clear();
            for &member in members {
                match self.joinable(member, sink) {
                    Maybe::Present(read) => joined.push(read),
                    Maybe::Absent(_) => break,
                }
            }
            if joined.len() == count {
                self.join(&joined, sink);
            }
        }
    }

    /// Read each recursive call through the joint of a mutual block holding a
    /// member the lowering refused as the call it is without the joint, which
    /// [`Self::mint_joints`] leaves unformed for that block.
    ///
    /// **Choice.** Without the joint, a member is its own fixpoint over its own
    /// domain: a call on itself passes its argument uninjected, and a call
    /// through a sibling names the sibling's declaration, as a call of a
    /// declaration outside the block does. The checker then meets the
    /// refused sibling as a constant it has no type for, and the report reads
    /// that refusal as the sibling's consequence, a note naming it, rather
    /// than refusing the injection into a sum the joint never formed (#2340).
    /// **Alternative.** Refusing every other member at the lowering, which
    /// needs a refusal of its own for what the cascade cut already reports.
    ///
    /// # Specification
    /// - requires: the source is classified and not yet minted.
    /// - ensures: every call through a joint ([`Self::instantiation`]) whose
    ///   block holds a member refused before the mint carries no injection, and
    ///   one through a sibling member is planned as that member's constant;
    ///   every other call through a joint is unchanged.
    /// - provides: a lowered member of such a block typed at its own domain.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the clause compares the injections and plans before
    ///   and after, a walk no clause makes; the witness reads the report back.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a member calling a sibling refused at its head and at
    ///   its body is not refused by a shape of its own.
    /// - witness: `lower::native::tests::a_member_beside_a_refused_sibling_calls_its_declaration_2340`
    pub(super) fn unjoin_refused(&mut self)
    {
        let mut unjoined = Vec::new();
        for (&head, &summand) in &self.injected {
            let Maybe::Present(owner) = self.collected.owner_of(head)
            else {
                continue;
            };
            let joint = self.joint(owner);
            let refused = joint.members.iter().any(|&member| {
                self.faults.contains_key(&member)
                    || self
                        .collected
                        .slots
                        .get(usize::from(member))
                        .is_some_and(|slot| matches!(slot.refusal, Maybe::Present(_)))
            });
            let Maybe::Present((_, own)) = joint.own
            else {
                continue;
            };
            if !refused {
                continue;
            }
            let called = if summand == own {
                None
            }
            else {
                joint
                    .members
                    .get(usize::from(summand))
                    .and_then(|&member| self.collected.slots.get(usize::from(member)))
                    .map(|slot| slot.constant)
            };
            unjoined.push((head, called));
        }
        for (head, called) in unjoined {
            let _injected = self.injected.remove(&head);
            if let Some(constant) = called
                && let Some(plan) = self.plans.get_mut(head)
            {
                *plan = Plan::Constant(constant);
            }
        }
    }

    /// The member at `member` as the joint fixpoint reads it.
    ///
    /// # Specification
    /// - requires: the mint sweep has run.
    /// - ensures: a function tail staging its first parameter, lowered to
    ///   `thunk (fix. λ. b)` at `+U (A -> C)`, reads as its declaration, `A`,
    ///   `C`, `b` and the fixpoint's claim; `b` holds the lambdas of the
    ///   parameters after the first, and `C` the arrow over their types.
    /// - fails: [`joint::Absent::Unjoined`] for anything else.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Joint`].
    /// - witness: `lower::native::tests::a_mutual_blocks_recursive_functions_share_one_fixpoint`
    /// - witness: `lower::native::tests::a_mutual_block_member_takes_a_parameter_after_its_staged_one_3722`
    #[spec(ensures: |ret| match ret {
        Maybe::Present(read) => sink.arena.computation(read.branch).is_some(),
        Maybe::Absent(reason) => reason == joint::Absent::Unjoined,
    })]
    fn joinable(
        &self,
        member: SlotIndex,
        sink: &Sink<'_>,
    ) -> Maybe<Joinable, joint::Absent>
    {
        let unjoined = Maybe::Absent(joint::Absent::Unjoined);
        let Some(&Maybe::Present(Half {
            operand: Operand::Function,
            declaration,
            ..
        })) = self
            .collected
            .slots
            .get(usize::from(member))
            .map(|slot| &slot.definition)
        else {
            return unjoined;
        };
        // A member joins over its first parameter, the one it stages; the
        // plans are spent by the mint sweep, so its recursion record, keyed by
        // the frame the declaration form types, says which it stages.
        let staged_first = self.recursions.iter().any(|(&binder, recursion)| {
            self.scope.declared(binder) == Maybe::Present(declaration.node)
                && !stretch(&self.parameters, recursion.parameters).is_empty()
                && recursion.staged == ParameterAt(0)
        });
        if !staged_first {
            return unjoined;
        }
        let (Maybe::Present(signature), Maybe::Present(body), Maybe::Present(origin)) = (
            self.signature_at(declaration.node),
            self.function_body_at(declaration.node),
            self.origin_at(declaration.node),
        )
        else {
            return unjoined;
        };
        let arena = &*sink.arena;
        let Some(&gandr_core_term::ValueType::Thunk(arrow)) = arena.value_type(signature)
        else {
            return unjoined;
        };
        let Some(&CompType::Arrow { domain, codomain }) = arena.comp_type(arrow)
        else {
            return unjoined;
        };
        let Some(&Value::Thunk(fixpoint)) = arena.value(body)
        else {
            return unjoined;
        };
        let Some(&gandr_core_term::Computation::Fixpoint {
            body: lambda,
            evidence,
        }) = arena.computation(fixpoint)
        else {
            return unjoined;
        };
        let Some(&gandr_core_term::Computation::Lambda(branch)) = arena.computation(lambda)
        else {
            return unjoined;
        };
        Maybe::Present(Joinable {
            declaration: declaration.node,
            signature,
            domain,
            codomain,
            branch,
            evidence,
            origin,
        })
    }

    /// Mint the joint fixpoint of `joined` and make each member's body that
    /// fixpoint at its summand, as [`Self::mint_joints`] states.
    ///
    /// # Specification
    /// - requires: `joined` is one block's members in block order, at least
    ///   two, each read by [`Self::joinable`].
    /// - ensures: as [`Self::mint_joints`] states for one block.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Joint`].
    /// - witness: `lower::native::tests::a_mutual_blocks_recursive_functions_share_one_fixpoint`
    #[spec(requires: joined.len() >= 2)]
    fn join(
        &mut self,
        joined: &[Joinable],
        sink: &mut Sink<'_>,
    )
    {
        let Some(first) = joined.first()
        else {
            return;
        };
        let mark = sink.arena.watermark();
        let mut carried = Vec::new();
        let domains: Vec<ValueTypeId> = joined.iter().map(|member| member.domain).collect();
        let sum = sink.arena.value_type_sum(&domains);
        let ascribed = sink.arena.comp_type_arrow(sum, first.codomain);
        // Each member's body stands under its own fixpoint binder and its
        // parameter; in the joint it stands under the fixpoint binder, the
        // case's scrutinee and the summand the case binds.
        let mut branches = Vec::with_capacity(joined.len());
        for member in joined {
            branches.push(
                gandr_core_term::shift_computation_under(
                    sink.arena,
                    member.branch,
                    Binders::ONE,
                    Binders::ONE,
                )
                .settle_traced(sink.arena, &mut carried),
            );
        }
        let evidence = if joined
            .iter()
            .any(|member| member.evidence == FixpointEvidence::StructuralDescent)
        {
            FixpointEvidence::StructuralDescent
        }
        else {
            FixpointEvidence::Partial
        };
        let scrutinee = sink
            .arena
            .value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
        let case = sink.arena.computation_case(scrutinee, &branches);
        let lambda = sink.arena.computation_lambda(case);
        let fixpoint = sink.arena.computation_fixpoint(lambda, evidence);
        let joint = sink.arena.computation_ascribe(fixpoint, ascribed);
        record_copied_since(
            sink,
            mark,
            first.origin.inserted(Insertion::Fixpoint),
            Maybe::Absent(rooted::Absent::Unminted),
            &carried,
        );
        for (at, member) in joined.iter().enumerate() {
            let inserted = member.origin.inserted(Insertion::Fixpoint);
            let own = sink
                .arena
                .value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
            sink.origins.record_value(own, inserted);
            let injected = sink.arena.value_injection(Summand::from(at), own);
            sink.origins.record_value(injected, inserted);
            let applied = sink.arena.computation_application(joint, injected);
            sink.origins.record_computation(applied, inserted);
            let lambda = sink.arena.computation_lambda(applied);
            sink.origins.record_computation(lambda, inserted);
            let thunk = sink.arena.value_thunk(lambda);
            sink.origins
                .record_value(thunk, member.origin.inserted(Insertion::Thunk));
            if let Some(lowered) = self.lowered.get_mut(usize::from(member.declaration)) {
                *lowered = Maybe::Present(Lowered::Function {
                    signature: Maybe::Present(member.signature),
                    body: thunk,
                });
            }
        }
    }
}

/// Whether a rule side binds its variables or reads the left side's.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Binding
{
    /// The left side: a variable's first occurrence takes the next ordinal.
    Binds,
    /// The right side: a variable reads the ordinal the left side gave it.
    Reads,
}

/// Which applications of a rule side apply the generators it is read over.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Heads
{
    /// A data declaration's constructors: an operation is another reading's.
    Constructors,
    /// A theory's operations, each the constructor of its terms: a
    /// constructor is no operation of the theory.
    Operations,
}

quenchant_shape::reason_enum! {
    /// Why a rule side is not a presented type's.
    pub(crate) mod rule_side {
        /// The reason the side was passed over.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub(crate) enum Absent {
            /// It applies what is no generator: an operation of a family, a
            /// constructor of a theory, a results tuple, or a generator `names`
            /// does not hold.
            Foreign,
            /// Its right side names a variable its left side does not bind.
            Unbound,
        }
    }
}

/// One rule side in pre-order over the generators `names`, the applications
/// `heads` names, its variables numbered through `variables`.
///
/// # Specification
/// - requires: `variables` holds the left side's variables when `binding` reads
///   them.
/// - ensures: one node per term node, a generator by its position in `names`
///   and a variable by its position in `variables` — appended there on its
///   first occurrence when `binding` binds.
/// - fails: [`rule_side::Absent::Foreign`] for an application `heads` does not
///   name, a results tuple, an instantiation or a generator `names` does not
///   hold; [`rule_side::Absent::Unbound`] for a variable a reading side meets
///   unbound.
/// - panics: none.
///
/// # Termination
/// - reason: the `while let` worklist, not recursion.
/// - measure: the term nodes still to visit.
///
/// # Adequacy
/// - hypothesis: L3 — as [`Lowerer::presentation`] and [`Lowerer::term_rules`].
/// - witness: `lower::native::tests::a_presented_family_lowers_its_rules`
/// - witness: `tests::modules::models::a_theory_s_terms_are_its_operations_over_its_rules_4143`
#[spec(ensures: |ret| match ret {
    Maybe::Present(ref nodes) => !nodes.is_empty(),
    Maybe::Absent(_) => true,
})]
#[cfg_attr(
    dylint_lib = "quenchant_dylints",
    expect(
        linear_search_in_loop,
        reason = "bounded: `variables` holds one rule side's variables and `names` one family's constructors"
    )
)]
fn rule_side(
    side: &gandr_theory_levitation::FreeTerm,
    names: &[SourceFragment<'_>],
    variables: &mut Vec<gandr_theory_levitation::Name>,
    binding: Binding,
    heads: Heads,
) -> Maybe<alloc::boxed::Box<[gandr_core_term::RuleNode]>, rule_side::Absent>
{
    let mut nodes = Vec::new();
    let mut pending = Vec::from([side.to_node()]);
    while let Some(node) = pending.pop() {
        match (node.view(), heads) {
            (gandr_theory_levitation::TermView::Var(name), _) => {
                let position = match variables.iter().position(|bound| bound == name) {
                    Some(position) => position,
                    None if binding == Binding::Binds => {
                        variables.push(name.clone());
                        variables.len().saturating_sub(1)
                    },
                    None => return Maybe::Absent(rule_side::Absent::Unbound),
                };
                let Ok(ordinal) = u32::try_from(position)
                else {
                    return Maybe::Absent(rule_side::Absent::Unbound);
                };
                nodes.push(gandr_core_term::RuleNode::Variable(
                    gandr_core_term::RuleVariable::from(ordinal),
                ));
            },
            (gandr_theory_levitation::TermView::Ctor { name, args }, Heads::Constructors)
            | (gandr_theory_levitation::TermView::Op { name, args }, Heads::Operations) => {
                let Some(tag) = names
                    .iter()
                    .position(|&written| <&str>::from(written) == name.as_ref())
                else {
                    return Maybe::Absent(rule_side::Absent::Foreign);
                };
                nodes.push(gandr_core_term::RuleNode::Constructor(
                    ConstructorTag::from(tag),
                ));
                let mark = pending.len();
                pending.extend(args);
                if let Some(children) = pending.get_mut(mark ..) {
                    children.reverse();
                }
            },
            (
                gandr_theory_levitation::TermView::Op { .. }
                | gandr_theory_levitation::TermView::Ctor { .. }
                | gandr_theory_levitation::TermView::Results { .. }
                | gandr_theory_levitation::TermView::Inst { .. }
                | gandr_theory_levitation::TermView::Abs { .. }
                | gandr_theory_levitation::TermView::Atom(_)
                | gandr_theory_levitation::TermView::Lam { .. }
                | gandr_theory_levitation::TermView::Bound(_),
                _,
            ) => {
                return Maybe::Absent(rule_side::Absent::Foreign);
            },
        }
    }
    Maybe::Present(nodes.into_boxed_slice())
}
