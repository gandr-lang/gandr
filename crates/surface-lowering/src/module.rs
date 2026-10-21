//! The module collection pass and what it produces: [`LoweredModule`], the
//! [`LoweredDeclaration`]s it holds, and the [`DeclarationOutcome`] each name
//! ends the module at.
//!
//! # Collect by name, resolve by position
//!
//! A module is collected by *name*, so `def x : T ;` pairs with `def x = e ;`
//! wherever the two sit and the signature-then-definition form stays
//! spellable. References still resolve by *admission position* — a name's
//! position is fixed by its first declaration, and a body may name only
//! strictly earlier positions — so outside a `rec { }` block (§ A `rec` block
//! is one admission) self-reference and mutual reference are refused by the
//! rule as well as by the core's own definition chain.
//!
//! # A signature no definition completes is the obligation producer
//!
//! `def x : T ;` states a typing; a later `def x = e ;` discharges it by
//! deriving what the signature asserted. What survives the whole module — a
//! signature whose name no definition ever supplies — is an obligation,
//! addressable by that name, carrying its own span and its declared type, and
//! producing no term at all. That is why [`DeclarationOutcome`] separates the
//! completed pair from the uncompleted signature rather than carrying two
//! optional halves: the distinction is the ledger's producer, not a detail of
//! it.
//!
//! # One declaration form, read by its own tiles
//!
//! The grammar writes every declaration as one form, `def name …`, whose tail
//! decides what it is: `: T ;` a signature, `= e ;` a definition, and a
//! parameter list `(params) -> T? { … }` a function, which writes a definition
//! and, when every parameter and the result carry a type, a signature too. An
//! implicit telescope is a form the fragment does not admit. `rec`, which the
//! grammar writes before a function tail alone, is that tail's own tile: the
//! classification closes the function by a fixpoint over its staged parameter.
//! Attributes written before `def` are tiles of that same form, so a
//! declaration's attributes are read with it. A data declaration's form holds
//! none: the grammar leaves an attribute block before `data` standing on its
//! own, and the pass files every block that runs up to a data declaration
//! under it. Any other attribute block standing on its own — after the last
//! declaration, or before a form that is not a data declaration — decorates
//! nothing and refuses the module.
//!
//! The collection pass reads a function tail only as far as the halves it
//! writes: the parameter list, the result and the block are the function's own
//! reading, which the classification makes over the declaration form once the
//! halves are filed, so a refusal inside the function leaves its expectation
//! readable.
//!
//! # One refusal per declaration, and the run continues
//!
//! A declaration reports its first refusal and the module keeps going with the
//! next one. "First" is by arena position, which the level-order layout makes
//! the shallowest and then leftmost refusing node. Distinct positions have a
//! traversal-independent winner; equal positions retain the first offered
//! refusal. A fault in the declaration form's own tiles is offered at the
//! declaration node itself, so it outranks every refusal from inside its
//! operands. A fault in the module's own shape — a root child that is not a
//! declaration or an import, an import out of shape, two imports of one alias,
//! or a declaration with no name to file a refusal under — refuses the module.
//!
//! # Imports are collected beside the declarations
//!
//! `import "<path>" ;` and `import "<path>" as name ;` are kept in source
//! order, under the source that writes them, and an alias is bound in that
//! source's import scope as it is read; the [`Unit`] says what
//! each path import resolved to, and a name the source does not declare is
//! read through its resolved imports (the `import` module).
//!
//! # A data declaration is one more slot
//!
//! `data T(a : A) : U { C : (x : B) --> T(a) ; … }` takes the next admission
//! position under its family's name and files a definition half lowered at the
//! declaration form itself, like a function tail. Its constructors go into one
//! table by name, each with its family, tag and arity, so a term or a pattern
//! naming one resolves it without searching the declarations.
//!
//! # A `rec` block is one admission
//!
//! `rec { data … ; def … ; def rec … }` collects each member as a declaration
//! of its own, in one run of slots ([`MutualBlock`]), and its members name
//! one another in any order: a universe's code names its decoder, a rose
//! tree's node names its forest. The checkers admit the run as one block, its
//! data declarations first. Its `def rec` functions, when two or more, are one
//! fixpoint over the sum of their domains, each at its summand
//! (`lower::native` § A recursive function is one fixpoint over its last
//! parameter).
//!
//! # A `theory` block defines a value of `Theory`
//!
//! `theory S { … }` takes the next admission position under `S` and files a
//! definition half lowered at the block itself: `S : Theory`, whose body is the
//! presentation's value the description route read (`crate::model`). `Theory`,
//! the presentation code `gandr_theory_levitation::theory_desc` describes, is
//! minted once per module as a slot of its own, just before the first block
//! that refuses nothing, and its constructors enter the constructor table
//! beside the written families'; a module with no such block declares neither,
//! so a module that presents nothing loses no name to them. A block some member
//! of which the description route or the cell gate refused still takes its
//! slot, refused by its first refusal, and each further refusal is held at its
//! member's span. The alternatives were `Theory` in a prelude every module
//! imports, which the fragment has none of, and `Theory` minted in every
//! module, which takes eleven constructor names from modules that present
//! nothing. The choice reverses with a prelude: `Theory` becomes one of its
//! declarations.
//!
//! # A module is collected by name and resolved by position
//!
//! A signature pairs with its definition wherever the two sit in the module, so
//! the signature-then-definition form stays spellable; a second signature or
//! definition for one name is refused naming the first, except that a written
//! signature beside a function tail, which derives one of its own, keeps the
//! written one and checks the derived one as a witness (§ A module declaration
//! flattens to named members). References resolve by admission position — the
//! position of the declaration that introduced the name — so a declaration's
//! own body and every later declaration are out of its scope, and
//! self-reference and mutual reference outside a `rec` block are refused as
//! unresolved names. A
//! module whose own shape is wrong — a root that is not a module, a root child
//! that is neither a declaration, a module declaration nor an import, a
//! declaration with no name, an import out of shape, two imports of one alias,
//! an attribute block decorating nothing — refuses the whole run, because
//! nothing can be filed without the name.
//!
//! # One refusal per declaration
//!
//! Every refusal found inside a declaration is offered to the declaration that
//! owns the refusing node, and the declaration keeps the refusal at the lowest
//! arena position, so distinct positions have a traversal-independent winner.
//! Refusals offered at the same position retain the first offer. The
//! declaration form's own faults sit at the declaration node itself and
//! therefore outrank anything in its operands, and an attribute's tiles precede
//! the declaration's operands, so an attribute's refusal outranks a refusal in
//! its signature or body. A refused declaration lowers nothing but its
//! attribute payloads, and every other declaration lowers regardless. Engine
//! faults — an exhausted allowance, a tree of another grammar, a mold outside
//! the grammar's table — abort the whole run instead, because no declaration's
//! verdict can be trusted past one.
//!
//! Before minting, manifest-type refusals propagate in signature order through
//! later aliases and into the members whose types name them. The original
//! refusal and its span are retained, but it competes at each referencing
//! head’s position. This can outrank an independently refused member body
//! without preventing a following declaration from lowering.
//! `tests::modules::manifest_refusals_propagate_transitively_before_minting`
//! exercises that chain and precedence together.
//!
//! The alternative was to collect every refusal of a declaration. It was
//! declined because later refusals under a refused form are frequently
//! consequences of the first. Reversal: when a consumer reports all independent
//! faults at once, a slot keeps a list ordered by position.
//!
//! # A module declaration flattens to named members
//!
//! `module M { … }` declares no value of its own. Each member `def` is one
//! declaration, admitted among every other declaration in source order — a
//! nested module's members between the parent's members written before and
//! after it — so `Config.limits.hard.detail.note` is one declaration at the
//! position its place in the source gives it. Its structured name is the
//! enclosing modules' names, outermost first, then its own:
//! `LoweredModule::path_of` spells it, and `LoweredModule::structured_names`
//! hands every declared name's segments to a checker's export, which writes
//! them into the kernel declaration's name record. Every reference reads the
//! admission position; no check reads a name. The alternatives were a module as
//! a record value — a record type ascribed to a record of the members, a path
//! as a record projection — which makes every member's check wait on the whole
//! record and the namespace a value the fragment has to type, and one dotted
//! string per declaration, which makes the namespace's spelling the identity.
//! The choice reverses for modules passed as values, which need the record
//! carrier beside the flat members.
//!
//! A member names the members before it in its own module, then those of each
//! enclosing module outward, then the top-level declarations before it. A
//! member of an enclosing module named at or after the referring declaration's
//! position is `ForwardMemberReference`, carrying where the member is declared;
//! a top-level name keeps the unresolved-name refusal. The alternative was
//! refusing a later member as unresolved, which hides that the name exists one
//! position too late. `def rec` does not reverse this: it binds its own name
//! inside its own body, never a later declaration's; a `rec` block's members
//! name one another (§ A `rec` block is one admission).
//!
//! Each top-level module declares one namespace in the outermost scope,
//! governing exactly what it exports: a value component as a component and a
//! nested module as a namespace of its own; a hidden member appears nowhere. A
//! selection chain headed by a capitalised name is resolved as one path at the
//! depth that binds it. A path complete at a component is the member's
//! constant, under the same position rule; a path stopped at a governing module
//! is `UnknownMember`, naming the module as the path spells it and the member;
//! a path ending at a module is the wrong sort, because a module is not a
//! value; and a selection no module governs is a record projection, unadmitted
//! until the fragment has a record former. Paths name from the top level, so a
//! nested module is reached through its top-level module. The alternative was
//! resolving paths against the collected modules directly, which would leave
//! the namespace engine registering names that nothing consults.
//!
//! An inline signature `module M : #{ x : A, type T = τ } { … }` is matched
//! coercively. A value component's type becomes its member's signature when the
//! member has none, or only the type a function tail derives; a member already
//! signed is checked by a witness — a declaration at the component's type whose
//! body is the member's constant — so the checker refuses a disagreement as a
//! type mismatch at the witness. The exports are reordered to signature order
//! and narrowed to the components: a member the signature omits is admitted and
//! checked, but absent from the namespace and from the module's stratum item. A
//! nested module component takes a record type `#{ … }` and is matched against
//! the nested module's own exports the same way, as is a member signature `def
//! inner : #{ … } ;` written beside `module inner`. A manifest type component
//! `type T = τ` lowers `τ` once, and a later component naming `T` stands for
//! that type; an earlier one cannot name it. The alternatives were checking the
//! whole module against one record type, declined with the record carrier, and
//! refusing a second stated type, which loses the agreement check. A witness
//! becomes an annotation on the member's body when the core has an annotation
//! former. An abstract component `type T` or `type T : κ`, and the opaque
//! ascription `:>` that seals it, are `sealing`'s: a type member of the body
//! gives the component its meaning, and `:>` declares one abstract type per
//! component.
//!
//! A refusal that belongs to no member — a top-level module with a lowercase
//! name, an unread module body, a missing component, an abstract component
//! the body writes no type member for, and a type component that declares a
//! family or binds parameters — is carried by a held declaration under the
//! module's or the component's name. A held declaration owns nothing a
//! checker reads, takes a position like any other, and yields a declaration
//! only when it carries a refusal; one owning a type member's form yields
//! none. Its refusal stands at a form with no half, so no expectation
//! attribute reaches it. The family and parameterized forms are
//! `UnreadAscription`, naming the form and what gives it meaning. The
//! alternatives were refusing the whole run, which loses every other module's
//! members, and dropping the refusal, which reads the module as if it were
//! whole. The choice reverses when a refusal at a declaration's own form can
//! carry an expectation.
//!
//! `LoweredModule::structures` holds one `LoweredStructure` per module, in
//! pre-order: its path, its bytes, the value components with their positions
//! and the nested modules it exports, in export order, its manifest type
//! components with the types they lowered to, the abstract components it
//! sealed with the positions of their atoms, and whether matching coerced its
//! body.
//!
//! `LoweredModule::structured_names` exports declared and sealed abstract
//! positions only: witness and held slots take no entry, and any path
//! containing the segment separator is omitted. Construction accepts supplied
//! metadata, so positions need not be unique: the last eligible declaration
//! at a repeated position wins, while an invalid later path leaves the earlier
//! name intact. These boundaries are witnessed by
//! `module::tests::structured_export_omits_invalid_segments_and_keeps_the_last_declared_name`;
//! arity and ownership routing are separated by
//! `module::tests::signature_holes_distinguish_missing_single_and_extra_operands`
//! and `module::tests::ownership_routes_refusals_without_touching_other_slots`.

use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use alloc::string::String;
use alloc::sync::Arc;
use alloc::vec::Vec;

use anodized::spec;
use gandr_core_term::CodataSignature;
use gandr_core_term::DataSignature;
use gandr_core_term::ValueId;
use gandr_core_term::ValueTypeId;
use gandr_core_term::effect::Purity;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::NameSegment;
use gandr_kernel_term::StructuredName;
use gandr_surface_grammar::Pbg;
use gandr_surface_syntax::ByteOffset;
use gandr_surface_syntax::ByteSpan;
use gandr_surface_syntax::NodeCount;
use gandr_surface_syntax::NodeIndex;
use gandr_surface_syntax::NodeLabel;
use gandr_surface_syntax::SourceFragment;
use gandr_surface_syntax::SyntaxTree;
use gandr_theory_levitation::THEORY_CONSTRUCTORS;
use gandr_theory_levitation::theory_desc;
use quenchant_shape::shape::Maybe;

use crate::attribute::AttributeTable;
use crate::description::DescriptionFault;
use crate::doc::Documentation;
use crate::error::AscriptionForm;
use crate::error::FormFault;
use crate::error::FragmentBoundary;
use crate::error::FragmentSort;
use crate::error::LoweringRefusal;
use crate::form::Cursor;
use crate::form::FormName;
use crate::form::Former;
use crate::form::Piece;
use crate::form::Pieces;
use crate::form::Placed;
use crate::form::Run;
use crate::form::Shape;
use crate::form::TileName;
use crate::form::read_pieces;
use crate::form::repair_at;
use crate::form::shape_of;
use crate::import::ImportBinding;
use crate::import::ImportDeclaration;
use crate::import::ImportIndex;
use crate::import::ImportResolution;
use crate::import::ImportUri;
use crate::import::ModuleImports;
use crate::lower::ElidableExit;
use crate::lower::Fuel;
use crate::lower::InferredExit;
use crate::lower::InferredRun;
use crate::lower::LinearRun;
use crate::lower::NestedSite;
use crate::lower::decode_escapes;
use crate::namespace::Recognition;
use crate::namespace::Scope;
use crate::origin::Insertion;
use crate::origin::OriginTable;
use crate::origin::OriginToken;
use crate::origin::Provenance;
use crate::resolve::InScope;
use crate::resolve::Resolution;
use crate::resolve::SurfaceName;
use crate::unit::ImportTarget;
use crate::unit::PathImportOrdinal;
use crate::unit::SourceIndex;
use crate::unit::Unit;
use crate::unit::UnitKey;

mod data;

mod functor;

mod model;

mod plicity;

mod receiver;

mod sealing;

mod world;

pub use self::data::Constructor;
pub use self::data::DataForm;
pub use self::data::Generators;
pub use self::data::WordsForm;
pub use self::data::closed_term;
use self::functor::Applied;
pub use self::functor::Functor;
pub use self::functor::FunctorIndex;
pub use self::functor::Instance;
pub use self::functor::InstanceIndex;
pub use self::functor::Matched;
pub use self::functor::ParameterComponent;
pub use self::functor::ParameterForm;
pub use self::functor::Stratum;
use self::functor::WrittenParameter;
pub use self::functor::parameter;
pub use self::model::FamilyCheck;
pub use self::model::FamilyForm;
pub use self::model::FamilyIndex;
pub use self::model::FamilyMember;
pub use self::model::FamilyParameter;
pub use self::model::ModelIndex;
pub use self::model::ModelPart;
pub use self::model::ParameterList;
pub use self::model::derived;
pub use self::model::spine_domains;
pub use self::model::ungrouped;
pub use self::plicity::Plicity;
pub use self::plicity::TelescopeEntry;
pub use self::plicity::merged;
pub use self::receiver::ReceiverMode;
use self::receiver::receiver_of;
pub use self::sealing::AbstractSlot;
pub use self::sealing::ComponentPlace;
use self::sealing::KindForm;
pub use self::sealing::Mark;
pub use self::sealing::Sealed;
pub use self::sealing::SealedComponent;
pub use self::sealing::Sealing;
pub use self::sealing::TypeMeaning;

quenchant_shape::reason_enum! {
    /// Why a declared name has no half of one kind.
    pub mod declaration_half {
        /// The name carries no declaration of that kind.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// No declaration of that kind was written for the name.
            Unwritten,
        }
    }
}

quenchant_shape::reason_enum! {
    /// Why a module holds no data signature at an index.
    pub mod data_signature {
        /// The index is past the module's signature list.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The module lowered fewer data declarations than the index.
            Unlisted,
        }
    }
}

quenchant_shape::reason_enum! {
    /// Why a module holds no codata signature at an index.
    pub mod codata_signature {
        /// The index is past the module's codata signature list.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The module lowered fewer codata declarations than the index.
            Unlisted,
        }
    }
}

quenchant_shape::reason_enum! {
    /// Why a slot holds no refusal.
    pub mod slot_refusal {
        /// Nothing about the declared name has refused.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// Every node offered so far read cleanly.
            Unrefused,
        }
    }
}

quenchant_shape::reason_enum! {
    /// Why a node belongs to no declaration.
    pub mod slot_owner {
        /// The node sits outside every declaration.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The node is the root, layout, or not under a filed declaration.
            Unowned,
        }
    }
}

quenchant_shape::reason_enum! {
    /// Why a slot belongs to no mutual block.
    pub mod mutual_block {
        /// The slot stands outside every block.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// No `rec { … }` block's run holds the slot.
            Outside,
        }
    }
}

quenchant_shape::reason_enum! {
    /// Why a module form's tail reads no functor application.
    pub mod application {
        /// The tail is out of shape.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// A tile of `F(P(.p)*) ;` is missing or out of place.
            Misplaced,
        }
    }
}

quenchant_shape::reason_enum! {
    /// Why a module carries no inline signature.
    pub mod ascription {
        /// The module is written without one.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// No `:` signature follows the module's name.
            Unascribed,
        }
    }
}

quenchant_shape::reason_enum! {
    /// Why an abstract type component states no kind.
    pub mod component_kind {
        /// The component is written without one.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// No `: κ` follows the component's name, so it inhabits the
            /// fuss-free universe `Type`.
            Unkinded,
            /// The component is a sort a model signature derives, which
            /// states no kind: a sort is as large as its model makes it.
            Derived,
        }
    }
}

/// The position of one declaration slot in a module's admission order.
///
/// # Specification
/// - requires: nothing to construct this data; its producers and consumers
///   state coordinate preconditions separately.
/// - ensures: The number is a zero-based slot coordinate relative to a
///   collection, without authenticating ownership or proving that the slot
///   exists.
/// - fails: not applicable to the data item.
/// - panics: not applicable to the data item.
/// - executable: none — the enabled specification facade does not expose
///   type-invariant expansion; executable predicates cover the producing and
///   consuming operations.
///
/// # Adequacy
/// - hypothesis: L3 — independent slot coordinates route refusals to their
///   current owner.
/// - witness: `module::tests::ownership_routes_refusals_without_touching_other_slots`
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct SlotIndex(usize);

impl From<usize> for SlotIndex
{
    /// The slot at admission position `position`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(position: usize) -> Self
    {
        Self(position)
    }
}

impl From<SlotIndex> for usize
{
    /// The admission position `position` names.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(position: SlotIndex) -> Self
    {
        position.0
    }
}

/// A number of declarations.
///
/// # Specification
/// - requires: nothing to construct this data; its producers and consumers
///   state coordinate preconditions separately.
/// - ensures: The number counts admitted slots, including witness and held
///   positions rather than only exported declarations.
/// - fails: not applicable to the data item.
/// - panics: not applicable to the data item.
/// - executable: none — the enabled specification facade does not expose
///   type-invariant expansion; executable predicates cover the producing and
///   consuming operations.
///
/// # Adequacy
/// - hypothesis: L3 — signature witnesses occupy their own admitted positions
///   without exporting names.
/// - witness: `tests::modules::member_signature_attaches_and_wins_over_derived_function_type`
/// - witness: `tests::modules::signatures_attach_to_their_defs`
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct DeclarationCount(usize);

impl From<usize> for DeclarationCount
{
    /// The count `count`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(count: usize) -> Self
    {
        Self(count)
    }
}

impl From<DeclarationCount> for usize
{
    /// The number `count` holds.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(count: DeclarationCount) -> Self
    {
        count.0
    }
}

/// The position of one module in a source's pre-order of modules: a module
/// before every module nested in it.
///
/// # Specification
/// - requires: nothing to construct this data; its producers and consumers
///   state coordinate preconditions separately.
/// - ensures: The number is a pre-order structure coordinate relative to its
///   collection, without certifying that the structure exists.
/// - fails: not applicable to the data item.
/// - panics: not applicable to the data item.
/// - executable: none — the enabled specification facade does not expose
///   type-invariant expansion; executable predicates cover the producing and
///   consuming operations.
///
/// # Adequacy
/// - hypothesis: L3 — nested modules are recorded before their descendants.
/// - witness: `tests::modules::deeply_nested_modules_lower_and_resolve_at_every_depth`
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct StructureIndex(usize);

impl From<usize> for StructureIndex
{
    /// The module at pre-order position `position`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(position: usize) -> Self
    {
        Self(position)
    }
}

impl From<StructureIndex> for usize
{
    /// The pre-order position `position` names.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(position: StructureIndex) -> Self
    {
        position.0
    }
}

/// Where a name is declared: the source's top level, or a module's body.
///
/// # Specification
/// - requires: nothing to construct this data; its producers and consumers
///   state coordinate preconditions separately.
/// - ensures: A top-level name is distinct from every module-local name; a
///   module position is relative to its collection, not an ownership token.
/// - fails: not applicable to the data item.
/// - panics: not applicable to the data item.
/// - executable: none — the enabled specification facade does not expose
///   type-invariant expansion; executable predicates cover the producing and
///   consuming operations.
///
/// # Adequacy
/// - hypothesis: L3 — nested and top-level definitions resolve under their own
///   containers.
/// - witness: `tests::modules::modules_lower_to_named_member_declarations`
/// - witness: `tests::modules::module_members_admit_in_source_order`
/// - witness: `tests::modules::a_readable_module_keeps_its_members_and_its_successor`
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Container
{
    /// The top level of this source of the unit.
    TopLevel(SourceIndex),
    /// The body of this module.
    Module(StructureIndex),
}

/// What a slot stands for.
///
/// # Specification
/// - requires: nothing to construct this data; its producers and consumers
///   state coordinate preconditions separately.
/// - ensures: Declared slots introduce names, witnesses check an extra type
///   without declaring a name, held slots own components or refusals without
///   becoming exports, and abstract slots declare the atom an opaque ascription
///   mints without entering a name table.
/// - fails: not applicable to the data item.
/// - panics: not applicable to the data item.
/// - executable: none — the enabled specification facade does not expose
///   type-invariant expansion; executable predicates cover the producing and
///   consuming operations.
///
/// # Adequacy
/// - hypothesis: L3 — declared names export while signature witnesses and held
///   refusals do not; an opaque ascription's abstract component is declared
///   before the members.
/// - witness: `tests::modules::member_signature_attaches_and_wins_over_derived_function_type`
/// - witness: `tests::modules::signatures_attach_to_their_defs`
/// - witness: `module::tests::structured_export_omits_invalid_segments_and_keeps_the_last_declared_name`
/// - witness: `tests::modules::opaque_ascription_seals`
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Role
{
    /// A name the source declared: a top-level definition or a module
    /// member.
    Declared,
    /// A second type stated for a member, checked by a declaration whose body
    /// is that member; or the kind a transparent ascription states for a type
    /// member, checked by a declaration whose body is that member's code.
    Witness,
    /// A slot that declares nothing: it carries a refusal a module or a
    /// signature component raised, or owns a manifest type component's type,
    /// and yields a declaration only when it holds a refusal.
    Held,
    /// An operation a `data` family declares and the module can call: entered
    /// in no namespace, its body compiled from its rules.
    Operation,
    /// The abstract type an opaque ascription declares for one abstract
    /// component of its signature: admitted before the module's members,
    /// entered in no name table, and named through the namespace as the atom
    /// it mints.
    Abstract,
    /// The words of a `data` family's loops at one point: the presented type a
    /// path at that point reads as, minted from the family's form and entered
    /// in no namespace.
    Words,
    /// A component of a functor's parameter: the template's stand-in for the
    /// argument's component, which each application renames and which
    /// declares nothing.
    Parameter,
}

/// One member of a module's body, or one component it exports.
///
/// # Specification
/// - requires: nothing to construct this data; its producers and consumers
///   state coordinate preconditions separately.
/// - ensures: Definition slots and nested structures occupy distinct
///   alternatives; their positions require the corresponding collection to
///   resolve.
/// - fails: not applicable to the data item.
/// - panics: not applicable to the data item.
/// - executable: none — the enabled specification facade does not expose
///   type-invariant expansion; executable predicates cover the producing and
///   consuming operations.
///
/// # Adequacy
/// - hypothesis: L3 — value and nested-module components project through
///   distinct member paths.
/// - witness: `tests::modules::nested_modules_lower_as_parent_members_and_project`
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Member
{
    /// A definition member, by its slot.
    Slot(SlotIndex),
    /// A nested module.
    Module(StructureIndex),
}

/// What one component of a module signature states.
///
/// # Specification
/// - requires: nothing to construct this data; its producers and consumers
///   state coordinate preconditions separately.
/// - ensures: Value signatures and manifest definitions retain their operands;
///   an abstract component retains its written kind, when it has one, and a
///   family its written kind or its derivation; a derived value component is
///   read off the model signature at its own place; unread type components
///   retain the specific ascription form rather than being treated as values.
/// - fails: not applicable to the data item.
/// - panics: not applicable to the data item.
/// - executable: none — the enabled specification facade does not expose
///   type-invariant expansion; executable predicates cover the producing and
///   consuming operations.
///
/// # Adequacy
/// - hypothesis: L3 — manifest, abstract, universe-kinded, family-kinded and
///   derived components have distinct outcomes.
/// - witness: `tests::modules::a_kinded_type_component_forms_at_its_classifier`
/// - witness: `tests::modules::a_manifest_family_component_binds_two_parameters`
/// - witness: `tests::modules::a_transparent_abstract_component_reads_its_type_member`
/// - witness: `tests::modules::an_abstract_component_kinds_at_a_universe`
/// - witness: `tests::modules::models::a_derived_signature_states_what_the_written_one_does`
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum ComponentForm
{
    /// A value component `x : T`, with its type.
    Value(Placed),
    /// A manifest type component `type T = τ`, with the type it names.
    Manifest(Placed),
    /// An abstract type component `type T` or `type T : κ`, with the kind
    /// written for it: its meaning is the body's type member of its name,
    /// sealed by an opaque ascription and strengthened by a transparent one.
    Abstract(Maybe<Placed, component_kind::Absent>),
    /// A type family component `type F : (a : A, …) => Type` or `type F : A ->
    /// … -> Type`, or an indexed sort a model signature derives: its meaning
    /// is the body's family member of its name.
    Family(FamilyForm),
    /// A manifest family component `type F(a : A, …) = τ`: its parameters'
    /// place among the collection's parameter lists, and the type it names
    /// over them.
    Parameterized
    {
        /// The parameters' place.
        parameters: ParameterList,
        /// The type the family names.
        defined: Placed,
    },
    /// A value component a model signature derives at the component's own
    /// place: an operation, a law, or a member the derivation cannot state.
    Derived,
    /// A type component the fragment does not read yet.
    Unread(AscriptionForm),
}

/// One component of a module signature, as written.
///
/// # Specification
/// - requires: nothing to construct this data; its producers and consumers
///   state coordinate preconditions separately.
/// - ensures: A written component associates its source spelling and name tile
///   with its value, manifest, abstract or unread form; the record does not
///   authenticate those coordinates.
/// - fails: not applicable to the data item.
/// - panics: not applicable to the data item.
/// - executable: none — the enabled specification facade does not expose
///   type-invariant expansion; executable predicates cover the producing and
///   consuming operations.
///
/// # Adequacy
/// - hypothesis: L3 — a reordered signature retains component names while
///   selecting its export order.
/// - witness: `tests::modules::a_reordered_signature_matches_and_canonicalizes`
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct Component<'source>
{
    /// The component's name.
    pub name: SurfaceName<'source>,
    /// The name's tile.
    pub named: Placed,
    /// What the component states.
    pub form: ComponentForm,
    /// Whether the signature marks it `mobile`, which only an abstract type
    /// component is written with.
    pub mark: Mark,
}

/// A type a module states by name — a manifest component, an abstract
/// component, or a body type member — kept for the module's stratum item and
/// for the types after it that name it.
///
/// # Specification
/// - requires: nothing to construct this data; its producers and consumers
///   state coordinate preconditions separately.
/// - ensures: A stated type carries the slot that owns its errors — the held
///   slot owning a written type, or the abstract slot an opaque ascription
///   declared — and what a reference to it reads; its meaning requires the
///   collection and source tree that produced it.
/// - fails: not applicable to the data item.
/// - panics: not applicable to the data item.
/// - executable: none — the enabled specification facade does not expose
///   type-invariant expansion; executable predicates cover the producing and
///   consuming operations.
///
/// # Adequacy
/// - hypothesis: L3 — earlier manifest components expand in later component
///   types, and a sealed component reads as its atom.
/// - witness: `tests::modules::a_manifest_type_component_expands_in_later_components`
/// - witness: `tests::modules::opaque_ascription_seals`
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct TypeComponent<'source>
{
    /// The component's name.
    pub name: SurfaceName<'source>,
    /// What a reference to it reads.
    pub meaning: TypeMeaning,
    /// The slot carrying its refusal: the held slot owning its written type,
    /// or the abstract slot declaring its atom.
    pub held: SlotIndex,
}

/// The type components a signature type sees: those of `structure` written
/// before the component the type belongs to.
///
/// # Specification
/// - requires: nothing to construct this data; its producers and consumers
///   state coordinate preconditions separately.
/// - ensures: The prefix length selects only preceding type components of the
///   named structure; the fields alone do not certify a live structure or
///   bounded prefix.
/// - fails: not applicable to the data item.
/// - panics: not applicable to the data item.
/// - executable: none — the enabled specification facade does not expose
///   type-invariant expansion; executable predicates cover the producing and
///   consuming operations.
///
/// # Adequacy
/// - hypothesis: L3 — type component order controls which definitions later
///   types can name.
/// - witness: `tests::modules::a_manifest_type_component_expands_in_later_components`
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ComponentScope
{
    /// The module whose signature the type is written in.
    pub structure: StructureIndex,
    /// How many of its type components precede the type.
    pub before: usize,
}

/// Whether matching against a signature coerced a module's body.
///
/// # Specification
/// - requires: nothing to construct this data; its producers and consumers
///   state coordinate preconditions separately.
/// - ensures: The flag records that signature matching selected the body
///   exports; the flag alone does not certify agreement with a particular
///   signature.
/// - fails: not applicable to the data item.
/// - panics: not applicable to the data item.
/// - executable: none — the enabled specification facade does not expose
///   type-invariant expansion; executable predicates cover the producing and
///   consuming operations.
///
/// # Adequacy
/// - hypothesis: L3 — a transparent ascription hides or reorders existing
///   exports.
/// - witness: `tests::modules::a_reordered_signature_matches_and_canonicalizes`
/// - witness: `tests::modules::module_signature_matching_hides_extra_members`
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Coerced(pub bool);

/// One module as the collection pass found it: a stratum item.
///
/// # Specification
/// - requires: nothing to construct this data; its producers and consumers
///   state coordinate preconditions separately.
/// - ensures: Collection records a module before its nested modules, keeps
///   source members separately from selected exports, records type components
///   in signature order and type members in source order, and maps each member
///   an opaque ascription restated to the witness a reference reads.
/// - fails: not applicable to the data item.
/// - panics: not applicable to the data item.
/// - executable: none — the enabled specification facade does not expose
///   type-invariant expansion; executable predicates cover the producing and
///   consuming operations.
///
/// # Adequacy
/// - hypothesis: L3 — nested admission order, hidden members and reordered
///   signatures distinguish these sequences.
/// - witness: `tests::modules::modules_lower_to_named_member_declarations`
/// - witness: `tests::modules::module_members_admit_in_source_order`
/// - witness: `tests::modules::a_readable_module_keeps_its_members_and_its_successor`
/// - witness: `tests::modules::a_reordered_signature_matches_and_canonicalizes`
/// - witness: `tests::modules::module_signature_matching_hides_extra_members`
/// - witness: `tests::modules::opaque_ascription_seals`
#[derive(Clone, Debug)]
pub struct Structure<'source>
{
    /// The module's own name.
    pub name: SurfaceName<'source>,
    /// Where the module is declared.
    pub container: Container,
    /// The module form.
    pub declared_by: Placed,
    /// The module's name tile.
    pub named: Placed,
    /// The inline signature's components, in signature order, when the
    /// module is ascribed.
    pub ascription: Maybe<Vec<Component<'source>>, ascription::Absent>,
    /// The model signature the ascription derives, `: Model(S)`, at its place
    /// in the collection's model list.
    pub model: Maybe<ModelIndex, derived::Absent>,
    /// Whether the ascription is opaque, `:>`, and seals what it hides.
    pub sealed: Sealed,
    /// The body's members, in source order.
    pub members: Vec<Member>,
    /// The components the module exports, in signature order once matched.
    pub exports: Vec<Member>,
    /// The type components, in signature order.
    pub types: Vec<TypeComponent<'source>>,
    /// The body's type members, `type T = τ ;`, in source order.
    pub type_members: Vec<TypeComponent<'source>>,
    /// Each exported member of an opaquely ascribed module whose own written
    /// type is not its component's, by the witness stating the component's
    /// type: a reference through the namespace reads the witness, so the
    /// member's own type does not leak past the seal.
    pub exported_as: BTreeMap<SlotIndex, SlotIndex>,
    /// Each record type an enclosing module's signature states this module
    /// at, in the order matched: a type the signature writes, lowered on its
    /// own so it answers for itself.
    pub stated_at: Vec<Placed>,
    /// Whether matching coerced the body.
    pub coerced: Coerced,
    /// What the module is in the stratum: a module, a functor's body or
    /// parameter, or an application's instance.
    pub stratum: Stratum,
}

/// What one half of a declared name lowers from.
///
/// # Specification
/// - requires: nothing to construct this data; its producers and consumers
///   state coordinate preconditions separately.
/// - ensures: A written operand uses its syntax form, a function uses the whole
///   declaration tail, a witness body names an existing member slot, and a data
///   declaration names its position in the collection's data list.
/// - fails: not applicable to the data item.
/// - panics: not applicable to the data item.
/// - executable: none — the enabled specification facade does not expose
///   type-invariant expansion; executable predicates cover the producing and
///   consuming operations.
///
/// # Adequacy
/// - hypothesis: L3 — ordinary halves and a signed-function witness lower
///   through their respective operands.
/// - witness: `module::tests::a_signature_pairs_with_its_definition`
/// - witness: `module::tests::a_definition_pairs_with_a_later_signature`
/// - witness: `tests::modules::member_signature_attaches_and_wins_over_derived_function_type`
/// - witness: `tests::modules::signatures_attach_to_their_defs`
/// - witness: `lower::native::tests::a_data_declaration_lowers_to_its_signature`
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Operand
{
    /// The one form written in the hole of `: T ;` or `= e ;`.
    Written(Placed),
    /// The function tail `(params) -> T? { … }`, lowered at the declaration
    /// form itself.
    Function,
    /// The member a witness re-states, whose constant is the witness's body.
    Member(SlotIndex),
    /// The data declaration `data T … { … }` at this position of the
    /// collection's data list, lowered at the declaration form itself.
    Data(usize),
    /// The words at this position of the collection's words list, minted
    /// from the loops of the data declaration that wrote this half.
    Words(usize),
    /// The loop of the words at `words` whose letter is the `generator`-th:
    /// the word of that one letter, at the path type of its point.
    Loop
    {
        /// The words' position in the collection's words list.
        words: usize,
        /// The loop's position among the words' loops.
        generator: usize,
    },
    /// An operation of the data declaration that wrote this half, its body
    /// compiled from its rules by the plan the collection keeps for its slot.
    Operation,
    /// A top-level `oper`, which lowers to no core term, a refusal held beside
    /// a `theory` block, or a root child that is no declaration: the half that
    /// carries the refusal and the expectation stating it.
    Signature,
    /// The `theory` block that defines its name as a value of `Theory`: the
    /// presentation it reads, minted from its value.
    Presented,
    /// `Theory`, the presentation code, decoded from its description rather
    /// than read from a written form.
    Code,
    /// The type a model signature derives for one of its value components,
    /// minted from the derivation rather than from a written form.
    Model(ModelPart),
    /// A world declaration `world w ;`, which lowers to no core term: the
    /// declaration's admission position is the world's identity.
    World,
}

/// One half of a declared name: the declaration form that wrote it and what
/// it lowers from.
///
/// # Specification
/// - requires: nothing to construct this data; its producers and consumers
///   state coordinate preconditions separately.
/// - ensures: Each half preserves the declaration that introduced its operand;
///   filing determines whether it is a signature, definition or checking
///   witness.
/// - fails: not applicable to the data item.
/// - panics: not applicable to the data item.
/// - executable: none — the enabled specification facade does not expose
///   type-invariant expansion; executable predicates cover the producing and
///   consuming operations.
///
/// # Adequacy
/// - hypothesis: L3 — signature and definition source orders pair by name and
///   duplicate halves retain the first.
/// - witness: `module::tests::a_signature_pairs_with_its_definition`
/// - witness: `module::tests::a_definition_pairs_with_a_later_signature`
/// - witness: `module::tests::a_second_signature_is_refused`
/// - witness: `module::tests::a_second_definition_is_refused`
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Half
{
    /// The declaration form.
    pub declaration: Placed,
    /// The name tile the form writes, or the form standing where a name
    /// belongs when it writes none: where a face going to this half lands.
    pub named: Placed,
    /// The declared type of a signature, or the body of a definition.
    pub operand: Operand,
}

/// The payload an attribute was written with.
///
/// # Specification
/// - requires: nothing to construct this data; its producers and consumers
///   state coordinate preconditions separately.
/// - ensures: An absent payload is distinct from an operand written in
///   parentheses; payload schema validation belongs to the attribute registry.
/// - fails: not applicable to the data item.
/// - panics: not applicable to the data item.
/// - executable: none — the enabled specification facade does not expose
///   type-invariant expansion; executable predicates cover the producing and
///   consuming operations.
///
/// # Adequacy
/// - hypothesis: L3 — a concrete payload remains attached to its declaration
///   and span.
/// - witness: `lower::tests::an_attribute_is_filed_under_its_declaration_key`
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Payload
{
    /// No payload was written, or the parentheses hold nothing.
    Unwritten,
    /// The form written between the parentheses.
    Written(Placed),
}

/// One attribute as the declaration form wrote it.
///
/// # Specification
/// - requires: nothing to construct this data; its producers and consumers
///   state coordinate preconditions separately.
/// - ensures: The reading associates a spelling, name tile, enclosing attribute
///   span and optional payload with the decorated declaration position.
/// - fails: not applicable to the data item.
/// - panics: not applicable to the data item.
/// - executable: none — the enabled specification facade does not expose
///   type-invariant expansion; executable predicates cover the producing and
///   consuming operations.
///
/// # Adequacy
/// - hypothesis: L3 — adjacent attribute blocks retain their order and concrete
///   payloads retain their own syntax.
/// - witness: `module::tests::an_attribute_block_decorates_the_declaration_after_it`
/// - witness: `lower::tests::an_attribute_is_filed_under_its_declaration_key`
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct WrittenAttribute<'source>
{
    /// The attribute's name as it was written.
    pub name: SurfaceName<'source>,
    /// The name's tile.
    pub at: Placed,
    /// The bytes the attribute covers: its name, through the closing
    /// parenthesis when it has a payload.
    pub span: ByteSpan,
    /// The payload it was written with.
    pub payload: Payload,
    /// The declaration form the attribute decorates.
    pub decorates: NodeIndex,
}

/// One piece of documentation a declaration form wrote before itself: a run
/// of `///` lines or a `doc("…")` entry, grouped by the parser.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct WrittenDoc
{
    /// The documentation node.
    pub at: Placed,
    /// The declaration form it documents.
    pub documents: NodeIndex,
}

/// One name's declarations, as the collection pass found them.
///
/// # Specification
/// - requires: nothing to construct this data; its producers and consumers
///   state coordinate preconditions separately.
/// - ensures: A collected slot retains its first admission position, at most
///   one stored half of each kind, source-ordered accepted attributes, and the
///   first refusal offered at the minimum syntax position.
/// - fails: not applicable to the data item.
/// - panics: not applicable to the data item.
/// - executable: none — the enabled specification facade does not expose
///   type-invariant expansion; executable predicates cover the producing and
///   consuming operations.
///
/// # Adequacy
/// - hypothesis: L3 — pairing, duplicates and independently routed refusals
///   separate slot state from source name.
/// - witness: `module::tests::a_signature_pairs_with_its_definition`
/// - witness: `module::tests::a_definition_pairs_with_a_later_signature`
/// - witness: `module::tests::a_second_signature_is_refused`
/// - witness: `module::tests::a_second_definition_is_refused`
/// - witness: `module::tests::ownership_routes_refusals_without_touching_other_slots`
/// - witness: `module::tests::the_lowest_positioned_refusal_is_the_one_kept`
#[derive(Clone, Debug)]
pub struct DeclarationSlot<'source>
{
    /// The declared name.
    pub name: SurfaceName<'source>,
    /// Where the name is declared.
    pub container: Container,
    /// What the slot stands for.
    pub role: Role,
    /// The admission position this name takes.
    pub constant: ConstantIndex,
    /// The declaration form that introduced the name.
    pub introduced_by: Placed,
    /// The name tile of that form.
    pub named: Placed,
    /// This name's signature, when it has one.
    pub signature: Maybe<Half, declaration_half::Absent>,
    /// This name's definition, when it has one.
    pub definition: Maybe<Half, declaration_half::Absent>,
    /// The attributes decorating this name's declarations, in source order.
    pub attributes: Vec<WrittenAttribute<'source>>,
    /// The documentation written for this name's declarations, in source
    /// order.
    pub docs: Vec<WrittenDoc>,
    /// The lowest-positioned refusal found for this name so far.
    pub refusal: Maybe<(NodeIndex, LoweringRefusal<'source>), slot_refusal::Absent>,
}

impl<'source> DeclarationSlot<'source>
{
    /// Keep `refusal` when it sits below every refusal already found.
    ///
    /// # Specification
    /// - requires: `at` is the arena position of the node that refused.
    /// - ensures: the slot keeps the first refusal offered at the lowest
    ///   position. Higher or equal positions leave it unchanged; ordering is
    ///   independent across distinct positions, while a tie keeps the first
    ///   offer at that node.
    /// - provides: the one-refusal-per-declaration rule, decided in one place
    ///   rather than at each refusing site.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — one comparison, separated by an offer into an empty
    ///   slot, a strictly lower offer that must replace, a strictly higher
    ///   offer that must not, and an offer at the incumbent's own position,
    ///   each asserted as the exact retained refusal.
    /// - witness: `module::tests::the_lowest_positioned_refusal_is_the_one_kept`
    #[spec(
        captures: before = self.refusal,
        ensures: self.refusal
            == match before {
                | Maybe::Present((position, _)) if position <= at => before,
                | Maybe::Present(_) | Maybe::Absent(_) => Maybe::Present((at, refusal)),
            },
    )]
    #[inline]
    pub fn refuse(
        &mut self,
        at: NodeIndex,
        refusal: LoweringRefusal<'source>,
    )
    {
        let replaces = match self.refusal {
            Maybe::Present((incumbent, _held)) => at < incumbent,
            Maybe::Absent(_) => true,
        };
        if replaces {
            self.refusal = Maybe::Present((at, refusal));
        }
    }

    /// Whether this slot already holds a refusal.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: affirmative exactly when a refusal is already retained.
    /// - provides: the declaration-local skip decision.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — initially empty refusal storage, lower replacement,
    ///   higher rejection and equal-position stability preserve the chosen
    ///   refusal.
    /// - witness: `module::tests::the_lowest_positioned_refusal_is_the_one_kept`
    #[spec(
        ensures: |ret| ret.0 == matches!(self.refusal, Maybe::Present(_)),
    )]
    #[inline]
    #[must_use]
    pub const fn refused(&self) -> SlotRefused
    {
        SlotRefused(matches!(self.refusal, Maybe::Present(_)))
    }
}

/// Whether a declaration slot already holds a refusal.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct SlotRefused(pub bool);

/// A module's declarations as the collection pass found them, with the slot
/// every declaration form belongs to, and its imports.
///
/// # Specification
/// - requires: nothing to construct this data; its producers and consumers
///   state coordinate preconditions separately.
/// - ensures: Successful collection indexes live slots and structures,
///   distinguishes named slots from held and witness slots, and routes
///   syntax-owned failures without changing admission positions.
/// - fails: not applicable to the data item.
/// - panics: not applicable to the data item.
/// - executable: none — the enabled specification facade does not expose
///   type-invariant expansion; executable predicates cover the producing and
///   consuming operations.
///
/// # Adequacy
/// - hypothesis: L3 — nested collection and independent refusal routing
///   preserve the table relationships.
/// - witness: `tests::modules::modules_lower_to_named_member_declarations`
/// - witness: `tests::modules::module_members_admit_in_source_order`
/// - witness: `tests::modules::a_readable_module_keeps_its_members_and_its_successor`
/// - witness: `module::tests::ownership_routes_refusals_without_touching_other_slots`
#[derive(Clone, Debug)]
pub struct Collected<'source>
{
    /// Descriptions keyed by their written declaration, sharing the normal
    /// slots.
    pub descriptions: BTreeMap<NodeIndex, crate::description::DescribedDeclaration>,
    /// Member-local diagnostics retained independently of native admission.
    pub description_diagnostics: Vec<crate::description::DescriptionDiagnostic>,
    /// The data families the native reading owns whole, where their members
    /// are written.
    pub natives: Vec<crate::description::NativeFamily>,
    /// Cell stores and their independently retained member refusals.
    pub cells: crate::desc_cells::CellReport,
    /// The slots, in admission order.
    pub slots: Vec<DeclarationSlot<'source>>,
    /// Each arena position's owning slot, where it has one.
    pub owner: Vec<Maybe<SlotIndex, slot_owner::Absent>>,
    /// Each declared name's slot by where it is declared, for the term-name
    /// resolution table.
    pub by_name: BTreeMap<(Container, SurfaceName<'source>), SlotIndex>,
    /// The modules, in pre-order: a module before every module nested in it.
    pub structures: Vec<Structure<'source>>,
    /// Each module's position by where it is declared.
    pub modules: BTreeMap<(Container, SurfaceName<'source>), StructureIndex>,
    /// Every signature type's root, with the manifest type components it
    /// sees.
    pub scopes: Vec<(NodeIndex, ComponentScope)>,
    /// The imports, in source order, with their aliases bound.
    pub imports: ModuleImports<'source>,
    /// The sources the tree lays end to end, and what their imports name.
    pub unit: Unit,
    /// The data declarations, in source order.
    pub data: Vec<DataForm>,
    /// The words of the data declarations' loops, one per point, in the order
    /// they are admitted.
    pub words: Vec<WordsForm>,
    /// Every constructor a data declaration declares, by the source declaring
    /// it and its name.
    pub constructors: BTreeMap<(SourceIndex, SurfaceName<'source>), Constructor>,
    /// Each callable operation's plan, by its slot.
    pub operations: BTreeMap<SlotIndex, crate::operation::OperationPlan>,
    /// Each callable operation's slot, by the source declaring it and its
    /// name: operations are declared at the top level only.
    pub operation_names: BTreeMap<(SourceIndex, SurfaceName<'source>), SlotIndex>,
    /// Each abstract component's slot — the abstract type an opaque
    /// ascription declares, or the witness checking the kind a transparent
    /// one states — with what the slot is built from.
    pub abstracts: BTreeMap<SlotIndex, AbstractSlot>,
    /// Every top-level module an attribute block decorates, in source order.
    pub decorated: Vec<DecoratedModule<'source>>,
    /// Every module form's documentation, each piece documenting its module
    /// form, in source order: a module is no slot, so its documentation is
    /// kept beside the slots' rather than in one (#1135).
    pub module_docs: Vec<WrittenDoc>,
    /// The type family members, `type F(a : A, …) = τ ;`, and the manifest
    /// family components signatures state, in the order they are matched.
    pub families: Vec<FamilyMember>,
    /// The parameters of each manifest family component a signature writes,
    /// `type F(a : A, …) = τ`, in reading order.
    pub parameter_lists: Vec<Vec<FamilyParameter>>,
    /// The model signatures ascriptions derive, in the order their modules
    /// open.
    pub models: Vec<crate::model::ModelSignature>,
    /// Each family component's check slot — the witness checking a written
    /// kind, or the held slot of a derived sort — with what it compares.
    pub family_checks: BTreeMap<SlotIndex, FamilyCheck>,
    /// The functors, in source order: each a template its applications
    /// rename.
    pub functors: Vec<Functor<'source>>,
    /// The applications, in source order: each an instance of a functor.
    pub instances: Vec<Instance<'source>>,
    /// `Theory`, the presentation code, when a `theory` block that refuses
    /// nothing has minted it.
    pub theory: Maybe<TheorySlot, theory_slot::Absent>,
    /// The sources whose `theory` blocks take `Theory`: the source that minted
    /// it and every later source holding a block, each of which enters the
    /// code's constructors under its own names.
    pub theory_sources: BTreeSet<SourceIndex>,
    /// The mutual blocks, in source order: each the run of slots its members
    /// took, admitted as one block.
    pub blocks: Vec<MutualBlock>,
    /// The slots declared `def rec`: in a mutual block, its recursive
    /// functions recurse through one another.
    pub recursive: BTreeSet<SlotIndex>,
    /// The merged telescope of each function whose implicit telescope binds a
    /// value, by its slot: every parameter in the order the declared type
    /// binds it, with where it is written; or the refusal the merge met,
    /// which the function's lowering raises.
    pub plicities:
        BTreeMap<SlotIndex, Result<Vec<TelescopeEntry<'source>>, LoweringRefusal<'source>>>,
    /// The stage binders of each function quantified over stages, by its
    /// slot: each binder's name in written order, its position the ordinal of
    /// the stage the checker mints for it.
    pub stage_binders: BTreeMap<SlotIndex, Vec<SurfaceName<'source>>>,
    /// Each method, by its slot: a module member whose first parameter is
    /// `self`, written with its type, with the mode that parameter is written
    /// at. A call `s.f(…)` selects one off its receiver `s`.
    pub receivers: BTreeMap<SlotIndex, ReceiverMode>,
    /// Each declaration's name the collection resolved where it is written,
    /// beside the slot it names: a model ascription's theory and a `theory`
    /// block's include.
    pub declared_uses: Vec<(ByteSpan, SlotIndex)>,
    /// The bytes of each import a name lookup was answered through.
    pub reached: BTreeSet<ByteSpan>,
}

quenchant_shape::reason_enum! {
    /// Why a source's imports answer no name.
    pub mod imported {
        /// The reason nothing answers.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// No source the source imports unqualified declares the name.
            Unbound,
        }
    }
}

/// Two unqualified imports of one source binding one name to two
/// declarations.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct Ambiguity
{
    /// The bytes of the later import.
    pub import: ByteSpan,
    /// The bytes of the earlier import.
    pub other: ByteSpan,
}

quenchant_shape::reason_enum! {
    /// Why a module holds no `Theory`.
    pub mod theory_slot {
        /// The reason the module minted no `Theory`.
        #[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
        pub enum Absent {
            /// No `theory` block that refuses nothing stands in the module.
            Unminted,
            /// No `theory` block stands in the source the name is read in,
            /// nor in a source it imports unqualified.
            Unseen,
        }
    }
}

/// `Theory`, the presentation code, as a module mints it: the slot it takes,
/// the field count of each of its constructors, in tag order, and the name tile
/// of the block that minted it.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: the slot is a declared one named `Theory`; the arities follow the
///   description's constructor table.
/// - executable: none — the slot index holds no table to check it against.
///
/// # Adequacy
/// - hypothesis: L3 — a module with a theory that refuses nothing mints
///   `Theory` once, before the theory's own slot, and a generic program matches
///   on it; a later source's block takes the same code.
/// - witness: `description::theory::tests::a_theory_block_defines_its_presentation`
/// - witness: `tests::namespace::a_theory_lowers_alike_whatever_the_unit_lays_before_it_1078`
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct TheorySlot
{
    /// The slot `Theory` takes.
    pub slot: SlotIndex,
    /// Each constructor's field count, in tag order.
    pub arities: Vec<usize>,
    /// The name tile of the block that minted the code, where each of its
    /// constructors is entered as declared.
    pub named: Placed,
}

/// A mutual block `rec { … }` and the run of slots its members took.
///
/// # Specification
/// - requires: nothing to construct this data; the collection produces it.
/// - ensures: the slots from `first` up to `end` are the block's members, in
///   source order, and nothing else.
/// - executable: none — the slot range holds no table to check it against.
///
/// # Adequacy
/// - hypothesis: L3 — a block of a data declaration and its decoder takes two
///   consecutive slots, and a declaration after it takes none of the block's.
/// - witness: `module::tests::a_mutual_block_collects_its_members_as_one_run`
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct MutualBlock
{
    /// The block form.
    pub form: Placed,
    /// The first slot a member took.
    pub first: SlotIndex,
    /// The slot after the last a member took.
    pub end: SlotIndex,
}

/// A top-level module an attribute block decorates, with the slots of the
/// members its attributes reach.
///
/// # Specification
/// - requires: nothing to construct this data; the collection produces it.
/// - ensures: every attribute decorates the module form; the member slots are
///   the ones the module's collection admitted, nested modules' included.
/// - fails: not applicable to the data item.
/// - panics: not applicable to the data item.
///
/// # Adequacy
/// - hypothesis: L3 — a decorated module of two members and an undecorated
///   declaration after it, the attribute reaching the members only.
/// - witness: `lower::exits::tests::an_explicit_exits_attribute_asks_within_its_form`
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct DecoratedModule<'source>
{
    /// The module form.
    pub module: Placed,
    /// The attributes written before it, in source order.
    pub attributes: Vec<WrittenAttribute<'source>>,
    /// The first slot its collection admitted.
    pub first: SlotIndex,
    /// The slot after the last its collection admitted.
    pub end: SlotIndex,
}

impl<'source> Collected<'source>
{
    /// The slot owning `position`.
    ///
    /// # Specification
    /// - requires: nothing — an out-of-range node position is admissible.
    /// - ensures: a stored owner is returned exactly; an unowned or
    ///   out-of-range position answers unowned.
    /// - provides: node-to-declaration routing without allocating.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — owned, unowned and out-of-range positions distinguish
    ///   routing from the absence of a declaration owner.
    /// - witness: `module::tests::an_attribute_block_decorates_the_declaration_after_it`
    /// - witness: `module::tests::ownership_routes_refusals_without_touching_other_slots`
    #[spec(
        ensures: |ret| {
            ret == self
                .owner
                .get(usize::from(position))
                .copied()
                .unwrap_or(Maybe::Absent(slot_owner::Absent::Unowned))
        },
    )]
    #[inline]
    pub fn owner_of(
        &self,
        position: NodeIndex,
    ) -> Maybe<SlotIndex, slot_owner::Absent>
    {
        self.owner
            .get(usize::from(position))
            .copied()
            .unwrap_or(Maybe::Absent(slot_owner::Absent::Unowned))
    }

    /// The mutual block whose run of slots holds `slot`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the block of [`Self::blocks`] whose slots from `first` up to
    ///   `end` hold `slot`; [`mutual_block::Absent::Outside`] when none does.
    /// - provides: the one-block test name resolution makes, where members name
    ///   one another in any order.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the answer is the walk itself; a clause restating
    ///   it would walk the blocks again.
    ///
    /// # Clause cost
    /// - bound: walks the module's blocks once; every block holds a slot of its
    ///   own, so no more steps than the module has declarations.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — members of one block name one another in either
    ///   order, and a declaration after the block does not reach into it.
    /// - witness: `lower::native::tests::a_mutual_blocks_recursive_functions_share_one_fixpoint`
    /// - witness: `module::tests::a_mutual_block_collects_its_members_as_one_run`
    #[inline]
    pub fn block_of(
        &self,
        slot: SlotIndex,
    ) -> Maybe<MutualBlock, mutual_block::Absent>
    {
        self.blocks
            .iter()
            .find(|block| (block.first .. block.end).contains(&slot))
            .copied()
            .map_or(Maybe::Absent(mutual_block::Absent::Outside), Maybe::Present)
    }

    /// The top level of the source whose text holds `offset`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn top(
        &self,
        offset: ByteOffset,
    ) -> Container
    {
        Container::TopLevel(self.unit.source_at(offset))
    }

    /// The top-level declaration `source`'s unqualified imports answer `name`
    /// with, and the import that answers it.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the slot one source `source` imports unqualified declares at
    ///   its top level under `name`, with that import's bytes; two such imports
    ///   answering two slots are [`Ambiguity`], naming both imports; an import
    ///   whose address did not resolve to a source of the unit answers nothing.
    ///   Imports are not re-exported: only the imported source's own
    ///   declarations answer.
    /// - provides: the import fallback of every top-level name lookup.
    /// - fails: [`Ambiguity`] for two imports binding one name.
    /// - panics: none.
    ///
    /// # Errors
    /// [`Ambiguity`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a name one import binds, a name two bind, and a name
    ///   only an import of the imported source binds, each answered exactly.
    /// - witness: `tests::namespace::an_unqualified_import_answers_a_name_its_source_declares`
    /// - witness: `tests::namespace::two_imports_binding_one_name_refuse_its_use`
    #[spec(ensures: |ref ret| match *ret {
        Ok(Maybe::Present((slot, _))) => self.slots.get(usize::from(slot)).is_some(),
        Ok(Maybe::Absent(_)) => true,
        Err(ref ambiguity) => ambiguity.import != ambiguity.other,
    })]
    pub fn imported_slot(
        &self,
        source: SourceIndex,
        name: SurfaceName<'source>,
    ) -> Result<Maybe<(SlotIndex, ByteSpan), imported::Absent>, Ambiguity>
    {
        self.through_imports(source, |target| {
            self.by_name
                .get(&(Container::TopLevel(target), name))
                .copied()
        })
    }

    /// The code the name `Theory` reads in `source`, where no declaration of
    /// the source or of its imports binds it.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the slot of the unit's `Theory` when `source`, or a source
    ///   one of its unqualified imports resolves to, stands among
    ///   [`Self::theory_sources`]; [`theory_slot::Absent::Unminted`] when the
    ///   unit holds no code; [`theory_slot::Absent::Unseen`] otherwise. The
    ///   answer does not depend on which of those sources minted the code, so a
    ///   source names `Theory` alike whatever the unit lays before it.
    /// - provides: the fallback that resolves `Theory` in a source whose block
    ///   took the code another source minted, and in its importers.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a source behind a block it does not import, and one
    ///   importing two sources that hold blocks, each name the one code.
    /// - witness: `tests::namespace::a_theory_lowers_alike_whatever_the_unit_lays_before_it_1078`
    #[spec(ensures: |ref ret| match *ret {
        Maybe::Present(slot) => matches!(self.theory, Maybe::Present(ref theory) if theory.slot == slot),
        Maybe::Absent(_) => true,
    })]
    pub fn theory_in(
        &self,
        source: SourceIndex,
    ) -> Maybe<SlotIndex, theory_slot::Absent>
    {
        let Maybe::Present(ref theory) = self.theory
        else {
            return Maybe::Absent(theory_slot::Absent::Unminted);
        };
        let holds = |held: SourceIndex| self.theory_sources.contains(&held);
        let imported = self.imports.of(source).any(|import| {
            matches!(
                (import.binding(), import.resolution()),
                (ImportBinding::Unqualified, ImportResolution::Path(ImportTarget::Source(target)))
                    if holds(target)
            )
        });
        if holds(source) || imported {
            Maybe::Present(theory.slot)
        }
        else {
            Maybe::Absent(theory_slot::Absent::Unseen)
        }
    }

    /// The constructor `source`'s unqualified imports answer `name` with, and
    /// the import that answers it.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: as [`Self::imported_slot`], over the constructors each
    ///   imported source declares.
    /// - provides: the import fallback of constructor lookup.
    /// - fails: [`Ambiguity`] for two imports binding one constructor name.
    /// - panics: none.
    ///
    /// # Errors
    /// [`Ambiguity`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an imported family's constructor in a case arm and a
    ///   value, answered exactly.
    /// - witness: `tests::namespace::an_unqualified_import_answers_a_name_its_source_declares`
    #[spec(ensures: |ref ret| match *ret {
        Ok(_) => true,
        Err(ref ambiguity) => ambiguity.import != ambiguity.other,
    })]
    pub fn imported_constructor(
        &self,
        source: SourceIndex,
        name: SurfaceName<'source>,
    ) -> Result<Maybe<(Constructor, ByteSpan), imported::Absent>, Ambiguity>
    {
        self.through_imports(source, |target| {
            self.constructors.get(&(target, name)).copied()
        })
    }

    /// What `lookup` answers in the sources `source` imports unqualified.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: as [`Self::imported_slot`], `lookup` standing for the table
    ///   read in each imported source.
    /// - fails: [`Ambiguity`] for two imports answering two values.
    /// - panics: none.
    ///
    /// # Errors
    /// [`Ambiguity`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the two entries above.
    /// - witness: `tests::namespace::two_imports_binding_one_name_refuse_its_use`
    #[spec(ensures: |ref ret| match *ret {
        Ok(_) => true,
        Err(ref ambiguity) => ambiguity.import != ambiguity.other,
    })]
    fn through_imports<Found, Lookup>(
        &self,
        source: SourceIndex,
        lookup: Lookup,
    ) -> Result<Maybe<(Found, ByteSpan), imported::Absent>, Ambiguity>
    where
        Found: Copy + Eq,
        Lookup: Fn(SourceIndex) -> Option<Found>,
    {
        let mut answered: Maybe<(Found, ByteSpan), imported::Absent> =
            Maybe::Absent(imported::Absent::Unbound);
        for import in self.imports.of(source) {
            let (ImportBinding::Unqualified, ImportResolution::Path(ImportTarget::Source(target))) =
                (import.binding(), import.resolution())
            else {
                continue;
            };
            let Some(found) = lookup(target)
            else {
                continue;
            };
            match answered {
                Maybe::Present((held, first)) if held != found => {
                    return Err(Ambiguity {
                        import: import.span(),
                        other: first,
                    });
                },
                Maybe::Present(_) => {},
                Maybe::Absent(_) => answered = Maybe::Present((found, import.span())),
            }
        }
        Ok(answered)
    }

    /// The import of `source` that makes the unit's theory code visible to
    /// it, when [`Self::theory_in`] answers through one.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the bytes of the first unqualified import of `source`
    ///   resolving to a source among [`Self::theory_sources`]; none when
    ///   `source` stands among them itself or no import reaches one.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the answer is a search of the receiver's imports.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`LoweredModule::reached_imports`].
    /// - witness: `tests::namespace::each_import_a_name_is_read_through_is_reached`
    #[must_use]
    pub fn theory_import(
        &self,
        source: SourceIndex,
    ) -> Option<ByteSpan>
    {
        if self.theory_sources.contains(&source) {
            return None;
        }
        self.imports
            .of(source)
            .find(|import| {
                matches!(
                    (import.binding(), import.resolution()),
                    (ImportBinding::Unqualified, ImportResolution::Path(ImportTarget::Source(target)))
                        if self.theory_sources.contains(&target)
                )
            })
            .map(ImportDeclaration::span)
    }

    /// Record that a name lookup was answered through the import written at
    /// `import`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: `import` is among the reached imports.
    /// - provides: the record [`LoweredModule::reached_imports`] answers.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — membership is a search of the receiver's set.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`LoweredModule::reached_imports`].
    /// - witness: `tests::namespace::each_import_a_name_is_read_through_is_reached`
    pub fn reach(
        &mut self,
        import: ByteSpan,
    )
    {
        let _fresh = self.reached.insert(import);
    }

    /// Record every import of `source` whose target, or a source the target
    /// imports in turn, declares a module named `head` at its top level.
    ///
    /// A dotted path is read in the unit's one outermost scope, so its head
    /// may be a module of a source `source` reaches only through another: the
    /// import that brought it into the unit is the one the path needs.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: each import of `source` resolving to a source whose import
    ///   closure, itself included, holds a top-level module `head` is among the
    ///   reached imports.
    /// - provides: the reach of a path read in the outermost scope.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — membership is a search of the receiver's set.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a module member read through a direct import and
    ///   through an import of an import.
    /// - witness: `tests::namespace::each_import_a_name_is_read_through_is_reached`
    pub fn reach_declaring(
        &mut self,
        source: SourceIndex,
        head: SurfaceName<'source>,
    )
    {
        let mut reached = Vec::new();
        for import in self.imports.of(source) {
            let ImportResolution::Path(ImportTarget::Source(target)) = import.resolution()
            else {
                continue;
            };
            let mut seen: BTreeSet<SourceIndex> = BTreeSet::new();
            let mut pending = Vec::from([target]);
            while let Some(at) = pending.pop() {
                if !seen.insert(at) {
                    continue;
                }
                if self.modules.contains_key(&(Container::TopLevel(at), head)) {
                    reached.push(import.span());
                    break;
                }
                pending.extend(self.imports.of(at).filter_map(
                    |further| match further.resolution() {
                        ImportResolution::Path(ImportTarget::Source(next)) => Some(next),
                        ImportResolution::Path(ImportTarget::Unresolved | ImportTarget::Cycle)
                        | ImportResolution::Foreign => None,
                    },
                ));
            }
        }
        self.reached.extend(reached);
    }

    /// Record every import of `source` resolving to `target`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: each import of `source` whose address resolved to `target` is
    ///   among the reached imports.
    /// - provides: the reach of a method or an included theory a sibling source
    ///   declares.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — membership is a search of the receiver's set.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a method an imported source declares, called.
    /// - witness: `tests::namespace::each_import_a_name_is_read_through_is_reached`
    pub fn reach_source(
        &mut self,
        source: SourceIndex,
        target: SourceIndex,
    )
    {
        let reached: Vec<ByteSpan> = self
            .imports
            .of(source)
            .filter(|import| {
                import.resolution() == ImportResolution::Path(ImportTarget::Source(target))
            })
            .map(ImportDeclaration::span)
            .collect();
        self.reached.extend(reached);
    }

    /// Give `position` to `slot`.
    ///
    /// # Specification
    /// - requires: slot names a live declaration slot.
    /// - ensures: an in-range owner entry becomes slot; an out-of-range node
    ///   position changes nothing.
    /// - provides: the ownership relation that routes descendant refusals.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — ownership assignment redirects one node while leaving
    ///   other nodes, unowned positions and out-of-range lookups distinct.
    /// - witness: `module::tests::ownership_routes_refusals_without_touching_other_slots`
    #[spec(
        requires: slot.0 < self.slots.len(),
        captures: before = self.owner.len(),
        ensures: self.owner.len() == before
            && self
                .owner
                .get(usize::from(position))
                .is_none_or(|held| *held == Maybe::Present(slot)),
    )]
    #[inline]
    pub fn own(
        &mut self,
        position: NodeIndex,
        slot: SlotIndex,
    )
    {
        if let Some(held) = self.owner.get_mut(usize::from(position)) {
            *held = Maybe::Present(slot);
        }
    }

    /// Offer `refusal`, found at `position`, to the slot owning `position`.
    ///
    /// # Specification
    /// - requires: `position` is the node that refused.
    /// - ensures: the owning slot keeps the lower-positioned of the refusal it
    ///   held and this one; a position no slot owns drops the refusal, which
    ///   only a node outside every declaration can be.
    /// - provides: the routing of every refusal found inside a declaration.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — two slots receive independent offers; lower positions
    ///   win, ties keep the incumbent, and unowned nodes change neither slot.
    /// - witness: `module::tests::ownership_routes_refusals_without_touching_other_slots`
    /// - witness: `module::tests::the_lowest_positioned_refusal_is_the_one_kept`
    #[spec(
        captures: before = (
            self.slots.len(),
            self.owner.len(),
            self.owner_of(position),
            match self.owner_of(position) {
                | Maybe::Present(slot) => self
                    .slots
                    .get(slot.0)
                    .map_or(Maybe::Absent(slot_refusal::Absent::Unrefused), |entry| {
                        entry.refusal
                    }),
                | Maybe::Absent(_) => Maybe::Absent(slot_refusal::Absent::Unrefused),
            },
        ),
        ensures: self.slots.len() == before.0
            && self.owner.len() == before.1
            && self.owner_of(position) == before.2
            && match before.2 {
                | Maybe::Absent(_) => true,
                | Maybe::Present(slot) => self.slots.get(slot.0).is_none_or(|entry| {
                    entry.refusal
                        == match before.3 {
                            | Maybe::Present((at, _)) if at <= position => before.3,
                            | Maybe::Present(_) | Maybe::Absent(_) => {
                                Maybe::Present((position, refusal))
                            },
                        }
                }),
            },
    )]
    #[inline]
    pub fn offer(
        &mut self,
        position: NodeIndex,
        refusal: LoweringRefusal<'source>,
    )
    {
        let Maybe::Present(slot) = self.owner_of(position)
        else {
            return;
        };
        if let Some(entry) = self.slots.get_mut(slot.0) {
            entry.refuse(position, refusal);
        }
    }

    /// Whether the declaration owning `position` already holds a refusal.
    ///
    /// # Specification
    /// - requires: nothing — a position no declaration owns is admissible
    ///   input.
    /// - ensures: affirmative exactly when the owning declaration already holds
    ///   a refusal, so a refused declaration's subtree is left unminted outside
    ///   its attribute payloads.
    /// - provides: the skip test the mint sweep takes.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — refusal routes to its owning slot only; unowned and
    ///   out-of-range positions do not report another declaration's failure.
    /// - witness: `module::tests::ownership_routes_refusals_without_touching_other_slots`
    #[spec(
        ensures: |ret| {
            ret.0
                == match self.owner_of(position) {
                    | Maybe::Absent(_) => false,
                    | Maybe::Present(slot) => self
                        .slots
                        .get(slot.0)
                        .is_some_and(|entry| matches!(entry.refusal, Maybe::Present(_))),
                }
        },
    )]
    #[inline]
    #[must_use]
    pub fn refused(
        &self,
        position: NodeIndex,
    ) -> SlotRefused
    {
        let Maybe::Present(slot) = self.owner_of(position)
        else {
            return SlotRefused(false);
        };

        self.slots
            .get(slot.0)
            .map_or(SlotRefused(false), DeclarationSlot::refused)
    }

    /// The path of the modules enclosing a name declared in `container`,
    /// outermost first; empty at the top level.
    ///
    /// # Specification
    /// - requires: every module index reachable from `container` names a
    ///   collected module.
    /// - ensures: the names of the modules from the outermost to `container`'s
    ///   own, walked up by an explicit loop; a module index the collection does
    ///   not hold ends the walk.
    /// - provides: a declaration's structured name, less its own segment.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — top-level and deeply nested declarations have exact
    ///   outermost-first names, independent of witness and held slots.
    /// - witness: `tests::modules::modules_lower_to_named_member_declarations`
    /// - witness: `tests::modules::deeply_nested_modules_lower_and_resolve_at_every_depth`
    #[spec(
        ensures: |ret| {
            let mut current = container;
            let mut names = ret.iter().rev();
            let mut walked = 0_usize;
            while let Container::Module(index) = current {
                let Some(module) = self.structures.get(index.0)
                else {
                    break;
                };
                if walked >= self.structures.len() || names.next() != Some(&module.name) {
                    return false;
                }
                walked = walked.saturating_add(1);
                current = module.container;
            }
            names.next().is_none()
        },
    )]
    #[must_use]
    pub fn path(
        &self,
        container: Container,
    ) -> Vec<SurfaceName<'source>>
    {
        let mut path = Vec::new();
        let mut at = container;
        while let Container::Module(index) = at
            && let Some(structure) = self.structures.get(index.0)
        {
            path.push(structure.name);
            at = structure.container;
        }
        path.reverse();

        path
    }

    /// What the module a declaration in `container` belongs to is in the
    /// stratum: the innermost enclosing functor's body or parameter, or
    /// application's instance, a plain module otherwise.
    ///
    /// # Specification
    /// - requires: `container` is a container of this collection.
    /// - ensures: walking out from `container` by an explicit loop, the first
    ///   module whose stratum is not [`Stratum::Module`] gives its stratum; the
    ///   top level, or a module index the collection does not hold, ends the
    ///   walk at [`Stratum::Module`].
    /// - provides: the template and instance test [`crate::lower`] reads for
    ///   every slot.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a member of a functor's body, of a module nested in
    ///   it, of its parameter, and of an application's instance each read their
    ///   own stratum, and a top-level declaration reads a module.
    /// - witness: `tests::modules::functors::a_functor_body_never_reaches_the_kernel`
    /// - witness: `tests::modules::functors::two_applications_mint_distinct_atoms`
    #[spec(
        ensures: |ret| {
            let mut current = container;
            let mut walked = 0_usize;
            while let Container::Module(index) = current
                && let Some(module) = self.structures.get(index.0)
                && walked <= self.structures.len()
            {
                if module.stratum != Stratum::Module {
                    return ret == module.stratum;
                }
                walked = walked.saturating_add(1);
                current = module.container;
            }
            ret == Stratum::Module
        },
    )]
    #[must_use]
    pub fn stratum_of(
        &self,
        container: Container,
    ) -> Stratum
    {
        let mut at = container;
        while let Container::Module(index) = at
            && let Some(structure) = self.structures.get(index.0)
        {
            if structure.stratum != Stratum::Module {
                return structure.stratum;
            }
            at = structure.container;
        }

        Stratum::Module
    }
}

/// Which half of a declared name a declaration form writes.
///
/// # Specification
/// - requires: nothing to construct this data; its producers and consumers
///   state coordinate preconditions separately.
/// - ensures: Signatures and definitions are distinct filing alternatives, and
///   duplication is checked per kind.
/// - fails: not applicable to the data item.
/// - panics: not applicable to the data item.
/// - executable: none — the enabled specification facade does not expose
///   type-invariant expansion; executable predicates cover the producing and
///   consuming operations.
///
/// # Adequacy
/// - hypothesis: L3 — a signature pairs with a definition while another half of
///   the same kind is refused.
/// - witness: `module::tests::a_signature_pairs_with_its_definition`
/// - witness: `module::tests::a_definition_pairs_with_a_later_signature`
/// - witness: `module::tests::a_second_signature_is_refused`
/// - witness: `module::tests::a_second_definition_is_refused`
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
enum HalfKind
{
    /// `: T ;`, the signature.
    Signature,
    /// `= e ;`, the definition.
    Definition,
}

/// Whether a function tail states its type: every parameter and the result
/// carry one.
///
/// # Specification
/// - requires: nothing to construct this data; its producers and consumers
///   state coordinate preconditions separately.
/// - ensures: The signed alternative marks a function tail whose typed
///   parameters are followed by a result arrow; it does not certify the result
///   type.
/// - fails: not applicable to the data item.
/// - panics: not applicable to the data item.
/// - executable: none — the enabled specification facade does not expose
///   type-invariant expansion; executable predicates cover the producing and
///   consuming operations.
///
/// # Adequacy
/// - hypothesis: L3 — a signed function supplies a derived signature checked
///   against either ordering of a written one.
/// - witness: `tests::modules::member_signature_attaches_and_wins_over_derived_function_type`
/// - witness: `tests::modules::signatures_attach_to_their_defs`
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
enum Signing
{
    /// The tail states every type its declared type is built from, so it
    /// writes a signature beside its definition.
    Signed,
    /// A parameter or the result is untyped, so the tail writes a definition
    /// alone, whose body must synthesise or meet a signature written apart.
    Unsigned,
}

/// What one declaration form's tail wrote.
///
/// # Specification
/// - requires: nothing to construct this data; its producers and consumers
///   state coordinate preconditions separately.
/// - ensures: Reading separates a written half, a deferred function tail and a
///   located refusal; refused tails do not file halves or attributes.
/// - fails: not applicable to the data item.
/// - panics: not applicable to the data item.
/// - executable: none — the enabled specification facade does not expose
///   type-invariant expansion; executable predicates cover the producing and
///   consuming operations.
///
/// # Adequacy
/// - hypothesis: L3 — normal halves, signed functions and a missing body select
///   distinct outcomes.
/// - witness: `module::tests::a_signature_pairs_with_its_definition`
/// - witness: `module::tests::a_definition_pairs_with_a_later_signature`
/// - witness: `tests::modules::member_signature_attaches_and_wins_over_derived_function_type`
/// - witness: `tests::modules::signatures_attach_to_their_defs`
/// - witness: `module::tests::a_declaration_missing_its_body_is_refused`
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
enum Tail<'source>
{
    /// A signature or a definition over this operand.
    Wrote(HalfKind, Placed),
    /// A function tail: a definition, and a signature when it is signed.
    Function(Signing),
    /// The first fault of the form.
    Refused(LoweringRefusal<'source>),
    /// A data declaration, its form read into the collection's data list at
    /// this position.
    Data(usize),
    /// A world declaration, `world w ;`.
    World,
}

/// The collection pass's working state.
///
/// # Specification
/// - requires: nothing to construct this data; its producers and consumers
///   state coordinate preconditions separately.
/// - ensures: The traversal keeps its source and grammar borrowed, spends the
///   shared budget on traversal, and accumulates admission, ownership and
///   signature state in one collection.
/// - fails: not applicable to the data item.
/// - panics: not applicable to the data item.
/// - executable: none — the enabled specification facade does not expose
///   type-invariant expansion; executable predicates cover the producing and
///   consuming operations.
///
/// # Adequacy
/// - hypothesis: L3 — nested modules, malformed members and imports retain
///   their respective declarations or refusals.
/// - witness: `tests::modules::modules_lower_to_named_member_declarations`
/// - witness: `tests::modules::module_members_admit_in_source_order`
/// - witness: `tests::modules::a_readable_module_keeps_its_members_and_its_successor`
/// - witness: `tests::namespace::source_import_reaches_the_namespace_engine_and_exposes_its_alias`
/// - witness: `tests::namespace::an_unqualified_import_binds_no_alias`
/// - witness: `tests::namespace::duplicate_source_import_alias_becomes_a_refusal`
struct Collector<'run, 'source>
{
    /// The grammar the tree was molded under.
    pbg: &'run Pbg,
    /// The tree being collected.
    tree: &'run SyntaxTree<'source>,
    /// The lowering's remaining allowance.
    fuel: &'run mut Fuel,
    /// What has been collected so far, every earlier source included.
    collected: &'run mut Collected<'source>,
    /// The scratch reading of the declaration form being collected.
    pieces: Pieces,
    /// The next path import's ordinal in each source that has written one.
    ordinals: BTreeMap<SourceIndex, PathImportOrdinal>,
}

/// Collect every source of `unit` at once, as the lowering collects them a
/// source at a time: what a test reads of a whole collection.
///
/// # Specification
/// - requires: as [`collect_source`], for the whole tree.
/// - ensures: [`begin_collection`], then [`collect_source`] over each source of
///   `unit` in its order; every owner names a slot, every slot's constant is
///   its position, every name and module the tables hold points at its entry,
///   and every module comes after the module holding it.
/// - fails: as [`begin_collection`], [`root_pieces`] and [`collect_source`].
/// - panics: none.
///
/// # Errors
/// As [`collect_source`].
///
/// # Adequacy
/// - hypothesis: L3 — the collection tests read every list it builds.
/// - witness: `module::tests::a_signature_pairs_with_its_definition`
/// - witness: `module::tests::a_mutual_block_collects_its_members_as_one_run`
#[cfg(test)]
#[spec(ensures: |ret| ret.as_ref().map_or(true, |collected| {
    collected.owner.len() == usize::from(tree.node_count())
        && collected.owner.iter().all(|owner| match *owner {
            | Maybe::Present(slot) => slot.0 < collected.slots.len(),
            | Maybe::Absent(_) => true,
        })
        && collected
            .slots
            .iter()
            .enumerate()
            .all(|(index, slot)| usize::from(slot.constant) == index)
        && collected.by_name.iter().all(|(&(container, name), index)| {
            collected.slots.get(index.0).is_some_and(|slot| {
                slot.container == container && slot.name == name && slot.role == Role::Declared
            })
        })
        && collected.modules.iter().all(|(&(container, name), index)| {
            collected
                .structures
                .get(index.0)
                .is_some_and(|module| module.container == container && module.name == name)
        })
        && collected
            .structures
            .iter()
            .enumerate()
            .all(|(index, module)| match module.container {
                | Container::TopLevel(_) => true,
                | Container::Module(parent) => parent.0 < index,
            })
}))]
pub fn collect<'source>(
    pbg: &Pbg,
    tree: &SyntaxTree<'source>,
    unit: &Unit,
    fuel: &mut Fuel,
) -> Result<Collected<'source>, LoweringRefusal<'source>>
{
    let mut collected = begin_collection(pbg, tree, unit)?;
    let pieces = root_pieces(pbg, tree)?;
    for own in source_pieces(unit, pieces) {
        collect_source((pbg, tree), &mut collected, fuel, own)?;
    }

    Ok(collected)
}

/// A unit's collection before any of its sources is collected: its
/// descriptions elaborated, nothing else admitted.
///
/// # Specification
/// - requires: `tree` was molded under `pbg`.
/// - ensures: the descriptions, their diagnostics, the native families and the
///   cell stores are the tree's; every list and table is empty; one unowned
///   entry per node.
/// - provides: the collection [`collect_source`] appends each source to.
/// - fails: as the description elaboration.
/// - panics: none.
///
/// # Errors
/// The description elaboration's refusal.
///
/// # Adequacy
/// - hypothesis: L3 — every collection starts here, so every witness of
///   [`collect_source`] reaches it.
/// - witness: `module::tests::a_signature_pairs_with_its_definition`
/// - witness: `tests::namespace::source_import_reaches_the_namespace_engine_and_exposes_its_alias`
#[spec(ensures: |ret| ret.as_ref().map_or(true, |collected| {
    collected.slots.is_empty()
        && collected.structures.is_empty()
        && collected.owner.len() == usize::from(tree.node_count())
}))]
pub fn begin_collection<'source>(
    pbg: &Pbg,
    tree: &SyntaxTree<'source>,
    unit: &Unit,
) -> Result<Collected<'source>, LoweringRefusal<'source>>
{
    let described = crate::description::elaborate_descriptions(pbg, tree, unit)?;
    let cells = crate::desc_cells::elaborate_desc_cells(&described.declarations);
    let mut owner = Vec::new();
    owner.resize(
        usize::from(tree.node_count()),
        Maybe::Absent(slot_owner::Absent::Unowned),
    );

    Ok(Collected {
        descriptions: described
            .declarations
            .into_iter()
            .map(|entry| (entry.at.node, entry))
            .collect(),
        description_diagnostics: described.diagnostics,
        natives: described.natives,
        cells,
        slots: Vec::new(),
        owner,
        by_name: BTreeMap::new(),
        structures: Vec::new(),
        modules: BTreeMap::new(),
        scopes: Vec::new(),
        imports: ModuleImports::new(),
        unit: unit.clone(),
        data: Vec::new(),
        words: Vec::new(),
        constructors: BTreeMap::new(),
        operations: BTreeMap::new(),
        operation_names: BTreeMap::new(),
        abstracts: BTreeMap::new(),
        decorated: Vec::new(),
        module_docs: Vec::new(),
        families: Vec::new(),
        parameter_lists: Vec::new(),
        models: Vec::new(),
        family_checks: BTreeMap::new(),
        functors: Vec::new(),
        instances: Vec::new(),
        theory: Maybe::Absent(theory_slot::Absent::Unminted),
        theory_sources: BTreeSet::new(),
        blocks: Vec::new(),
        recursive: BTreeSet::new(),
        plicities: BTreeMap::new(),
        stage_binders: BTreeMap::new(),
        receivers: BTreeMap::new(),
        declared_uses: Vec::new(),
        reached: BTreeSet::new(),
    })
}

impl Collected<'_>
{
    /// Widen the collection to a tree of `count` nodes laid out by `unit`,
    /// whose added roots `described` reads: their descriptions, diagnostics,
    /// native families and cell stores appended, every added node unowned.
    ///
    /// # Specification
    /// - requires: `count` is no fewer nodes than the collection owns, and
    ///   `described` is [`crate::description::elaborate_roots`] over the roots
    ///   the tree adds, numbered after the descriptions held.
    /// - ensures: as [`begin_collection`] over the whole tree, the slots,
    ///   structures and every other table kept.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a document resumed after its closure collects as the
    ///   whole unit does.
    /// - witness: `tests::namespace::a_document_resumed_after_its_closure_lowers_as_the_whole_1033`
    #[spec(ensures: self.owner.len() >= usize::from(count))]
    pub(crate) fn widen(
        &mut self,
        count: NodeCount,
        unit: &Unit,
        described: crate::description::DescriptionReport,
    )
    {
        let cells = crate::desc_cells::elaborate_desc_cells(&described.declarations);
        self.descriptions.extend(
            described
                .declarations
                .into_iter()
                .map(|entry| (entry.at.node, entry)),
        );
        self.description_diagnostics.extend(described.diagnostics);
        self.natives.extend(described.natives);
        self.cells.declarations.extend(cells.declarations);
        self.cells.diagnostics.extend(cells.diagnostics);
        let count = usize::from(count);
        if self.owner.len() < count {
            self.owner
                .resize(count, Maybe::Absent(slot_owner::Absent::Unowned));
        }
        self.unit = unit.clone();
    }
}

/// The roots' pieces: every top-level form of every source, in source order.
///
/// # Specification
/// - requires: `tree` was molded under `pbg`.
/// - ensures: [`pieces_under`] every root of `tree`.
/// - provides: what [`source_pieces`] splits by source.
/// - fails: [`LoweringRefusal::UnknownMold`] for a mold the grammar does not
///   hold.
/// - panics: none.
///
/// # Errors
/// As the specification's fails clause.
///
/// # Adequacy
/// - hypothesis: L3 — as [`pieces_under`].
/// - witness: `module::tests::a_stray_root_child_refuses_itself_alone_1058`
#[spec(ensures: |ret| ret.is_err() || tree.node(tree.root()).is_some() || ret.as_ref().is_ok_and(Vec::is_empty))]
pub fn root_pieces<'source>(
    pbg: &Pbg,
    tree: &SyntaxTree<'source>,
) -> Result<Vec<Piece>, LoweringRefusal<'source>>
{
    pieces_under(pbg, tree, tree.roots())
}

/// The pieces of `roots`: each root's children, layout dropped, in source
/// order, the roots in their order.
///
/// # Specification
/// - requires: `tree` was molded under `pbg`, and `roots` are roots of it.
/// - ensures: every root's children, layout dropped, root after root; a repair
///   the parser inserted among a root's children is a piece in its place, for
///   the collection to refuse on its own.
/// - provides: the top-level forms of a document laid after a closure whose
///   roots were read before.
/// - fails: [`LoweringRefusal::UnknownMold`] for a mold the grammar does not
///   hold.
/// - panics: none.
///
/// # Errors
/// As the specification's fails clause.
///
/// # Adequacy
/// - hypothesis: L3 — a byte no label molds between two declarations is a piece
///   between theirs.
/// - witness: `module::tests::a_stray_root_child_refuses_itself_alone_1058`
/// - witness: `tests::namespace::a_document_resumed_after_its_closure_lowers_as_the_whole_1033`
#[spec(ensures: |ret| ret.is_err() || !roots.is_empty() || ret.as_ref().is_ok_and(Vec::is_empty))]
pub fn pieces_under<'source>(
    pbg: &Pbg,
    tree: &SyntaxTree<'source>,
    roots: &[NodeIndex],
) -> Result<Vec<Piece>, LoweringRefusal<'source>>
{
    let mut pieces = Vec::new();
    let mut root = Pieces::new();
    for &at in roots {
        read_pieces(pbg, tree, at, &mut root)?;
        if let Maybe::Present(_) = root.repair {
            for child in tree.children(at) {
                if let Some(held) = tree.node(child)
                    && matches!(
                        held.label(),
                        NodeLabel::Grout { .. } | NodeLabel::GhostClose { .. }
                    )
                {
                    root.pieces.push(Piece::Operand(Placed::of(child, held)));
                }
            }
            root.pieces.sort_by_key(|piece| piece.placed().span.start());
        }
        pieces.append(&mut root.pieces);
    }

    Ok(pieces)
}

/// The root's pieces split by the source each starts in: one list per source
/// of `unit`, in the unit's order, each in source order.
///
/// # Specification
/// - requires: `pieces` are a tree's root pieces over the text `unit` lays out.
/// - ensures: one list per source; the lists concatenated are `pieces`.
/// - provides: the share of the root each source's collection reads.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a unit of two sources collects each source's forms under
///   its own source.
/// - witness: `tests::namespace::source_import_reaches_the_namespace_engine_and_exposes_its_alias`
#[spec(ensures: |ret| ret.len() == unit.sources().len())]
pub fn source_pieces(
    unit: &Unit,
    pieces: Vec<Piece>,
) -> Vec<Vec<Piece>>
{
    let mut split: Vec<Vec<Piece>> = unit.sources().iter().map(|_| Vec::new()).collect();
    for piece in pieces {
        let source = unit.source_at(piece.placed().span.start());
        if let Some(own) = split.get_mut(usize::from(source)) {
            own.push(piece);
        }
    }

    split
}

/// Collect one source's top-level forms into `collected`, after every source
/// before it: pair every signature with its definition, in one pass over the
/// source.
///
/// # Specification
/// - requires: `pieces` are one source's root pieces, in source order, of a
///   tree molded under `pbg`; `collected` holds every earlier source of the
///   unit; `fuel` holds the lowering's remaining allowance.
/// - ensures: appended to what `collected` held, one slot per distinct declared
///   name, in the order the names were first declared, each carrying that
///   name's signature and definition wherever the two sat, and every attribute
///   written on its first clean declaration form of each kind; a second
///   signature or a second definition for one name leaves the slot's first
///   refusal set and the first occurrence intact. A fault in a declaration
///   form's own tiles — a repair, an empty or overfull hole, a tile out of
///   place, a tail the fragment does not admit — is offered to the
///   declaration's slot at the declaration form itself. The attributes written
///   before a top-level module are kept with the slots its collection admitted;
///   an attribute block decorates the form after it in the source, and one
///   standing at the source's end decorates nothing. Each import is kept in
///   source order with its address decoded and its alias bound in the import
///   scope.
/// - provides: the admission order every later pass resolves names against,
///   which the lowering builds a source at a time, before its passes over that
///   source.
/// - fails: [`LoweringRefusal::MalformedForm`] when a declaration has no name
///   to file a refusal under, or an import is out of shape;
///   [`LoweringRefusal::DuplicateImportAlias`] when two imports bind one alias;
///   [`LoweringRefusal::OutOfFragment`] when a root child is neither a
///   declaration, a module nor an import — an attribute block decorating
///   nothing, or a module with no member, included — or when a declaration's
///   name is a form rather than an identifier; [`LoweringRefusal::UnknownMold`]
///   for a mold the grammar does not hold; [`LoweringRefusal::BudgetExceeded`]
///   when the walk outruns the allowance.
/// - panics: none. A position the tree does not hold contributes nothing.
///
/// # Errors
/// [`LoweringRefusal::MalformedForm`], [`LoweringRefusal::OutOfFragment`] and
/// [`LoweringRefusal::DuplicateImportAlias`] for a source whose own children
/// are not declarations and well-formed imports,
/// [`LoweringRefusal::UnknownMold`] for a foreign mold, and
/// [`LoweringRefusal::BudgetExceeded`] when the allowance runs out.
///
/// # Adequacy
/// - hypothesis: L3 — the decision surfaces (the child kind, the name tile, the
///   slot lookup, the tail tile, the hole run, the attribute reading, the
///   import tiles) separated by a signature and definition in each order, a
///   signature and definition separated by an unrelated declaration, a second
///   signature, a second definition, a stray module child, a declaration
///   missing its body, a declaration whose name is not a name, a trailing
///   attribute block, two stacked attribute blocks, two imports, an import with
///   no alias and two imports of one alias, each asserted as an exact slot
///   list, import list or refusal variant.
/// - witness: `module::tests::a_signature_pairs_with_its_definition`
/// - witness: `module::tests::a_definition_pairs_with_a_later_signature`
/// - witness: `module::tests::a_second_signature_is_refused`
/// - witness: `module::tests::a_second_definition_is_refused`
/// - witness: `module::tests::a_stray_module_child_refuses_the_module`
/// - witness: `module::tests::a_declaration_missing_its_body_is_refused`
/// - witness: `module::tests::a_declaration_whose_name_is_not_a_name_refuses_the_module`
/// - witness: `module::tests::a_trailing_attribute_block_refuses_itself`
/// - witness: `module::tests::a_stray_root_child_refuses_itself_alone_1058`
/// - witness: `module::tests::an_attribute_block_decorates_the_declaration_after_it`
/// - witness: `tests::namespace::source_import_reaches_the_namespace_engine_and_exposes_its_alias`
/// - witness: `tests::namespace::an_unqualified_import_binds_no_alias`
/// - witness: `tests::namespace::duplicate_source_import_alias_becomes_a_refusal`
#[spec(
    captures: before = collected.slots.len(),
    ensures: |ret| {
        ret.is_err()
            || (collected.slots.len() >= before
                && collected.owner.len() == usize::from(tree.node_count()))
    },
)]
pub fn collect_source<'source>(
    (pbg, tree): (&Pbg, &SyntaxTree<'source>),
    collected: &mut Collected<'source>,
    fuel: &mut Fuel,
    pieces: Vec<Piece>,
) -> Result<(), LoweringRefusal<'source>>
{
    let mut collector = Collector {
        pbg,
        tree,
        fuel,
        collected,
        pieces: Pieces::new(),
        ordinals: BTreeMap::new(),
    };
    let declared_before = (
        collector.collected.slots.len(),
        collector.collected.structures.len(),
        collector.collected.data.len(),
    );
    let mut strays: Vec<Stray<'source>> = Vec::new();
    let mut decorations: Vec<Placed> = Vec::new();
    let mut after_stray = false;
    for piece in pieces {
        collector.fuel.spend()?;
        let child = piece.placed();
        let follows_stray = core::mem::replace(&mut after_stray, false);
        let former = collector.root_former(child)?;
        if former == Former::AttributeBlock {
            decorations.push(child);
            continue;
        }
        if former == Former::WorldDeclaration {
            collector.world(child, &decorations)?;
            decorations.clear();
            continue;
        }
        if former == Former::Data {
            collector.data(child, &decorations)?;
            collector.hold_described_refusals(child);
            collector.route_operations(child);
            decorations.clear();
            continue;
        }
        if former == Former::Declaration {
            if let Some(refusal) = strayed(collector.declaration(child, &decorations))? {
                strays.push(Stray::of(child, refusal, core::mem::take(&mut decorations)));
                after_stray = true;
            }
            decorations.clear();
            continue;
        }
        if former == Former::Mutual {
            if let Some(&block) = decorations.first()
                && let Some(refusal) = strayed(collector.module_child(block))?
            {
                strays.push(Stray::of(block, refusal, Vec::new()));
            }
            collector.mutual(child)?;
            decorations.clear();
            continue;
        }
        if former == Former::Module
            && let Some(&block) = decorations.first()
        {
            collector.decorated_module(child, block, &decorations)?;
            decorations.clear();
            continue;
        }
        if collector
            .collected
            .descriptions
            .get(&child.node)
            .is_some_and(|entry| matches!(entry.presentation, Maybe::Present(_)))
        {
            collector.theory(child, &decorations);
            decorations.clear();
            continue;
        }
        if collector
            .collected
            .descriptions
            .get(&child.node)
            .is_some_and(|entry| matches!(entry.classifier, Maybe::Present(_)))
        {
            collector.admit_described(child, &decorations);
            collector.hold_described_refusals(child);
            decorations.clear();
            continue;
        }
        if collector.refuses_signature(child).0 {
            collector.refuse_signature(child, &decorations);
            decorations.clear();
            continue;
        }
        // The `;` that ends a stray statement belongs to it.
        if follows_stray
            && collector
                .tree
                .fragment(child.node)
                .is_some_and(|text| <&str>::from(text).trim() == ";")
            && let Some(last) = strays.last_mut()
        {
            last.terminator = Some(child);
            continue;
        }
        // The blocks before a child that stands on its own decorate it; before
        // a module, an import or a member they decorate nothing.
        if let Some(refusal) = strayed(collector.module_child(child))? {
            strays.push(Stray::of(child, refusal, core::mem::take(&mut decorations)));
            after_stray = true;
        }
        else if let Some(&block) = decorations.first()
            && let Some(refusal) = strayed(collector.module_child(block))?
        {
            strays.push(Stray::of(block, refusal, Vec::new()));
        }
        decorations.clear();
    }
    if let Some(&block) = decorations.first()
        && let Some(refusal) = strayed(collector.module_child(block))?
    {
        strays.push(Stray::of(block, refusal, Vec::new()));
    }
    // A source that declares nothing is no list of declarations: its first
    // stray refuses it whole.
    let declared = collector.collected.slots.len() > declared_before.0
        || collector.collected.structures.len() > declared_before.1
        || collector.collected.data.len() > declared_before.2;
    let mut strays = strays.into_iter();
    if !declared && let Some(first) = strays.next() {
        return Err(first.refusal);
    }
    for stray in strays {
        collector.refuse_stray(stray);
    }
    collector.stray_expectations();

    Ok(())
}

/// A root child that is no declaration, the refusal it raised, the attribute
/// blocks written before it and the `;` that ends it, when one does.
#[derive(Debug)]
struct Stray<'source>
{
    /// The child no declaration owns.
    child: Placed,
    /// What collecting the child raised.
    refusal: LoweringRefusal<'source>,
    /// The attribute blocks standing on their own before the child.
    decorations: Vec<Placed>,
    /// The `;` written right after the child, which ends it as a statement.
    terminator: Option<Placed>,
}

impl<'source> Stray<'source>
{
    /// The stray `child`, refused by `refusal` and decorated by
    /// `decorations`, with no terminator yet.
    ///
    /// # Specification
    /// trivial.
    const fn of(
        child: Placed,
        refusal: LoweringRefusal<'source>,
        decorations: Vec<Placed>,
    ) -> Self
    {
        Self {
            child,
            refusal,
            decorations,
            terminator: None,
        }
    }
}

/// What collecting one root child came to: nothing to refuse, a refusal of
/// that child alone, or a refusal of the whole source.
///
/// # Specification
/// - requires: nothing.
/// - ensures: a success is none; a form of the wrong sort or a malformed form
///   is that child's own refusal; every other refusal — a mold the grammar does
///   not hold, an exhausted allowance, an import out of reach — refuses the
///   source.
/// - provides: the line between a stray root child and a fault of the source.
/// - fails: the refusals that are no child's own.
/// - panics: none.
///
/// # Errors
/// Every refusal other than [`LoweringRefusal::OutOfFragment`] and
/// [`LoweringRefusal::MalformedForm`].
///
/// # Adequacy
/// - hypothesis: L3 — a stray between two declarations is its own refusal, and
///   a stray in a source declaring nothing refuses the source.
/// - witness: `module::tests::a_stray_root_child_refuses_itself_alone_1058`
#[spec(ensures: |ret| match ret {
    | Ok(Some(ref refusal)) => matches!(*refusal,
        LoweringRefusal::OutOfFragment { .. } | LoweringRefusal::MalformedForm { .. }),
    | Ok(None) | Err(_) => true,
})]
fn strayed<'source>(
    collected: Result<(), LoweringRefusal<'source>>
) -> Result<Option<LoweringRefusal<'source>>, LoweringRefusal<'source>>
{
    match collected {
        Ok(()) => Ok(None),
        Err(
            refusal @ (LoweringRefusal::OutOfFragment { .. }
            | LoweringRefusal::MalformedForm { .. }),
        ) => Ok(Some(refusal)),
        Err(refusal) => Err(refusal),
    }
}

/// Whether an import's address names a scheme or a path.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Address
{
    /// `scheme:…`: a letter, then letters, digits, `+`, `-` or `.`, then a
    /// colon (RFC 3986 § 3.1).
    Scheme,
    /// Anything else: a path relative to the importing source.
    Path,
}

impl Address
{
    /// What `uri` names.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: [`Address::Scheme`] exactly when `uri` opens with an RFC 3986
    ///   scheme and its colon; [`Address::Path`] otherwise.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a `file:` URL, a relative path, a path holding a
    ///   colon after a slash and a scheme opening with a digit each classify
    ///   exactly.
    /// - witness: `module::tests::an_address_names_a_scheme_or_a_path`
    #[inline]
    #[must_use]
    #[spec(ensures: |ret| ret == Self::Path || uri.as_ref().contains(':'))]
    pub fn of(uri: &ImportUri) -> Self
    {
        let text = uri.as_ref();
        let Some(colon) = text.find(':')
        else {
            return Self::Path;
        };
        let scheme = text.get(.. colon).unwrap_or_default();
        let mut characters = scheme.chars();
        let opens = characters
            .next()
            .is_some_and(|first| first.is_ascii_alphabetic());
        let rest = characters
            .all(|later| later.is_ascii_alphanumeric() || matches!(later, '+' | '-' | '.'));
        if opens && rest {
            Self::Scheme
        }
        else {
            Self::Path
        }
    }
}

/// One import as its tiles spell it.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct WrittenImport
{
    /// The address, its escapes decoded.
    pub uri: ImportUri,
    /// The alias, when one is written.
    pub alias: Maybe<Placed, unaliased::Absent>,
    /// The bytes the import covers.
    pub span: ByteSpan,
    /// The bytes between the address's quotes, as written, escapes included.
    pub addressed: ByteSpan,
    /// What the address names.
    pub address: Address,
}

quenchant_shape::reason_enum! {
    /// Why an import has no alias.
    pub mod unaliased {
        /// The reason none is written.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The import binds its sibling's exports unqualified.
            Unqualified,
        }
    }
}

/// Read one import form's pieces.
///
/// # Specification
/// - requires: `pieces` is the reading of the import `import`.
/// - ensures: the import the tiles `import " … " (as name)? ;` spell, in that
///   order with nothing after them, its address read between the quotes.
/// - provides: the reading the collection and [`written_imports`] share.
/// - fails: [`LoweringRefusal::MalformedForm`] for a repair, naming the form
///   inside the import that holds it or else `form`, as
///   [`Repaired::refusal`](crate::form::Repaired::refusal) names it; and naming
///   `form` for a tile out of place.
/// - panics: none.
///
/// # Errors
/// [`LoweringRefusal::MalformedForm`].
///
/// # Adequacy
/// - hypothesis: L3 — exact address decoding with and without an alias, and a
///   tile out of place, distinguish reading from binding refusal.
/// - witness: `tests::namespace::source_import_reaches_the_namespace_engine_and_exposes_its_alias`
/// - witness: `tests::namespace::an_unqualified_import_binds_no_alias`
/// - witness: `tests::namespace::an_import_repaired_inside_a_nested_form_is_refused_by_that_form`
#[spec(
    ensures: |ret| match ret {
        | Ok(ref entry) => entry.span == import.span && {
            let (outer, inner) = (import.span, entry.addressed);
            outer.start() <= inner.start() && inner.end() <= outer.end()
        },
        | Err(LoweringRefusal::MalformedForm { form: found, .. }) => found == form
            || matches!(pieces.repair, Maybe::Present(crate::form::Repaired { nested: Maybe::Present(inner), .. }) if inner == found),
        | Err(_) => false,
    },
)]
fn read_import<'source>(
    tree: &SyntaxTree<'source>,
    import: Placed,
    form: FormName,
    pieces: &Pieces,
) -> Result<WrittenImport, LoweringRefusal<'source>>
{
    if let Maybe::Present(repaired) = pieces.repair {
        return Err(repaired.refusal(form));
    }
    let out_of_place = |cursor: &Cursor<'_>| LoweringRefusal::MalformedForm {
        span: cursor.here(),
        form,
        fault: FormFault::MisplacedTile,
    };
    let mut cursor = Cursor::new(&pieces.pieces, import.span);
    if let Maybe::Absent(_) = cursor.tile(TileName::IMPORT) {
        return Err(out_of_place(&cursor));
    }
    let Maybe::Present(opened) = cursor.tile(TileName::QUOTE)
    else {
        return Err(out_of_place(&cursor));
    };
    let mut written = String::new();
    loop {
        let piece = match cursor.tile(TileName::STRING_FRAGMENT) {
            Maybe::Present(fragment) => fragment,
            Maybe::Absent(_) => match cursor.tile(TileName::ESCAPE_SEQUENCE) {
                Maybe::Present(escape) => escape,
                Maybe::Absent(_) => break,
            },
        };
        if let Some(text) = tree.fragment(piece.node) {
            written.push_str(text.as_ref());
        }
    }
    let Maybe::Present(closed) = cursor.tile(TileName::QUOTE)
    else {
        return Err(out_of_place(&cursor));
    };
    let addressed = ByteSpan::new(opened.span.end(), closed.span.start())
        .map_err(|_inverted| out_of_place(&cursor))?;
    let alias = match cursor.tile(TileName::AS) {
        Maybe::Present(_) => match cursor.tile(TileName::IDENTIFIER) {
            Maybe::Present(alias) => Maybe::Present(alias),
            Maybe::Absent(_) => return Err(out_of_place(&cursor)),
        },
        Maybe::Absent(_) => Maybe::Absent(unaliased::Absent::Unqualified),
    };
    if let Maybe::Absent(_) = cursor.tile(TileName::SEMICOLON) {
        return Err(out_of_place(&cursor));
    }
    if let Maybe::Present(_) = cursor.peek() {
        return Err(out_of_place(&cursor));
    }
    let uri = ImportUri::from(decode_escapes(SourceFragment::from(written.as_str())));
    let address = Address::of(&uri);

    Ok(WrittenImport {
        uri,
        alias,
        span: import.span,
        addressed,
        address,
    })
}

/// Every import `tree`'s root writes, in source order, read as the collection
/// reads it.
///
/// # Specification
/// - requires: `tree` was molded under `pbg`.
/// - ensures: one entry per import form at the root, in source order; every
///   other root child is passed over.
/// - provides: what a caller reads to lay out a [`Unit`] before lowering it:
///   the sources an import names, without collecting a declaration.
/// - fails: [`LoweringRefusal::MalformedForm`] for a repaired root or an import
///   out of shape, and [`LoweringRefusal::UnknownMold`] for a mold the grammar
///   does not hold.
/// - panics: none.
///
/// # Errors
/// [`LoweringRefusal::MalformedForm`] and [`LoweringRefusal::UnknownMold`].
///
/// # Adequacy
/// - hypothesis: L3 — a source with an unqualified and an aliased import
///   between two declarations lists exactly the two imports.
/// - witness: `tests::namespace::an_unqualified_import_binds_no_alias`
#[spec(ensures: |ret| ret.as_ref().map_or(true, |found| found.windows(2).all(|pair| match *pair {
    [ref first, ref second] => first.span.start() < second.span.start(),
    _ => false,
})))]
#[inline]
pub fn written_imports<'source>(
    pbg: &Pbg,
    tree: &SyntaxTree<'source>,
) -> Result<Vec<WrittenImport>, LoweringRefusal<'source>>
{
    let mut root = Pieces::new();
    read_pieces(pbg, tree, tree.root(), &mut root)?;
    if let Maybe::Present(repaired) = root.repair {
        return Err(repaired.refusal(FormName::ROOT));
    }
    let mut found = Vec::new();
    let mut pieces = Pieces::new();
    for piece in root.pieces {
        let child = piece.placed();
        let Some(node) = tree.node(child.node)
        else {
            continue;
        };
        if let Shape::Form {
            former: Former::Import,
            name,
            ..
        } = shape_of(pbg, node)?
        {
            read_pieces(pbg, tree, child.node, &mut pieces)?;
            found.push(read_import(tree, child, name, &pieces)?);
        }
    }

    Ok(found)
}

/// The sources each source under `roots` imports unqualified, as `unit` lays
/// its path imports out.
///
/// # Specification
/// - requires: `tree` was molded under `pbg`, and `unit` lays out its text.
/// - ensures: for each source written under `roots`, the targets of its
///   unaliased path imports that `unit` resolves to a source; an import that
///   does not read, a scheme address and an unresolved path add nothing, the
///   collection refusing or binding them as it does.
/// - provides: the sources whose `theory` blocks an `include` may name.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a source importing one sibling unqualified and another
///   under an alias sees the first alone.
/// - witness: `tests::namespace::an_include_reads_the_theories_its_source_imports_1224`
#[spec(ensures: |ret| ret.values().all(|targets| !targets.is_empty()))]
pub fn unqualified_imports(
    pbg: &Pbg,
    tree: &SyntaxTree<'_>,
    roots: &[NodeIndex],
    unit: &Unit,
) -> BTreeMap<SourceIndex, BTreeSet<SourceIndex>>
{
    let mut seen: BTreeMap<SourceIndex, BTreeSet<SourceIndex>> = BTreeMap::new();
    let mut ordinals: BTreeMap<SourceIndex, PathImportOrdinal> = BTreeMap::new();
    let mut root = Pieces::new();
    let mut pieces = Pieces::new();
    for &position in roots {
        if read_pieces(pbg, tree, position, &mut root).is_err() {
            continue;
        }
        for piece in &root.pieces {
            let child = piece.placed();
            let Some(node) = tree.node(child.node)
            else {
                continue;
            };
            let Ok(Shape::Form {
                former: Former::Import,
                name,
                ..
            }) = shape_of(pbg, node)
            else {
                continue;
            };
            if read_pieces(pbg, tree, child.node, &mut pieces).is_err() {
                continue;
            }
            let Ok(written) = read_import(tree, child, name, &pieces)
            else {
                continue;
            };
            if written.address != Address::Path {
                continue;
            }
            let source = unit.source_at(child.span.start());
            let ordinal = ordinals.entry(source).or_default();
            let target = unit.target(source, *ordinal);
            *ordinal = ordinal.next();
            if let (Maybe::Absent(_), ImportTarget::Source(target)) = (written.alias, target) {
                let _fresh = seen.entry(source).or_default().insert(target);
            }
        }
    }

    seen
}

impl<'source> Collector<'_, 'source>
{
    /// Collect one child of the root.
    ///
    /// # Specification
    /// - requires: `child` is a written child of the root.
    /// - ensures: a declaration form is collected into its slot, a module into
    ///   its structures and member slots, and an import into the import list;
    ///   every other form refuses as a form of the wrong sort, and a repair the
    ///   parser inserted as that repair.
    /// - provides: the module-shape half of [`collect_source`].
    /// - fails: [`LoweringRefusal::OutOfFragment`] for a child that is neither
    ///   a declaration, a module nor an import;
    ///   [`LoweringRefusal::MalformedForm`] for a repair; and every
    ///   module-level fault [`Self::declaration`], [`Self::module`] and
    ///   [`Self::import`] raise.
    /// - panics: none.
    ///
    /// # Errors
    /// As [`collect_source`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — declaration, nested-module and import children are
    ///   collected; a value at the root is refused as the wrong sort.
    /// - witness: `tests::modules::modules_lower_to_named_member_declarations`
    /// - witness: `tests::namespace::source_import_reaches_the_namespace_engine_and_exposes_its_alias`
    /// - witness: `module::tests::a_stray_module_child_refuses_the_module`
    /// - witness: `module::tests::a_stray_root_child_refuses_itself_alone_1058`
    #[spec(
        captures: before = (
            self.collected.slots.len(),
            self.collected.structures.len(),
            self.collected.owner.len(),
        ),
        ensures: self.collected.slots.len() >= before.0
            && self.collected.structures.len() >= before.1
            && self.collected.owner.len() == before.2,
    )]
    fn module_child(
        &mut self,
        child: Placed,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        if self.collected.descriptions.contains_key(&child.node) {
            self.admit_described(child, &[]);
            self.hold_described_refusals(child);
            return Ok(());
        }
        let Some(node) = self.tree.node(child.node)
        else {
            return Ok(());
        };
        match shape_of(self.pbg, node)? {
            Shape::Form {
                former: Former::Declaration,
                ..
            } => self.declaration(child, &[]),
            Shape::Form {
                former: Former::Module,
                ..
            } => self.module(child),
            Shape::Form {
                former: Former::Import,
                name,
                ..
            } => self.import(child, name),
            Shape::Form { name, .. } => Err(LoweringRefusal::OutOfFragment {
                span: child.span,
                form: name,
                sort: FragmentSort::Declaration,
                boundary: FragmentBoundary::WrongSort,
            }),
            Shape::Repair(_) => match repair_at(self.pbg, self.tree, child) {
                Maybe::Present(found) => Err(found.refusal(FormName::ROOT)),
                Maybe::Absent(_) => Ok(()),
            },
            Shape::Root | Shape::Layout => Ok(()),
        }
    }

    /// File `stray`, a root child that is no declaration, as the one held
    /// slot carrying its refusal, decorated by the attribute blocks written
    /// before it.
    ///
    /// # Specification
    /// - requires: `stray.refusal` is what collecting `stray.child` raised;
    ///   `stray.decorations` are attribute blocks standing on their own before
    ///   it, and `stray.terminator` the `;` written right after it.
    /// - ensures: one held slot, entered in no name table, named by the child's
    ///   first word, refused at the child; it owns the child, its decorations
    ///   and its terminator, and carries the decorations' attributes, so an
    ///   expectation written before a stray states its refusal. An unreadable
    ///   decoration refuses the slot instead where it stands first.
    /// - provides: a refusal for a root child no declaration owns, beside the
    ///   declarations the source keeps.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a statement keyword, an expression, a lone brace and
    ///   a byte no label molds, each between two declarations, refuse
    ///   themselves alone and leave both declarations completed; an expectation
    ///   before one states its refusal, and the `;` ending one is no second
    ///   stray.
    /// - witness: `module::tests::a_stray_root_child_refuses_itself_alone_1058`
    #[spec(
        captures: before = (self.collected.slots.len(), self.collected.by_name.len()),
        ensures: self.collected.slots.len() == before.0.saturating_add(1)
            && self.collected.by_name.len() == before.1,
    )]
    fn refuse_stray(
        &mut self,
        stray: Stray<'source>,
    )
    {
        let Stray {
            child,
            refusal,
            decorations,
            terminator,
        } = stray;
        let mut attributes = Vec::new();
        let mut attributed = Ok(());
        for &block in &decorations {
            if attributed.is_ok() {
                attributed = self.decoration(block, child.node, &mut attributes);
            }
        }
        let name = self
            .tree
            .fragment(child.node)
            .map_or("", <&str>::from)
            .split_whitespace()
            .next()
            .unwrap_or_default();
        let top = self.collected.top(child.span.start());
        let held = self.refuse_held(top, SurfaceName::from(name), child, child, refusal);
        self.collected.own(child.node, held);
        for block in decorations.into_iter().chain(terminator) {
            self.collected.own(block.node, held);
        }
        if let Some(slot) = self.collected.slots.get_mut(held.0) {
            slot.signature = Maybe::Present(Half {
                declaration: child,
                named: child,
                operand: Operand::Signature,
            });
            slot.attributes.append(&mut attributes);
            if let Err(unread) = attributed {
                slot.refuse(child.node, unread);
            }
        }
    }

    /// Collect the mutual block `block`: each member as the root collects
    /// one, and the run of slots the members take.
    ///
    /// # Specification
    /// - requires: `block` is a `rec { … }` form standing at the root.
    /// - ensures: an attribute block decorates the member after it, a data
    ///   declaration and a definition are collected into their slots, and the
    ///   block is recorded with the slots its members took, in source order.
    /// - provides: the block half of [`collect_source`]: what the lowering
    ///   admits as one block.
    /// - fails: [`LoweringRefusal::OutOfFragment`] for a member that is no data
    ///   declaration, definition or attribute block, and an attribute block
    ///   decorating nothing; a repaired block as its repair; every fault
    ///   [`Self::data`] and [`Self::declaration`] raise.
    /// - panics: none.
    ///
    /// # Errors
    /// As `- fails:`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a block of a data declaration and its decoder takes
    ///   two consecutive slots, and a declaration after it takes none of the
    ///   block's.
    /// - witness: `module::tests::a_mutual_block_collects_its_members_as_one_run`
    #[spec(
        captures: before = (self.collected.slots.len(), self.collected.blocks.len()),
        ensures: |ret| ret.is_err()
            || self.collected.blocks.get(before.1).is_some_and(|entry| {
                entry.form == block
                    && entry.first.0 == before.0
                    && entry.end.0 == self.collected.slots.len()
            }),
    )]
    fn mutual(
        &mut self,
        block: Placed,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let mut pieces = Pieces::new();
        read_pieces(self.pbg, self.tree, block.node, &mut pieces)?;
        if let Maybe::Present(repaired) = pieces.repair {
            return Err(repaired.refusal(FormName::MUTUAL));
        }
        let first = SlotIndex(self.collected.slots.len());
        let mut decorations: Vec<Placed> = Vec::new();
        for piece in pieces.pieces {
            let Piece::Operand(member) = piece
            else {
                continue;
            };
            self.fuel.spend()?;
            match self.root_former(member)? {
                Former::AttributeBlock => decorations.push(member),
                Former::Data => {
                    self.data(member, &decorations)?;
                    self.hold_described_refusals(member);
                    self.route_operations(member);
                    decorations.clear();
                },
                Former::Declaration => {
                    self.declaration(member, &decorations)?;
                    decorations.clear();
                },
                Former::Name
                | Former::Constructor
                | Former::Hole
                | Former::Number
                | Former::Text
                | Former::TypeQuote
                | Former::Parenthesized
                | Former::Unit
                | Former::Thunk
                | Former::Lambda
                | Former::Block
                | Former::Return
                | Former::Exit
                | Former::Become
                | Former::Loop
                | Former::While
                | Former::For
                | Former::Break
                | Former::Continue
                | Former::Force
                | Former::Run
                | Former::Call
                | Former::Case
                | Former::Telescope
                | Former::List
                | Former::PackModel
                | Former::Injection
                | Former::LazyRecord
                | Former::Binary
                | Former::Unary
                | Former::Projection
                | Former::TypeHead
                | Former::TypePath
                | Former::Universe
                | Former::TypeApplication
                | Former::ThunkType
                | Former::ReturnerType
                | Former::ArrowType
                | Former::ProductType
                | Former::SumType
                | Former::LazyProductType
                | Former::TelescopeType
                | Former::LabelledSumType
                | Former::LazyRecordType
                | Former::ValueFunctionType
                | Former::StaticAbstraction
                | Former::ParenthesizedType
                | Former::PathType
                | Former::RelationType
                | Former::ManifestType
                | Former::CapabilityType
                | Former::AtType
                | Former::StagedType
                | Former::ModedType
                | Former::Scope
                | Former::Import
                | Former::Module
                | Former::Mutual
                | Former::Instantiation
                | Former::SessionType
                | Former::Action
                | Former::Offer
                | Former::Access
                | Former::World
                | Former::WorldDeclaration
                | Former::Reserved
                | Former::Unadmitted => {
                    let Some(node) = self.tree.node(member.node)
                    else {
                        continue;
                    };
                    if let Shape::Form { name, .. } = shape_of(self.pbg, node)? {
                        return Err(LoweringRefusal::OutOfFragment {
                            span: member.span,
                            form: name,
                            sort: FragmentSort::Declaration,
                            boundary: FragmentBoundary::WrongSort,
                        });
                    }
                },
            }
        }
        if let Some(&stray) = decorations.first() {
            self.module_child(stray)?;
        }
        self.collected.blocks.push(MutualBlock {
            form: block,
            first,
            end: SlotIndex(self.collected.slots.len()),
        });

        Ok(())
    }

    /// Collect a top-level module the attribute blocks `decorations` decorate,
    /// `block` the first of them.
    ///
    /// # Specification
    /// - requires: `module` is a module form standing at the root, and
    ///   `decorations` the attribute blocks written before it.
    /// - ensures: the module is collected as an undecorated one is, and its
    ///   attributes are kept with the slots its collection admitted, the blocks
    ///   owned by the first of them so a fault in a payload refuses that
    ///   member; a module whose collection admits no slot decorates nothing,
    ///   and refuses the run as a stray attribute block does.
    /// - provides: the decorated half of [`collect_source`]'s module reading.
    /// - fails: a block out of shape, and every fault [`Self::module`] raises.
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoweringRefusal::MalformedForm`] for a block out of shape,
    /// [`LoweringRefusal::OutOfFragment`] for a module with no member, and as
    /// [`Self::module`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a decorated module of two members and an undecorated
    ///   declaration after it, the attribute reaching the members only.
    /// - witness: `lower::exits::tests::an_explicit_exits_attribute_asks_within_its_form`
    #[spec(
        captures: before = (self.collected.slots.len(), self.collected.decorated.len()),
        ensures: |ret| ret.is_err()
            || self.collected.decorated.get(before.1).is_some_and(|decorated| {
                decorated.first.0 == before.0
                    && decorated.end.0 == self.collected.slots.len()
                    && decorated.first < decorated.end
                    && decorated.attributes.iter().all(|attribute| attribute.decorates == module.node)
            }),
    )]
    fn decorated_module(
        &mut self,
        module: Placed,
        block: Placed,
        decorations: &[Placed],
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let mut attributes = Vec::new();
        for &written in decorations {
            self.decoration(written, module.node, &mut attributes)?;
        }
        for &written in decorations {
            self.document_module(written.node, written.span.end(), module.node);
        }
        let first = SlotIndex(self.collected.slots.len());
        self.module(module)?;
        let end = SlotIndex(self.collected.slots.len());
        if first == end {
            return self.module_child(block);
        }
        for &written in decorations {
            self.collected.own(written.node, first);
        }
        self.collected.decorated.push(DecoratedModule {
            module,
            attributes,
            first,
            end,
        });

        Ok(())
    }

    /// Admit the described family at `child`, which the native data reading
    /// does not own, under its classifier, decorated by the attribute blocks
    /// `decorations` written before it.
    ///
    /// # Specification
    /// - requires: `child` is a root child the description route described;
    ///   `decorations` are attribute blocks standing on their own before it.
    /// - ensures: a family with a classifier takes a slot owning `child` and
    ///   its decorations, whose signature half is the classifier and whose
    ///   attributes decorate `child`; a second family of one name refuses the
    ///   slot as a duplicate; an unreadable decoration refuses the family; a
    ///   family with no classifier takes no slot.
    /// - panics: none.
    /// - executable: none — the slot it takes is chosen by the name table,
    ///   which the call reads and writes in one step.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a codata family is admitted under its classifier and
    ///   reaches the decoder, which refuses it at its own span, and an
    ///   attribute written before a codata family is filed under it rather than
    ///   refusing the module as a stray block.
    /// - witness: `description::tests::a_codata_declaration_lowers_to_its_signature`
    /// - witness: `description::tests::an_attribute_block_decorates_the_codata_declaration_after_it`
    fn admit_described(
        &mut self,
        child: Placed,
        decorations: &[Placed],
    )
    {
        let Some(entry) = self.collected.descriptions.get(&child.node)
        else {
            return;
        };
        let named = entry.named;
        let Maybe::Present(classifier) = entry.classifier
        else {
            return;
        };
        let name = self.name_of(named);
        let position = self.admit(self.collected.top(child.span.start()), name, child, named);
        self.collected.own(child.node, position);
        let mut attributes = Vec::new();
        let mut attributed = Ok(());
        for &block in decorations {
            self.collected.own(block.node, position);
            if attributed.is_ok() {
                attributed = self.decoration(block, child.node, &mut attributes);
            }
        }
        for &block in decorations {
            self.document(position, block.node, block.span.end(), child.node);
        }
        self.document(position, child.node, named.span.start(), child.node);
        if let Some(slot) = self.collected.slots.get_mut(usize::from(position)) {
            if slot.introduced_by.node == child.node {
                slot.signature = Maybe::Present(Half {
                    declaration: child,
                    named,
                    operand: Operand::Written(classifier),
                });
                slot.attributes.extend(attributes);
                if let Err(refusal) = attributed {
                    slot.refuse(child.node, refusal);
                }
            }
            else {
                slot.refuse(child.node, LoweringRefusal::DuplicateDefinition {
                    span: child.span,
                    name,
                    first: slot.introduced_by.span,
                });
            }
        }
    }

    /// Hold every description and cell refusal raised inside the described
    /// declaration at `child`, each at its member's own span; a declaration
    /// whose form the parser repaired is refused by the repair alone.
    ///
    /// # Specification
    /// - requires: `child` is a root child.
    /// - ensures: when a [`FormFault::Repaired`] refusal lies inside `child`,
    ///   it is the one refusal filed: offered to the declaration's own slot at
    ///   `child` when the declaration owns one — so a native reading that
    ///   refused the form for the same repair keeps one refusal, and a family
    ///   admitted under its classifier is refused by the repair rather than
    ///   decoded — and held under the family's name otherwise; with no repair,
    ///   a refusal of the family's rules as one rewriting system
    ///   (`RulesUnoriented`, `RulesDiverge`, `RulesUncompleted`,
    ///   `RulesUndecided`) is offered to the family's own slot, and every other
    ///   diagnostic whose span lies inside `child`'s takes one held slot under
    ///   the family's name, in report order; nothing for a child the
    ///   description route did not describe.
    /// - provides: member-local refusal beside native admission: a declined
    ///   member leaves its family and its siblings standing, a family whose
    ///   rules part is refused whole, and a malformed form is reported once, at
    ///   its repair.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a retired rule arrow inside a data family is held at
    ///   the arrow while the family keeps both generators and the declaration
    ///   after it lowers; an unended data or codata family is refused once, at
    ///   its missing close, whatever its members would refuse; a family two of
    ///   whose rules rewrite one term apart is refused under its own name.
    /// - witness: `description::tests::member_refusals_keep_their_spans_and_other_declarations`
    /// - witness: `description::tests::an_unended_family_is_refused_once_at_its_close`
    /// - witness: `coincide::tests::two_rules_rewriting_one_term_apart_refuse_the_block`
    #[spec(
        captures: before = self.collected.slots.len(),
        ensures: self.collected.slots.len() >= before,
    )]
    fn hold_described_refusals(
        &mut self,
        child: Placed,
    )
    {
        let Some(entry) = self.collected.descriptions.get(&child.node)
        else {
            return;
        };
        let named = entry.named;
        let name = self.name_of(named);
        let refusals = self.described_refusals(child);
        if let [
            (
                _,
                repaired @ LoweringRefusal::MalformedForm {
                    fault: FormFault::Repaired(_),
                    ..
                },
            ),
        ] = refusals[..]
            && let Maybe::Present(owner) = self.collected.owner_of(child.node)
            && let Some(slot) = self.collected.slots.get_mut(usize::from(owner))
        {
            slot.refuse(child.node, repaired);
            return;
        }
        for (span, refusal) in refusals {
            if matches!(
                refusal,
                LoweringRefusal::RulesUnoriented { .. }
                    | LoweringRefusal::RulesDiverge { .. }
                    | LoweringRefusal::RulesUncompleted { .. }
                    | LoweringRefusal::RulesUndecided { .. }
            ) && let Maybe::Present(owner) = self.collected.owner_of(child.node)
                && let Some(slot) = self.collected.slots.get_mut(usize::from(owner))
            {
                slot.refuse(child.node, refusal);
                continue;
            }
            let introduced = Placed {
                node: child.node,
                span,
            };
            let top = self.collected.top(child.span.start());
            let _held = self.refuse_held(top, name, introduced, named, refusal);
        }
    }

    /// Every description and cell refusal raised inside the declaration at
    /// `child`, with its member's span, in report order; the parser's repair
    /// of the form alone when it repaired one.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the one [`FormFault::Repaired`] refusal the description route
    ///   raised inside `child`'s span when it raised one; otherwise the
    ///   description diagnostics whose span lies inside `child`'s, then the
    ///   cell diagnostics, each with its own span.
    /// - provides: the cascade cut for described declarations: what a reading
    ///   of a repaired form refuses follows from the repair and is not reported
    ///   beside it.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::hold_described_refusals`] and
    ///   [`Self::refuse_signature`]; an unended `theory` block whose last
    ///   member the cell gate refuses is refused once, at its missing close.
    /// - witness: `description::tests::member_refusals_keep_their_spans_and_other_declarations`
    /// - witness: `description::tests::an_unended_family_is_refused_once_at_its_close`
    #[spec(ensures: |ret| ret.iter().all(|&(span, _)| span.start() >= child.span.start() && span.end() <= child.span.end()))]
    fn described_refusals(
        &self,
        child: Placed,
    ) -> Vec<(ByteSpan, LoweringRefusal<'source>)>
    {
        let inside =
            |span: ByteSpan| span.start() >= child.span.start() && span.end() <= child.span.end();
        let written = self
            .tree
            .fragment(child.node)
            .unwrap_or_else(|| SourceFragment::from(""));
        let described = self
            .collected
            .description_diagnostics
            .iter()
            .filter(|diagnostic| inside(diagnostic.span));
        if let Some(repaired) = described
            .clone()
            .find(|diagnostic| matches!(diagnostic.fault, DescriptionFault::Repaired { .. }))
        {
            return Vec::from([(repaired.span, repaired.lowering_refusal(written))]);
        }
        described
            .map(|diagnostic| (diagnostic.span, diagnostic.lowering_refusal(written)))
            .chain(
                self.collected
                    .cells
                    .diagnostics
                    .iter()
                    .filter(|diagnostic| inside(diagnostic.span))
                    .map(|diagnostic| (diagnostic.span, diagnostic.lowering_refusal())),
            )
            .collect()
    }

    /// Whether `child` is a top-level `oper` some member of which the
    /// description route or the cell gate refused.
    ///
    /// # Specification
    /// trivial.
    fn refuses_signature(
        &self,
        child: Placed,
    ) -> SignatureRefused
    {
        SignatureRefused(
            self.collected
                .descriptions
                .get(&child.node)
                .is_some_and(|entry| matches!(entry.classifier, Maybe::Absent(_)))
                && !self.described_refusals(child).is_empty(),
        )
    }

    /// File the refusals raised inside the top-level `oper` at `child` as
    /// declarations an expectation states, decorated by the attribute blocks
    /// `decorations` written before it.
    ///
    /// # Specification
    /// - requires: [`Self::refuses_signature`] holds of `child`; `decorations`
    ///   are attribute blocks standing on their own before it.
    /// - ensures: one held slot under the declaration's name per refusal, in
    ///   report order, each at its member's span with the declaration itself as
    ///   its signature half, so the attributes the decorations file under it
    ///   are read off every one of them; the first owns the declaration and its
    ///   decorations, and an unreadable decoration refuses it.
    /// - provides: refusals inside a top-level operation an expectation can
    ///   state.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a refused operation keeps its span, a decoration
    ///   before it states it, and its name enters no namespace.
    /// - witness: `description::theory::tests::a_refused_top_level_operation_states_its_refusal`
    #[spec(
        captures: before = (self.collected.slots.len(), self.collected.by_name.len()),
        ensures: self.collected.slots.len() >= before.0 && self.collected.by_name.len() == before.1,
    )]
    fn refuse_signature(
        &mut self,
        child: Placed,
        decorations: &[Placed],
    )
    {
        let Some(entry) = self.collected.descriptions.get(&child.node)
        else {
            return;
        };
        let named = entry.named;
        let name = self.name_of(named);
        let mut attributes = Vec::new();
        let mut attributed = Ok(());
        for &block in decorations {
            if attributed.is_ok() {
                attributed = self.decoration(block, child.node, &mut attributes);
            }
        }
        let mut first = Maybe::Absent(slot_owner::Absent::Unowned);
        for (span, refusal) in self.described_refusals(child) {
            let introduced = Placed {
                node: child.node,
                span,
            };
            let top = self.collected.top(child.span.start());
            let held = self.held(top, name, introduced, named);
            if let Some(slot) = self.collected.slots.get_mut(held.0) {
                slot.signature = Maybe::Present(Half {
                    declaration: child,
                    named,
                    operand: Operand::Signature,
                });
                slot.refuse(child.node, refusal);
            }
            if let Maybe::Absent(_) = first {
                first = Maybe::Present(held);
            }
        }
        let Maybe::Present(owner) = first
        else {
            return;
        };
        self.collected.own(child.node, owner);
        for &block in decorations {
            self.collected.own(block.node, owner);
        }
        if let Some(slot) = self.collected.slots.get_mut(owner.0) {
            slot.attributes.append(&mut attributes);
            if let Err(refusal) = attributed {
                slot.refuse(child.node, refusal);
            }
        }
    }

    /// Collect the `theory` block at `child` as the definition of its name, a
    /// value of `Theory`, decorated by the attribute blocks `decorations`
    /// before it.
    ///
    /// # Specification
    /// - requires: `child` is a root child the description route described as a
    ///   `theory` block; `decorations` are attribute blocks standing on their
    ///   own before it.
    /// - ensures: a block none of whose members the description route or the
    ///   cell gate refused mints `Theory` when the module holds none, then
    ///   takes a declared slot under its name whose definition half is the
    ///   block itself; a refused block takes that slot too, refused by its
    ///   first refusal, and each further refusal one held slot at its member's
    ///   span with the block as its signature half, so the attributes the
    ///   decorations file under the block are read off every one of them. The
    ///   slot owns the block and its decorations; an unreadable decoration, or
    ///   a `Theory` the module declared otherwise, refuses it; a name declared
    ///   before refuses the block as a duplicate. Each `include` the block
    ///   writes is kept among the declared uses, its name tile beside the slot
    ///   owning the theory it includes.
    /// - provides: `theory S { … }` as the declaration `S : Theory` whose body
    ///   is the presentation's value.
    /// - panics: none.
    /// - executable: none — the slot it takes is chosen by the name table,
    ///   which the call reads and writes in one step.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a clean block defines its name as a value of `Theory`
    ///   that a program matching on `Theory` reads, and a refused block's name
    ///   is a declaration refused at its first member refusal that a decoration
    ///   before the block states.
    /// - witness: `description::theory::tests::a_theory_block_defines_its_presentation`
    /// - witness: `description::theory::tests::a_refused_theory_block_states_its_refusal`
    fn theory(
        &mut self,
        child: Placed,
        decorations: &[Placed],
    )
    {
        let Some(entry) = self.collected.descriptions.get(&child.node)
        else {
            return;
        };
        let named = entry.named;
        let included: Vec<(ByteSpan, NodeIndex)> = match entry.presentation {
            Maybe::Present(ref presentation) => presentation
                .inclusions
                .iter()
                .map(|inclusion| (inclusion.named.span, inclusion.block.node))
                .collect(),
            Maybe::Absent(_) => Vec::new(),
        };
        for (span, block) in included {
            if let Maybe::Present(slot) = self.collected.owner_of(block) {
                self.collected.declared_uses.push((span, slot));
            }
        }
        let name = self.name_of(named);
        let mut refusals = self.described_refusals(child).into_iter().peekable();
        let minted = match refusals.peek() {
            Some(_) => Ok(()),
            None => self.mint_theory(named),
        };
        let position = self.admit(self.collected.top(child.span.start()), name, child, named);
        self.collected.own(child.node, position);
        let mut attributes = Vec::new();
        let mut attributed = Ok(());
        for &block in decorations {
            self.collected.own(block.node, position);
            if attributed.is_ok() {
                attributed = self.decoration(block, child.node, &mut attributes);
            }
        }
        for &block in decorations {
            self.document(position, block.node, block.span.end(), child.node);
        }
        self.document(position, child.node, named.span.start(), child.node);
        if let Some(slot) = self.collected.slots.get_mut(usize::from(position)) {
            if slot.introduced_by.node == child.node {
                slot.definition = Maybe::Present(Half {
                    declaration: child,
                    named,
                    operand: Operand::Presented,
                });
                slot.attributes.extend(attributes);
                for refused in [attributed, minted] {
                    if let Err(refusal) = refused {
                        slot.refuse(child.node, refusal);
                    }
                }
                if let Some((_, refusal)) = refusals.next() {
                    slot.refuse(child.node, refusal);
                }
            }
            else {
                slot.refuse(child.node, LoweringRefusal::DuplicateDefinition {
                    span: child.span,
                    name,
                    first: slot.introduced_by.span,
                });
            }
        }
        for (span, refusal) in refusals {
            let introduced = Placed {
                node: child.node,
                span,
            };
            let top = self.collected.top(child.span.start());
            let held = self.held(top, name, introduced, named);
            if let Some(slot) = self.collected.slots.get_mut(held.0) {
                slot.signature = Maybe::Present(Half {
                    declaration: child,
                    named,
                    operand: Operand::Signature,
                });
                slot.refuse(child.node, refusal);
            }
        }
    }

    /// Admit `Theory`, the presentation code, and enter its constructors, at
    /// the name tile `named` of the `theory` block that first needs it; give a
    /// later block's source the code the module holds.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: on the first call, a declared slot `Theory` introduced at
    ///   `named`, whose definition half is the code, recorded as the module's
    ///   `Theory`. On the first call from each source, each constructor of
    ///   [`theory_desc`] entered by name in that source with its tag and field
    ///   count, as the minting block declares it, and the source recorded among
    ///   [`Collected::theory_sources`]: a later block's source names the one
    ///   code, and so do its importers ([`Collected::theory_in`]), whatever the
    ///   unit lays before it. On a later call from a recorded source, nothing.
    ///   When `Theory` or one of its constructors names something the source
    ///   declared before, nothing is admitted.
    /// - fails: [`LoweringRefusal::DuplicateDefinition`] naming the first
    ///   declaration of a name `Theory` would take.
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoweringRefusal::DuplicateDefinition`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — two clean blocks share one `Theory`, which a program
    ///   matches on by its constructors' names; a block of a source laid after
    ///   another source's block takes its code and names it.
    /// - witness: `description::theory::tests::a_theory_block_defines_its_presentation`
    /// - witness: `tests::namespace::a_theory_lowers_alike_whatever_the_unit_lays_before_it_1078`
    #[spec(
        captures: before = self.collected.theory.clone(),
        ensures: |ret| {
            (ret.is_err()
                || self
                    .collected
                    .theory_sources
                    .contains(&self.collected.unit.source_at(named.span.start())))
                && match before {
                    | Maybe::Present(ref held) => self.collected.theory == Maybe::Present(held.clone()),
                    | Maybe::Absent(_) => ret.is_err() || matches!(self.collected.theory, Maybe::Present(ref theory) if theory.arities.len() == THEORY_CONSTRUCTORS.len()),
                }
        },
    )]
    fn mint_theory(
        &mut self,
        named: Placed,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let source = self.collected.unit.source_at(named.span.start());
        if self.collected.theory_sources.contains(&source) {
            return Ok(());
        }
        let code = SurfaceName::from(THEORY_CODE);
        let taken = |name: SurfaceName<'source>, first: ByteSpan| {
            Err(LoweringRefusal::DuplicateDefinition {
                span: named.span,
                name,
                first,
            })
        };
        let top = self.collected.top(named.span.start());
        if let Some(slot) = self
            .collected
            .by_name
            .get(&(top, code))
            .and_then(|&position| self.collected.slots.get(position.0))
        {
            return taken(code, slot.introduced_by.span);
        }
        for constructor in THEORY_CONSTRUCTORS {
            let name = SurfaceName::from(constructor);
            if let Some(entry) = self.collected.constructors.get(&(source, name)) {
                return taken(name, entry.named.span);
            }
        }
        let theory = if let Maybe::Present(ref theory) = self.collected.theory {
            theory.clone()
        }
        else {
            let slot = self.admit(top, code, named, named);
            if let Some(entry) = self.collected.slots.get_mut(slot.0) {
                entry.definition = Maybe::Present(Half {
                    declaration: named,
                    named,
                    operand: Operand::Code,
                });
            }
            let arities = theory_desc(())
                .ctors
                .iter()
                .map(|constructor| constructor.arity().inputs.len())
                .collect();
            let theory = TheorySlot {
                slot,
                arities,
                named,
            };
            self.collected.theory = Maybe::Present(theory.clone());
            theory
        };
        for (tag, (&arity, name)) in theory.arities.iter().zip(THEORY_CONSTRUCTORS).enumerate() {
            let _fresh = self.collected.constructors.insert(
                (source, SurfaceName::from(name)),
                Constructor {
                    family: theory.slot,
                    form: Generators::Presentation,
                    tag,
                    arity,
                    named: theory.named,
                },
            );
        }
        let _first = self.collected.theory_sources.insert(source);

        Ok(())
    }

    /// Collect one declaration form, decorated by the attribute blocks
    /// `decorations` standing before it.
    ///
    /// # Specification
    /// - requires: `declaration` is a declaration form, and each of
    ///   `decorations` an attribute block standing before it.
    /// - ensures: the form's attributes, name and tail are read in that order,
    ///   the decorations' attributes before the form's own; the name is
    ///   admitted to its slot and the form and its decorations are owned by it;
    ///   the first fault of the form or a decoration is offered to the slot at
    ///   the form itself, and a form with no fault files its half and its
    ///   attributes.
    /// - provides: the per-declaration half of [`collect_source`].
    /// - fails: when the form has no name: the repair it holds, the form
    ///   standing where the name belongs, or a misplaced tile.
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoweringRefusal::MalformedForm`] and
    /// [`LoweringRefusal::OutOfFragment`] for a declaration with no name,
    /// and [`LoweringRefusal::UnknownMold`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — both half orders, duplicate halves and a nameless
    ///   form separate admission, refusal retention and module-level failure.
    /// - witness: `module::tests::a_signature_pairs_with_its_definition`
    /// - witness: `module::tests::a_definition_pairs_with_a_later_signature`
    /// - witness: `module::tests::a_second_signature_is_refused`
    /// - witness: `module::tests::a_second_definition_is_refused`
    /// - witness: `module::tests::a_declaration_whose_name_is_not_a_name_refuses_the_module`
    #[spec(
        captures: before = (
            self.collected.slots.len(),
            self.collected.structures.len(),
            self.collected.imports.declarations().len(),
        ),
        ensures: |ret| {
            self.collected.slots.len() >= before.0
                && self.collected.structures.len() == before.1
                && self.collected.imports.declarations().len() == before.2
                && (ret.is_err()
                    || matches!(self.collected.owner_of(declaration.node), Maybe::Present(_)))
        },
    )]
    fn declaration(
        &mut self,
        declaration: Placed,
        decorations: &[Placed],
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let mut pieces = core::mem::take(&mut self.pieces);
        read_pieces(self.pbg, self.tree, declaration.node, &mut pieces)?;
        let top = self.collected.top(declaration.span.start());
        let outcome = self.read_declaration(top, declaration, &pieces, decorations);
        self.pieces = pieces;

        outcome
    }

    /// Collect one import, `import "URI" ;` or `import "URI" as name ;`, of
    /// form `form`.
    ///
    /// # Specification
    /// - requires: `import` is an import form named `form`.
    /// - ensures: the import's address — the text between its quotes with its
    ///   escapes decoded — its binding, its bytes, its source and what its
    ///   address came to are kept after every earlier import, and its alias,
    ///   when it has one, is bound in its source's scope. An address with a
    ///   scheme is [`ImportResolution::Foreign`]; a path is the unit's target
    ///   for the source's next path import.
    /// - provides: the import half of [`collect_source`].
    /// - fails: [`LoweringRefusal::MalformedForm`] for a repair or a tile out
    ///   of place, and [`LoweringRefusal::DuplicateImportAlias`] for an alias
    ///   an earlier import of its source binds.
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoweringRefusal::MalformedForm`],
    /// [`LoweringRefusal::DuplicateImportAlias`] and
    /// [`LoweringRefusal::UnknownMold`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — two imports, an escaped address, an unqualified
    ///   import and two imports of one alias, each asserted as the exact import
    ///   list or refusal over the parsed source.
    /// - witness: `tests::namespace::source_import_reaches_the_namespace_engine_and_exposes_its_alias`
    /// - witness: `tests::namespace::an_import_binds_its_alias_and_resolves_no_address`
    /// - witness: `tests::namespace::an_unqualified_import_binds_no_alias`
    /// - witness: `tests::namespace::duplicate_source_import_alias_becomes_a_refusal`
    #[spec(
        captures: before = (
            self.collected.imports.declarations().len(),
            self.collected.slots.len(),
            self.collected.structures.len(),
        ),
        ensures: |ret| {
            self.collected.slots.len() == before.1
                && self.collected.structures.len() == before.2
                && self.collected.imports.declarations().len()
                    == before.0.saturating_add(usize::from(ret.is_ok()))
                && (ret.is_err()
                    || self
                        .collected
                        .imports
                        .declarations()
                        .last()
                        .is_some_and(|entry| entry.span() == import.span))
        },
    )]
    fn import(
        &mut self,
        import: Placed,
        form: FormName,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let mut pieces = core::mem::take(&mut self.pieces);
        read_pieces(self.pbg, self.tree, import.node, &mut pieces)?;
        let outcome = read_import(self.tree, import, form, &pieces);
        self.pieces = pieces;
        let written = outcome?;
        let source = self.collected.unit.source_at(import.span.start());
        let resolution = match written.address {
            Address::Scheme => ImportResolution::Foreign,
            Address::Path => {
                let ordinal = self.ordinals.entry(source).or_default();
                let target = self.collected.unit.target(source, *ordinal);
                *ordinal = ordinal.next();
                ImportResolution::Path(target)
            },
        };
        let binding = match written.alias {
            Maybe::Present(alias) => ImportBinding::Aliased(self.name_of(alias)),
            Maybe::Absent(_) => ImportBinding::Unqualified,
        };

        self.collected.imports.bind(ImportDeclaration::new(
            written.uri,
            binding,
            import.span,
            source,
            resolution,
        ))
    }

    /// Read one declaration form's pieces into its slot in `container`,
    /// decorated by the attribute blocks `decorations` standing before it.
    ///
    /// # Specification
    /// - requires: `pieces` is the reading of the form `declaration`, a
    ///   top-level declaration or a definition member of the module `container`
    ///   names, and each of `decorations` an attribute block standing before
    ///   it.
    /// - ensures: as [`Self::declaration`], the name admitted in `container`.
    /// - provides: the reading half of [`Self::declaration`] and of a module's
    ///   definition members, whose blocks are inside the form, over a borrowed
    ///   reading.
    /// - fails: as [`Self::declaration`].
    /// - panics: none.
    ///
    /// # Errors
    /// As [`Self::declaration`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — separate half order, duplicate declarations and
    ///   stacked attribute blocks preserve admission and owning-slot
    ///   correspondence.
    /// - witness: `module::tests::a_signature_pairs_with_its_definition`
    /// - witness: `module::tests::a_definition_pairs_with_a_later_signature`
    /// - witness: `module::tests::a_second_signature_is_refused`
    /// - witness: `module::tests::a_second_definition_is_refused`
    /// - witness: `module::tests::an_attribute_block_decorates_the_declaration_after_it`
    /// - witness: `module::tests::a_module_member_reads_the_blocks_inside_its_form`
    #[spec(
        captures: before = (self.collected.slots.len(), self.collected.structures.len()),
        ensures: |ret| {
            self.collected.slots.len() >= before.0
                && self.collected.structures.len() == before.1
                && (ret.is_err()
                    || match self.collected.owner_of(declaration.node) {
                        | Maybe::Present(slot) => self
                            .collected
                            .slots
                            .get(slot.0)
                            .is_some_and(|entry| entry.container == container),
                        | Maybe::Absent(_) => false,
                    })
        },
    )]
    fn read_declaration(
        &mut self,
        container: Container,
        declaration: Placed,
        pieces: &Pieces,
        decorations: &[Placed],
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let split = pieces.pieces.iter().position(
            |piece| matches!(*piece, Piece::Tile { label, .. } if label == TileName::DEF),
        );
        let Some((before, after)) = split.and_then(|at| pieces.pieces.split_at_checked(at))
        else {
            let header = Cursor::new(&pieces.pieces, declaration.span);
            return Err(self.unnamed(pieces, declaration, &header));
        };
        let mut attributes = Vec::new();
        let mut attributed = Ok(());
        for &block in decorations {
            if attributed.is_ok() {
                attributed = self.decoration(block, declaration.node, &mut attributes);
            }
        }
        if attributed.is_ok() {
            attributed = self.read_attributes(
                Cursor::new(before, declaration.span),
                declaration.node,
                &mut attributes,
            );
        }
        let mut header = Cursor::new(after, declaration.span);
        let _def = header.tile(TileName::DEF);
        let recursive = header.tile(TileName::REC);
        let Maybe::Present(named) = header.tile(TileName::IDENTIFIER)
        else {
            return Err(self.unnamed(pieces, declaration, &header));
        };
        let name = self.name_of(named);
        let slot = self.admit(container, name, declaration, named);
        self.collected.own(declaration.node, slot);
        if let Maybe::Present(_) = recursive {
            let _fresh = self.collected.recursive.insert(slot);
        }
        for &block in decorations {
            self.collected.own(block.node, slot);
            self.document(slot, block.node, block.span.end(), declaration.node);
        }
        self.document(slot, declaration.node, named.span.start(), declaration.node);
        let tail = if let Maybe::Present(repaired) = pieces.repair {
            Tail::Refused(repaired.refusal(FormName::DECLARATION))
        }
        else if let Err(refusal) = attributed {
            Tail::Refused(refusal)
        }
        else {
            let merged = match self.merged_telescope(&header, declaration) {
                Ok(Maybe::Present(entries)) => Some(Ok(entries)),
                Ok(Maybe::Absent(_)) => None,
                Err(refusal) => Some(Err(refusal)),
            };
            if let Some(merged) = merged {
                let _first = self.collected.plicities.insert(slot, merged);
            }
            if let Ok(binders) = self.stage_binders(&header)
                && !binders.is_empty()
            {
                let _first = self.collected.stage_binders.insert(slot, binders);
            }
            if let Container::Module(_) = container
                && let Some(mode) = receiver_of(
                    &header,
                    |tile| self.name_of(tile),
                    |operand| self.root_former(operand).ok(),
                )
            {
                let _first = self.collected.receivers.insert(slot, mode);
            }
            read_tail(&mut header, declaration)
        };
        self.file(slot, declaration, named, tail, attributes);

        Ok(())
    }

    /// The module refusal for a declaration form with no name.
    ///
    /// # Specification
    /// - requires: `header` stands where the name belongs.
    /// - ensures: the form's repair when it holds one, the form standing where
    ///   the name belongs when one does, and a misplaced tile otherwise.
    /// - provides: the one module-level refusal a declaration form raises.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an operand where the identifier belongs is refused at
    ///   its exact span and wrong sort; this witness does not enumerate repair
    ///   shapes.
    /// - witness: `module::tests::a_declaration_whose_name_is_not_a_name_refuses_the_module`
    #[spec(
        ensures: |ret| match pieces.repair {
            | Maybe::Present(repaired) => {
                ret == repaired.refusal(FormName::DECLARATION)
            },
            | Maybe::Absent(_) => matches!(
                ret,
                LoweringRefusal::MalformedForm {
                    form: FormName::DECLARATION,
                    fault: FormFault::MisplacedTile,
                    ..
                } | LoweringRefusal::OutOfFragment {
                    sort: FragmentSort::Declaration,
                    boundary: FragmentBoundary::WrongSort,
                    ..
                }
            ),
        },
    )]
    fn unnamed(
        &self,
        pieces: &Pieces,
        declaration: Placed,
        header: &Cursor<'_>,
    ) -> LoweringRefusal<'source>
    {
        if let Maybe::Present(repaired) = pieces.repair {
            return repaired.refusal(FormName::DECLARATION);
        }
        if let Maybe::Present(Piece::Operand(standing)) = header.peek()
            && let Some(held) = self.tree.node(standing.node)
            && let Ok(Shape::Form { name, .. }) = shape_of(self.pbg, held)
        {
            return LoweringRefusal::OutOfFragment {
                span: standing.span,
                form: name,
                sort: FragmentSort::Declaration,
                boundary: FragmentBoundary::WrongSort,
            };
        }
        let span = match header.peek() {
            Maybe::Present(_) => header.here(),
            Maybe::Absent(_) => declaration.span,
        };

        misplaced(span)
    }

    /// Read the attribute blocks written before `def`.
    ///
    /// # Specification
    /// - requires: `cursor` stands over the pieces before the form's `def`
    ///   tile.
    /// - ensures: every attribute of every block is pushed onto `attributes` in
    ///   source order, decorating `declaration`; the first fault stops the
    ///   reading.
    /// - provides: the attribute half of a declaration form.
    /// - fails: yields the first fault, as [`Self::read_block`] does.
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoweringRefusal::MalformedForm`] for a block out of shape.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — stacked blocks retain source order and their
    ///   declaration owner; malformed or duplicate attributes remain located by
    ///   lowering. The predicate reads only the attributes this call appended.
    /// - witness: `module::tests::an_attribute_block_decorates_the_declaration_after_it`
    /// - witness: `lower::tests::an_attribute_is_filed_under_its_declaration_key`
    #[spec(
        captures: before = attributes.len(),
        ensures: attributes.get(before ..).is_some_and(|appended| {
            appended.iter().all(|entry| entry.decorates == declaration)
        }),
    )]
    fn read_attributes(
        &self,
        mut cursor: Cursor<'_>,
        declaration: NodeIndex,
        attributes: &mut Vec<WrittenAttribute<'source>>,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        while let Maybe::Present(_) = cursor.peek() {
            if let Maybe::Absent(_) = cursor.tile(TileName::ATTRIBUTES) {
                return Err(misplaced(cursor.here()));
            }
            self.read_block(&mut cursor, declaration, attributes)?;
        }

        Ok(())
    }

    /// Read one attribute block, after its `@[`.
    ///
    /// # Specification
    /// - requires: `cursor` stands just past a block's `@[` tile.
    /// - ensures: each `name` or `name(payload)` up to the block's `]` is
    ///   pushed onto `attributes`, separated by commas.
    /// - provides: the per-block half of [`Self::read_attributes`].
    /// - fails: yields a misplaced-tile refusal for a block whose tiles are out
    ///   of order, and an extra-operand refusal for a payload of more than one
    ///   form or an operand following a name.
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoweringRefusal::MalformedForm`] for a block out of shape.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a block with a payload and stacked marker blocks
    ///   attach to the same declaration, preserving their source order. The
    ///   predicate reads only the attributes this call appended.
    /// - witness: `module::tests::an_attribute_block_decorates_the_declaration_after_it`
    /// - witness: `lower::tests::an_attribute_is_filed_under_its_declaration_key`
    #[spec(
        captures: before = attributes.len(),
        ensures: attributes.get(before ..).is_some_and(|appended| {
            appended.iter().all(|entry| entry.decorates == declaration)
        }),
    )]
    fn read_block(
        &self,
        cursor: &mut Cursor<'_>,
        declaration: NodeIndex,
        attributes: &mut Vec<WrittenAttribute<'source>>,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        loop {
            attributes.push(self.read_attribute(cursor, declaration)?);
            if let Maybe::Present(_) = cursor.tile(TileName::COMMA)
                && let Maybe::Absent(_) = cursor.at(TileName::BRACKET_CLOSE)
            {
                continue;
            }
            if let Maybe::Present(_) = cursor.tile(TileName::BRACKET_CLOSE) {
                return Ok(());
            }
            return Err(misplaced(cursor.here()));
        }
    }

    /// Read one attribute: its name, and its payload when parenthesised.
    ///
    /// # Specification
    /// - requires: `cursor` stands where an attribute's name belongs.
    /// - ensures: the attribute's name, the bytes from its name through its
    ///   closing parenthesis, and its payload, which is unwritten for a bare
    ///   name and for empty parentheses.
    /// - provides: the per-attribute half of [`Self::read_block`].
    /// - fails: as [`Self::read_block`].
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoweringRefusal::MalformedForm`] for an attribute out of shape.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — bare marker and integer-payload records retain the
    ///   owning declaration, exact spelling and covering source span. The
    ///   predicate asks for the name tile's own bytes, by address and length.
    /// - witness: `module::tests::an_attribute_block_decorates_the_declaration_after_it`
    /// - witness: `lower::tests::an_attribute_is_filed_under_its_declaration_key`
    #[spec(
        ensures: |ret| {
            ret.as_ref().map_or(true, |entry| {
                entry.decorates == declaration
                    && core::ptr::eq(
                        core::ptr::from_ref::<str>(entry.name.as_ref()),
                        core::ptr::from_ref::<str>(self.name_of(entry.at).as_ref()),
                    )
                    && entry.span.start() <= entry.at.span.start()
                    && entry.span.end() >= entry.at.span.end()
            })
        },
    )]
    fn read_attribute(
        &self,
        cursor: &mut Cursor<'_>,
        declaration: NodeIndex,
    ) -> Result<WrittenAttribute<'source>, LoweringRefusal<'source>>
    {
        let Maybe::Present(at) = cursor.tile(TileName::IDENTIFIER)
        else {
            return Err(misplaced(cursor.here()));
        };
        let mut written = WrittenAttribute {
            name: self.name_of(at),
            at,
            span: at.span,
            payload: Payload::Unwritten,
            decorates: declaration,
        };
        if let Maybe::Present(_) = cursor.tile(TileName::PAREN_OPEN) {
            written.payload = match cursor.operands() {
                Run::Empty(_) => Payload::Unwritten,
                Run::One(payload) => Payload::Written(payload),
                Run::Several { extra, .. } => {
                    return Err(extra_operand(FormName::ATTRIBUTE, extra));
                },
            };
            let Maybe::Present(close) = cursor.tile(TileName::PAREN_CLOSE)
            else {
                return Err(misplaced(cursor.here()));
            };
            written.span = at.span.join(close.span);
        }
        match cursor.operands() {
            Run::Empty(_) => Ok(written),
            Run::One(stray) | Run::Several { first: stray, .. } => {
                Err(extra_operand(FormName::ATTRIBUTE, stray))
            },
        }
    }

    /// File one read declaration form into its slot.
    ///
    /// # Specification
    /// - requires: `slot` names a live slot; `declaration` is the form read,
    ///   and `named` the name tile it writes.
    /// - ensures: a fault is offered to the slot at the form itself; a clean
    ///   form's halves — one for a signature or a definition, the definition
    ///   for a function tail and its signature too when the tail is signed —
    ///   are recorded unless the slot already holds one of their kinds, which
    ///   offers the duplicate refusal naming the first instead and records none
    ///   of them. A written signature and the signature a signed function tail
    ///   derives are not duplicates: the written one is the slot's, whichever
    ///   came first, and the derived one is filed as a witness checking it. A
    ///   clean form's attributes join the slot's in source order, once whatever
    ///   the halves it writes.
    /// - provides: the filing half of [`Self::declaration`].
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — paired halves, duplicate halves,
    ///   written-versus-derived signatures, a signature written after its
    ///   signed function, and rejected tails separate filing from refusal and
    ///   witness creation.
    /// - witness: `module::tests::a_signature_pairs_with_its_definition`
    /// - witness: `module::tests::a_definition_pairs_with_a_later_signature`
    /// - witness: `module::tests::a_second_signature_is_refused`
    /// - witness: `module::tests::a_second_definition_is_refused`
    /// - witness: `tests::modules::member_signature_attaches_and_wins_over_derived_function_type`
    /// - witness: `tests::modules::signatures_attach_to_their_defs`
    /// - witness: `module::tests::a_declaration_missing_its_body_is_refused`
    /// - witness: `lower::tests::a_signature_written_after_its_signed_function_is_no_duplicate`
    #[spec(
        captures: before = (
            self.collected.slots.len(),
            self.collected
                .slots
                .get(slot.0)
                .map(|entry| (entry.signature, entry.definition, entry.attributes.len())),
            attributes.len(),
        ),
        ensures: |_| {
            let Some((signature, definition, count)) = before.1
            else {
                return self.collected.slots.len() == before.0;
            };
            let Some(entry) = self.collected.slots.get(slot.0)
            else {
                return false;
            };
            let (incoming, signs, defines) = match tail {
                | Tail::Wrote(HalfKind::Signature, operand) => {
                    (Operand::Written(operand), true, false)
                },
                | Tail::Wrote(HalfKind::Definition, operand) => {
                    (Operand::Written(operand), false, true)
                },
                | Tail::Function(signing) => (Operand::Function, signing == Signing::Signed, true),
                | Tail::Data(form) => (Operand::Data(form), false, true),
                | Tail::World => (Operand::World, false, true),
                | Tail::Refused(_) => {
                    return entry.signature == signature
                        && entry.definition == definition
                        && entry.attributes.len() == count
                        && self.collected.slots.len() == before.0;
                },
            };
            let mixed = matches!(
                (signature, incoming),
                (
                    Maybe::Present(Half {
                        operand: Operand::Written(_),
                        ..
                    }),
                    Operand::Function
                ) | (
                    Maybe::Present(Half {
                        operand: Operand::Function,
                        ..
                    }),
                    Operand::Written(_)
                )
            );
            let duplicate = (signs && matches!(signature, Maybe::Present(_)) && !mixed)
                || (defines && matches!(definition, Maybe::Present(_)));
            if duplicate {
                entry.signature == signature
                    && entry.definition == definition
                    && entry.attributes.len() == count
                    && self.collected.slots.len() == before.0
            }
            else {
                let half = Maybe::Present(Half {
                    declaration,
                    named,
                    operand: incoming,
                });
                entry.signature
                    == if signs && !(mixed && incoming == Operand::Function) {
                        half
                    }
                    else {
                        signature
                    }
                    && entry.definition == if defines { half } else { definition }
                    && entry.attributes.len() == count.saturating_add(before.2)
                    && self.collected.slots.len()
                        == before.0.saturating_add(usize::from(signs && mixed))
            }
        },
    )]
    fn file(
        &mut self,
        slot: SlotIndex,
        declaration: Placed,
        named: Placed,
        tail: Tail<'source>,
        attributes: Vec<WrittenAttribute<'source>>,
    )
    {
        let Some(entry) = self.collected.slots.get_mut(slot.0)
        else {
            return;
        };
        let (operand, kinds): (Operand, &[HalfKind]) = match tail {
            Tail::Wrote(HalfKind::Signature, operand) => {
                (Operand::Written(operand), &[HalfKind::Signature])
            },
            Tail::Wrote(HalfKind::Definition, operand) => {
                (Operand::Written(operand), &[HalfKind::Definition])
            },
            Tail::Function(Signing::Signed) => (Operand::Function, &[
                HalfKind::Signature,
                HalfKind::Definition,
            ]),
            Tail::Function(Signing::Unsigned) => (Operand::Function, &[HalfKind::Definition]),
            Tail::Data(form) => (Operand::Data(form), &[HalfKind::Definition]),
            Tail::World => (Operand::World, &[HalfKind::Definition]),
            Tail::Refused(refusal) => {
                entry.refuse(declaration.node, refusal);
                return;
            },
        };
        let incoming = Half {
            declaration,
            named,
            operand,
        };
        let mut derived = Maybe::Absent(declaration_half::Absent::Unwritten);
        for &kind in kinds {
            let held = match kind {
                HalfKind::Signature => entry.signature,
                HalfKind::Definition => entry.definition,
            };
            let Maybe::Present(first) = held
            else {
                continue;
            };
            if kind == HalfKind::Signature {
                match (first.operand, operand) {
                    (Operand::Written(_), Operand::Function) => {
                        derived = Maybe::Present(incoming);
                        continue;
                    },
                    (Operand::Function, Operand::Written(_)) => {
                        derived = Maybe::Present(first);
                        continue;
                    },
                    _ => {},
                }
            }
            let (span, name, first) = (declaration.span, entry.name, first.declaration.span);
            let refusal = match kind {
                HalfKind::Signature => LoweringRefusal::DuplicateSignature { span, name, first },
                HalfKind::Definition => LoweringRefusal::DuplicateDefinition { span, name, first },
            };
            entry.refuse(declaration.node, refusal);
            return;
        }
        for &kind in kinds {
            match kind {
                HalfKind::Signature => {
                    if derived != Maybe::Present(incoming) {
                        entry.signature = Maybe::Present(incoming);
                    }
                },
                HalfKind::Definition => entry.definition = Maybe::Present(incoming),
            }
        }
        entry.attributes.extend(attributes);
        if let Maybe::Present(stated) = derived {
            let _witness = self.witness(slot, stated);
        }
    }

    /// The slot `name` occupies in `container`, creating it at the next
    /// admission position when this is the name's first declaration there,
    /// written by the tile `named` of the form `declaration`.
    ///
    /// # Specification
    /// - requires: the collection's slots and name table describe the same
    ///   collection so far.
    /// - ensures: a name already declared in `container` keeps its admission
    ///   position, and a fresh name takes the next one and joins its module's
    ///   members; the returned index always names a live slot.
    /// - provides: the collect-by-name half of the pass.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a repeated name retains its original slot while a new
    ///   name appends, including names local to distinct module containers.
    /// - witness: `module::tests::a_signature_pairs_with_its_definition`
    /// - witness: `module::tests::a_definition_pairs_with_a_later_signature`
    /// - witness: `module::tests::a_second_signature_is_refused`
    /// - witness: `module::tests::a_second_definition_is_refused`
    /// - witness: `tests::modules::modules_lower_to_named_member_declarations`
    /// - witness: `tests::modules::module_members_admit_in_source_order`
    #[spec(
        captures: before = (
            self.collected.slots.len(),
            self.collected.by_name.get(&(container, name)).copied(),
        ),
        ensures: |ret| {
            self.collected.by_name.get(&(container, name)) == Some(&ret)
                && self.collected.slots.get(ret.0).is_some_and(|slot| {
                    slot.name == name && slot.container == container && slot.role == Role::Declared
                })
                && match before.1 {
                    | Some(prior) => ret == prior && self.collected.slots.len() == before.0,
                    | None => {
                        ret.0 == before.0
                            && self.collected.slots.len() == before.0.saturating_add(1)
                    },
                }
        },
    )]
    fn admit(
        &mut self,
        container: Container,
        name: SurfaceName<'source>,
        declaration: Placed,
        named: Placed,
    ) -> SlotIndex
    {
        if let Some(&existing) = self.collected.by_name.get(&(container, name)) {
            return existing;
        }
        let minted = SlotIndex(self.collected.slots.len());
        self.collected.slots.push(DeclarationSlot {
            name,
            container,
            role: Role::Declared,
            constant: ConstantIndex::from(minted.0),
            introduced_by: declaration,
            named,
            signature: Maybe::Absent(declaration_half::Absent::Unwritten),
            definition: Maybe::Absent(declaration_half::Absent::Unwritten),
            attributes: Vec::new(),
            docs: Vec::new(),
            refusal: Maybe::Absent(slot_refusal::Absent::Unrefused),
        });
        self.collected.by_name.insert((container, name), minted);
        if let Container::Module(module) = container
            && let Some(entry) = self.collected.structures.get_mut(module.0)
        {
            entry.members.push(Member::Slot(minted));
        }

        minted
    }

    /// File `stated`, a second type for the member at `target`, as a witness:
    /// a slot whose signature is `stated` and whose body is the member.
    ///
    /// # Specification
    /// - requires: `target` names a live slot.
    /// - ensures: the witness takes the next admission position, after the
    ///   member's, under the member's name and module, and is entered in no
    ///   name table; it declares nothing a reference can reach.
    /// - provides: the check that two types stated for one member agree,
    ///   carried out by the checker as the body's type meeting the signature.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a written signature before or after a signed tail
    ///   keeps the written type and checks the derived type through a separate
    ///   witness.
    /// - witness: `tests::modules::member_signature_attaches_and_wins_over_derived_function_type`
    /// - witness: `tests::modules::signatures_attach_to_their_defs`
    #[spec(
        requires: target.0 < self.collected.slots.len(),
        captures: before = (self.collected.slots.len(), self.collected.by_name.len()),
        ensures: |ret| {
            ret.0 == before.0
                && self.collected.slots.len() == before.0.saturating_add(1)
                && self.collected.by_name.len() == before.1
                && self.collected.slots.get(ret.0).is_some_and(|slot| {
                    slot.role == Role::Witness
                        && slot.signature == Maybe::Present(stated)
                        && slot.definition
                            == Maybe::Present(Half {
                                declaration: stated.declaration,
                                named: stated.named,
                                operand: Operand::Member(target),
                            })
                        && slot.attributes.is_empty()
                        && matches!(slot.refusal, Maybe::Absent(_))
                })
        },
    )]
    fn witness(
        &mut self,
        target: SlotIndex,
        stated: Half,
    ) -> SlotIndex
    {
        let minted = SlotIndex(self.collected.slots.len());
        let Some(entry) = self.collected.slots.get(target.0)
        else {
            return minted;
        };
        let witness = DeclarationSlot {
            name: entry.name,
            container: entry.container,
            role: Role::Witness,
            constant: ConstantIndex::from(minted.0),
            introduced_by: stated.declaration,
            named: entry.named,
            signature: Maybe::Present(stated),
            definition: Maybe::Present(Half {
                declaration: stated.declaration,
                named: stated.named,
                operand: Operand::Member(target),
            }),
            attributes: Vec::new(),
            docs: Vec::new(),
            refusal: Maybe::Absent(slot_refusal::Absent::Unrefused),
        };
        self.collected.slots.push(witness);

        minted
    }

    /// The identifier the tile `tile` spells.
    ///
    /// # Specification
    /// - requires: nothing — a node without source text is admissible.
    /// - ensures: the stored source fragment is returned unchanged; a missing
    ///   fragment answers the empty name.
    /// - provides: identifier spelling without lexing or copying its bytes.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — paired declarations and differently named nested
    ///   members retain their source spellings through collection.
    /// - witness: `module::tests::a_signature_pairs_with_its_definition`
    /// - witness: `tests::modules::modules_lower_to_named_member_declarations`
    #[spec(
        ensures: |ret| {
            self.tree.fragment(tile.node).map_or_else(
                || ret.as_ref().is_empty(),
                |fragment| ret.as_ref() == fragment.as_ref(),
            )
        },
    )]
    fn name_of(
        &self,
        tile: Placed,
    ) -> SurfaceName<'source>
    {
        self.tree
            .fragment(tile.node)
            .map_or_else(|| SurfaceName::from(""), SurfaceName::from)
    }

    /// File under `slot` the documentation `holder` holds, ending at or before
    /// `before`, as documenting the declaration form at `documents`.
    ///
    /// # Specification
    /// - requires: `holder` is the declaration form at `documents`, or an
    ///   attribute block standing before it.
    /// - ensures: each [`NodeLabel::Doc`] child of `holder` whose span ends at
    ///   or before `before` joins the slot's documentation, in child order; a
    ///   documentation node after `before` documents something inside the form
    ///   rather than the form, and is left alone.
    /// - provides: the documentation half of collection.
    /// - fails: never; an unlisted slot files nothing.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — documentation before a definition, before a data
    ///   declaration and in its own block reach the declaration, while a
    ///   comment of `///` lines inside a data body does not.
    /// - witness: `lower::tests::documentation_is_filed_under_the_declaration_key`
    #[spec(
        captures: before_docs = self.collected.slots.get(slot.0).map_or(0, |entry| entry.docs.len()),
        ensures: self.collected.slots.get(slot.0).is_none_or(|entry| entry.docs.len() >= before_docs),
    )]
    fn document(
        &mut self,
        slot: SlotIndex,
        holder: NodeIndex,
        before: ByteOffset,
        documents: NodeIndex,
    )
    {
        let tree = self.tree;
        if let Some(entry) = self.collected.slots.get_mut(slot.0) {
            written_docs(tree, holder, before, documents, &mut entry.docs);
        }
    }

    /// Keep beside the slots the documentation `holder` holds, ending at or
    /// before `before`, as documenting the module form at `documents`.
    ///
    /// # Specification
    /// - requires: `holder` is the module form at `documents`, or an attribute
    ///   block standing before it.
    /// - ensures: as [`Self::document`], into the collection's module
    ///   documentation rather than a slot's.
    /// - provides: the module half of the documentation's collection.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — documentation before a module, before a decorated one
    ///   and before a nested one reaches its module form, while a member's
    ///   stays its own.
    /// - witness: `lower::tests::a_module_s_documentation_is_filed_under_its_key_1135`
    #[spec(
        captures: before_docs = self.collected.module_docs.len(),
        ensures: self.collected.module_docs.len() >= before_docs,
    )]
    fn document_module(
        &mut self,
        holder: NodeIndex,
        before: ByteOffset,
        documents: NodeIndex,
    )
    {
        written_docs(
            self.tree,
            holder,
            before,
            documents,
            &mut self.collected.module_docs,
        );
    }
}

/// Push onto `out` each documentation child of `holder` in `tree` ending at or
/// before `before`, as documenting the form at `documents`, in child order.
///
/// # Specification
/// trivial.
fn written_docs(
    tree: &SyntaxTree<'_>,
    holder: NodeIndex,
    before: ByteOffset,
    documents: NodeIndex,
    out: &mut Vec<WrittenDoc>,
)
{
    for child in tree.children(holder) {
        let Some(node) = tree.node(child)
        else {
            continue;
        };
        if node.label() == NodeLabel::Doc && node.span().end() <= before {
            out.push(WrittenDoc {
                at: Placed::of(child, node),
                documents,
            });
        }
    }
}

/// The kind a telescope type is written as, the only form a signature states
/// a nested module's components with: its labelled entries are the
/// components.
const TELESCOPE_TYPE: &str = "telescope_type";

/// The name the presentation code takes.
pub const THEORY_CODE: &str = "Theory";

/// A module form's header, read.
///
/// # Specification
/// - requires: nothing to construct this data; its producers and consumers
///   state coordinate preconditions separately.
/// - ensures: A readable module header retains the name tile, optional
///   transparent signature and source-ordered member forms for subsequent
///   traversal.
/// - fails: not applicable to the data item.
/// - panics: not applicable to the data item.
/// - executable: none — the enabled specification facade does not expose
///   type-invariant expansion; executable predicates cover the producing and
///   consuming operations.
///
/// # Adequacy
/// - hypothesis: L3 — readable and empty bodies stay distinct from unread
///   bodies, and a sealed body from a transparently ascribed one.
/// - witness: `tests::modules::modules_lower_to_named_member_declarations`
/// - witness: `tests::modules::module_members_admit_in_source_order`
/// - witness: `tests::modules::a_readable_module_keeps_its_members_and_its_successor`
/// - witness: `tests::modules::an_empty_module_is_not_an_unread_one`
/// - witness: `tests::modules::opaque_ascription_seals`
#[derive(Clone, Debug)]
struct Opened<'source>
{
    /// The module's name.
    name: SurfaceName<'source>,
    /// The name's tile.
    named: Placed,
    /// The inline signature's components, when ascribed.
    ascription: Maybe<Vec<Component<'source>>, ascription::Absent>,
    /// The model signature the ascription derives, when it is `Model(S)`.
    model: Maybe<crate::model::ModelSignature, derived::Absent>,
    /// Whether the ascription is opaque.
    sealed: Sealed,
    /// The body's member forms, in source order.
    members: Vec<Placed>,
    /// The functor parameter, when the form declares a functor.
    parameter: Maybe<WrittenParameter<'source>, parameter::Absent>,
}

/// What reading a module form's header found.
///
/// # Specification
/// - requires: nothing to construct this data; its producers and consumers
///   state coordinate preconditions separately.
/// - ensures: A readable header carries its body, a named refusal suppresses
///   that body, and an unnamed refusal cannot be filed under a module name.
/// - fails: not applicable to the data item.
/// - panics: not applicable to the data item.
/// - executable: none — the enabled specification facade does not expose
///   type-invariant expansion; executable predicates cover the producing and
///   consuming operations.
///
/// # Adequacy
/// - hypothesis: L3 — readable, lowercase and unread bodies take separate
///   header outcomes.
/// - witness: `tests::modules::modules_lower_to_named_member_declarations`
/// - witness: `tests::modules::module_members_admit_in_source_order`
/// - witness: `tests::modules::a_readable_module_keeps_its_members_and_its_successor`
/// - witness: `tests::modules::opaque_ascription_seals`
/// - witness: `tests::modules::module_name_case_boundary_covers_single_and_multi_names`
/// - witness: `tests::modules::an_unread_module_body_is_refused_not_emptied`
#[derive(Clone, Debug)]
enum Header<'source>
{
    /// A module whose body is read.
    Opened(Opened<'source>),
    /// A functor application binding its instance.
    Applied(Applied<'source>),
    /// A named module refused as a whole, its body unread.
    Refused
    {
        /// The module's name.
        name: SurfaceName<'source>,
        /// The name's tile, or the form standing where it belongs.
        named: Placed,
        /// Why the module is refused.
        refusal: LoweringRefusal<'source>,
    },
    /// A module with no name to refuse it under.
    Unnamed(LoweringRefusal<'source>),
}

/// One module whose body is being read.
///
/// # Specification
/// - requires: nothing to construct this data; its producers and consumers
///   state coordinate preconditions separately.
/// - ensures: The stack frame associates one admitted structure with its
///   remaining source members; its cursor counts members already visited.
/// - fails: not applicable to the data item.
/// - panics: not applicable to the data item.
/// - executable: none — the enabled specification facade does not expose
///   type-invariant expansion; executable predicates cover the producing and
///   consuming operations.
///
/// # Adequacy
/// - hypothesis: L3 — depth-eight traversal preserves pre-order admission and
///   resolves each nested level.
/// - witness: `tests::modules::deeply_nested_modules_lower_and_resolve_at_every_depth`
#[derive(Clone, Debug)]
struct Open
{
    /// The module.
    structure: StructureIndex,
    /// The body's member forms, in source order.
    members: Vec<Placed>,
    /// How many of them have been read.
    next: usize,
}

/// A signature a module's enclosing module states for it, applied after the
/// module's own.
///
/// # Specification
/// - requires: nothing to construct this data; its producers and consumers
///   state coordinate preconditions separately.
/// - ensures: An enclosing signature records the nested structure it constrains
///   and the manifest prefix visible to its field types; the original export
///   set bounds the result.
/// - fails: not applicable to the data item.
/// - panics: not applicable to the data item.
/// - executable: none — the enabled specification facade does not expose
///   type-invariant expansion; executable predicates cover the producing and
///   consuming operations.
///
/// # Adequacy
/// - hypothesis: L3 — a nested member signature constrains the parent binding
///   and hides omitted fields.
/// - witness: `tests::modules::nested_member_signature_constrains_the_parent_binding`
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Layer
{
    /// The module the signature is stated for.
    structure: StructureIndex,
    /// The record type stating it.
    record: Placed,
    /// The manifest type components its types see.
    scope: Maybe<ComponentScope, component_scope::Absent>,
}

/// One field `name : T` of a record type.
///
/// # Specification
/// - requires: nothing to construct this data; its producers and consumers
///   state coordinate preconditions separately.
/// - ensures: A record field pairs the source spelling and name tile with
///   exactly one stated type operand.
/// - fails: not applicable to the data item.
/// - panics: not applicable to the data item.
/// - executable: none — the enabled specification facade does not expose
///   type-invariant expansion; executable predicates cover the producing and
///   consuming operations.
///
/// # Adequacy
/// - hypothesis: L3 — nested record matching retains the named field and
///   applies its type.
/// - witness: `tests::modules::nested_member_signature_constrains_the_parent_binding`
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Field<'source>
{
    /// The field's name.
    name: SurfaceName<'source>,
    /// The name's tile.
    named: Placed,
    /// The field's type.
    stated: Placed,
}

/// Whether a module form's operands carry the repair its own pieces hold.
///
/// # Specification
/// - requires: nothing to construct this data; its producers and consumers
///   state coordinate preconditions separately.
/// - ensures: The flag reports whether an operand directly carries a grout or
///   minted-close repair, separating a repaired member from an unread
///   container.
/// - fails: not applicable to the data item.
/// - panics: not applicable to the data item.
/// - executable: none — the enabled specification facade does not expose
///   type-invariant expansion; executable predicates cover the producing and
///   consuming operations.
///
/// # Adequacy
/// - hypothesis: L3 — a repaired container retains its readable member rather
///   than refusing the whole body.
/// - witness: `tests::modules::a_repaired_container_keeps_its_member`
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct Carried(bool);

/// Whether a `theory` block or a top-level `oper` holds a member refusal.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct SignatureRefused(bool);

/// Whether a container's body declares a name in a form the parser repaired.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct MemberRepaired(bool);

quenchant_shape::reason_enum! {
    /// Why a signature type sees no manifest type component.
    pub mod component_scope {
        /// The type is written where no signature binds one.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The type is a member signature in a module's body.
            Body,
        }
    }
}

quenchant_shape::reason_enum! {
    /// Why a module has no member of a name.
    pub mod declared_member {
        /// Nothing in the module's body declares the name.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// No definition member and no nested module carries it.
            Undeclared,
        }
    }
}

impl<'source> Collector<'_, 'source>
{
    /// Collect one top-level module and every module nested in it.
    ///
    /// # Specification
    /// - requires: `module` is a module form standing at the root.
    /// - ensures: the modules are walked in pre-order by an explicit stack:
    ///   each module is recorded before the modules nested in it, its
    ///   definition members are admitted in source order under it, and once its
    ///   body is read it is matched against its signatures. A module refused as
    ///   a whole — unread, sealed, misnamed or declared twice — files a held
    ///   slot carrying the refusal under its name, and its body is not read; a
    ///   malformed member files one under its module's name and the module's
    ///   other members are kept.
    /// - provides: the module half of [`collect_source`].
    /// - fails: when the module has no name to refuse it under, as a
    ///   declaration with no name does; [`LoweringRefusal::UnknownMold`] and
    ///   [`LoweringRefusal::BudgetExceeded`].
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoweringRefusal::MalformedForm`] for a module with no name,
    /// [`LoweringRefusal::UnknownMold`] and
    /// [`LoweringRefusal::BudgetExceeded`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — nesting separated by depth one and depth eight, a
    ///   sealed module whose abstract type its clients read, and the refusals
    ///   of the module as a whole by an unread body, an empty body, a lowercase
    ///   name and a malformed member, each asserted as the exact declaration
    ///   list. The predicate reads only the structures this call appended.
    /// - witness: `tests::modules::modules_lower_to_named_member_declarations`
    /// - witness: `tests::modules::deeply_nested_modules_lower_and_resolve_at_every_depth`
    /// - witness: `tests::modules::an_unread_module_body_is_refused_not_emptied`
    /// - witness: `tests::modules::an_empty_module_is_not_an_unread_one`
    /// - witness: `tests::modules::opaque_ascription_seals`
    /// - witness: `tests::modules::module_name_case_boundary_covers_single_and_multi_names`
    /// - witness: `tests::modules::an_unread_member_keeps_its_own_report`
    /// - witness: `tests::modules::a_readable_module_keeps_its_members_and_its_successor`
    /// - witness: `tests::modules::a_nested_module_declares_under_either_case_spelling`
    /// - witness: `tests::modules::a_repaired_container_keeps_its_member`
    /// - witness: `tests::modules::a_malformed_member_is_repaired_and_its_siblings_kept`
    /// - witness: `tests::modules::duplicate_module_member_definition_is_rejected`
    /// - witness: `tests::modules::module_members_admit_in_source_order`
    /// - witness: `tests::modules::computation_signed_module_member_origin_mirrors_ascription_encoding`
    #[spec(
        captures: before = (
            self.collected.slots.len(),
            self.collected.structures.len(),
            self.collected.owner.len(),
        ),
        ensures: |_| {
            self.collected.slots.len() >= before.0
                && self.collected.structures.len() >= before.1
                && self.collected.owner.len() == before.2
                && self.collected.structures.get(before.1 ..).is_some_and(|appended| {
                    appended.iter().zip(before.1 ..).all(|(module, index)| match module.container {
                        | Container::TopLevel(_) => true,
                        | Container::Module(parent) => parent.0 < index,
                    })
                })
        },
    )]
    fn module(
        &mut self,
        module: Placed,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let mut pieces = Pieces::new();
        read_pieces(self.pbg, self.tree, module.node, &mut pieces)?;
        let mut stack = Vec::new();
        let opened_at = StructureIndex(self.collected.structures.len());
        let top = self.collected.top(module.span.start());
        match self.header(module, &pieces, top)? {
            Header::Opened(opened) => self.open(top, module, opened, &mut stack),
            Header::Applied(applied) => {
                self.apply(module, &applied);
                return Ok(());
            },
            Header::Refused {
                name,
                named,
                refusal,
            } => {
                let _held = self.refuse_held(top, name, module, named, refusal);
            },
            Header::Unnamed(refusal) => return Err(refusal),
        }
        while let Some(top) = stack.last_mut() {
            let structure = top.structure;
            let Some(&member) = top.members.get(top.next)
            else {
                let _closed = stack.pop();
                self.close(structure)?;
                continue;
            };
            top.next = top.next.saturating_add(1_usize);
            self.fuel.spend()?;
            let mut read = core::mem::take(&mut self.pieces);
            let outcome = read_pieces(self.pbg, self.tree, member.node, &mut read)
                .and_then(|()| self.member(structure, member, &read, &mut stack));
            self.pieces = read;
            outcome?;
        }
        self.close_functor(opened_at);

        Ok(())
    }

    /// Read a module form's header: its name, its signature and its body's
    /// member forms, or the functor application it binds.
    ///
    /// # Specification
    /// - requires: `pieces` is the reading of the module form `form`, declared
    ///   in `container`.
    /// - ensures: the opened module when its tiles read `module Name ((X : #{ …
    ///   }))? ((: | :>) (#{ … } | Model(S)))? { members }`, a top-level name
    ///   taking the uppercase spelling and a nested one either, sealed exactly
    ///   when the ascription is `:>`, carrying the model signature `Model(S)`
    ///   derives and the functor parameter when one is written; the application
    ///   when they read `module Name = F(P(.p)*) ;`; a top-level module named
    ///   in lowercase, a repair no operand carries, or a parameter, signature,
    ///   application or body out of shape refuses the module under its name; a
    ///   form with no name is unnamed.
    /// - provides: the per-module reading of [`Self::module`] and
    ///   [`Self::member`].
    /// - fails: [`LoweringRefusal::UnknownMold`] for a foreign mold; every
    ///   fault of the form itself is yielded rather than raised.
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoweringRefusal::UnknownMold`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — readable, empty, sealed, lowercase and repaired
    ///   modules separate a readable header from a named refusal or an unnamed
    ///   form, and a sealed header from a transparent one. The predicate asks
    ///   for the name tile's own bytes, by address and length.
    /// - witness: `tests::modules::modules_lower_to_named_member_declarations`
    /// - witness: `tests::modules::an_empty_module_is_not_an_unread_one`
    /// - witness: `tests::modules::opaque_ascription_seals`
    /// - witness: `tests::modules::module_name_case_boundary_covers_single_and_multi_names`
    /// - witness: `tests::modules::a_repaired_container_keeps_its_member`
    #[spec(
        ensures: |ret| {
            ret.as_ref().map_or_else(
                |refusal| matches!(*refusal, LoweringRefusal::UnknownMold { .. }),
                |header| match *header {
                    | Header::Applied(ref applied) => core::ptr::eq(
                        core::ptr::from_ref::<str>(applied.name.as_ref()),
                        core::ptr::from_ref::<str>(self.name_of(applied.named).as_ref()),
                    ) && !applied.argument.is_empty(),
                    | Header::Opened(ref opened) => {
                        core::ptr::eq(
                            core::ptr::from_ref::<str>(opened.name.as_ref()),
                            core::ptr::from_ref::<str>(self.name_of(opened.named).as_ref()),
                        )
                            && opened
                                .members
                                .iter()
                                .all(|&member| pieces.pieces.contains(&Piece::Operand(member)))
                    },
                    | Header::Refused { name, named, .. } => core::ptr::eq(
                        core::ptr::from_ref::<str>(name.as_ref()),
                        core::ptr::from_ref::<str>(self.name_of(named).as_ref()),
                    ),
                    | Header::Unnamed(_) => true,
                },
            )
        },
    )]
    fn header(
        &mut self,
        form: Placed,
        pieces: &Pieces,
        container: Container,
    ) -> Result<Header<'source>, LoweringRefusal<'source>>
    {
        let mut cursor = Cursor::new(&pieces.pieces, form.span);
        let unnamed = |cursor: &Cursor<'_>| match pieces.repair {
            Maybe::Present(repaired) => Header::Unnamed(repaired.refusal(FormName::MODULE)),
            Maybe::Absent(_) => Header::Unnamed(misplaced_in(FormName::MODULE, cursor.here())),
        };
        if let Maybe::Absent(_) = cursor.tile(TileName::MODULE) {
            return Ok(unnamed(&cursor));
        }
        let named = match cursor.peek() {
            Maybe::Present(Piece::Tile { label, at })
                if label == TileName::TYPE_IDENTIFIER || label == TileName::IDENTIFIER =>
            {
                let _name = cursor.read();
                if label == TileName::IDENTIFIER && matches!(container, Container::TopLevel(_)) {
                    let name = self.name_of(at);
                    return Ok(Header::Refused {
                        name,
                        named: at,
                        refusal: LoweringRefusal::LowercaseModuleName {
                            span: form.span,
                            name,
                        },
                    });
                }
                at
            },
            Maybe::Present(_) | Maybe::Absent(_) => return Ok(unnamed(&cursor)),
        };
        let name = self.name_of(named);
        let refused = |refusal| {
            Ok(Header::Refused {
                name,
                named,
                refusal,
            })
        };
        if let Maybe::Present(repaired) = pieces.repair
            && !self.carried(pieces).0
        {
            return refused(repaired.refusal(FormName::MODULE));
        }
        if let Maybe::Present(_) = cursor.tile(TileName::EQUALS) {
            return match Self::application(&mut cursor) {
                Maybe::Present((functor, argument)) => Ok(Header::Applied(Applied {
                    name,
                    named,
                    functor,
                    argument,
                })),
                Maybe::Absent(_) => refused(misplaced_in(FormName::MODULE, cursor.here())),
            };
        }
        let parameter = if let Maybe::Present(_) = cursor.tile(TileName::PAREN_OPEN) {
            let Maybe::Present(parameter_named) = cursor.tile(TileName::TYPE_IDENTIFIER)
            else {
                return refused(misplaced_in(FormName::MODULE, cursor.here()));
            };
            if let Maybe::Absent(_) = cursor.tile(TileName::COLON) {
                return refused(misplaced_in(FormName::MODULE, cursor.here()));
            }
            let (components, model) =
                if let Maybe::Present(_) = cursor.at(TileName::TYPE_IDENTIFIER) {
                    match self.model_signature(&mut cursor, form) {
                        Ok((components, derived, used)) => {
                            self.collected.declared_uses.push(used);
                            (components, Maybe::Present(derived))
                        },
                        Err(refusal) => return refused(refusal),
                    }
                }
                else {
                    match self.signature(&mut cursor) {
                        Ok(components) => (components, Maybe::Absent(derived::Absent::Written)),
                        Err(refusal) => return refused(refusal),
                    }
                };
            if let Maybe::Absent(_) = cursor.tile(TileName::PAREN_CLOSE) {
                return refused(misplaced_in(FormName::MODULE, cursor.here()));
            }
            Maybe::Present(WrittenParameter {
                name: self.name_of(parameter_named),
                named: parameter_named,
                components,
                model,
            })
        }
        else {
            Maybe::Absent(parameter::Absent::Unparameterized)
        };
        let sealed = Sealed(matches!(cursor.tile(TileName::SEAL), Maybe::Present(_)));
        let mut model = Maybe::Absent(derived::Absent::Written);
        let ascription = if sealed.0 || matches!(cursor.tile(TileName::COLON), Maybe::Present(_)) {
            let read = if let Maybe::Present(_) = cursor.at(TileName::TYPE_IDENTIFIER) {
                self.model_signature(&mut cursor, form)
                    .map(|(components, derived, named)| {
                        model = Maybe::Present(derived);
                        self.collected.declared_uses.push(named);
                        components
                    })
            }
            else {
                self.signature(&mut cursor)
            };
            match read {
                Ok(components) => Maybe::Present(components),
                Err(refusal) => return refused(refusal),
            }
        }
        else {
            Maybe::Absent(ascription::Absent::Unascribed)
        };
        if let Maybe::Absent(_) = cursor.tile(TileName::BRACE_OPEN) {
            return refused(misplaced_in(FormName::MODULE, cursor.here()));
        }
        let mut members = Vec::new();
        while let Maybe::Present(Piece::Operand(member)) = cursor.peek() {
            let _member = cursor.read();
            members.push(member);
        }
        let _close = cursor.tile(TileName::BRACE_CLOSE);
        if let Maybe::Present(_) = cursor.peek() {
            return refused(misplaced_in(FormName::MODULE, cursor.here()));
        }

        Ok(Header::Opened(Opened {
            name,
            named,
            ascription,
            model,
            sealed,
            members,
            parameter,
        }))
    }

    /// Read a functor application's tail past its `=`: `F(P(.p)*) ;`.
    ///
    /// # Specification
    /// - requires: `cursor` stands just past the binding's `=`.
    /// - ensures: the functor's name tile and the argument path's segment
    ///   tiles, at least one, when the tail reads `F(P(.p)*) ;` and nothing
    ///   follows it; absent, the cursor at the first tile out of place,
    ///   otherwise.
    /// - provides: the application half of [`Self::header`].
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a one-segment and a dotted argument are read, and a
    ///   tail out of shape is refused under the binding's name.
    /// - witness: `tests::modules::functors::two_applications_mint_distinct_atoms`
    /// - witness: `tests::modules::functors::an_application_is_bound_before_anything_projects_from_it`
    #[spec(ensures: |ret| match ret {
        | Maybe::Present((_, ref argument)) => !argument.is_empty(),
        | Maybe::Absent(_) => true,
    })]
    fn application(cursor: &mut Cursor<'_>) -> Maybe<(Placed, Vec<Placed>), application::Absent>
    {
        let misplaced = Maybe::Absent(application::Absent::Misplaced);
        let Maybe::Present(functor) = cursor.tile(TileName::TYPE_IDENTIFIER)
        else {
            return misplaced;
        };
        if let Maybe::Absent(_) = cursor.tile(TileName::PAREN_OPEN) {
            return misplaced;
        }
        let Maybe::Present(head) = cursor.tile(TileName::TYPE_IDENTIFIER)
        else {
            return misplaced;
        };
        let mut argument = Vec::from([head]);
        while let Maybe::Present(_) = cursor.tile(TileName::DOT) {
            let segment = match cursor.tile(TileName::TYPE_IDENTIFIER) {
                Maybe::Present(segment) => segment,
                Maybe::Absent(_) => match cursor.tile(TileName::IDENTIFIER) {
                    Maybe::Present(segment) => segment,
                    Maybe::Absent(_) => return misplaced,
                },
            };
            argument.push(segment);
        }
        if let (Maybe::Present(_), Maybe::Present(_), Maybe::Absent(_)) = (
            cursor.tile(TileName::PAREN_CLOSE),
            cursor.tile(TileName::SEMICOLON),
            cursor.peek(),
        ) {
            return Maybe::Present((functor, argument));
        }

        misplaced
    }

    /// Whether an operand of a module form carries a repair of its own: the
    /// repair the module's pieces hold then belongs to a member, which reports
    /// it more precisely.
    ///
    /// # Specification
    /// - requires: `pieces` is the reading of a module form.
    /// - ensures: affirmative exactly when some operand's own children include
    ///   grout or a minted close.
    /// - provides: the separating test between an unread module and a module
    ///   with an unread member.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an unread module and a repaired member separate
    ///   container refusal from retaining readable siblings.
    /// - witness: `tests::modules::an_unread_module_body_is_refused_not_emptied`
    /// - witness: `tests::modules::a_repaired_container_keeps_its_member`
    /// - witness: `tests::modules::a_malformed_member_is_repaired_and_its_siblings_kept`
    #[spec(
        ensures: |ret| {
            ret.0
                == pieces.pieces.iter().any(|piece| match *piece {
                    | Piece::Operand(operand) => self.tree.children(operand.node).any(|child| {
                        self.tree.node(child).is_some_and(|node| {
                            matches!(
                                node.label(),
                                NodeLabel::Grout { .. } | NodeLabel::GhostClose { .. }
                            )
                        })
                    }),
                    | Piece::Tile { .. } => false,
                })
        },
    )]
    fn carried(
        &self,
        pieces: &Pieces,
    ) -> Carried
    {
        let repaired = |operand: Placed| {
            self.tree.children(operand.node).any(|child| {
                self.tree.node(child).is_some_and(|node| {
                    matches!(
                        node.label(),
                        NodeLabel::Grout { .. } | NodeLabel::GhostClose { .. }
                    )
                })
            })
        };

        Carried(pieces.pieces.iter().any(|piece| match *piece {
            Piece::Operand(operand) => repaired(operand),
            Piece::Tile { .. } => false,
        }))
    }

    /// Read a module signature, `#{ components }`, after its `:` or `:>`.
    ///
    /// # Specification
    /// - requires: `cursor` stands just past the ascription's `:` or `:>`.
    /// - ensures: every component in signature order, the cursor past the
    ///   closing `}`: `x : T` a value component; `type T = τ` a manifest one;
    ///   `type F(a : A, …) = τ` a manifest family, its parameters filed among
    ///   the collection's parameter lists; `type T` and `type T : κ` an
    ///   abstract one, but for a kind written as a telescope, which declares a
    ///   family; a parameter list before anything but `= τ` kept as a form the
    ///   fragment does not read.
    /// - provides: the signature half of [`Self::header`].
    /// - fails: yields a misplaced-tile refusal for a signature out of shape
    ///   and the hole's refusal for a type not written as one form.
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoweringRefusal::MalformedForm`] naming the module form.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — reordered value components and manifest, kinded and
    ///   abstract type components retain their names and select distinct forms.
    ///   The predicate asks for each name tile's own bytes, by address and
    ///   length.
    /// - witness: `tests::modules::a_reordered_signature_matches_and_canonicalizes`
    /// - witness: `tests::modules::a_manifest_type_component_expands_in_later_components`
    /// - witness: `tests::modules::a_kinded_type_component_forms_at_its_classifier`
    /// - witness: `tests::modules::a_manifest_family_component_binds_two_parameters`
    /// - witness: `tests::modules::a_transparent_abstract_component_reads_its_type_member`
    /// - witness: `tests::modules::an_abstract_component_kinds_at_a_universe`
    #[spec(
        captures: starts_record = matches!(cursor.at(TileName::RECORD), Maybe::Present(_)),
        ensures: |ret| {
            ret.as_ref().map_or(true, |components| {
                starts_record
                    && components
                        .iter()
                        .all(|component| core::ptr::eq(
                            core::ptr::from_ref::<str>(component.name.as_ref()),
                            core::ptr::from_ref::<str>(self.name_of(component.named).as_ref()),
                        ))
            })
        },
    )]
    fn signature(
        &mut self,
        cursor: &mut Cursor<'_>,
    ) -> Result<Vec<Component<'source>>, LoweringRefusal<'source>>
    {
        if let Maybe::Absent(_) = cursor.tile(TileName::RECORD) {
            return Err(misplaced_in(FormName::MODULE, cursor.here()));
        }
        let mut components = Vec::new();
        loop {
            if let Maybe::Present(_) = cursor.tile(TileName::BRACE_CLOSE) {
                return Ok(components);
            }
            let component = if let Maybe::Present(named) = cursor.tile(TileName::IDENTIFIER) {
                if let Maybe::Absent(_) = cursor.tile(TileName::COLON) {
                    return Err(misplaced_in(FormName::MODULE, cursor.here()));
                }
                Component {
                    name: self.name_of(named),
                    named,
                    form: ComponentForm::Value(one_in(FormName::MODULE, cursor.operands())?),
                    mark: Mark::Unmarked,
                }
            }
            else if let Maybe::Present(_) = cursor.tile(TileName::MOBILE) {
                if let Maybe::Absent(_) = cursor.tile(TileName::TYPE) {
                    return Err(misplaced_in(FormName::MODULE, cursor.here()));
                }
                let Maybe::Present(named) = cursor.tile(TileName::TYPE_IDENTIFIER)
                else {
                    return Err(misplaced_in(FormName::MODULE, cursor.here()));
                };
                Component {
                    name: self.name_of(named),
                    named,
                    form: ComponentForm::Abstract(Maybe::Absent(component_kind::Absent::Unkinded)),
                    mark: Mark::Mobile,
                }
            }
            else if let Maybe::Present(_) = cursor.tile(TileName::TYPE) {
                let Maybe::Present(named) = cursor.tile(TileName::TYPE_IDENTIFIER)
                else {
                    return Err(misplaced_in(FormName::MODULE, cursor.here()));
                };
                let form = match type_component(cursor)? {
                    WrittenType::Formed(ComponentForm::Abstract(Maybe::Present(kind))) => {
                        match self.kind_form(kind)? {
                            KindForm::Universe | KindForm::Arrow => {
                                ComponentForm::Abstract(Maybe::Present(kind))
                            },
                            KindForm::Family => ComponentForm::Family(FamilyForm::Written(kind)),
                        }
                    },
                    WrittenType::Formed(form) => form,
                    WrittenType::Family {
                        parameters,
                        defined,
                    } => {
                        let list = ParameterList(self.collected.parameter_lists.len());
                        self.collected.parameter_lists.push(parameters);
                        ComponentForm::Parameterized {
                            parameters: list,
                            defined,
                        }
                    },
                };
                Component {
                    name: self.name_of(named),
                    named,
                    form,
                    mark: Mark::Unmarked,
                }
            }
            else {
                return Err(misplaced_in(FormName::MODULE, cursor.here()));
            };
            components.push(component);
            if let Maybe::Absent(_) = cursor.tile(TileName::COMMA)
                && let Maybe::Absent(_) = cursor.at(TileName::BRACE_CLOSE)
            {
                return Err(misplaced_in(FormName::MODULE, cursor.here()));
            }
        }
    }

    /// Record the opened module `opened`, declared in `container` by `form`,
    /// and push its body onto `stack`.
    ///
    /// # Specification
    /// - requires: `opened` is the header of `form`.
    /// - ensures: a module name already declared in `container` files a held
    ///   slot carrying the duplicate refusal and leaves the body unread;
    ///   otherwise the module takes the next pre-order position, joins its
    ///   enclosing module's members, a functor's parameter takes the position
    ///   after it, the module declares one abstract type per abstract component
    ///   when it is sealed — by its own `:>`, or as the nested model a sealed
    ///   enclosing module's model signature states under its name — and its
    ///   body is pushed.
    /// - provides: the recording half of [`Self::module`].
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — nested module headers are admitted before their
    ///   bodies, duplicate names refuse without replacing the first module, and
    ///   a functor's body is admitted before its parameter.
    /// - witness: `tests::modules::modules_lower_to_named_member_declarations`
    /// - witness: `tests::modules::module_members_admit_in_source_order`
    /// - witness: `tests::modules::a_readable_module_keeps_its_members_and_its_successor`
    /// - witness: `tests::modules::duplicate_module_member_definition_is_rejected`
    /// - witness: `tests::modules::opaque_ascription_seals`
    /// - witness: `tests::modules::models::a_nested_model_is_a_module_ascribed_its_theory_1226`
    /// - witness: `tests::modules::functors::the_classic_functor_pair_checks`
    #[spec(
        captures: before = (
            self.collected.structures.len(),
            self.collected.slots.len(),
            stack.len(),
            opened.name,
            opened.named,
            opened.members.len(),
            self.collected
                .modules
                .get(&(container, opened.name))
                .copied(),
            Sealed(opened.sealed.0 || self.seals_nested(container, opened.name).0),
            usize::from(matches!(opened.parameter, Maybe::Present(_))),
        ),
        ensures: |_| match before.6 {
            | Some(first) => {
                self.collected.modules.get(&(container, before.3)) == Some(&first)
                    && self.collected.structures.len() == before.0
                    && self.collected.slots.len() == before.1.saturating_add(1)
                    && stack.len() == before.2
            },
            | None => {
                self.collected.modules.get(&(container, before.3))
                    == Some(&StructureIndex(before.0))
                    && self.collected.structures.len()
                        == before.0.saturating_add(1).saturating_add(before.8)
                    && self.collected.structures.get(before.0).is_some_and(|entry| {
                        entry.name == before.3
                            && entry.container == container
                            && entry.named == before.4
                            && entry.members.is_empty()
                            && entry.exports.is_empty()
                            && entry.types.is_empty()
                            && entry.type_members.is_empty()
                            && entry.exported_as.is_empty()
                            && entry.sealed == before.7
                            && !entry.coerced.0
                    })
                    && stack.len() == before.2.saturating_add(1)
                    && stack.last().is_some_and(|entry| {
                        entry.structure.0 == before.0
                            && entry.next == 0
                            && entry.members.len() == before.5
                    })
            },
        },
    )]
    fn open(
        &mut self,
        container: Container,
        form: Placed,
        opened: Opened<'source>,
        stack: &mut Vec<Open>,
    )
    {
        let key = (container, opened.name);
        if let Some(&first) = self.collected.modules.get(&key) {
            let first = self
                .collected
                .structures
                .get(first.0)
                .map_or(form.span, |earlier| earlier.named.span);
            let refusal = LoweringRefusal::DuplicateDefinition {
                span: opened.named.span,
                name: opened.name,
                first,
            };
            let _held = self.refuse_held(container, opened.name, form, opened.named, refusal);
            return;
        }
        let structure = StructureIndex(self.collected.structures.len());
        let sealed = Sealed(opened.sealed.0 || self.seals_nested(container, opened.name).0);
        let model = opened.model.map(|derived| {
            let index = ModelIndex(self.collected.models.len());
            self.collected.models.push(derived);
            index
        });
        self.collected.structures.push(Structure {
            name: opened.name,
            container,
            declared_by: form,
            named: opened.named,
            ascription: opened.ascription,
            model,
            sealed,
            members: Vec::new(),
            exports: Vec::new(),
            types: Vec::new(),
            type_members: Vec::new(),
            exported_as: BTreeMap::new(),
            stated_at: Vec::new(),
            coerced: Coerced(false),
            stratum: Stratum::Module,
        });
        self.collected.modules.insert(key, structure);
        self.document_module(form.node, opened.named.span.start(), form.node);
        if let Container::Module(parent) = container
            && let Some(entry) = self.collected.structures.get_mut(parent.0)
        {
            entry.members.push(Member::Module(structure));
        }
        if let Maybe::Present(parameter) = opened.parameter {
            self.declare_parameter(structure, parameter);
        }
        self.declare_abstracts(structure);
        stack.push(Open {
            structure,
            members: opened.members,
            next: 0_usize,
        });
    }

    /// Whether the module `container` names seals the nested module `name` it
    /// declares: the container is sealed, and its model signature states a
    /// nested model under that name.
    ///
    /// # Specification
    /// - ensures: affirmative exactly when `container` is a sealed module whose
    ///   derived model signature has a nested-model component named `name`.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the predicate is the body's one lookup.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a nested model under a sealed module reads its sorts
    ///   as atoms, and under a transparent one as the nested module states.
    /// - witness: `tests::modules::models::a_nested_model_is_a_module_ascribed_its_theory_1226`
    fn seals_nested(
        &self,
        container: Container,
        name: SurfaceName<'source>,
    ) -> Sealed
    {
        let Container::Module(parent) = container
        else {
            return Sealed(false);
        };
        let Some(entry) = self.collected.structures.get(parent.0)
        else {
            return Sealed(false);
        };
        let Maybe::Present(model) = entry.model
        else {
            return Sealed(false);
        };
        Sealed(
            entry.sealed.0
                && self.collected.models.get(model.0).is_some_and(|signature| {
                    signature.components.iter().any(|component| {
                        component.name.as_ref() == name.as_ref()
                            && matches!(component.form, Ok(crate::model::ModelForm::Nested(_)))
                    })
                }),
        )
    }

    /// Read one member form of `structure`'s body.
    ///
    /// # Specification
    /// - requires: `pieces` is the reading of `member`, a member form of the
    ///   module at `structure`.
    /// - ensures: a form holding a `def` tile is a definition member, read as a
    ///   declaration in the module; a form opening on `type` is a type member,
    ///   filed among the module's type members; a form opening on `module` is a
    ///   nested module, opened onto `stack` or refused as a whole under its
    ///   name; every other form is a malformed member, refused under the
    ///   module's name at the member, and the module's other members are kept.
    /// - provides: the per-member half of [`Self::module`].
    /// - fails: [`LoweringRefusal::UnknownMold`] for a foreign mold.
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoweringRefusal::UnknownMold`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — valid members and nested modules stay under their
    ///   container; malformed members leave siblings readable and report at the
    ///   module. The predicate reads only the slots and structures this call
    ///   appended.
    /// - witness: `tests::modules::a_malformed_member_is_repaired_and_its_siblings_kept`
    /// - witness: `tests::modules::modules_lower_to_named_member_declarations`
    /// - witness: `tests::modules::module_members_admit_in_source_order`
    /// - witness: `tests::modules::a_readable_module_keeps_its_members_and_its_successor`
    /// - witness: `tests::modules::opaque_ascription_seals`
    #[spec(
        captures: before = (
            self.collected.slots.len(),
            self.collected.structures.len(),
            self.collected
                .structures
                .get(structure.0)
                .map(|entry| entry.container),
        ),
        ensures: |_| {
            self.collected.slots.len() >= before.0
                && self.collected.structures.len() >= before.1
                && self.collected.slots.get(before.0 ..).is_some_and(|appended| {
                    appended.iter().all(|slot| {
                        slot.container == Container::Module(structure)
                            || slot.role == Role::Abstract
                            || (slot.role == Role::Held && Some(slot.container) == before.2)
                    })
                })
                && self.collected.structures.get(before.1 ..).is_some_and(|appended| {
                    appended.iter().all(|entry| entry.container == Container::Module(structure))
                })
        },
    )]
    fn member(
        &mut self,
        structure: StructureIndex,
        member: Placed,
        pieces: &Pieces,
        stack: &mut Vec<Open>,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let container = Container::Module(structure);
        let Some(node) = self.tree.node(member.node)
        else {
            return Ok(());
        };
        let form = match shape_of(self.pbg, node)? {
            Shape::Form {
                former: Former::Module | Former::Declaration,
                name,
            } => name,
            Shape::Form { name, .. } => {
                self.fault_at(structure, member, LoweringRefusal::OutOfFragment {
                    span: member.span,
                    form: name,
                    sort: FragmentSort::Declaration,
                    boundary: FragmentBoundary::WrongSort,
                });
                return Ok(());
            },
            Shape::Root | Shape::Repair(_) | Shape::Layout => return Ok(()),
        };
        let defines = pieces
            .pieces
            .iter()
            .any(|piece| matches!(*piece, Piece::Tile { label, .. } if label == TileName::DEF));
        if defines {
            if let Err(refusal) = self.read_declaration(container, member, pieces, &[]) {
                self.fault_at(structure, member, refusal);
            }
            return Ok(());
        }
        if Self::opens_type_member(pieces).0 {
            self.type_member(structure, member, pieces);
            return Ok(());
        }
        let cursor = Cursor::new(&pieces.pieces, member.span);
        if let Maybe::Absent(_) = cursor.at(TileName::MODULE) {
            self.fault_at(structure, member, misplaced_in(form, cursor.here()));
            return Ok(());
        }
        match self.header(member, pieces, container)? {
            Header::Opened(opened) => self.open(container, member, opened, stack),
            Header::Applied(applied) => {
                self.fault_at(structure, member, misplaced_in(form, applied.named.span));
            },
            Header::Refused {
                name,
                named,
                refusal,
            } => {
                let _held = self.refuse_held(container, name, member, named, refusal);
            },
            Header::Unnamed(refusal) => self.fault_at(structure, member, refusal),
        }

        Ok(())
    }

    /// A slot named `name` in `container` that declares nothing, introduced
    /// by `introduced_by` with its name at `named`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the slot takes the next admission position, holds no half and
    ///   no refusal, and is entered in no name table.
    /// - provides: the owner of a manifest type component's type, and the
    ///   carrier of a refusal no declaration owns.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — unread modules, type members, missing components and
    ///   manifest types use held slots without introducing referenceable names.
    /// - witness: `tests::modules::an_unread_module_body_is_refused_not_emptied`
    /// - witness: `tests::modules::opaque_ascription_seals`
    /// - witness: `tests::modules::a_missing_signature_component_is_rejected_at_the_signature`
    /// - witness: `tests::modules::a_manifest_type_component_expands_in_later_components`
    #[spec(
        captures: before = (self.collected.slots.len(), self.collected.by_name.len()),
        ensures: |ret| {
            ret.0 == before.0
                && self.collected.slots.len() == before.0.saturating_add(1)
                && self.collected.by_name.len() == before.1
                && self.collected.slots.get(ret.0).is_some_and(|slot| {
                    slot.role == Role::Held
                        && slot.name == name
                        && slot.container == container
                        && slot.introduced_by == introduced_by
                        && slot.named == named
                        && matches!(slot.signature, Maybe::Absent(_))
                        && matches!(slot.definition, Maybe::Absent(_))
                        && matches!(slot.refusal, Maybe::Absent(_))
                        && slot.attributes.is_empty()
                })
        },
    )]
    fn held(
        &mut self,
        container: Container,
        name: SurfaceName<'source>,
        introduced_by: Placed,
        named: Placed,
    ) -> SlotIndex
    {
        let minted = SlotIndex(self.collected.slots.len());
        self.collected.slots.push(DeclarationSlot {
            name,
            container,
            role: Role::Held,
            constant: ConstantIndex::from(minted.0),
            introduced_by,
            named,
            signature: Maybe::Absent(declaration_half::Absent::Unwritten),
            definition: Maybe::Absent(declaration_half::Absent::Unwritten),
            attributes: Vec::new(),
            docs: Vec::new(),
            refusal: Maybe::Absent(slot_refusal::Absent::Unrefused),
        });

        minted
    }

    /// A held slot carrying `refusal`, at the form `introduced_by`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: one fresh held slot carries the supplied refusal and is not
    ///   entered in the name table.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — unread and lowercase-named modules, missing
    ///   components and manifest types use held slots without introducing
    ///   referenceable names.
    /// - witness: `tests::modules::an_unread_module_body_is_refused_not_emptied`
    /// - witness: `tests::modules::module_name_case_boundary_covers_single_and_multi_names`
    /// - witness: `tests::modules::a_missing_signature_component_is_rejected_at_the_signature`
    /// - witness: `tests::modules::a_manifest_type_component_expands_in_later_components`
    #[spec(
        captures: before = (self.collected.slots.len(), self.collected.by_name.len()),
        ensures: |ret| {
            ret.0 == before.0
                && self.collected.slots.len() == before.0.saturating_add(1)
                && self.collected.by_name.len() == before.1
                && self.collected.slots.get(ret.0).is_some_and(|slot| {
                    slot.role == Role::Held
                        && slot.name == name
                        && slot.container == container
                        && slot.refusal == Maybe::Present((introduced_by.node, refusal))
                })
        },
    )]
    fn refuse_held(
        &mut self,
        container: Container,
        name: SurfaceName<'source>,
        introduced_by: Placed,
        named: Placed,
        refusal: LoweringRefusal<'source>,
    ) -> SlotIndex
    {
        let held = self.held(container, name, introduced_by, named);
        if let Some(entry) = self.collected.slots.get_mut(held.0) {
            entry.refuse(introduced_by.node, refusal);
        }

        held
    }

    /// A held slot carrying `refusal`, raised at `at` inside the module at
    /// `structure`, under that module's own name.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a live module receives one held refusal under its own name
    ///   and parent container; an absent module changes nothing.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a malformed member is refused under its module while
    ///   its well-formed sibling remains admitted.
    /// - witness: `tests::modules::a_malformed_member_is_repaired_and_its_siblings_kept`
    #[spec(
        captures: before = (
            self.collected.slots.len(),
            self.collected
                .structures
                .get(structure.0)
                .map(|entry| (entry.container, entry.name)),
        ),
        ensures: |_| match before.1 {
            | Some((container, name)) => {
                self.collected.slots.len() == before.0.saturating_add(1)
                    && self.collected.slots.last().is_some_and(|slot| {
                        slot.role == Role::Held
                            && slot.container == container
                            && slot.name == name
                            && slot.refusal == Maybe::Present((at.node, refusal))
                    })
            },
            | None => self.collected.slots.len() == before.0,
        },
    )]
    fn fault_at(
        &mut self,
        structure: StructureIndex,
        at: Placed,
        refusal: LoweringRefusal<'source>,
    )
    {
        let Some(entry) = self.collected.structures.get(structure.0)
        else {
            return;
        };
        let (container, name, named) = (entry.container, entry.name, entry.named);
        let _held = self.refuse_held(container, name, at, named, refusal);
    }

    /// Match the module at `structure` against its signatures, once its body
    /// is read.
    ///
    /// # Specification
    /// - requires: every module nested in `structure` is already closed.
    /// - ensures: a member signature naming a nested module states that
    ///   module's signature; the module's own signature is matched; then every
    ///   signature the module states for a nested module is applied after that
    ///   module's own, deepest last, by an explicit queue; last, each seal the
    ///   module declared reaches every slot taken so far.
    /// - provides: coercive matching.
    /// - fails: [`LoweringRefusal::UnknownMold`] and
    ///   [`LoweringRefusal::BudgetExceeded`].
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoweringRefusal::UnknownMold`] and
    /// [`LoweringRefusal::BudgetExceeded`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — closing a module retains declared members without an
    ///   ascription, and applies explicit and enclosing signatures to its
    ///   exports.
    /// - witness: `tests::modules::modules_lower_to_named_member_declarations`
    /// - witness: `tests::modules::module_members_admit_in_source_order`
    /// - witness: `tests::modules::a_readable_module_keeps_its_members_and_its_successor`
    /// - witness: `tests::modules::a_reordered_signature_matches_and_canonicalizes`
    /// - witness: `tests::modules::module_signature_matching_hides_extra_members`
    /// - witness: `tests::modules::a_missing_signature_component_is_rejected_at_the_signature`
    /// - witness: `tests::modules::nested_member_signature_constrains_the_parent_binding`
    /// - witness: `tests::modules::opaque_ascription_seals`
    #[spec(
        captures: structures = self.collected.structures.len(),
        ensures: |ret| {
            self.collected.structures.len() == structures
                && (ret.is_err()
                    || self
                        .collected
                        .structures
                        .get(structure.0)
                        .is_none_or(|entry| {
                            entry.exports.iter().enumerate().all(|(index, member)| {
                                entry.members.contains(member)
                                    && entry
                                        .exports
                                        .iter()
                                        .take(index)
                                        .all(|prior| prior != member)
                            })
                        }))
        },
    )]
    fn close(
        &mut self,
        structure: StructureIndex,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let mut layers = Vec::new();
        self.absorb(structure, &mut layers)?;
        self.match_signature(structure, &mut layers)?;
        let mut next = 0_usize;
        while let Some(&layer) = layers.get(next) {
            next = next.saturating_add(1_usize);
            self.fuel.spend()?;
            self.layer(layer, &mut layers)?;
        }
        self.seal(structure);

        Ok(())
    }

    /// Read every member signature of `structure` that names a nested module
    /// as that module's signature.
    ///
    /// # Specification
    /// - requires: `structure`'s body is read.
    /// - ensures: a definition member of a nested module's name holding a
    ///   record-typed signature and no definition becomes a layer over that
    ///   module and declares nothing; any other definition member sharing a
    ///   nested module's name is refused as a second definition of it.
    /// - provides: the member-signature half of matching.
    /// - fails: [`LoweringRefusal::UnknownMold`].
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoweringRefusal::UnknownMold`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a nested module signature is absorbed as a constraint
    ///   rather than exported as a value, while a conflicting definition is
    ///   refused. The predicate reads only the layers this call appended.
    /// - witness: `tests::modules::nested_member_signature_constrains_the_parent_binding`
    /// - witness: `tests::modules::duplicate_module_member_definition_is_rejected`
    #[spec(
        captures: before = (
            self.collected.slots.len(),
            self.collected.structures.len(),
            self.collected.by_name.len(),
            layers.len(),
        ),
        ensures: |_| {
            self.collected.slots.len() == before.0
                && self.collected.structures.len() == before.1
                && self.collected.by_name.len() <= before.2
                && layers.len() >= before.3
                && layers.get(before.3 ..).is_some_and(|appended| appended.iter().all(|layer| {
                    layer.scope == Maybe::Absent(component_scope::Absent::Body)
                        && self
                            .collected
                            .structures
                            .get(layer.structure.0)
                            .is_some_and(|entry| entry.container == Container::Module(structure))
                }))
        },
    )]
    fn absorb(
        &mut self,
        structure: StructureIndex,
        layers: &mut Vec<Layer>,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let container = Container::Module(structure);
        let nested: Vec<StructureIndex> = self
            .collected
            .structures
            .get(structure.0)
            .map(|entry| {
                entry
                    .members
                    .iter()
                    .filter_map(|member| match *member {
                        Member::Module(nested) => Some(nested),
                        Member::Slot(_) => None,
                    })
                    .collect()
            })
            .unwrap_or_default();
        for nested in nested {
            let Some((name, named)) = self
                .collected
                .structures
                .get(nested.0)
                .map(|entry| (entry.name, entry.named))
            else {
                continue;
            };
            let Some(&slot) = self.collected.by_name.get(&(container, name))
            else {
                continue;
            };
            let Some(entry) = self.collected.slots.get(slot.0)
            else {
                continue;
            };
            let (signature, definition, introduced) =
                (entry.signature, entry.definition, entry.introduced_by);
            if let (Maybe::Present(stated), Maybe::Absent(_)) = (signature, definition)
                && let Operand::Written(record) = stated.operand
                && self.form_name(record)?.as_ref() == TELESCOPE_TYPE
            {
                if let Some(absorbed) = self.collected.slots.get_mut(slot.0) {
                    absorbed.signature = Maybe::Absent(declaration_half::Absent::Unwritten);
                    absorbed.role = Role::Held;
                }
                let _absorbed = self.collected.by_name.remove(&(container, name));
                layers.push(Layer {
                    structure: nested,
                    record,
                    scope: Maybe::Absent(component_scope::Absent::Body),
                });
                continue;
            }
            if let Some(clashing) = self.collected.slots.get_mut(slot.0) {
                clashing.refuse(introduced.node, LoweringRefusal::DuplicateDefinition {
                    span: named.span,
                    name,
                    first: introduced.span,
                });
            }
        }

        Ok(())
    }

    /// Match the module at `structure` against its own signature.
    ///
    /// # Specification
    /// - requires: `structure`'s body is read and its member signatures
    ///   absorbed.
    /// - ensures: an unascribed module exports every member it declares, in
    ///   source order. An ascribed module exports exactly its value components,
    ///   in signature order, each found by name: a definition member takes the
    ///   component's type, as its signature when it has none or only a derived
    ///   one, and as a witness otherwise; a nested module takes a record-typed
    ///   component as a layer. A manifest type component is recorded with a
    ///   held slot owning its type, and an abstract one with the body's type
    ///   member of its name, read as its atom under a sealing and as the
    ///   member's type otherwise; every type sees the type components before
    ///   it. A component no member supplies, a nested module stated a type
    ///   other than a record, and a type component the fragment does not read
    ///   each file a refusal under the component's name; members the signature
    ///   omits stay admitted and are not exported.
    /// - provides: the module's own coercive matching.
    /// - fails: [`LoweringRefusal::UnknownMold`] and
    ///   [`LoweringRefusal::BudgetExceeded`].
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoweringRefusal::UnknownMold`] and
    /// [`LoweringRefusal::BudgetExceeded`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the component forms separated by a value component
    ///   met by an untyped member, by a member with its own signature, by a
    ///   nested module and by nothing, a manifest component named by a later
    ///   one, an abstract one sealed and strengthened, and each unread type
    ///   component; hiding by a member the signature omits; order by a
    ///   reordered signature, each asserted as the exact exports, declared
    ///   types or refusal.
    /// - witness: `tests::modules::a_reordered_signature_matches_and_canonicalizes`
    /// - witness: `tests::modules::module_signature_matching_hides_extra_members`
    /// - witness: `tests::modules::a_missing_signature_component_is_rejected_at_the_signature`
    /// - witness: `tests::modules::a_manifest_type_component_expands_in_later_components`
    /// - witness: `tests::modules::a_kinded_type_component_forms_at_its_classifier`
    /// - witness: `tests::modules::a_manifest_family_component_binds_two_parameters`
    /// - witness: `tests::modules::a_transparent_abstract_component_reads_its_type_member`
    /// - witness: `tests::modules::opaque_ascription_seals`
    /// - witness: `tests::modules::a_nonempty_ascription_checks_each_component_at_its_member`
    /// - witness: `tests::modules::a_dangling_member_signature_is_an_obligation`
    #[spec(
        ensures: |ret| {
            ret.is_err()
                || self
                    .collected
                    .structures
                    .get(structure.0)
                    .is_none_or(|entry| match entry.ascription {
                        | Maybe::Absent(_) => entry.exports.iter().copied().eq(entry
                            .members
                            .iter()
                            .copied()
                            .filter(|member| match *member {
                                | Member::Slot(slot) => self
                                    .collected
                                    .slots
                                    .get(slot.0)
                                    .is_some_and(|slot| slot.role == Role::Declared),
                                | Member::Module(_) => true,
                            })),
                        | Maybe::Present(ref components) => {
                            entry.coerced.0
                                && entry.exports.iter().enumerate().all(|(index, member)| {
                                    entry.members.contains(member)
                                        && entry
                                            .exports
                                            .iter()
                                            .take(index)
                                            .all(|prior| prior != member)
                                })
                                && entry.types.len() <= components.len()
                                && components
                                    .iter()
                                    .filter_map(|component| match component.form {
                                        | ComponentForm::Manifest(defined) => {
                                            Some((component.name, TypeMeaning::Manifest(defined)))
                                        },
                                        | ComponentForm::Value(_)
                                        | ComponentForm::Abstract(_)
                                        | ComponentForm::Family(_)
                                        | ComponentForm::Parameterized { .. }
                                        | ComponentForm::Derived
                                        | ComponentForm::Unread(_) => None,
                                    })
                                    .all(|stated| {
                                        entry
                                            .types
                                            .iter()
                                            .any(|component| (component.name, component.meaning) == stated)
                                    })
                        },
                    })
        },
    )]
    fn match_signature(
        &mut self,
        structure: StructureIndex,
        layers: &mut Vec<Layer>,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let container = Container::Module(structure);
        let Some(entry) = self.collected.structures.get(structure.0)
        else {
            return Ok(());
        };
        let (module, sealed) = (entry.name, entry.sealed);
        let Maybe::Present(components) = entry.ascription.clone()
        else {
            let exports = entry
                .members
                .iter()
                .copied()
                .filter(|member| match *member {
                    Member::Slot(slot) => self
                        .collected
                        .slots
                        .get(slot.0)
                        .is_some_and(|held| held.role == Role::Declared),
                    Member::Module(_) => true,
                })
                .collect();
            if let Some(opened) = self.collected.structures.get_mut(structure.0) {
                opened.exports = exports;
            }
            return Ok(());
        };
        let mut exports = Vec::new();
        let mut exported = BTreeSet::new();
        let mut types = Vec::new();
        for (ordinal, component) in components.into_iter().enumerate() {
            self.fuel.spend()?;
            let scope = ComponentScope {
                structure,
                before: types.len(),
            };
            let stated = match component.form {
                ComponentForm::Value(stated) => stated,
                ComponentForm::Manifest(defined) => {
                    let held =
                        self.held(container, component.name, component.named, component.named);
                    self.collected.own(defined.node, held);
                    self.collected.scopes.push((defined.node, scope));
                    types.push(TypeComponent {
                        name: component.name,
                        meaning: TypeMeaning::Manifest(defined),
                        held,
                    });
                    continue;
                },
                ComponentForm::Parameterized {
                    parameters,
                    defined,
                } => {
                    self.manifest_family(
                        container, component, parameters, defined, scope, &mut types,
                    );
                    continue;
                },
                ComponentForm::Abstract(Maybe::Present(kind))
                    if !sealed.0 && matches!(self.kind_form(kind), Ok(KindForm::Arrow)) =>
                {
                    self.family_component(
                        structure,
                        ComponentPlace(ordinal),
                        component,
                        FamilyForm::Written(kind),
                        scope,
                        &mut types,
                    );
                    continue;
                },
                ComponentForm::Abstract(kind) => {
                    self.abstract_component(
                        structure,
                        ComponentPlace(ordinal),
                        component,
                        kind,
                        &mut types,
                    );
                    continue;
                },
                ComponentForm::Family(form) => {
                    self.family_component(
                        structure,
                        ComponentPlace(ordinal),
                        component,
                        form,
                        scope,
                        &mut types,
                    );
                    continue;
                },
                ComponentForm::Derived => {
                    if let Maybe::Present(found) =
                        self.derived_component(structure, component, ComponentPlace(ordinal), scope)
                        && exported.insert(found)
                    {
                        exports.push(found);
                    }
                    continue;
                },
                ComponentForm::Unread(form) => {
                    let refusal = LoweringRefusal::UnreadAscription {
                        span: component.named.span,
                        name: component.name,
                        form,
                    };
                    let _held = self.refuse_held(
                        container,
                        component.name,
                        component.named,
                        component.named,
                        refusal,
                    );
                    continue;
                },
            };
            if let Maybe::Present(found) =
                self.state_component(container, module, component, stated, scope, layers)?
                && exported.insert(found)
            {
                exports.push(found);
            }
        }
        if let Some(matched) = self.collected.structures.get_mut(structure.0) {
            matched.exports = exports;
            matched.types = types;
            matched.coerced = Coerced(true);
        }

        Ok(())
    }

    /// State the value component `component`, of type `stated`, for the
    /// member of its name in `container`, the module `module` names.
    ///
    /// # Specification
    /// - requires: `container` is the module the component's signature
    ///   ascribes.
    /// - ensures: as [`Self::match_signature`] for one value component; the
    ///   member found is yielded, and nothing when the component refused.
    /// - provides: the per-component half of [`Self::match_signature`] and of
    ///   [`Self::layer`].
    /// - fails: [`LoweringRefusal::UnknownMold`].
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoweringRefusal::UnknownMold`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a named value is constrained directly, a nested
    ///   module queues a record layer, and an absent component receives its own
    ///   refusal.
    /// - witness: `tests::modules::a_reordered_signature_matches_and_canonicalizes`
    /// - witness: `tests::modules::module_signature_matching_hides_extra_members`
    /// - witness: `tests::modules::a_missing_signature_component_is_rejected_at_the_signature`
    /// - witness: `tests::modules::nested_member_signature_constrains_the_parent_binding`
    #[spec(
        captures: before = (self.member_named(container, component.name), layers.len()),
        ensures: |ret| {
            ret.as_ref().map_or(true, |found| match *found {
                | Maybe::Present(Member::Slot(_)) => *found == before.0 && layers.len() == before.1,
                | Maybe::Present(Member::Module(nested)) => {
                    *found == before.0
                        && layers.len() == before.1.saturating_add(1)
                        && layers.last()
                            == Some(&Layer {
                                structure: nested,
                                record: stated,
                                scope: Maybe::Present(scope),
                            })
                },
                | Maybe::Absent(_) => {
                    !matches!(before.0, Maybe::Present(Member::Slot(_))) && layers.len() == before.1
                },
            })
        },
    )]
    fn state_component(
        &mut self,
        container: Container,
        module: SurfaceName<'source>,
        component: Component<'source>,
        stated: Placed,
        scope: ComponentScope,
        layers: &mut Vec<Layer>,
    ) -> Result<Maybe<Member, declared_member::Absent>, LoweringRefusal<'source>>
    {
        let found = self.member_named(container, component.name);
        match found {
            Maybe::Present(Member::Slot(slot)) => {
                self.state(
                    slot,
                    Operand::Written(stated),
                    component.named,
                    Maybe::Present(scope),
                );
            },
            Maybe::Present(Member::Module(nested)) => {
                let form = self.form_name(stated)?;
                if form.as_ref() != TELESCOPE_TYPE {
                    let refusal = LoweringRefusal::OutOfFragment {
                        span: stated.span,
                        form,
                        sort: FragmentSort::Module,
                        boundary: FragmentBoundary::WrongSort,
                    };
                    let _held = self.refuse_held(
                        container,
                        component.name,
                        component.named,
                        component.named,
                        refusal,
                    );
                    return Ok(Maybe::Absent(declared_member::Absent::Undeclared));
                }
                layers.push(Layer {
                    structure: nested,
                    record: stated,
                    scope: Maybe::Present(scope),
                });
            },
            Maybe::Absent(_) if self.repaired_member(container, component.name).0 => {},
            Maybe::Absent(_) => {
                let refusal = LoweringRefusal::UnknownMember {
                    span: component.named.span,
                    module,
                    member: component.name,
                };
                let _held = self.refuse_held(
                    container,
                    component.name,
                    component.named,
                    component.named,
                    refusal,
                );
            },
        }

        Ok(found)
    }

    /// Whether `container`'s body declares `name` in a form the parser
    /// repaired: the member is written, and its own refusal reports it.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: affirmative exactly when some slot of `container` named
    ///   `name` carries a [`FormFault::Repaired`] refusal.
    /// - provides: the cascade cut for a component naming a malformed member:
    ///   the member's parse error stands alone, with no unknown-member error
    ///   beside it.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a nested module left open is reported at its missing
    ///   close alone, its parent's signature component naming it raising
    ///   nothing, while a sibling component the body never declares is still
    ///   reported.
    /// - witness: `tests::modules::a_malformed_member_named_by_the_signature_is_reported_once`
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            spec_clause_traversal,
            reason = "parity: the body walks the slots once for the answer; the check walks them once more"
        )
    )]
    #[spec(ensures: |ret| ret.0 == self.collected.slots.iter().any(|slot| slot.container == container && slot.name == name && matches!(slot.refusal, Maybe::Present((_, LoweringRefusal::MalformedForm { fault: FormFault::Repaired(_), .. })))))]
    fn repaired_member(
        &self,
        container: Container,
        name: SurfaceName<'source>,
    ) -> MemberRepaired
    {
        MemberRepaired(self.collected.slots.iter().any(|slot| {
            slot.container == container
                && slot.name == name
                && matches!(
                    slot.refusal,
                    Maybe::Present((_, LoweringRefusal::MalformedForm {
                        fault: FormFault::Repaired(_),
                        ..
                    }))
                )
        }))
    }

    /// The member `container`'s body declares under `name`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a declaration slot wins over a module of the same name and
    ///   container; otherwise the module or an undeclared reason is returned.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — signatures resolve definition members and nested
    ///   modules within the named container, and reject a missing component.
    /// - witness: `tests::modules::a_reordered_signature_matches_and_canonicalizes`
    /// - witness: `tests::modules::module_signature_matching_hides_extra_members`
    /// - witness: `tests::modules::a_missing_signature_component_is_rejected_at_the_signature`
    /// - witness: `tests::modules::nested_member_signature_constrains_the_parent_binding`
    #[spec(
        ensures: |ret| {
            ret == match self.collected.by_name.get(&(container, name)) {
                | Some(&slot) => Maybe::Present(Member::Slot(slot)),
                | None => match self.collected.modules.get(&(container, name)) {
                    | Some(&nested) => Maybe::Present(Member::Module(nested)),
                    | None => Maybe::Absent(declared_member::Absent::Undeclared),
                },
            }
        },
    )]
    fn member_named(
        &self,
        container: Container,
        name: SurfaceName<'source>,
    ) -> Maybe<Member, declared_member::Absent>
    {
        if let Some(&slot) = self.collected.by_name.get(&(container, name)) {
            return Maybe::Present(Member::Slot(slot));
        }
        match self.collected.modules.get(&(container, name)) {
            Some(&nested) => Maybe::Present(Member::Module(nested)),
            None => Maybe::Absent(declared_member::Absent::Undeclared),
        }
    }

    /// State `operand`, a type written or derived at `at`, for the definition
    /// member at `member`.
    ///
    /// # Specification
    /// - requires: `member` names a live slot.
    /// - ensures: a member with no signature, or with only the one a function
    ///   tail derives, takes `operand` as its signature, the derived one filed
    ///   as a witness; a member with a written signature keeps it and `operand`
    ///   is filed as a witness, which a sealing `scope` exports in the member's
    ///   place. A written type is owned by the slot it lands on and sees
    ///   `scope`'s type components; a derived one has no node to own.
    /// - provides: the one way a signature types a member.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a written member signature wins over a derived one
    ///   and an additional signature becomes a separate checking witness.
    /// - witness: `tests::modules::member_signature_attaches_and_wins_over_derived_function_type`
    /// - witness: `tests::modules::signatures_attach_to_their_defs`
    /// - witness: `tests::modules::nested_member_signature_constrains_the_parent_binding`
    /// - witness: `tests::modules::a_signed_member_of_a_sealed_module_exports_its_witness`
    #[spec(
        captures: before = (
            self.collected.slots.len(),
            self.collected.scopes.len(),
            self.collected
                .slots
                .get(member.0)
                .map(|entry| entry.signature),
        ),
        ensures: |_| {
            let Some(prior) = before.2
            else {
                return self.collected.slots.len() == before.0
                    && self.collected.scopes.len() == before.1;
            };
            let half = Half {
                declaration: at,
                named: at,
                operand,
            };
            let written = match operand {
                | Operand::Written(stated) => Some(stated.node),
                | Operand::Function
                | Operand::Member(_)
                | Operand::Data(_)
                | Operand::Words(_)
                | Operand::Loop { .. }
                | Operand::Operation
                | Operand::Signature
                | Operand::Presented
                | Operand::Code
                | Operand::Model(_)
                | Operand::World => None,
            };
            let has_signature = matches!(prior, Maybe::Present(_));
            let keeps_signature = matches!(
                prior,
                Maybe::Present(Half {
                    operand: Operand::Written(_) | Operand::Member(_) | Operand::Model(_),
                    ..
                })
            );
            let owner = if keeps_signature {
                SlotIndex(before.0)
            }
            else {
                member
            };
            self.collected.slots.len() == before.0.saturating_add(usize::from(has_signature))
                && self.collected.slots.get(member.0).is_some_and(|entry| {
                    entry.signature
                        == if keeps_signature {
                            prior
                        }
                        else {
                            Maybe::Present(half)
                        }
                })
                && written.is_none_or(|node| {
                    self.collected
                        .owner
                        .get(usize::from(node))
                        .is_none_or(|held| *held == Maybe::Present(owner))
                })
                && match (scope, written) {
                    | (Maybe::Present(seen), Some(node)) => {
                        self.collected.scopes.len() == before.1.saturating_add(1)
                            && self.collected.scopes.last() == Some(&(node, seen))
                    },
                    | (Maybe::Present(_) | Maybe::Absent(_), _) => {
                        self.collected.scopes.len() == before.1
                    },
                }
        },
    )]
    fn state(
        &mut self,
        member: SlotIndex,
        operand: Operand,
        at: Placed,
        scope: Maybe<ComponentScope, component_scope::Absent>,
    )
    {
        let half = Half {
            declaration: at,
            named: at,
            operand,
        };
        let Some(entry) = self.collected.slots.get_mut(member.0)
        else {
            return;
        };
        let home = entry.container;
        let owner = match entry.signature {
            Maybe::Absent(_) => {
                entry.signature = Maybe::Present(half);
                member
            },
            Maybe::Present(
                derived @ Half {
                    operand: Operand::Function,
                    ..
                },
            ) => {
                entry.signature = Maybe::Present(half);
                let _witness = self.witness(member, derived);
                member
            },
            Maybe::Present(_) => self.witness(member, half),
        };
        if let Operand::Written(stated) = operand {
            self.collected.own(stated.node, owner);
        }
        if let Maybe::Present(seen) = scope {
            if let Operand::Written(stated) = operand {
                self.collected.scopes.push((stated.node, seen));
            }
            let sealing = self
                .collected
                .structures
                .get(seen.structure.0)
                .is_some_and(|ascribing| ascribing.sealed.0);
            if sealing
                && owner != member
                && let Container::Module(exporting) = home
                && let Some(exporter) = self.collected.structures.get_mut(exporting.0)
            {
                let _restated = exporter.exported_as.insert(member, owner);
            }
        }
    }

    /// Apply one layer: a record type stating the signature of a nested
    /// module, after the signatures already applied to it.
    ///
    /// # Specification
    /// - requires: the layer's module is closed.
    /// - ensures: the module's exports become the record's fields, in field
    ///   order, each found among the exports so far: a definition member takes
    ///   the field's type as [`Self::state`] states it, and a nested module a
    ///   record-typed field as a further layer queued on `queue`. A field the
    ///   exports do not hold files a held slot carrying the refusal under its
    ///   name; a record out of shape files one under the module's name. A
    ///   record in shape is kept among the module's [`Structure::stated_at`],
    ///   read in the layer's scope, so it lowers as the type it writes.
    /// - provides: the matching of a module against a signature its enclosing
    ///   module states for it.
    /// - fails: [`LoweringRefusal::UnknownMold`].
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoweringRefusal::UnknownMold`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a layer from the enclosing module's signature and one
    ///   from a member signature, the latter disagreeing with the module's own,
    ///   each asserted as the exact exports and the checker's verdict; a nested
    ///   module stated at a non-record type, the wrong sort.
    /// - witness: `tests::modules::nested_modules_lower_as_parent_members_and_project`
    /// - witness: `tests::modules::nested_member_signature_constrains_the_parent_binding`
    /// - witness: `tests::modules::a_nested_module_stated_at_a_non_record_type_is_the_wrong_sort`
    #[spec(
        captures: before = (
            self.collected.structures.len(),
            self.collected
                .structures
                .get(layer.structure.0)
                .map(|entry| entry.exports.len()),
            queue.len(),
        ),
        ensures: |_| {
            self.collected.structures.len() == before.0
                && queue.len() >= before.2
                && self
                    .collected
                    .structures
                    .get(layer.structure.0)
                    .is_none_or(|entry| {
                        Some(entry.exports.len()) <= before.1
                            && entry.exports.iter().enumerate().all(|(index, member)| {
                                entry.members.contains(member)
                                    && entry
                                        .exports
                                        .iter()
                                        .take(index)
                                        .all(|prior| prior != member)
                            })
                    })
        },
    )]
    fn layer(
        &mut self,
        layer: Layer,
        queue: &mut Vec<Layer>,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let mut pieces = Pieces::new();
        read_pieces(self.pbg, self.tree, layer.record.node, &mut pieces)?;
        let fields = match self.fields(layer.record, &pieces) {
            Ok(fields) => fields,
            Err(refusal) => {
                self.fault_at(layer.structure, layer.record, refusal);
                return Ok(());
            },
        };
        if let Maybe::Present(seen) = layer.scope {
            self.collected.scopes.push((layer.record.node, seen));
        }
        if let Some(entry) = self.collected.structures.get_mut(layer.structure.0) {
            entry.stated_at.push(layer.record);
        }
        let container = Container::Module(layer.structure);
        let Some((module, exports)) = self
            .collected
            .structures
            .get(layer.structure.0)
            .map(|entry| (entry.name, entry.exports.clone()))
        else {
            return Ok(());
        };
        let mut kept = Vec::new();
        let mut retained = BTreeSet::new();
        for field in fields {
            let found = exports
                .iter()
                .copied()
                .find(|export| self.member_name(*export) == field.name);
            match found {
                Some(Member::Slot(slot)) => {
                    self.state(
                        slot,
                        Operand::Written(field.stated),
                        field.named,
                        layer.scope,
                    );
                },
                Some(Member::Module(nested)) => {
                    let form = self.form_name(field.stated)?;
                    if form.as_ref() != TELESCOPE_TYPE {
                        let refusal = LoweringRefusal::OutOfFragment {
                            span: field.stated.span,
                            form,
                            sort: FragmentSort::Module,
                            boundary: FragmentBoundary::WrongSort,
                        };
                        let _held = self.refuse_held(
                            container,
                            field.name,
                            field.named,
                            field.named,
                            refusal,
                        );
                        continue;
                    }
                    queue.push(Layer {
                        structure: nested,
                        record: field.stated,
                        scope: layer.scope,
                    });
                },
                None => {
                    let refusal = LoweringRefusal::UnknownMember {
                        span: field.named.span,
                        module,
                        member: field.name,
                    };
                    let _held =
                        self.refuse_held(container, field.name, field.named, field.named, refusal);
                    continue;
                },
            }
            if let Some(export) = found
                && retained.insert(export)
            {
                kept.push(export);
            }
        }
        if let Some(entry) = self.collected.structures.get_mut(layer.structure.0) {
            entry.exports = kept;
            entry.coerced = Coerced(true);
        }

        Ok(())
    }

    /// Read a record type's fields, `#{ name : T, … }`, each name the bare
    /// type-variable word its key hole holds.
    ///
    /// # Specification
    /// - requires: `pieces` is the reading of the record type `record`.
    /// - ensures: every field in order, when the tiles read `#{`, fields whose
    ///   key is a bare lowercase word and whose type follows its `:`, separated
    ///   by `,`, and `}` with nothing after.
    /// - provides: the reading half of [`Self::layer`].
    /// - fails: yields the repair the record holds, a misplaced tile or key, or
    ///   the hole's refusal for a field type not written as one form, each
    ///   naming the record form.
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoweringRefusal::MalformedForm`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a nested record signature names the retained field
    ///   and constrains its binding rather than exposing an omitted member. The
    ///   predicate asks for each name tile's own bytes, by address and length.
    /// - witness: `tests::modules::nested_member_signature_constrains_the_parent_binding`
    #[spec(
        ensures: |ret| {
            ret.as_ref().map_or(true, |fields| {
                matches!(pieces.repair, Maybe::Absent(_))
                    && fields.iter().all(|field| {
                        core::ptr::eq(
                            core::ptr::from_ref::<str>(field.name.as_ref()),
                            core::ptr::from_ref::<str>(self.name_of(field.named).as_ref()),
                        )
                            && pieces.pieces.contains(&Piece::Operand(field.stated))
                    })
            })
        },
    )]
    fn fields(
        &self,
        record: Placed,
        pieces: &Pieces,
    ) -> Result<Vec<Field<'source>>, LoweringRefusal<'source>>
    {
        let form = self.form_name(record)?;
        if let Maybe::Present(repaired) = pieces.repair {
            return Err(repaired.refusal(form));
        }
        let mut cursor = Cursor::new(&pieces.pieces, record.span);
        if let Maybe::Absent(_) = cursor.tile(TileName::RECORD) {
            return Err(misplaced_in(form, cursor.here()));
        }
        let mut fields = Vec::new();
        loop {
            if let Maybe::Present(_) = cursor.tile(TileName::BRACE_CLOSE) {
                break;
            }
            let named = one_in(form, cursor.operands())?;
            if self.form_name(named)? != FormName::TYPE_VARIABLE {
                return Err(misplaced_in(form, named.span));
            }
            if let Maybe::Absent(_) = cursor.tile(TileName::COLON) {
                return Err(misplaced_in(form, cursor.here()));
            }
            fields.push(Field {
                name: self.name_of(named),
                named,
                stated: one_in(form, cursor.operands())?,
            });
            if let Maybe::Absent(_) = cursor.tile(TileName::COMMA)
                && let Maybe::Absent(_) = cursor.at(TileName::BRACE_CLOSE)
            {
                return Err(misplaced_in(form, cursor.here()));
            }
        }
        if let Maybe::Present(_) = cursor.peek() {
            return Err(misplaced_in(form, cursor.here()));
        }

        Ok(fields)
    }

    /// The name `member` is declared under.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a live member yields its stored name; an absent slot or
    ///   module yields the empty name.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — nested signature matching distinguishes definition
    ///   and module names while retaining only the stated exports.
    /// - witness: `tests::modules::nested_member_signature_constrains_the_parent_binding`
    /// - witness: `tests::modules::a_reordered_signature_matches_and_canonicalizes`
    /// - witness: `tests::modules::module_signature_matching_hides_extra_members`
    #[spec(
        ensures: |ret| match member {
            | Member::Slot(slot) => self
                .collected
                .slots
                .get(slot.0)
                .map_or_else(|| ret.as_ref().is_empty(), |entry| ret == entry.name),
            | Member::Module(nested) => self
                .collected
                .structures
                .get(nested.0)
                .map_or_else(|| ret.as_ref().is_empty(), |entry| ret == entry.name),
        },
    )]
    fn member_name(
        &self,
        member: Member,
    ) -> SurfaceName<'source>
    {
        match member {
            Member::Slot(slot) => self
                .collected
                .slots
                .get(slot.0)
                .map_or_else(|| SurfaceName::from(""), |entry| entry.name),
            Member::Module(nested) => self
                .collected
                .structures
                .get(nested.0)
                .map_or_else(|| SurfaceName::from(""), |entry| entry.name),
        }
    }

    /// The name of the form `placed` stands for.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a form yields its classified name; a missing or non-form node
    ///   yields the root name.
    /// - fails: with an unknown mold when classification cannot read the node.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — nested record signatures report their own malformed
    ///   form while valid records constrain the parent binding.
    /// - witness: `tests::modules::nested_member_signature_constrains_the_parent_binding`
    #[spec(
        ensures: |ret| {
            ret == self
                .tree
                .node(placed.node)
                .map_or(Ok(FormName::ROOT), |node| {
                    shape_of(self.pbg, node).map(|shape| match shape {
                        | Shape::Form { name, .. } => name,
                        | Shape::Root | Shape::Repair(_) | Shape::Layout => FormName::ROOT,
                    })
                })
        },
    )]
    fn form_name(
        &self,
        placed: Placed,
    ) -> Result<FormName, LoweringRefusal<'source>>
    {
        let Some(node) = self.tree.node(placed.node)
        else {
            return Ok(FormName::ROOT);
        };

        Ok(match shape_of(self.pbg, node)? {
            Shape::Form { name, .. } => name,
            Shape::Root | Shape::Repair(_) | Shape::Layout => FormName::ROOT,
        })
    }
}

/// A type component as its signature writes it, before a manifest family's
/// parameters are filed with the collection.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Eq, PartialEq)]
enum WrittenType
{
    /// Any form but a manifest family.
    Formed(ComponentForm),
    /// A manifest family `type F(a : A, …) = τ`.
    Family
    {
        /// The parameters, in source order.
        parameters: Vec<FamilyParameter>,
        /// The type the family names.
        defined: Placed,
    },
}

/// What a type component written `type T` states after its name.
///
/// # Specification
/// - requires: `cursor` stands just past the component's name.
/// - ensures: `= τ` a manifest component; `: κ` an abstract one of kind `κ`; a
///   parameter list followed by `= τ` a manifest family over the parameters,
///   and followed by anything else a parameterized form the fragment does not
///   read, since a kind written as an arrow states an operator's parameters;
///   nothing an abstract one of no written kind. The cursor stands past the
///   component.
/// - provides: the type-component half of a module signature.
/// - fails: yields the parameter list's refusal for a list out of shape, and
///   the hole's refusal for a type not written as one form.
/// - panics: none.
///
/// # Errors
/// [`LoweringRefusal::MalformedForm`].
///
/// # Adequacy
/// - hypothesis: L3 — manifest, manifest family, kinded and bare components are
///   distinct, and a bare one keeps its later siblings.
/// - witness: `tests::modules::a_manifest_type_component_expands_in_later_components`
/// - witness: `tests::modules::a_manifest_family_component_binds_two_parameters`
/// - witness: `tests::modules::a_kinded_type_component_forms_at_its_classifier`
/// - witness: `tests::modules::a_transparent_abstract_component_reads_its_type_member`
/// - witness: `tests::modules::an_abstract_component_kinds_at_a_universe`
#[spec(
    captures: first = cursor.peek(),
    ensures: |ret| {
        ret.as_ref().map_or(true, |written| match first {
            | Maybe::Present(Piece::Tile { label, .. }) if label == TileName::PAREN_OPEN => {
                matches!(*written, WrittenType::Family { .. })
                    || *written == WrittenType::Formed(ComponentForm::Unread(AscriptionForm::Parameterized))
            },
            | Maybe::Present(Piece::Tile { label, .. }) if label == TileName::EQUALS => {
                matches!(*written, WrittenType::Formed(ComponentForm::Manifest(_)))
            },
            | Maybe::Present(Piece::Tile { label, .. }) if label == TileName::COLON => {
                matches!(*written, WrittenType::Formed(ComponentForm::Abstract(Maybe::Present(_))))
            },
            | _ => matches!(*written, WrittenType::Formed(ComponentForm::Abstract(Maybe::Absent(_)))),
        })
    },
)]
fn type_component<'source>(cursor: &mut Cursor<'_>)
-> Result<WrittenType, LoweringRefusal<'source>>
{
    let parameterized = matches!(cursor.at(TileName::PAREN_OPEN), Maybe::Present(_));
    let parameters = Collector::family_parameters(cursor)?;
    let form = if let Maybe::Present(_) = cursor.tile(TileName::EQUALS) {
        let defined = one_in(FormName::MODULE, cursor.operands())?;
        if parameterized {
            return Ok(WrittenType::Family {
                parameters,
                defined,
            });
        }
        ComponentForm::Manifest(defined)
    }
    else if let Maybe::Present(_) = cursor.tile(TileName::COLON) {
        let kind = one_in(FormName::MODULE, cursor.operands())?;
        ComponentForm::Abstract(Maybe::Present(kind))
    }
    else {
        ComponentForm::Abstract(Maybe::Absent(component_kind::Absent::Unkinded))
    };

    Ok(WrittenType::Formed(if parameterized {
        ComponentForm::Unread(AscriptionForm::Parameterized)
    }
    else {
        form
    }))
}

/// The operand a one-operand hole of `form` holds, or the fault its run
/// earns.
///
/// # Specification
/// - requires: nothing.
/// - ensures: exactly one operand succeeds; an empty hole reports a missing
///   operand and an overfull hole reports the first extra operand.
/// - fails: with the located arity refusal of the supplied form.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — empty, single and overfull holes preserve the selected
///   operand or the exact gap/extra location and distinguish their fault kinds.
/// - witness: `module::tests::signature_holes_distinguish_missing_single_and_extra_operands`
#[spec(
    ensures: |ret| {
        matches!(
            (run, ret),
            (Run::One(_), Ok(_))
                | (
                    Run::Empty(_),
                    Err(LoweringRefusal::MalformedForm {
                        fault: FormFault::MissingOperand,
                        ..
                    })
                )
                | (
                    Run::Several { .. },
                    Err(LoweringRefusal::MalformedForm {
                        fault: FormFault::ExtraOperand,
                        ..
                    })
                )
        )
    },
)]
const fn one_in<'source>(
    form: FormName,
    run: Run,
) -> Result<Placed, LoweringRefusal<'source>>
{
    match run {
        Run::One(operand) => Ok(operand),
        Run::Empty(gap) => Err(LoweringRefusal::MalformedForm {
            span: gap,
            form,
            fault: FormFault::MissingOperand,
        }),
        Run::Several { extra, .. } => Err(extra_operand(form, extra)),
    }
}

/// The refusal a tile of `form` out of place earns.
///
/// # Specification
/// trivial.
const fn misplaced_in<'source>(
    form: FormName,
    span: ByteSpan,
) -> LoweringRefusal<'source>
{
    LoweringRefusal::MalformedForm {
        span,
        form,
        fault: FormFault::MisplacedTile,
    }
}

/// Read a declaration form's tail, after its name.
///
/// # Specification
/// - requires: `header` stands just past the form's name.
/// - ensures: the half the tail writes, when it is a signature or a definition
///   whose hole holds exactly one form and which closes with `;` and nothing
///   after it; a function tail, opening on `(` or on a telescope `@[ … ]`
///   followed by `(`, with whether it is signed; every other tail yields its
///   first fault — an implicit telescope declined by the folded form's own
///   name, an empty or overfull hole, or a tile out of place.
/// - provides: the tail half of a declaration form.
/// - fails: never; a fault is yielded rather than raised.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — signature, definition, signed function and malformed
///   tails select distinct filing paths without consuming a deferred function.
/// - witness: `module::tests::a_signature_pairs_with_its_definition`
/// - witness: `module::tests::a_definition_pairs_with_a_later_signature`
/// - witness: `module::tests::a_second_signature_is_refused`
/// - witness: `module::tests::a_second_definition_is_refused`
/// - witness: `tests::modules::member_signature_attaches_and_wins_over_derived_function_type`
/// - witness: `tests::modules::signatures_attach_to_their_defs`
/// - witness: `module::tests::a_declaration_missing_its_body_is_refused`
#[spec(
    captures: first = header.peek(),
    ensures: |ret| match ret {
        | Tail::Function(_) => {
            matches!(first, Maybe::Present(Piece::Tile { label, .. }) if label == TileName::PAREN_OPEN || label == TileName::ATTRIBUTES)
                && header.peek() == first
        },
        | Tail::Wrote(kind, _) => {
            matches!(header.peek(), Maybe::Absent(_))
                && matches!(first, Maybe::Present(Piece::Tile { label, .. }) if label == match kind { HalfKind::Signature => TileName::COLON, HalfKind::Definition => TileName::EQUALS })
        },
        | Tail::Refused(_) => {
            !matches!(first, Maybe::Present(Piece::Tile { label, .. }) if label == TileName::PAREN_OPEN)
        },
        | Tail::Data(_) | Tail::World => false,
    },
)]
fn read_tail<'source>(
    header: &mut Cursor<'_>,
    declaration: Placed,
) -> Tail<'source>
{
    let mut past = header.clone();
    if let Maybe::Present(_) = past.tile(TileName::ATTRIBUTES) {
        while let Maybe::Present(piece) = past.read() {
            if let Piece::Tile { label, .. } = piece
                && label == TileName::BRACKET_CLOSE
            {
                break;
            }
        }
    }
    if let Maybe::Present(_) = past.at(TileName::PAREN_OPEN) {
        return Tail::Function(signing(past));
    }
    let kind = if let Maybe::Present(_) = header.tile(TileName::COLON) {
        HalfKind::Signature
    }
    else if let Maybe::Present(_) = header.tile(TileName::EQUALS) {
        HalfKind::Definition
    }
    else {
        return Tail::Refused(unadmitted_tail(header, declaration));
    };
    let operand = match header.operands() {
        Run::One(operand) => operand,
        Run::Empty(gap) => {
            return Tail::Refused(LoweringRefusal::MalformedForm {
                span: gap,
                form: FormName::DECLARATION,
                fault: FormFault::MissingOperand,
            });
        },
        Run::Several { extra, .. } => {
            return Tail::Refused(extra_operand(FormName::DECLARATION, extra));
        },
    };
    let closed = header.tile(TileName::SEMICOLON);
    if let (Maybe::Present(_), Maybe::Absent(_)) = (closed, header.peek()) {
        return Tail::Wrote(kind, operand);
    }

    Tail::Refused(misplaced(header.here()))
}

/// Whether the function tail at `header` states its type.
///
/// # Specification
/// - requires: `header` stands at the tail's `(`.
/// - ensures: signed exactly when every binder tile before the parameter list's
///   own `)` is followed by `:`, and the `)` by `->`; unsigned otherwise, a
///   list with no `)` included. Only the tiles are read: whether each type and
///   the result hold exactly one form is the function's own reading, decided
///   where the classification reads the declaration.
/// - provides: which halves a function tail writes.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the two conditions separated by a fully typed tail, a
///   tail missing its result type, and a tail with one untyped parameter, each
///   asserted through the halves the lowered declaration reports.
/// - witness: `lower::tests::a_function_tail_lowers_to_a_thunked_lambda_chain`
/// - witness: `lower::tests::a_tail_missing_a_type_writes_its_definition_alone`
#[spec(
    ensures: |ret| {
        ret != Signing::Signed || matches!(header.at(TileName::ARROW), Maybe::Present(_))
    },
)]
fn signing(mut header: Cursor<'_>) -> Signing
{
    let _open = header.tile(TileName::PAREN_OPEN);
    loop {
        match header.read() {
            Maybe::Present(Piece::Tile { label, .. }) if label == TileName::PAREN_CLOSE => break,
            Maybe::Present(Piece::Tile { label, .. }) if TileName::BINDERS.contains(&label) => {
                if let Maybe::Absent(_) = header.at(TileName::COLON) {
                    return Signing::Unsigned;
                }
            },
            Maybe::Present(Piece::Tile { .. } | Piece::Operand(_)) => {},
            Maybe::Absent(_) => return Signing::Unsigned,
        }
    }
    match header.at(TileName::ARROW) {
        Maybe::Present(_) => Signing::Signed,
        Maybe::Absent(_) => Signing::Unsigned,
    }
}

/// The refusal a tail that is neither a signature, a definition nor a function
/// earns.
///
/// # Specification
/// - requires: `header` stands just past the form's name, at no `:`, `=` or
///   `(`.
/// - ensures: an implicit telescope, which only a function's parameters follow,
///   is refused by name at the declaration; an operand is one the form does not
///   take; every other piece is a misplaced tile.
/// - provides: the decline of the declaration tails the fragment does not read.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — an implicit telescope before a definition is refused by
///   name at the declaration, while a closing tile without a tail is misplaced
///   at its own span.
/// - witness: `lower::tests::an_implicit_telescope_on_no_function_is_refused_by_name`
/// - witness: `lower::tests::a_tile_out_of_place_is_refused`
#[spec(
    ensures: |ret| {
        ret == if matches!(header.at(TileName::ATTRIBUTES), Maybe::Present(_)) {
            LoweringRefusal::ImplicitTelescope { span: declaration.span }
        }
        else if let Maybe::Present(Piece::Operand(stray)) = header.peek() {
            extra_operand(FormName::DECLARATION, stray)
        }
        else {
            misplaced(header.here())
        }
    },
)]
fn unadmitted_tail<'source>(
    header: &Cursor<'_>,
    declaration: Placed,
) -> LoweringRefusal<'source>
{
    if let Maybe::Present(_) = header.at(TileName::ATTRIBUTES) {
        return LoweringRefusal::ImplicitTelescope {
            span: declaration.span,
        };
    }
    if let Maybe::Present(Piece::Operand(stray)) = header.peek() {
        return extra_operand(FormName::DECLARATION, stray);
    }

    misplaced(header.here())
}

/// The refusal a declaration tile out of place earns.
///
/// # Specification
/// trivial.
const fn misplaced<'source>(span: ByteSpan) -> LoweringRefusal<'source>
{
    LoweringRefusal::MalformedForm {
        span,
        form: FormName::DECLARATION,
        fault: FormFault::MisplacedTile,
    }
}

/// The refusal an operand `form` does not take earns.
///
/// # Specification
/// trivial.
const fn extra_operand<'source>(
    form: FormName,
    operand: Placed,
) -> LoweringRefusal<'source>
{
    LoweringRefusal::MalformedForm {
        span: operand.span,
        form,
        fault: FormFault::ExtraOperand,
    }
}

/// What a name's declarations amount to once the module has been walked.
///
/// # Specification
/// - requires: nothing to construct this data; its producers and consumers
///   state coordinate preconditions separately.
/// - ensures: Completed, type-only, body-only, nominal, abstract and refused
///   declarations remain distinct; identifiers refer to the producing core
///   arena, not to an authenticated arena identity, and a nominal outcome's
///   index to the producing module's signature list.
/// - fails: not applicable to the data item.
/// - panics: not applicable to the data item.
/// - executable: none — the enabled specification facade does not expose
///   type-invariant expansion; executable predicates cover the producing and
///   consuming operations.
///
/// # Adequacy
/// - hypothesis: L3 — paired halves complete, a dangling signature remains an
///   obligation, and duplicate definitions are refused.
/// - witness: `module::tests::a_signature_pairs_with_its_definition`
/// - witness: `module::tests::a_definition_pairs_with_a_later_signature`
/// - witness: `module::tests::a_second_signature_is_refused`
/// - witness: `module::tests::a_second_definition_is_refused`
/// - witness: `tests::modules::a_dangling_member_signature_is_an_obligation`
/// - witness: `lower::native::tests::a_data_declaration_lowers_to_its_signature`
/// - witness: `tests::modules::opaque_ascription_seals`
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum DeclarationOutcome<'source>
{
    /// A signature and the definition that completes it.
    Completed
    {
        /// The type the signature declared.
        declared_type: ValueTypeId,
        /// The value the definition lowered to.
        body: ValueId,
    },
    /// A signature no definition completes: the obligation this module owes.
    Uncompleted
    {
        /// The type the signature declared, which the obligation carries.
        declared_type: ValueTypeId,
    },
    /// A definition with no signature, whose body must synthesise.
    Bodied
    {
        /// The value the definition lowered to.
        body: ValueId,
    },
    /// A data declaration: a nominal family whose signature the module holds
    /// at this index.
    Data(DataIndex),
    /// A codata declaration: a nominal computation type whose signature the
    /// module holds at this index.
    Codata(CodataIndex),
    /// An abstract type an opaque ascription declares: the atom one of its
    /// abstract components mints, with its kind, its representation, the
    /// reach of its seal and its site.
    Abstract(Sealing),
    /// A world declaration `world w ;`: the world its admission position
    /// names, which has no type and no body.
    World,
    /// The declaration's first refusal.
    Refused(LoweringRefusal<'source>),
}

/// The position of a data declaration's signature in the module that lowered
/// it.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: the position is read against the module that produced it, by
///   [`LoweredModule::data`]; another module's list does not authenticate it.
/// - executable: none — the index holds no list to check its bound against.
///
/// # Adequacy
/// - hypothesis: L3 — two data declarations of one module take distinct,
///   ascending positions, each answering its own signature.
/// - witness: `lower::native::tests::a_data_declaration_lowers_to_its_signature`
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct DataIndex(usize);

impl From<usize> for DataIndex
{
    /// The data signature at `position`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(position: usize) -> Self
    {
        Self(position)
    }
}

impl From<DataIndex> for usize
{
    /// The position `index` names.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(index: DataIndex) -> Self
    {
        index.0
    }
}

/// The position of a codata declaration's signature in the module that
/// lowered it.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: the position is read against the module that produced it, by
///   [`LoweredModule::codata`].
/// - executable: none — the index holds no list to check its bound against.
///
/// # Adequacy
/// - hypothesis: L3 — a codata declaration answers its own signature.
/// - witness: `description::tests::a_codata_declaration_lowers_to_its_signature`
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct CodataIndex(usize);

impl From<usize> for CodataIndex
{
    /// The codata signature at `position`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(position: usize) -> Self
    {
        Self(position)
    }
}

/// Where one half of a declared name is written: its form, and the name tile
/// it writes or the form standing where a name belongs.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct HalfAt
{
    /// The bytes of the half's form.
    pub span: ByteSpan,
    /// The bytes of its name tile.
    pub named: ByteSpan,
}

/// Where each half of a declared name is written.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct Halves
{
    /// The signature, when the name has one.
    pub signature: Maybe<HalfAt, declaration_half::Absent>,
    /// The definition, when the name has one.
    pub definition: Maybe<HalfAt, declaration_half::Absent>,
}

/// The parts of one lowered declaration, as the pass that assembles a module
/// gathers them.
///
/// # Specification
/// - requires: nothing to construct this data; its producers and consumers
///   state coordinate preconditions separately.
/// - ensures: The supplied name, role, container, admission position, source
///   identities and lowering outcome travel together without validating their
///   cross-arena provenance.
/// - fails: not applicable to the data item.
/// - panics: not applicable to the data item.
/// - executable: none — the enabled specification facade does not expose
///   type-invariant expansion; executable predicates cover the producing and
///   consuming operations.
///
/// # Adequacy
/// - hypothesis: L3 — source pairing and composed export metadata distinguish
///   outcomes, repeated positions and roles.
/// - witness: `module::tests::a_signature_pairs_with_its_definition`
/// - witness: `module::tests::a_definition_pairs_with_a_later_signature`
/// - witness: `module::tests::structured_export_omits_invalid_segments_and_keeps_the_last_declared_name`
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct DeclarationParts<'source>
{
    /// The declared name.
    pub name: SurfaceName<'source>,
    /// Where the name is declared.
    pub container: Container,
    /// What the declaration stands for.
    pub role: Role,
    /// The admission position the name takes.
    pub constant: ConstantIndex,
    /// The bytes covered by the declaration that introduced the name.
    pub span: ByteSpan,
    /// The bytes of the name tile that declaration writes, or of the form
    /// standing where a name belongs when it writes none.
    pub named: ByteSpan,
    /// The opaque handle a checker echoes back in place of that span.
    pub origin: OriginToken,
    /// The unit key of this name's signature form.
    pub signature: Maybe<UnitKey, declaration_half::Absent>,
    /// The unit key of this name's definition form.
    pub definition: Maybe<UnitKey, declaration_half::Absent>,
    /// The unit key of the form that wrote a half of this name a second time,
    /// when that repetition is the name's refusal.
    pub duplicate: Maybe<UnitKey, declaration_half::Absent>,
    /// Where each of the name's halves is written.
    pub halves: Halves,
    /// What the name's declarations amount to.
    pub outcome: DeclarationOutcome<'source>,
}

/// One declared name, lowered.
///
/// # Specification
/// - requires: nothing to construct this data; its producers and consumers
///   state coordinate preconditions separately.
/// - ensures: The declaration exposes its supplied parts unchanged; its role
///   controls whether its position receives an exported structured name.
/// - fails: not applicable to the data item.
/// - panics: not applicable to the data item.
/// - executable: none — the enabled specification facade does not expose
///   type-invariant expansion; executable predicates cover the producing and
///   consuming operations.
///
/// # Adequacy
/// - hypothesis: L3 — concrete declaration outcomes survive lowering and
///   non-declared roles do not export names.
/// - witness: `module::tests::a_signature_pairs_with_its_definition`
/// - witness: `module::tests::a_definition_pairs_with_a_later_signature`
/// - witness: `module::tests::structured_export_omits_invalid_segments_and_keeps_the_last_declared_name`
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct LoweredDeclaration<'source>
{
    /// The declaration's parts.
    parts: DeclarationParts<'source>,
}

impl<'source> From<DeclarationParts<'source>> for LoweredDeclaration<'source>
{
    /// The declaration with these parts.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(parts: DeclarationParts<'source>) -> Self
    {
        Self { parts }
    }
}

impl<'source> LoweredDeclaration<'source>
{
    /// The declared name.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn name(&self) -> SurfaceName<'source>
    {
        self.parts.name
    }

    /// Where the name is declared: the top level, or the module whose path
    /// [`LoweredModule::path_of`] spells.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn container(&self) -> Container
    {
        self.parts.container
    }

    /// What the declaration stands for: a declared name, a witness checking
    /// a second type stated for a member, or a held refusal.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn role(&self) -> Role
    {
        self.parts.role
    }

    /// The admission position the name takes.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn constant(&self) -> ConstantIndex
    {
        self.parts.constant
    }

    /// The bytes covered by the declaration that introduced the name.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn span(&self) -> ByteSpan
    {
        self.parts.span
    }

    /// The bytes of the name tile the declaration introducing the name
    /// writes: where a face that goes from a use to its declaration lands.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn named(&self) -> ByteSpan
    {
        self.parts.named
    }

    /// The opaque handle a checker echoes back in place of the span.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn origin(&self) -> OriginToken
    {
        self.parts.origin
    }

    /// The unit key of this name's signature form, which its attributes are
    /// filed under.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub const fn signature(&self) -> Maybe<UnitKey, declaration_half::Absent>
    {
        self.parts.signature
    }

    /// The unit key of this name's definition form, which its attributes are
    /// filed under.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub const fn definition(&self) -> Maybe<UnitKey, declaration_half::Absent>
    {
        self.parts.definition
    }

    /// The unit key of the form that wrote a half of this name a second
    /// time, when that repetition is the name's refusal: the form no other
    /// key reaches, which answers at that refusal.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub const fn duplicate(&self) -> Maybe<UnitKey, declaration_half::Absent>
    {
        self.parts.duplicate
    }

    /// Where each of the name's halves is written: a name declared in two
    /// forms answers both, and one written once answers that form under the
    /// half it writes.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn halves(&self) -> Halves
    {
        self.parts.halves
    }

    /// What the name's declarations amount to.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn outcome(&self) -> DeclarationOutcome<'source>
    {
        self.parts.outcome
    }
}

quenchant_shape::reason_enum! {
    /// Why a manifest type component carries no lowered type.
    pub mod manifest_type {
        /// The type it names did not lower.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The type refused, and the refusal is carried by a held
            /// declaration under the component's name.
            Unlowered,
        }
    }
}

/// One value component a lowered module exports.
///
/// # Specification
/// - requires: nothing to construct this data; its producers and consumers
///   state coordinate preconditions separately.
/// - ensures: A value export pairs its source name with the flattened
///   declaration position used for references; it does not certify that the
///   position is live.
/// - fails: not applicable to the data item.
/// - panics: not applicable to the data item.
/// - executable: none — the enabled specification facade does not expose
///   type-invariant expansion; executable predicates cover the producing and
///   consuming operations.
///
/// # Adequacy
/// - hypothesis: L3 — module members project through their admitted constants.
/// - witness: `tests::modules::nested_modules_lower_as_parent_members_and_project`
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct ValueComponent<'source>
{
    /// The component's name.
    pub name: SurfaceName<'source>,
    /// The admission position of the member it resolves to.
    pub constant: ConstantIndex,
}

/// One manifest type component of a lowered module.
///
/// # Specification
/// - requires: nothing to construct this data; its producers and consumers
///   state coordinate preconditions separately.
/// - ensures: A manifest name retains its lowered type or the reason it lacks
///   one; its type identifier requires the producing core arena.
/// - fails: not applicable to the data item.
/// - panics: not applicable to the data item.
/// - executable: none — the enabled specification facade does not expose
///   type-invariant expansion; executable predicates cover the producing and
///   consuming operations.
///
/// # Adequacy
/// - hypothesis: L3 — manifest definitions expand in later signature
///   components.
/// - witness: `tests::modules::a_manifest_type_component_expands_in_later_components`
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct ManifestComponent<'source>
{
    /// The component's name.
    pub name: SurfaceName<'source>,
    /// The type it is manifestly equal to.
    pub defined: Maybe<ValueTypeId, manifest_type::Absent>,
}

/// One module, lowered: the stratum item recording its path, the components
/// it exports and whether matching coerced its body.
///
/// # Specification
/// - requires: nothing to construct this data; its producers and consumers
///   state coordinate preconditions separately.
/// - ensures: The lowered metadata keeps the full module path, source span,
///   selected value and nested-module exports, manifest types, sealed types,
///   coercion flag and stratum as separate fields.
/// - fails: not applicable to the data item.
/// - panics: not applicable to the data item.
/// - executable: none — the enabled specification facade does not expose
///   type-invariant expansion; executable predicates cover the producing and
///   consuming operations.
///
/// # Adequacy
/// - hypothesis: L3 — hidden, reordered and nested exports retain their
///   respective names and boundaries.
/// - witness: `tests::modules::a_reordered_signature_matches_and_canonicalizes`
/// - witness: `tests::modules::module_signature_matching_hides_extra_members`
/// - witness: `tests::modules::nested_modules_lower_as_parent_members_and_project`
/// - witness: `tests::modules::opaque_ascription_seals`
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct LoweredStructure<'source>
{
    /// The module's path, outermost first, its own name last.
    path: Vec<SurfaceName<'source>>,
    /// The bytes the module form covers.
    span: ByteSpan,
    /// The value components it exports, in signature order once matched and
    /// in source order otherwise.
    values: Vec<ValueComponent<'source>>,
    /// The nested modules it exports, by name, in the same order.
    modules: Vec<SurfaceName<'source>>,
    /// The manifest type components it exports, in signature order once
    /// matched and in source order otherwise.
    types: Vec<ManifestComponent<'source>>,
    /// The abstract type components an opaque ascription sealed, in
    /// signature order.
    sealed: Vec<SealedComponent<'source>>,
    /// Whether matching against a signature coerced the body.
    coerced: Coerced,
    /// What the module is in the stratum: a functor's body and parameter
    /// export nothing a declaration reads, an application's instance does.
    stratum: Stratum,
}

impl<'source> LoweredStructure<'source>
{
    /// The stratum item holding these parts.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    #[expect(
        clippy::too_many_arguments,
        reason = "one argument per field of the stratum item, each read independently"
    )]
    pub const fn new(
        path: Vec<SurfaceName<'source>>,
        span: ByteSpan,
        values: Vec<ValueComponent<'source>>,
        modules: Vec<SurfaceName<'source>>,
        types: Vec<ManifestComponent<'source>>,
        sealed: Vec<SealedComponent<'source>>,
        coerced: Coerced,
        stratum: Stratum,
    ) -> Self
    {
        Self {
            path,
            span,
            values,
            modules,
            types,
            sealed,
            coerced,
            stratum,
        }
    }

    /// The module's path, outermost first, its own name last.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn path(&self) -> &[SurfaceName<'source>]
    {
        &self.path
    }

    /// The bytes the module form covers.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn span(&self) -> ByteSpan
    {
        self.span
    }

    /// The value components it exports.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn values(&self) -> &[ValueComponent<'source>]
    {
        &self.values
    }

    /// The nested modules it exports, by name.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn modules(&self) -> &[SurfaceName<'source>]
    {
        &self.modules
    }

    /// The manifest type components it exports.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn types(&self) -> &[ManifestComponent<'source>]
    {
        &self.types
    }

    /// The abstract type components an opaque ascription sealed, each with
    /// its atom.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn sealed(&self) -> &[SealedComponent<'source>]
    {
        &self.sealed
    }

    /// Whether matching against a signature coerced the body.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn coerced(&self) -> Coerced
    {
        self.coerced
    }

    /// What the module is in the stratum.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn stratum(&self) -> Stratum
    {
        self.stratum
    }
}

/// One module, lowered: its declarations, its attributes, its origins, its
/// imports, and the outermost scope its names were declared in.
///
/// # Specification
/// - requires: nothing to construct this data; its producers and consumers
///   state coordinate preconditions separately.
/// - ensures: Declarations and structures retain their producer order alongside
///   attributes, origins, imports and recognition state; construction itself
///   does not certify their agreement.
/// - fails: not applicable to the data item.
/// - panics: not applicable to the data item.
/// - executable: none — the enabled specification facade does not expose
///   type-invariant expansion; executable predicates cover the producing and
///   consuming operations.
///
/// # Adequacy
/// - hypothesis: L3 — real source lowering and composed metadata separate
///   declared exports, refusals and invalid names.
/// - witness: `tests::modules::modules_lower_to_named_member_declarations`
/// - witness: `tests::modules::module_members_admit_in_source_order`
/// - witness: `tests::modules::a_readable_module_keeps_its_members_and_its_successor`
/// - witness: `tests::namespace::source_import_reaches_the_namespace_engine_and_exposes_its_alias`
/// - witness: `tests::namespace::an_unqualified_import_binds_no_alias`
/// - witness: `tests::namespace::duplicate_source_import_alias_becomes_a_refusal`
/// - witness: `module::tests::structured_export_omits_invalid_segments_and_keeps_the_last_declared_name`
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct LoweredModule<'source>
{
    /// Description-level structure and member refusals before native
    /// interpretation.
    descriptions: crate::description::DescriptionReport,
    /// Checked cells and every cell-layer member refusal.
    cells: crate::desc_cells::CellReport,
    /// The declarations, in admission order.
    declarations: Vec<LoweredDeclaration<'source>>,
    /// The data declarations' signatures, by [`DataIndex`].
    data: Vec<Arc<DataSignature>>,
    /// The names of each data declaration's constructors in tag order, by
    /// [`DataIndex`].
    constructors: Vec<Vec<String>>,
    /// The codata declarations' signatures, by [`CodataIndex`].
    codata: Vec<Arc<CodataSignature>>,
    /// The modules, in pre-order: a module before every module nested in it.
    structures: Vec<LoweredStructure<'source>>,
    /// The attribute side table, keyed by declaration content identity.
    attributes: AttributeTable,
    /// Each documented declaration form's documentation, keyed by its unit
    /// key.
    documentation: BTreeMap<UnitKey, Documentation<'source>>,
    /// Each documented source's own documentation, its `//!` runs, keyed by
    /// the source.
    sources: BTreeMap<SourceIndex, Documentation<'source>>,
    /// Every exit the lowering inferred where a path through a body ends in a
    /// form that is no exit, in source order.
    inferred_exits: Vec<InferredExit>,
    /// Every written `return` the lowering would infer were it left out, in
    /// source order.
    elidable_exits: Vec<ElidableExit>,
    /// Every `run` statement whose binder the next step reads once, first, in
    /// source order.
    linear_runs: Vec<LinearRun>,
    /// What the lowering recorded of each syntax node it held a computation
    /// nested at.
    nested: BTreeMap<NodeIndex, NestedSite>,
    /// The binders in scope at each offset the lowering read under one.
    in_scope: InScope,
    /// Each written name the lowering resolved, with what it names, ascending
    /// by span.
    resolutions: Vec<(ByteSpan, Resolution)>,
    /// The bytes of each import a name lookup was answered through,
    /// ascending.
    reached_imports: Vec<ByteSpan>,
    /// Every minted core node's origin, and the declarations' own.
    origins: OriginTable,
    /// The imports, in source order, with their aliases bound.
    imports: ModuleImports<'source>,
    /// The outermost scope, with every declared name declared in it.
    recognition: Recognition,
    /// The rules each operation's definition was written as, over module
    /// positions, by its position.
    operation_rules: BTreeMap<ConstantIndex, gandr_kernel_term::OperationRules>,
    /// The bound of each stage binder of each function quantified over
    /// stages, in written order, by the function's declaration key.
    stage_bounds: BTreeMap<UnitKey, Vec<gandr_kernel_term::StageBound>>,
    /// Each stage a call supplies its callee's binder at, `f[i = s]`, by the
    /// declaration whose body makes the call.
    supplies: BTreeMap<ConstantIndex, Vec<gandr_core_term::staged::Supply>>,
}

impl<'source> LoweredModule<'source>
{
    /// The module holding these parts, for the pass that assembles one, with
    /// an empty description report and no cell stores.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn new(
        declarations: Vec<LoweredDeclaration<'source>>,
        data: Vec<Arc<DataSignature>>,
        structures: Vec<LoweredStructure<'source>>,
        attributes: AttributeTable,
        origins: OriginTable,
        imports: ModuleImports<'source>,
        recognition: Recognition,
    ) -> Self
    {
        Self {
            descriptions: crate::description::DescriptionReport::default(),
            cells: crate::desc_cells::CellReport::default(),
            declarations,
            data,
            constructors: Vec::new(),
            codata: Vec::new(),
            structures,
            attributes,
            documentation: BTreeMap::new(),
            sources: BTreeMap::new(),
            inferred_exits: Vec::new(),
            elidable_exits: Vec::new(),
            linear_runs: Vec::new(),
            nested: BTreeMap::new(),
            in_scope: InScope::default(),
            resolutions: Vec::new(),
            reached_imports: Vec::new(),
            origins,
            imports,
            recognition,
            operation_rules: BTreeMap::new(),
            stage_bounds: BTreeMap::new(),
            supplies: BTreeMap::new(),
        }
    }

    /// This module, carrying the description route's report and cell stores.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn with_descriptions(
        mut self,
        descriptions: crate::description::DescriptionReport,
        cells: crate::desc_cells::CellReport,
    ) -> Self
    {
        self.descriptions = descriptions;
        self.cells = cells;
        self
    }

    /// This module, carrying `documentation`, keyed by declaration content
    /// identity, and `sources`, each source's own, keyed by the source.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn with_documentation(
        mut self,
        documentation: BTreeMap<UnitKey, Documentation<'source>>,
        sources: BTreeMap<SourceIndex, Documentation<'source>>,
    ) -> Self
    {
        self.documentation = documentation;
        self.sources = sources;
        self
    }

    /// This module, carrying `operation_rules`, each operation's rules by its
    /// position.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn with_operation_rules(
        mut self,
        operation_rules: BTreeMap<ConstantIndex, gandr_kernel_term::OperationRules>,
    ) -> Self
    {
        self.operation_rules = operation_rules;
        self
    }

    /// This module, carrying `stage_bounds`, each quantified function's
    /// binder bounds by its declaration key.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn with_stage_bounds(
        mut self,
        stage_bounds: BTreeMap<UnitKey, Vec<gandr_kernel_term::StageBound>>,
    ) -> Self
    {
        self.stage_bounds = stage_bounds;
        self
    }

    /// This module, carrying `supplies`, the stages each declaration's calls
    /// supply, by the declaration.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn with_supplies(
        mut self,
        supplies: BTreeMap<ConstantIndex, Vec<gandr_core_term::staged::Supply>>,
    ) -> Self
    {
        self.supplies = supplies;
        self
    }

    /// This module, carrying `inferred_exits`, in source order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn with_inferred_exits(
        mut self,
        inferred_exits: Vec<InferredExit>,
    ) -> Self
    {
        self.inferred_exits = inferred_exits;
        self
    }

    /// This module, carrying `elidable_exits`, in source order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn with_elidable_exits(
        mut self,
        elidable_exits: Vec<ElidableExit>,
    ) -> Self
    {
        self.elidable_exits = elidable_exits;
        self
    }

    /// This module, carrying `linear_runs`, in source order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn with_linear_runs(
        mut self,
        linear_runs: Vec<LinearRun>,
    ) -> Self
    {
        self.linear_runs = linear_runs;
        self
    }

    /// This module, carrying the names of each data declaration's
    /// constructors in tag order, by [`DataIndex`].
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn with_constructors(
        mut self,
        constructors: Vec<Vec<String>>,
    ) -> Self
    {
        self.constructors = constructors;
        self
    }

    /// This module, carrying the codata declarations' signatures, by
    /// [`CodataIndex`].
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn with_codata(
        mut self,
        codata: Vec<Arc<CodataSignature>>,
    ) -> Self
    {
        self.codata = codata;
        self
    }

    /// Every exit the lowering inferred where a path through a body ends in a
    /// form that is no exit, in source order: the keyword each tail left out,
    /// at the tail's own bytes.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn inferred_exits(&self) -> &[InferredExit]
    {
        &self.inferred_exits
    }

    /// Every written `return` the lowering would infer were it left out, in
    /// source order: a tail's `return` of a value, under no `explicit_exits`
    /// attribute, which the sugared form writes as the value alone.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn elidable_exits(&self) -> &[ElidableExit]
    {
        &self.elidable_exits
    }

    /// Every `run x <- c ;` statement whose binder the next step reads once,
    /// first, in source order: `c` and the read, which the sugared form
    /// writes as `c` at the read.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn linear_runs(&self) -> &[LinearRun]
    {
        &self.linear_runs
    }

    /// This module, carrying what the lowering recorded of each syntax node
    /// it held a computation nested at.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn with_nested_sites(
        mut self,
        nested: BTreeMap<NodeIndex, NestedSite>,
    ) -> Self
    {
        self.nested = nested;
        self
    }

    /// This module, carrying the binders in scope at each offset the lowering
    /// read under one.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn with_in_scope(
        mut self,
        in_scope: InScope,
    ) -> Self
    {
        self.in_scope = in_scope;
        self
    }

    /// The binders in scope at each offset the lowering read under one, the
    /// declarations it refused included.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn in_scope(&self) -> &InScope
    {
        &self.in_scope
    }

    /// The binders in scope at each offset the lowering read under one, the
    /// module given up for them.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn into_in_scope(self) -> InScope
    {
        self.in_scope
    }

    /// The binders in scope, the resolutions and the nested sites, the module
    /// given up for them.
    ///
    /// # Specification
    /// trivial.
    pub(crate) fn into_scope_tables(
        self
    ) -> (
        InScope,
        Vec<(ByteSpan, Resolution)>,
        BTreeMap<NodeIndex, NestedSite>,
    )
    {
        (self.in_scope, self.resolutions, self.nested)
    }

    /// This module, carrying each written name the lowering resolved, with
    /// what it names.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn with_resolutions(
        mut self,
        resolutions: Vec<(ByteSpan, Resolution)>,
    ) -> Self
    {
        self.resolutions = resolutions;
        self
    }

    /// Each written name the lowering resolved, with what it names, ascending
    /// by span; a name in a declaration the lowering refused included, when
    /// it was resolved before the refusal.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn resolutions(&self) -> &[(ByteSpan, Resolution)]
    {
        &self.resolutions
    }

    /// This module, carrying the bytes of each import a name lookup was
    /// answered through.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn with_reached_imports(
        mut self,
        reached: Vec<ByteSpan>,
    ) -> Self
    {
        self.reached_imports = reached;
        self
    }

    /// The bytes of each import a name lookup was answered through,
    /// ascending: an unqualified import that declared a name read, an aliased
    /// one whose member was read, and one reaching a source that holds the
    /// theory code where `Theory` is read. A name after a refusal in its
    /// declaration is never looked up.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the spans ascend without repeats, each the bytes of an import
    ///   of [`Self::imports`].
    /// - provides: what an importer's unused imports are read against.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an import a value, a type, a constructor, a module
    ///   member and an aliased member are each read through is reached; an
    ///   import nothing is read through is not.
    /// - witness: `tests::namespace::each_import_a_name_is_read_through_is_reached`
    #[spec(ensures: |ret| ret.windows(2).all(|pair| matches!(*pair, [first, second] if first < second)))]
    #[inline]
    #[must_use]
    pub fn reached_imports(&self) -> &[ByteSpan]
    {
        &self.reached_imports
    }

    /// The runs the checker inferred, of the nested values `ran` it decided
    /// to run, each with its returner's purity: located at the computation's
    /// own bytes, with the site the lowering recorded there, in source order.
    ///
    /// # Specification
    /// - requires: `ran` names values of this module's bodies, as the checker
    ///   judged them, with the purity it decided each at.
    /// - ensures: one record per distinct site among the values of `ran` the
    ///   lowering inserted as nested computations, at that span, with that
    ///   purity and the site recorded for its syntax node, an unrecorded one
    ///   asking nothing and spelled bare; a written `run` and an unrecorded
    ///   value give none; sorted, so a copy a rewrite made of one nested node
    ///   is listed once.
    /// - provides: the join of the checker's decisions with the lowering's
    ///   record, which a face shows and the `explicit-runs` lint reports.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — nested calls under a module's attribute, a
    ///   declaration's and none, run by the checker, asserted as the exact
    ///   list.
    /// - witness: `lower::runs::tests::an_explicit_runs_attribute_asks_within_its_form`
    #[inline]
    #[must_use]
    #[spec(ensures: |ret| ret.is_sorted() && ret.windows(2_usize).all(|pair| pair.first() != pair.get(1_usize)))]
    pub fn inferred_runs<Ran>(
        &self,
        ran: Ran,
    ) -> Vec<InferredRun>
    where
        Ran: IntoIterator<Item = (ValueId, Purity)>,
    {
        let mut found: Vec<InferredRun> = ran
            .into_iter()
            .filter_map(|(at, purity)| match self.origins.value(at) {
                Maybe::Present(origin)
                    if origin.provenance() == Provenance::Inserted(Insertion::Nested) =>
                {
                    Some(InferredRun {
                        span: origin.span(),
                        purity,
                        site: self.nested.get(&origin.node()).copied().unwrap_or_default(),
                    })
                },
                Maybe::Present(_) | Maybe::Absent(_) => None,
            })
            .collect();
        found.sort_unstable();
        found.dedup();

        found
    }

    /// The signature of the data declaration whose outcome holds `index`.
    ///
    /// # Specification
    /// - requires: `index` comes from one of this module's outcomes.
    /// - ensures: the signature at that position, which the declaration's
    ///   checker input carries unchanged; another module's index answers
    ///   whatever this module holds there, or nothing past its end.
    /// - fails: [`data_signature::Absent::Unlisted`] past the end.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — two declarations answer their own signatures and an
    ///   index past the list answers nothing.
    /// - witness: `lower::native::tests::a_data_declaration_lowers_to_its_signature`
    #[spec(ensures: |ret| match ret {
        | Maybe::Present(signature) => self.data.get(index.0).is_some_and(|held| Arc::ptr_eq(held, signature)),
        | Maybe::Absent(_) => index.0 >= self.data.len(),
    })]
    #[inline]
    pub fn data(
        &self,
        index: DataIndex,
    ) -> Maybe<&Arc<DataSignature>, data_signature::Absent>
    {
        self.data.get(index.0).map_or(
            Maybe::Absent(data_signature::Absent::Unlisted),
            Maybe::Present,
        )
    }

    /// The signature of the codata declaration whose outcome holds `index`.
    ///
    /// # Specification
    /// - requires: `index` comes from one of this module's outcomes.
    /// - ensures: the signature at that position, which the declaration's
    ///   checker input carries unchanged.
    /// - fails: [`codata_signature::Absent::Unlisted`] past the end.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a codata declaration answers its own signature.
    /// - witness: `description::tests::a_codata_declaration_lowers_to_its_signature`
    #[spec(ensures: |ret| match ret {
        | Maybe::Present(signature) => self.codata.get(index.0).is_some_and(|held| Arc::ptr_eq(held, signature)),
        | Maybe::Absent(_) => index.0 >= self.codata.len(),
    })]
    #[inline]
    pub fn codata(
        &self,
        index: CodataIndex,
    ) -> Maybe<&Arc<CodataSignature>, codata_signature::Absent>
    {
        self.codata.get(index.0).map_or(
            Maybe::Absent(codata_signature::Absent::Unlisted),
            Maybe::Present,
        )
    }

    /// The names of the constructors of the data declaration at `index`, in
    /// tag order; none past the list.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn constructors(
        &self,
        index: DataIndex,
    ) -> &[String]
    {
        self.constructors.get(index.0).map_or(&[], Vec::as_slice)
    }

    /// The descriptions consumed by native type and higher-cell interpretation.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn descriptions(&self) -> &crate::description::DescriptionReport
    {
        &self.descriptions
    }

    /// Every `theory` block the module declares, in declaration order: its
    /// description and the presentation its models' signature derives from.
    ///
    /// # Specification
    /// - ensures: one handle per described declaration presenting a model
    ///   signature, in the report's order; a family and a top-level operation
    ///   present none.
    /// - executable: none — the handles are read lazily off the report.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a module declaring `CatShape` beside a family hands
    ///   back the theory alone.
    /// - witness: `tests::modules::models::a_lowered_theory_exposes_its_description_and_its_model`
    #[inline]
    pub fn theories(&self) -> impl Iterator<Item = crate::model::LoweredTheory<'_>>
    {
        self.descriptions
            .declarations
            .iter()
            .filter_map(|declaration| match declaration.presentation {
                Maybe::Present(ref presentation) => Some(crate::model::LoweredTheory {
                    named: declaration.named,
                    description: &declaration.description,
                    presentation,
                }),
                Maybe::Absent(_) => None,
            })
    }

    /// The cell stores reached through the production description route.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn cells(&self) -> &crate::desc_cells::CellReport
    {
        &self.cells
    }

    /// The normal form `call` reaches under the rules of the described
    /// declaration whose bytes hold `declaration`'s: the engine's reading of a
    /// call into a family or a `theory` block, asked of the block or of one of
    /// its operations.
    ///
    /// # Specification
    /// - requires: `declaration` is one of this module's declarations.
    /// - ensures: `coincide::normal_form` over the description and the cells of
    ///   the described declaration whose interval contains `declaration`'s.
    /// - fails: [`crate::coincide::NormalFormFault::Undescribed`] when no
    ///   described declaration contains that interval; otherwise as the call's
    ///   normal form fails.
    /// - panics: none.
    ///
    /// # Errors
    /// As the failure clause states.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a family's declaration and its operation read one
    ///   call to one normal form, and a declaration outside every described one
    ///   is undescribed.
    /// - witness: `coincide::tests::a_call_reads_its_normal_form_or_says_why_not`
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            spec_clause_traversal,
            reason = "parity: the body walks the cells once for the containing block; the check walks them once more"
        )
    )]
    #[spec(ensures: |ret| !matches!(ret, Err(crate::coincide::NormalFormFault::Undescribed))
        || !self.cells.declarations.iter().any(|cells| cells.at.span.start() <= declaration.span().start()
            && declaration.span().end() <= cells.at.span.end()))]
    #[inline]
    pub fn normal_form(
        &self,
        declaration: &LoweredDeclaration<'source>,
        call: crate::coincide::CallText<'_>,
    ) -> Result<crate::coincide::NormalForm, crate::coincide::NormalFormFault>
    {
        let span = declaration.span();
        let holds = |at: ByteSpan| at.start() <= span.start() && span.end() <= at.end();
        let described = self
            .descriptions
            .declarations
            .iter()
            .find(|described| holds(described.at.span));
        let cells = self
            .cells
            .declarations
            .iter()
            .find(|cells| holds(cells.at.span));
        match (described, cells) {
            (Some(described), Some(cells)) => {
                crate::coincide::normal_form(&described.description, cells, call)
            },
            _ => Err(crate::coincide::NormalFormFault::Undescribed),
        }
    }

    /// The modules, in pre-order: a module before every module nested in it.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn structures(&self) -> &[LoweredStructure<'source>]
    {
        &self.structures
    }

    /// The structured name of `declaration`: the path of the module it is
    /// declared in, then its own name.
    ///
    /// # Specification
    /// - requires: `declaration` is one of this module's declarations.
    /// - ensures: one segment for a top-level declaration, and the enclosing
    ///   module's path followed by the name for a member, so a member nested at
    ///   depth `n` has `n + 1` segments.
    /// - provides: the name a declaration exports under.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — nested and top-level declarations preserve the
    ///   ordered container segments before their own name.
    /// - witness: `tests::modules::modules_lower_to_named_member_declarations`
    /// - witness: `module::tests::structured_export_omits_invalid_segments_and_keeps_the_last_declared_name`
    #[spec(
        ensures: |ret| {
            let prefix = match declaration.container() {
                | Container::TopLevel(_) => &[][..],
                | Container::Module(index) => self
                    .structures
                    .get(index.0)
                    .map_or(&[][..], |module| module.path.as_slice()),
            };
            ret.iter().copied().eq(prefix
                .iter()
                .copied()
                .chain(core::iter::once(declaration.name())))
        },
    )]
    #[inline]
    #[must_use]
    pub fn path_of(
        &self,
        declaration: &LoweredDeclaration<'source>,
    ) -> Vec<SurfaceName<'source>>
    {
        let mut path = match declaration.container() {
            Container::TopLevel(_) => Vec::new(),
            Container::Module(structure) => self
                .structures
                .get(structure.0)
                .map_or_else(Vec::new, |module| module.path.clone()),
        };
        path.push(declaration.name());

        path
    }

    /// The structured name of every declared name, by admission position:
    /// the names a checker's export writes into each declaration that crossed.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: each declared or sealed abstract position with separator-free
    ///   path segments has its structured name. Witnesses, held slots and
    ///   invalid paths are omitted. If admitted metadata repeats a position,
    ///   the last eligible declaration wins; an invalid later path does not
    ///   erase an earlier one.
    /// - provides: the name each flattened member is exported under, while
    ///   every reference still reads the admission position.
    /// - fails: never; a path containing the segment separator is omitted.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — real nested declarations export their exact paths.
    ///   Composed metadata separates repeated positions, held declarations,
    ///   invalid leaf segments and invalid container segments. The predicate
    ///   walks the declarations once from the last, so the first eligible one
    ///   met at a position is the one that wins, and compares the count of
    ///   positions met with the names returned.
    /// - witness: `tests::modules::modules_lower_to_named_member_declarations`
    /// - witness: `tests::modules::opaque_ascription_seals`
    /// - witness: `module::tests::structured_export_omits_invalid_segments_and_keeps_the_last_declared_name`
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            spec_clause_traversal,
            reason = "parity: the body walks every declaration and files each eligible one's name in an ordered map; the check walks them once in reverse, filing each position in an ordered set"
        )
    )]
    #[spec(
        ensures: |ret| {
            let prefix = |declaration: &LoweredDeclaration<'source>| match declaration.container() {
                | Container::TopLevel(_) => &[][..],
                | Container::Module(index) => self
                    .structures
                    .get(index.0)
                    .map_or(&[][..], |module| module.path.as_slice()),
            };
            let eligible = |declaration: &LoweredDeclaration<'source>| {
                matches!(declaration.role(), Role::Declared | Role::Abstract)
                    && !declaration.name().as_ref().contains(NameSegment::SEPARATOR)
                    && prefix(declaration)
                        .iter()
                        .all(|segment| !segment.as_ref().contains(NameSegment::SEPARATOR))
            };
            let mut named = alloc::collections::BTreeSet::new();
            self.declarations
                .iter()
                .rev()
                .filter(|declaration| eligible(declaration))
                .all(|declaration| {
                    !named.insert(declaration.constant())
                        || ret.get(&declaration.constant()).is_some_and(|name| {
                            name.segments()
                                .iter()
                                .map(AsRef::as_ref)
                                .eq(prefix(declaration)
                                    .iter()
                                    .map(AsRef::as_ref)
                                    .chain(core::iter::once(declaration.name().as_ref())))
                        })
                })
                && named.len() == ret.len()
        },
    )]
    #[inline]
    #[must_use]
    pub fn structured_names(&self) -> BTreeMap<ConstantIndex, StructuredName>
    {
        let mut names = BTreeMap::new();
        for declaration in &self.declarations {
            if !matches!(declaration.role(), Role::Declared | Role::Abstract) {
                continue;
            }
            let segments: Option<Vec<NameSegment>> = self
                .path_of(declaration)
                .into_iter()
                .map(|segment| NameSegment::from_text(String::from(segment.as_ref())))
                .collect();
            if let Some(segments) = segments {
                let _replaced =
                    names.insert(declaration.constant(), StructuredName::from(segments));
            }
        }

        names
    }

    /// The imports, in source order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn imports(&self) -> &[ImportDeclaration<'source>]
    {
        self.imports.declarations()
    }

    /// The scope `source`'s import aliases are bound in: each alias resolves
    /// to its import's position, tagged with the import's bytes, and the
    /// export is empty.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn import_scope(
        &self,
        source: SourceIndex,
    ) -> Maybe<&Scope<ImportIndex, ByteSpan>, crate::import::alias_scope::Absent>
    {
        self.imports.scope(source)
    }

    /// The outermost scope after the module: the seed tables it was lowered
    /// against, every declared name declared over them, and the builtins the
    /// source shadowed.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn recognition(&self) -> &Recognition
    {
        &self.recognition
    }

    /// The declarations, in admission order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn declarations(&self) -> &[LoweredDeclaration<'source>]
    {
        &self.declarations
    }

    /// The attribute side table.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn attributes(&self) -> &AttributeTable
    {
        &self.attributes
    }

    /// The laws `declaration`'s `respects` attribute names, in the order the
    /// rules they answer are written: what the checker's declaration carries
    /// as the evidence a fold rests on.
    ///
    /// # Specification
    /// - requires: `declaration` is one of this module's declarations.
    /// - ensures: the laws filed under the declaration's definition form, else
    ///   under its signature form; the empty slice for a declaration no
    ///   `respects` attribute decorates.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the answer is the receiver's attribute table read
    ///   at the declaration's keys, which a clause may not compare against.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a definition naming two laws, a signature naming one
    ///   and an undecorated declaration separate the three answers.
    /// - witness: `lower::tests::a_respects_attribute_names_its_laws_through_either_form`
    #[inline]
    #[must_use]
    pub fn laws(
        &self,
        declaration: &LoweredDeclaration<'source>,
    ) -> &[ConstantIndex]
    {
        [declaration.definition(), declaration.signature()]
            .into_iter()
            .find_map(|key| match key {
                Maybe::Present(key) => {
                    Some(self.attributes.laws(key)).filter(|laws| !laws.is_empty())
                },
                Maybe::Absent(_) => None,
            })
            .unwrap_or_default()
    }

    /// The bound of each stage binder `declaration`'s telescope writes, in
    /// written order: what the checker's declaration carries as the stages
    /// its signature is quantified over.
    ///
    /// # Specification
    /// - requires: `declaration` is one of this module's declarations.
    /// - ensures: the bounds filed under the declaration's definition form,
    ///   else under its signature form; the empty slice for a declaration no
    ///   telescope quantifies.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the module's own map, read at the declaration's
    ///   keys.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a quantified function and a plain one separate the
    ///   two answers.
    /// - witness: `lower::staged::tests::a_telescope_files_its_bounds_and_marks_its_stages`
    #[inline]
    #[must_use]
    pub fn stages(
        &self,
        declaration: &LoweredDeclaration<'source>,
    ) -> &[gandr_kernel_term::StageBound]
    {
        [declaration.definition(), declaration.signature()]
            .into_iter()
            .find_map(|key| match key {
                Maybe::Present(key) => self.stage_bounds.get(&key).map(Vec::as_slice),
                Maybe::Absent(_) => None,
            })
            .unwrap_or_default()
    }

    /// The stages `declaration`'s calls supply their callees' binders at,
    /// `f[i = s]`: what the checker's declaration carries for its judgement
    /// to hold each call to, and the kernel never reads.
    ///
    /// # Specification
    /// - requires: `declaration` is one of this module's declarations.
    /// - ensures: the supplies filed under the declaration's constant; the
    ///   empty slice for a declaration whose calls supply none.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the module's own map, read at the declaration's
    ///   constant.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a call writing a supply files it at its head, and a
    ///   call writing none files nothing.
    /// - witness: `lower::staged::tests::a_supplied_stage_crosses_at_the_call_s_head_1227`
    #[inline]
    #[must_use]
    pub fn supplies(
        &self,
        declaration: &LoweredDeclaration<'source>,
    ) -> &[gandr_core_term::staged::Supply]
    {
        self.supplies
            .get(&declaration.constant())
            .map(Vec::as_slice)
            .unwrap_or_default()
    }

    /// The rules `declaration`'s operation was written as, over module
    /// positions: what the checker's declaration carries for the kernel to
    /// decide they converge.
    ///
    /// # Specification
    /// - requires: `declaration` is one of this module's declarations.
    /// - ensures: the rules of the operation planned at the declaration's
    ///   position; none for a declaration no operation lowered to.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the module's own map, read once.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — every routed operation's rules cross to the kernel,
    ///   which admits the corpus's operations and refuses a forged pair.
    /// - witness: `operation::tests::an_operations_rules_read_in_pre_order_over_module_positions`
    #[inline]
    #[must_use]
    pub fn operation_rules(
        &self,
        declaration: &LoweredDeclaration<'source>,
    ) -> gandr_kernel_term::OperationRules
    {
        self.operation_rules
            .get(&declaration.constant())
            .cloned()
            .unwrap_or_default()
    }

    /// The worlds `declaration`'s `entry` attribute names, its home first and
    /// then the world of each capability it holds: what the checker's
    /// declaration carries as the world it is judged at.
    ///
    /// # Specification
    /// - requires: `declaration` is one of this module's declarations.
    /// - ensures: the worlds filed under the declaration's definition form,
    ///   else under its signature form; the empty slice for a declaration no
    ///   `entry` attribute decorates.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the answer is the receiver's attribute table read
    ///   at the declaration's keys, which a clause may not compare against.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a decorated declaration and an undecorated one
    ///   separate the two answers.
    /// - witness: `lower::world::tests::an_entry_names_its_home_then_its_capabilities`
    #[inline]
    #[must_use]
    pub fn worlds(
        &self,
        declaration: &LoweredDeclaration<'source>,
    ) -> &[ConstantIndex]
    {
        [declaration.definition(), declaration.signature()]
            .into_iter()
            .find_map(|key| match key {
                Maybe::Present(key) => {
                    Some(self.attributes.worlds(key)).filter(|worlds| !worlds.is_empty())
                },
                Maybe::Absent(_) => None,
            })
            .unwrap_or_default()
    }

    /// The documentation of the declaration form whose key is `key`.
    ///
    /// # Specification
    /// - requires: nothing — any key is admissible input.
    /// - ensures: the documentation filed under `key`, or the undocumented
    ///   absence when nothing was. A key excludes documentation, so it is the
    ///   same whichever spelling, if any, the documentation took.
    /// - provides: the read face hover and rendering consumers read.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a documented and an undocumented declaration are
    ///   separated by presence and the exact text.
    /// - witness: `lower::tests::documentation_is_filed_under_the_declaration_key`
    #[spec(ensures: |ret| match ret {
        | Maybe::Present(found) => self.documentation.get(&key) == Some(found),
        | Maybe::Absent(_) => !self.documentation.contains_key(&key),
    })]
    #[inline]
    pub fn documentation(
        &self,
        key: UnitKey,
    ) -> Maybe<&Documentation<'source>, crate::doc::documentation::Absent>
    {
        self.documentation.get(&key).map_or(
            Maybe::Absent(crate::doc::documentation::Absent::Undocumented),
            Maybe::Present,
        )
    }

    /// Every declaration form's documentation, by the form's unit key.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn documentations(&self) -> &BTreeMap<UnitKey, Documentation<'source>>
    {
        &self.documentation
    }

    /// The documentation the source at `source` writes of itself: its `//!`
    /// runs standing at its root.
    ///
    /// # Specification
    /// - requires: nothing — any source is admissible input.
    /// - ensures: the documentation filed under `source`, or the undocumented
    ///   absence when nothing was.
    /// - provides: the read face an import's hover reads its file through.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — two sources' documentation and an undocumented source
    ///   are separated by presence and the exact text.
    /// - witness: `lower::tests::a_source_s_documentation_is_filed_under_the_source_1365`
    #[spec(ensures: |ret| match ret {
        | Maybe::Present(found) => self.sources.get(&source) == Some(found),
        | Maybe::Absent(_) => !self.sources.contains_key(&source),
    })]
    #[inline]
    pub fn source_documentation(
        &self,
        source: SourceIndex,
    ) -> Maybe<&Documentation<'source>, crate::doc::documentation::Absent>
    {
        self.sources.get(&source).map_or(
            Maybe::Absent(crate::doc::documentation::Absent::Undocumented),
            Maybe::Present,
        )
    }

    /// Every source's own documentation, by the source.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn source_documentations(&self) -> &BTreeMap<SourceIndex, Documentation<'source>>
    {
        &self.sources
    }

    /// Every minted core node's origin, and the declarations' own.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn origins(&self) -> &OriginTable
    {
        &self.origins
    }

    /// Every minted core node's origin, for a judgement that records where
    /// the nodes it minted stand.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn origins_mut(&mut self) -> &mut OriginTable
    {
        &mut self.origins
    }

    /// The origin table, the module given up: what a consumer keeps once the
    /// declarations and attributes have been read.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn into_origins(self) -> OriginTable
    {
        self.origins
    }

    /// How many names the module declares.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn declaration_count(&self) -> DeclarationCount
    {
        DeclarationCount(self.declarations.len())
    }
}

#[cfg(test)]
mod tests
{
    use alloc::vec::Vec;

    use gandr_core_term::TrackingIssue;
    use gandr_kernel_term::ConstantIndex;
    use gandr_surface_grammar::NamedKind;
    use gandr_surface_syntax::ByteOffset;
    use gandr_surface_syntax::NodeIndex;
    use gandr_surface_syntax::NodeLabel;
    use gandr_surface_syntax::SourceText;
    use quenchant_shape::shape::Maybe;

    use super::Address;
    use super::Container;
    use super::DeclarationSlot;
    use super::Half;
    use super::Role;
    use super::SlotIndex;
    use super::collect;
    use super::declaration_half;
    use super::slot_refusal;
    use crate::classify::FailureClass;
    use crate::error::FormFault;
    use crate::error::FragmentBoundary;
    use crate::error::FragmentSort;
    use crate::error::LoweringRefusal;
    use crate::fixture::Handmade;
    use crate::fixture::Rule;
    use crate::fixture::Spelled;
    use crate::fixture::grammar;
    use crate::fixture::parsed;
    use crate::fixture::repaired;
    use crate::fixture::span;
    use crate::form::FormName;
    use crate::form::Placed;
    use crate::import::ImportUri;
    use crate::lower::Fuel;
    use crate::lower::LoweringBudget;
    use crate::resolve::SurfaceName;
    use crate::unit::SourceIndex;
    use crate::unit::Unit;

    /// A tank generous enough for a fixture-sized module.
    ///
    /// # Specification
    /// trivial.
    fn tank() -> Fuel
    {
        Fuel::new(LoweringBudget::DEFAULT)
    }

    #[test]
    fn signature_holes_distinguish_missing_single_and_extra_operands()
    {
        let gap = span(ByteOffset::from(2_usize), ByteOffset::from(2_usize));
        let first = Placed {
            node: NodeIndex::from(1_usize),
            span: span(ByteOffset::from(3_usize), ByteOffset::from(5_usize)),
        };
        let extra = Placed {
            node: NodeIndex::from(2_usize),
            span: span(ByteOffset::from(7_usize), ByteOffset::from(8_usize)),
        };
        assert_eq!(
            super::one_in(FormName::MODULE, crate::form::Run::Empty(gap)),
            Err(LoweringRefusal::MalformedForm {
                span: gap,
                form: FormName::MODULE,
                fault: FormFault::MissingOperand
            })
        );
        assert_eq!(
            super::one_in(FormName::MODULE, crate::form::Run::One(first)),
            Ok(first)
        );
        assert_eq!(
            super::one_in(FormName::MODULE, crate::form::Run::Several {
                first,
                extra,
                count: crate::resolve::OperandCount::from(2_usize)
            }),
            Err(LoweringRefusal::MalformedForm {
                span: extra.span,
                form: FormName::MODULE,
                fault: FormFault::ExtraOperand
            })
        );
    }

    #[test]
    fn an_address_names_a_scheme_or_a_path()
    {
        let of = |uri: &str| Address::of(&ImportUri::from(alloc::string::String::from(uri)));
        assert_eq!(
            of("file:///far.gandr"),
            Address::Scheme,
            "a URL names its scheme"
        );
        assert_eq!(of("./circle-base.gandr"), Address::Path, "a relative path");
        assert_eq!(
            of("./a:b.gandr"),
            Address::Path,
            "a colon after a slash opens no scheme"
        );
        assert_eq!(
            of("1file:far.gandr"),
            Address::Path,
            "a scheme opens with a letter"
        );
        assert_eq!(
            of("git+ssh:repo"),
            Address::Scheme,
            "a scheme continues with letters, digits, `+`, `-` and `.`"
        );
    }

    #[test]
    fn structured_export_omits_invalid_segments_and_keeps_the_last_declared_name()
    {
        let pbg = grammar();
        let tree = parsed(
            &pbg,
            SourceText::from(
                "module M { def first = 1 ; def last = 2 ; def dotted = 3 ; def hidden = 4 ; }",
            ),
        );
        let mut arena = gandr_core_term::CoreArena::new();
        let mut lowered = crate::lower::lower_module(
            &pbg,
            &tree,
            &mut arena,
            LoweringBudget::DEFAULT,
            crate::namespace::Recognition::default(),
        )
        .unwrap();
        let [ref mut first, ref mut last, ref mut dotted, ref mut hidden] =
            *lowered.declarations.as_mut_slice()
        else {
            panic!("four source definitions have four declarations");
        };
        let constant = first.constant();
        last.parts.constant = constant;
        dotted.parts.name = SurfaceName::from("bad.name");
        dotted.parts.constant = constant;
        hidden.parts.role = Role::Held;
        let names = lowered.structured_names();
        assert_eq!(names.keys().copied().collect::<Vec<_>>(), [constant]);
        let Some(exported) = names.get(&constant)
        else {
            panic!("the declared position has an exported name");
        };
        assert_eq!(
            exported
                .segments()
                .iter()
                .map(AsRef::as_ref)
                .collect::<Vec<&str>>(),
            ["M", "last"]
        );
        let module = lowered.structures.first_mut().unwrap();
        *module.path.first_mut().unwrap() = SurfaceName::from("bad.path");
        assert!(lowered.structured_names().is_empty());
    }

    #[test]
    fn a_mutual_block_collects_its_members_as_one_run()
    {
        let pbg = grammar();
        let tree = parsed(
            &pbg,
            SourceText::from(
                "def before = 1 ; rec { data N : Type { Z : N ; } def f = 1 ; } def after = 2 ;",
            ),
        );
        let collected = collect(&pbg, &tree, &Unit::single(), &mut tank()).unwrap();
        assert_eq!(collected.slots.len(), 4, "every member takes its own slot");
        let [block] = *collected.blocks.as_slice()
        else {
            panic!("one block");
        };
        assert_eq!(
            (block.first, block.end),
            (SlotIndex::from(1_usize), SlotIndex::from(3_usize)),
            "the members' run, and neither the declaration before nor after"
        );
    }

    #[test]
    fn ownership_routes_refusals_without_touching_other_slots()
    {
        let pbg = grammar();
        let tree = parsed(&pbg, SourceText::from("def x = 1 ; def y = 2 ;"));
        let mut collected = collect(&pbg, &tree, &Unit::single(), &mut tank()).unwrap();
        let [ref first, ref second] = *collected.slots.as_slice()
        else {
            panic!("two declared names have two slots");
        };
        let (first, second) = (first.introduced_by, second.introduced_by);
        let first_slot = SlotIndex::from(0_usize);
        let second_slot = SlotIndex::from(1_usize);
        let missing = NodeIndex::from(usize::MAX);
        let first_fault = LoweringRefusal::UnresolvedName {
            span: first.span,
            name: SurfaceName::from("first"),
        };
        let second_fault = LoweringRefusal::UnresolvedName {
            span: second.span,
            name: SurfaceName::from("second"),
        };
        assert_eq!(collected.owner_of(first.node), Maybe::Present(first_slot));
        assert_eq!(collected.owner_of(second.node), Maybe::Present(second_slot));
        assert!(!collected.refused(first.node).0);
        collected.offer(tree.root(), first_fault);
        collected.own(missing, first_slot);
        collected.offer(missing, first_fault);
        assert!(matches!(collected.owner_of(missing), Maybe::Absent(_)));
        assert!(!collected.refused(missing).0);
        assert!(!collected.refused(first.node).0 && !collected.refused(second.node).0);
        collected.offer(first.node, first_fault);
        collected.offer(first.node, second_fault);
        assert_eq!(
            collected.slots.first().unwrap().refusal,
            Maybe::Present((first.node, first_fault))
        );
        assert!(collected.refused(first.node).0 && !collected.refused(second.node).0);
        collected.offer(second.node, second_fault);
        assert_eq!(
            collected.slots.last().unwrap().refusal,
            Maybe::Present((second.node, second_fault))
        );
        collected.own(first.node, second_slot);
        collected.offer(first.node, first_fault);
        assert_eq!(
            collected.slots.last().unwrap().refusal,
            Maybe::Present((first.node, first_fault))
        );
        assert_eq!(
            collected.slots.first().unwrap().refusal,
            Maybe::Present((first.node, first_fault))
        );
    }
    #[test]
    fn a_signature_pairs_with_its_definition()
    {
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));
        let pbg = grammar();
        let tree = parsed(&pbg, SourceText::from("def x : Integer ; def x = 3 ;"));
        let collected = collect(&pbg, &tree, &Unit::single(), &mut tank()).unwrap();

        assert_eq!(
            collected.slots.len(),
            1_usize,
            "one name is one slot however many declarations carry it"
        );
        let slot = collected.slots.first().unwrap();
        assert_eq!(
            slot.name,
            SurfaceName::from("x"),
            "the slot carries the declared name"
        );
        assert_eq!(
            (
                slot.signature.map(|half| half.declaration.span),
                slot.definition.map(|half| half.declaration.span)
            ),
            (
                Maybe::Present(at(0_usize, 17_usize)),
                Maybe::Present(at(18_usize, 29_usize))
            ),
            "both halves are paired into the one slot"
        );
        assert_eq!(
            (
                slot.signature.map(|half| half.named.span),
                slot.definition.map(|half| half.named.span)
            ),
            (
                Maybe::Present(at(4_usize, 5_usize)),
                Maybe::Present(at(22_usize, 23_usize))
            ),
            "each half keeps the name tile it writes (#1034)"
        );
        assert_eq!(
            slot.refusal,
            Maybe::Absent(slot_refusal::Absent::Unrefused),
            "a well-formed pair refuses nothing"
        );
    }

    #[test]
    fn a_definition_pairs_with_a_later_signature()
    {
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));
        let pbg = grammar();
        let tree = parsed(
            &pbg,
            SourceText::from("def x = 3 ; def y = 4 ; def x : Integer ;"),
        );
        let collected = collect(&pbg, &tree, &Unit::single(), &mut tank()).unwrap();

        assert_eq!(
            collected.slots.len(),
            2_usize,
            "two names are two slots whatever order their halves sit in"
        );
        let slot = collected.slots.first().unwrap();
        assert_eq!(
            slot.name,
            SurfaceName::from("x"),
            "admission order is first-declaration order, not signature order"
        );
        assert_eq!(
            (
                slot.signature.map(|half| half.declaration.span),
                slot.definition.map(|half| half.declaration.span)
            ),
            (
                Maybe::Present(at(24_usize, 41_usize)),
                Maybe::Present(at(0_usize, 11_usize))
            ),
            "a signature separated from its definition still pairs with it"
        );
    }

    #[test]
    fn a_second_signature_is_refused()
    {
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));
        let pbg = grammar();
        let tree = parsed(&pbg, SourceText::from("def x : Integer ; def x : Unit ;"));
        let collected = collect(&pbg, &tree, &Unit::single(), &mut tank()).unwrap();
        let slot = collected.slots.first().unwrap();

        assert_eq!(
            slot.refusal.map(|(_at, refusal)| refusal),
            Maybe::Present(LoweringRefusal::DuplicateSignature {
                span: at(18_usize, 32_usize),
                name: SurfaceName::from("x"),
                first: at(0_usize, 17_usize),
            }),
            "the second signature is refused and names the first"
        );
        assert_eq!(
            slot.signature.map(|half| half.declaration.span),
            Maybe::Present(at(0_usize, 17_usize)),
            "the first signature survives the refusal"
        );
        assert_eq!(
            slot.refusal.map(|(_at, refusal)| refusal.classify()),
            Maybe::Present(FailureClass::MalformedSource),
            "a second signature is the author's mistake"
        );
    }

    #[test]
    fn a_second_definition_is_refused()
    {
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));
        let pbg = grammar();
        let tree = parsed(&pbg, SourceText::from("def x = 3 ; def x = 4 ;"));
        let collected = collect(&pbg, &tree, &Unit::single(), &mut tank()).unwrap();
        let slot = collected.slots.first().unwrap();

        assert_eq!(
            slot.refusal.map(|(_at, refusal)| refusal),
            Maybe::Present(LoweringRefusal::DuplicateDefinition {
                span: at(12_usize, 23_usize),
                name: SurfaceName::from("x"),
                first: at(0_usize, 11_usize),
            }),
            "the second definition is refused and names the first"
        );
        assert_eq!(
            slot.refusal.map(|(_at, refusal)| refusal.classify()),
            Maybe::Present(FailureClass::MalformedSource),
            "a second definition is the author's mistake"
        );
    }

    #[test]
    fn a_stray_module_child_refuses_the_module()
    {
        let pbg = grammar();
        let tree = parsed(&pbg, SourceText::from("3 ;"));

        assert_eq!(
            collect(&pbg, &tree, &Unit::single(), &mut tank()).unwrap_err(),
            LoweringRefusal::OutOfFragment {
                span: span(ByteOffset::from(0_usize), ByteOffset::from(1_usize)),
                form: FormName::from(NamedKind("number")),
                sort: FragmentSort::Declaration,
                boundary: FragmentBoundary::WrongSort,
            },
            "a source of nothing but a child that is not a declaration declares nothing, and is \
             refused whole"
        );
    }

    #[test]
    fn a_declaration_missing_its_body_is_refused()
    {
        let pbg = grammar();
        let tree = parsed(&pbg, SourceText::from("def x = ;"));
        let collected = collect(&pbg, &tree, &Unit::single(), &mut tank()).unwrap();
        let slot = collected.slots.first().unwrap();

        assert_eq!(
            slot.refusal.map(|(_at, refusal)| refusal),
            Maybe::Present(LoweringRefusal::MalformedForm {
                span: span(ByteOffset::from(7_usize), ByteOffset::from(7_usize)),
                form: FormName::DECLARATION,
                fault: FormFault::MissingOperand,
            }),
            "a definition is a name beside exactly one body, and an empty hole is no body"
        );
        assert_eq!(
            slot.definition,
            Maybe::Absent(declaration_half::Absent::Unwritten),
            "a refused declaration files no half"
        );
    }

    #[test]
    fn a_declaration_whose_name_is_not_a_name_refuses_the_module()
    {
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));
        let pbg = grammar();
        let mut made = Handmade::new(&pbg, SourceText::from("def 3 = 4 ;"));
        let keyword = made.tile(Rule("def_value"), Spelled("def"), at(0_usize, 3_usize));
        let mis_named = made.tile(
            Rule("number.expression"),
            Spelled("number"),
            at(4_usize, 5_usize),
        );
        let equals = made.tile(Rule("def_value"), Spelled("="), at(6_usize, 7_usize));
        let body = made.tile(
            Rule("number.expression"),
            Spelled("number"),
            at(8_usize, 9_usize),
        );
        let close = made.tile(Rule("def_value"), Spelled(";"), at(10_usize, 11_usize));
        let declaration = made.meld(Rule("def_value"), Spelled("def"), at(0_usize, 11_usize), &[
            keyword, mis_named, equals, body, close,
        ]);
        let tree = made.module(at(0_usize, 11_usize), &[declaration]);

        assert_eq!(
            collect(&pbg, &tree, &Unit::single(), &mut tank()).unwrap_err(),
            LoweringRefusal::OutOfFragment {
                span: at(4_usize, 5_usize),
                form: FormName::from(NamedKind("number")),
                sort: FragmentSort::Declaration,
                boundary: FragmentBoundary::WrongSort,
            },
            "a declaration's name is an identifier tile, and nothing can be filed without one"
        );
    }

    /// An attribute block decorates the declaration after it, so a trailing
    /// one decorates nothing: it refuses itself, and the declaration before
    /// it is collected as written. A source declaring nothing — a block and
    /// the repaired theory it decorates — is refused whole, at its first
    /// stray.
    #[test]
    fn a_trailing_attribute_block_refuses_itself()
    {
        let pbg = grammar();
        let tree = parsed(&pbg, SourceText::from("def x = 3 ; @[ checks ]"));
        let collected = collect(&pbg, &tree, &Unit::single(), &mut tank()).unwrap();
        let read: Vec<_> = collected
            .slots
            .iter()
            .map(|slot| {
                (
                    slot.name,
                    slot.role,
                    slot.refusal.map(|(_at, refusal)| refusal),
                )
            })
            .collect();

        assert_eq!(
            read,
            [
                (
                    SurfaceName::from("x"),
                    Role::Declared,
                    Maybe::Absent(slot_refusal::Absent::Unrefused)
                ),
                (
                    SurfaceName::from("@["),
                    Role::Held,
                    Maybe::Present(LoweringRefusal::OutOfFragment {
                        span: span(ByteOffset::from(12_usize), ByteOffset::from(23_usize)),
                        form: FormName::from(NamedKind("attribute_block")),
                        sort: FragmentSort::Declaration,
                        boundary: FragmentBoundary::WrongSort,
                    })
                ),
            ],
            "the declaration is kept and the block refused alone"
        );

        let tree = repaired(&pbg, SourceText::from("@[ checks ] theory Sta"));
        assert_eq!(
            collect(&pbg, &tree, &Unit::single(), &mut tank()).unwrap_err(),
            LoweringRefusal::OutOfFragment {
                span: span(ByteOffset::from(12_usize), ByteOffset::from(22_usize)),
                form: FormName::from(NamedKind("theory_declaration")),
                sort: FragmentSort::Declaration,
                boundary: FragmentBoundary::WrongSort,
            },
            "a theory the parser repaired declares nothing, and the source holding only it and \
             the block before it is refused whole, at the theory"
        );
    }

    /// A statement outside any block, an expression and a byte no label
    /// molds, standing among declarations, each refuse themselves alone as a
    /// held slot no name table enters; the declarations around them are
    /// collected as written (#1058).
    #[test]
    fn a_stray_root_child_refuses_itself_alone_1058()
    {
        let pbg = grammar();
        let text = "def a = 1 ;\n\u{a7}\nleta x = 1 ;\ndef b = a ;\n1 + 2 ;\n";
        let tree = repaired(&pbg, SourceText::from(text));
        let collected = collect(&pbg, &tree, &Unit::single(), &mut tank()).unwrap();
        let read: Vec<_> = collected
            .slots
            .iter()
            .map(|slot| {
                (
                    slot.name,
                    slot.role,
                    slot.refusal.map(|(_at, refusal)| refusal.classify()),
                )
            })
            .collect();

        assert_eq!(
            read,
            [
                (
                    SurfaceName::from("a"),
                    Role::Declared,
                    Maybe::Absent(slot_refusal::Absent::Unrefused)
                ),
                (
                    SurfaceName::from("b"),
                    Role::Declared,
                    Maybe::Absent(slot_refusal::Absent::Unrefused)
                ),
                (
                    SurfaceName::from("\u{a7}"),
                    Role::Held,
                    Maybe::Present(FailureClass::MalformedSource)
                ),
                (
                    SurfaceName::from("leta"),
                    Role::Held,
                    Maybe::Present(FailureClass::Unimplemented(TrackingIssue::RUN_TARGET))
                ),
                (
                    SurfaceName::from("1"),
                    Role::Held,
                    Maybe::Present(FailureClass::Unimplemented(TrackingIssue::RUN_TARGET))
                ),
            ],
            "both declarations are kept, and each stray refused on its own"
        );
        assert_eq!(collected.by_name.len(), 2, "a stray enters no name table");
    }

    #[test]
    fn an_attribute_block_decorates_the_declaration_after_it()
    {
        let pbg = grammar();
        let tree = parsed(&pbg, SourceText::from("@[ checks ] @[ owes ] def x = 3 ;"));
        let collected = collect(&pbg, &tree, &Unit::single(), &mut tank()).unwrap();
        let slot = collected.slots.first().unwrap();
        let names: Vec<SurfaceName<'_>> =
            slot.attributes.iter().map(|written| written.name).collect();

        assert_eq!(
            names,
            [SurfaceName::from("checks"), SurfaceName::from("owes")],
            "stacked blocks all attach, in source order, to the one declaration they precede"
        );
        assert!(
            slot.attributes
                .iter()
                .all(|written| written.decorates == slot.introduced_by.node),
            "both blocks decorate the same declaration form"
        );
        assert_eq!(
            collected.owner_of(slot.introduced_by.node),
            Maybe::Present(SlotIndex::from(0_usize)),
            "the declaration form belongs to the slot it was filed under"
        );
        assert_eq!(
            slot.introduced_by.span,
            span(ByteOffset::from(22_usize), ByteOffset::from(33_usize)),
            "the blocks stand outside the declaration form, so its identity excludes them"
        );
        let blocks: Vec<NodeIndex> = tree
            .children(tree.root())
            .filter(|&child| child != slot.introduced_by.node)
            .filter(|&child| {
                tree.node(child).is_some_and(|node| {
                    matches!(node.label(), NodeLabel::Meld(_) | NodeLabel::Tile(_))
                })
            })
            .collect();
        assert_eq!(blocks.len(), 2, "each block is a root form of its own");
        assert!(
            blocks
                .iter()
                .all(|&block| collected.owner_of(block) == Maybe::Present(SlotIndex::from(0_usize))),
            "each block belongs to the slot of the declaration it decorates"
        );
    }

    #[test]
    fn a_module_member_reads_the_blocks_inside_its_form()
    {
        let pbg = grammar();
        let tree = parsed(
            &pbg,
            SourceText::from("module M { @[ checks ] @[ owes ] def x = 3 ; }"),
        );
        let collected = collect(&pbg, &tree, &Unit::single(), &mut tank()).unwrap();
        let slot = collected
            .slots
            .iter()
            .find(|slot| slot.name == SurfaceName::from("x"))
            .unwrap();
        let names: Vec<SurfaceName<'_>> =
            slot.attributes.iter().map(|written| written.name).collect();

        assert_eq!(
            names,
            [SurfaceName::from("checks"), SurfaceName::from("owes")],
            "a member's stacked blocks attach in source order"
        );
        assert!(
            slot.attributes
                .iter()
                .all(|written| written.decorates == slot.introduced_by.node),
            "both blocks decorate the member form holding them"
        );
        assert_eq!(
            slot.introduced_by.span,
            span(ByteOffset::from(11_usize), ByteOffset::from(44_usize)),
            "a member's blocks are inside its form"
        );
    }

    #[test]
    fn the_lowest_positioned_refusal_is_the_one_kept()
    {
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));
        let introduced = Placed {
            node: NodeIndex::from(1_usize),
            span: at(0_usize, 1_usize),
        };
        let mut slot = DeclarationSlot {
            name: SurfaceName::from("x"),
            container: Container::TopLevel(SourceIndex::from(0_usize)),
            role: Role::Declared,
            constant: ConstantIndex::from(0_usize),
            introduced_by: introduced,
            named: introduced,
            signature: Maybe::<Half, _>::Absent(declaration_half::Absent::Unwritten),
            definition: Maybe::Absent(declaration_half::Absent::Unwritten),
            attributes: Vec::new(),
            docs: Vec::new(),
            refusal: Maybe::Absent(slot_refusal::Absent::Unrefused),
        };
        let deep = LoweringRefusal::UnresolvedName {
            span: at(9_usize, 10_usize),
            name: SurfaceName::from("deep"),
        };
        let shallow = LoweringRefusal::UnresolvedName {
            span: at(2_usize, 3_usize),
            name: SurfaceName::from("shallow"),
        };
        let later = LoweringRefusal::UnresolvedName {
            span: at(4_usize, 5_usize),
            name: SurfaceName::from("later"),
        };

        slot.refuse(NodeIndex::from(7_usize), deep);
        assert_eq!(
            slot.refusal.map(|(_at, held)| held),
            Maybe::Present(deep),
            "the first offer fills an empty slot"
        );
        slot.refuse(NodeIndex::from(3_usize), shallow);
        assert_eq!(
            slot.refusal.map(|(_at, held)| held),
            Maybe::Present(shallow),
            "a strictly lower position replaces the incumbent"
        );
        slot.refuse(NodeIndex::from(5_usize), later);
        assert_eq!(
            slot.refusal.map(|(_at, held)| held),
            Maybe::Present(shallow),
            "a higher position leaves the incumbent alone"
        );
        slot.refuse(NodeIndex::from(3_usize), later);
        assert_eq!(
            slot.refusal.map(|(_at, held)| held),
            Maybe::Present(shallow),
            "an offer at the incumbent's own position does not displace it"
        );
    }
}
