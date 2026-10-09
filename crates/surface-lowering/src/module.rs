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
//! strictly earlier positions — so self-reference and mutual reference are
//! refused by the rule as well as by the core's own definition chain.
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
//! implicit telescope or `rec` is a form the fragment does not admit.
//! Attributes written before `def` are tiles of that same form, so a
//! declaration's attributes are read with it, and an attribute block standing
//! on its own — after the last declaration — decorates nothing and refuses the
//! module.
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
//! the shallowest and then leftmost refusing node — a fixed rule rather than a
//! traversal accident, so two runs over one source report the same refusal. A
//! fault in the declaration form's own tiles is offered at the declaration
//! node itself, so it outranks every refusal from inside its operands. A fault
//! in the module's own shape — a root child that is not a declaration or an
//! import, an import out of shape, two imports of one alias, or a declaration
//! with no name to file a refusal under — refuses the module.
//!
//! # Imports are collected beside the declarations
//!
//! `import "URI" as name ;` is kept in source order and its alias bound in the
//! module's import scope as it is read; no address is resolved.

use alloc::collections::BTreeMap;
use alloc::string::String;
use alloc::vec::Vec;

use gandr_core_term::ValueId;
use gandr_core_term::ValueTypeId;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::NameSegment;
use gandr_kernel_term::StructuredName;
use gandr_surface_grammar::Pbg;
use gandr_surface_syntax::ByteSpan;
use gandr_surface_syntax::NodeDigest;
use gandr_surface_syntax::NodeIndex;
use gandr_surface_syntax::NodeLabel;
use gandr_surface_syntax::SourceFragment;
use gandr_surface_syntax::SyntaxTree;
use quenchant_shape::shape::Maybe;

use crate::attribute::AttributeTable;
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
use crate::form::Repair;
use crate::form::Run;
use crate::form::Shape;
use crate::form::TileName;
use crate::form::read_pieces;
use crate::form::shape_of;
use crate::import::ImportDeclaration;
use crate::import::ImportIndex;
use crate::import::ImportUri;
use crate::import::ModuleImports;
use crate::lower::Fuel;
use crate::lower::decode_escapes;
use crate::namespace::Recognition;
use crate::namespace::Scope;
use crate::origin::OriginTable;
use crate::origin::OriginToken;
use crate::resolve::SurfaceName;

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

/// The position of one declaration slot in a module's admission order.
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
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Container
{
    /// The source's top level.
    TopLevel,
    /// The body of this module.
    Module(StructureIndex),
}

/// What a slot stands for.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Role
{
    /// A name the source declared: a top-level definition or a module
    /// member.
    Declared,
    /// A second type stated for a member, checked by a declaration whose body
    /// is that member.
    Witness,
    /// A slot that declares nothing: it carries a refusal a module or a
    /// signature component raised, or owns a manifest type component's type,
    /// and yields a declaration only when it holds a refusal.
    Held,
}

/// One member of a module's body, or one component it exports.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Member
{
    /// A definition member, by its slot.
    Slot(SlotIndex),
    /// A nested module.
    Module(StructureIndex),
}

/// What one component of a module signature states.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum ComponentForm
{
    /// A value component `x : T`, with its type.
    Value(Placed),
    /// A manifest type component `type T = τ`, with the type it names.
    Manifest(Placed),
    /// A type component the fragment does not read yet.
    Unread(AscriptionForm),
}

/// One component of a module signature, as written.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Component<'source>
{
    /// The component's name.
    pub name: SurfaceName<'source>,
    /// The name's tile.
    pub named: Placed,
    /// What the component states.
    pub form: ComponentForm,
}

/// A manifest type component, kept for the module's stratum item and for the
/// components after it that name it.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct TypeComponent<'source>
{
    /// The component's name.
    pub name: SurfaceName<'source>,
    /// The type it is manifestly equal to.
    pub defined: Placed,
    /// The held slot owning that type, which carries its refusal.
    pub held: SlotIndex,
}

/// The manifest type components a signature type sees: those of `structure`
/// written before the component the type belongs to.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ComponentScope
{
    /// The module whose signature the type is written in.
    pub structure: StructureIndex,
    /// How many of its manifest type components precede the type.
    pub before: usize,
}

/// Whether matching against a signature coerced a module's body.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Coerced(pub bool);

/// One module as the collection pass found it: a stratum item.
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
    /// module is ascribed transparently.
    pub ascription: Maybe<Vec<Component<'source>>, ascription::Absent>,
    /// The body's members, in source order.
    pub members: Vec<Member>,
    /// The components the module exports, in signature order once matched.
    pub exports: Vec<Member>,
    /// The manifest type components, in signature order.
    pub types: Vec<TypeComponent<'source>>,
    /// Whether matching coerced the body.
    pub coerced: Coerced,
}

/// What one half of a declared name lowers from.
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
}

/// One half of a declared name: the declaration form that wrote it and what
/// it lowers from.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Half
{
    /// The declaration form.
    pub declaration: Placed,
    /// The declared type of a signature, or the body of a definition.
    pub operand: Operand,
}

/// The payload an attribute was written with.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Payload
{
    /// No payload was written, or the parentheses hold nothing.
    Unwritten,
    /// The form written between the parentheses.
    Written(Placed),
}

/// One attribute as the declaration form wrote it.
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

/// One name's declarations, as the collection pass found them.
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
    /// The lowest-positioned refusal found for this name so far.
    pub refusal: Maybe<(NodeIndex, LoweringRefusal<'source>), slot_refusal::Absent>,
}

impl<'source> DeclarationSlot<'source>
{
    /// Keep `refusal` when it sits below every refusal already found.
    ///
    /// # Specification
    /// - requires: `at` is the arena position of the node that refused.
    /// - ensures: the slot ends holding the refusal at the lowest position ever
    ///   offered, so the reported refusal does not depend on the order the
    ///   passes visit nodes in; an offer at a higher position leaves the slot
    ///   unchanged.
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
    #[inline]
    pub fn refuse(
        &mut self,
        at: NodeIndex,
        refusal: LoweringRefusal<'source>,
    )
    {
        let replaces = match self.refusal {
            | Maybe::Present((incumbent, _held)) => at < incumbent,
            | Maybe::Absent(_) => true,
        };
        if replaces {
            self.refusal = Maybe::Present((at, refusal));
        }
    }

    /// Whether this slot already holds a refusal.
    ///
    /// # Specification
    /// trivial.
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
#[derive(Clone, Debug)]
pub struct Collected<'source>
{
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
}

impl<'source> Collected<'source>
{
    /// The slot owning `position`.
    ///
    /// # Specification
    /// trivial.
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

    /// Give `position` to `slot`.
    ///
    /// # Specification
    /// trivial.
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
}

/// Which half of a declared name a declaration form writes.
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
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
enum Tail<'source>
{
    /// A signature or a definition over this operand.
    Wrote(HalfKind, Placed),
    /// A function tail: a definition, and a signature when it is signed.
    Function(Signing),
    /// The first fault of the form.
    Refused(LoweringRefusal<'source>),
}

/// The collection pass's working state.
struct Collector<'run, 'source>
{
    /// The grammar the tree was molded under.
    pbg: &'run Pbg,
    /// The tree being collected.
    tree: &'run SyntaxTree<'source>,
    /// The lowering's remaining allowance.
    fuel: &'run mut Fuel,
    /// What has been collected so far.
    collected: Collected<'source>,
    /// The scratch reading of the declaration form being collected.
    pieces: Pieces,
}

/// Pair every signature with its definition, in one pass over the module.
///
/// # Specification
/// - requires: `tree`'s root is the module being lowered, molded under `pbg`;
///   `fuel` holds the lowering's remaining allowance.
/// - ensures: one slot per distinct declared name, in the order the names were
///   first declared, each carrying that name's signature and definition
///   wherever the two sat, and every attribute written on its first clean
///   declaration form of each kind; a second signature or a second definition
///   for one name leaves the slot's first refusal set and the first occurrence
///   intact. A fault in a declaration form's own tiles — a repair, an empty or
///   overfull hole, a tile out of place, a tail the fragment does not admit —
///   is offered to the declaration's slot at the declaration form itself. Each
///   import is kept in source order with its address decoded and its alias
///   bound in the import scope.
/// - provides: the admission order every later pass resolves names against.
/// - fails: [`LoweringRefusal::MalformedForm`] when the root holds a repair, a
///   declaration has no name to file a refusal under, or an import is out of
///   shape; [`LoweringRefusal::DuplicateImportAlias`] when two imports bind one
///   alias; [`LoweringRefusal::OutOfFragment`] when a root child is neither a
///   declaration nor an import — an attribute block decorating nothing included
///   — or when a declaration's name is a form rather than an identifier;
///   [`LoweringRefusal::UnknownMold`] for a mold the grammar does not hold;
///   [`LoweringRefusal::BudgetExceeded`] when the walk outruns the allowance.
/// - panics: none. A position the tree does not hold contributes nothing.
///
/// # Errors
/// [`LoweringRefusal::MalformedForm`], [`LoweringRefusal::OutOfFragment`] and
/// [`LoweringRefusal::DuplicateImportAlias`] for a module whose own children
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
/// - witness: `module::tests::a_trailing_attribute_block_refuses_the_module`
/// - witness: `module::tests::an_attribute_block_decorates_the_declaration_after_it`
/// - witness: `namespace::namespace::source_import_reaches_the_namespace_engine_and_exposes_its_alias`
/// - witness: `namespace::namespace::source_import_without_alias_becomes_a_refusal`
/// - witness: `namespace::namespace::duplicate_source_import_alias_becomes_a_refusal`
#[inline]
pub fn collect<'source>(
    pbg: &Pbg,
    tree: &SyntaxTree<'source>,
    fuel: &mut Fuel,
) -> Result<Collected<'source>, LoweringRefusal<'source>>
{
    let mut owner = Vec::new();
    owner.resize(
        usize::from(tree.node_count()),
        Maybe::Absent(slot_owner::Absent::Unowned),
    );
    let mut collector = Collector {
        pbg,
        tree,
        fuel,
        collected: Collected {
            slots: Vec::new(),
            owner,
            by_name: BTreeMap::new(),
            structures: Vec::new(),
            modules: BTreeMap::new(),
            scopes: Vec::new(),
            imports: ModuleImports::new(),
        },
        pieces: Pieces::new(),
    };
    let mut root = Pieces::new();
    read_pieces(pbg, tree, tree.root(), &mut root)?;
    if let Maybe::Present(repaired) = root.repair {
        return Err(LoweringRefusal::MalformedForm {
            span: repaired.span,
            form: FormName::ROOT,
            fault: FormFault::Repaired(repaired.repair),
        });
    }
    for piece in root.pieces {
        collector.fuel.spend()?;
        collector.module_child(piece.placed())?;
    }

    Ok(collector.collected)
}

impl<'source> Collector<'_, 'source>
{
    /// Collect one child of the root.
    ///
    /// # Specification
    /// - requires: `child` is a written child of the root.
    /// - ensures: a declaration form is collected into its slot, a module into
    ///   its structures and member slots, and an import into the import list;
    ///   every other form refuses the module as a form of the wrong sort.
    /// - provides: the module-shape half of [`collect`].
    /// - fails: [`LoweringRefusal::OutOfFragment`] for a child that is neither
    ///   a declaration, a module nor an import, and every module-level fault
    ///   [`Self::declaration`], [`Self::module`] and [`Self::import`] raise.
    /// - panics: none.
    ///
    /// # Errors
    /// As [`collect`].
    fn module_child(
        &mut self,
        child: Placed,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let Some(node) = self.tree.node(child.node)
        else {
            return Ok(());
        };
        match shape_of(self.pbg, node)? {
            | Shape::Form {
                former: Former::Declaration,
                ..
            } => self.declaration(child),
            | Shape::Form {
                former: Former::Module,
                ..
            } => self.module(child),
            | Shape::Form {
                former: Former::Import,
                name,
                ..
            } => self.import(child, name),
            | Shape::Form { name, .. } => Err(LoweringRefusal::OutOfFragment {
                span: child.span,
                form: name,
                sort: FragmentSort::Declaration,
                boundary: FragmentBoundary::WrongSort,
            }),
            | Shape::Root | Shape::Repair(_) | Shape::Layout => Ok(()),
        }
    }

    /// Collect one declaration form.
    ///
    /// # Specification
    /// - requires: `declaration` is a declaration form.
    /// - ensures: the form's attributes, name and tail are read in that order;
    ///   the name is admitted to its slot and the form is owned by it; the
    ///   first fault of the form is offered to the slot at the form itself, and
    ///   a form with no fault files its half and its attributes.
    /// - provides: the per-declaration half of [`collect`].
    /// - fails: when the form has no name: the repair it holds, the form
    ///   standing where the name belongs, or a misplaced tile.
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoweringRefusal::MalformedForm`] and
    /// [`LoweringRefusal::OutOfFragment`] for a declaration with no name,
    /// and [`LoweringRefusal::UnknownMold`].
    fn declaration(
        &mut self,
        declaration: Placed,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let mut pieces = core::mem::take(&mut self.pieces);
        read_pieces(self.pbg, self.tree, declaration.node, &mut pieces)?;
        let outcome = self.read_declaration(Container::TopLevel, declaration, &pieces);
        self.pieces = pieces;

        outcome
    }

    /// Collect one import, `import "URI" as name ;`, of form `form`.
    ///
    /// # Specification
    /// - requires: `import` is an import form named `form`.
    /// - ensures: the import's address — the text between its quotes with its
    ///   escapes decoded — its alias and its bytes are kept after every earlier
    ///   import, and its alias is bound in the import scope.
    /// - provides: the import half of [`collect`].
    /// - fails: [`LoweringRefusal::MalformedForm`] for a repair or a tile out
    ///   of place — an import with no alias included — and
    ///   [`LoweringRefusal::DuplicateImportAlias`] for an alias an earlier
    ///   import binds.
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoweringRefusal::MalformedForm`],
    /// [`LoweringRefusal::DuplicateImportAlias`] and
    /// [`LoweringRefusal::UnknownMold`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — two imports, an escaped address, an import with no
    ///   alias and two imports of one alias, each asserted as the exact import
    ///   list or refusal over the parsed source.
    /// - witness: `namespace::namespace::source_import_reaches_the_namespace_engine_and_exposes_its_alias`
    /// - witness: `namespace::namespace::an_import_binds_its_alias_and_resolves_no_address`
    /// - witness: `namespace::namespace::source_import_without_alias_becomes_a_refusal`
    /// - witness: `namespace::namespace::duplicate_source_import_alias_becomes_a_refusal`
    fn import(
        &mut self,
        import: Placed,
        form: FormName,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let mut pieces = core::mem::take(&mut self.pieces);
        read_pieces(self.pbg, self.tree, import.node, &mut pieces)?;
        let outcome = self.read_import(import, form, &pieces);
        self.pieces = pieces;
        let declaration = outcome?;

        self.collected.imports.bind(declaration)
    }

    /// Read one import form's pieces.
    ///
    /// # Specification
    /// - requires: `pieces` is the reading of the import `import`.
    /// - ensures: the declaration the tiles `import " … " as name ;` spell, in
    ///   that order with nothing after them.
    /// - provides: the reading half of [`Self::import`].
    /// - fails: [`LoweringRefusal::MalformedForm`] naming `form` for a repair
    ///   or a tile out of place.
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoweringRefusal::MalformedForm`].
    fn read_import(
        &self,
        import: Placed,
        form: FormName,
        pieces: &Pieces,
    ) -> Result<ImportDeclaration<'source>, LoweringRefusal<'source>>
    {
        if let Maybe::Present(repaired) = pieces.repair {
            return Err(LoweringRefusal::MalformedForm {
                span: repaired.span,
                form,
                fault: FormFault::Repaired(repaired.repair),
            });
        }
        let out_of_place = |cursor: &Cursor<'_>| LoweringRefusal::MalformedForm {
            span: cursor.here(),
            form,
            fault: FormFault::MisplacedTile,
        };
        let mut cursor = Cursor::new(&pieces.pieces, import.span);
        for opening in [TileName::IMPORT, TileName::QUOTE] {
            if let Maybe::Absent(_) = cursor.tile(opening) {
                return Err(out_of_place(&cursor));
            }
        }
        let mut written = String::new();
        loop {
            let piece = match cursor.tile(TileName::STRING_FRAGMENT) {
                | Maybe::Present(fragment) => fragment,
                | Maybe::Absent(_) => match cursor.tile(TileName::ESCAPE_SEQUENCE) {
                    | Maybe::Present(escape) => escape,
                    | Maybe::Absent(_) => break,
                },
            };
            if let Some(text) = self.tree.fragment(piece.node) {
                written.push_str(text.as_ref());
            }
        }
        for closing in [TileName::QUOTE, TileName::AS] {
            if let Maybe::Absent(_) = cursor.tile(closing) {
                return Err(out_of_place(&cursor));
            }
        }
        let Maybe::Present(alias) = cursor.tile(TileName::IDENTIFIER)
        else {
            return Err(out_of_place(&cursor));
        };
        if let Maybe::Absent(_) = cursor.tile(TileName::SEMICOLON) {
            return Err(out_of_place(&cursor));
        }
        if let Maybe::Present(_) = cursor.peek() {
            return Err(out_of_place(&cursor));
        }
        let uri = ImportUri::from(decode_escapes(SourceFragment::from(written.as_str())));

        Ok(ImportDeclaration::new(
            uri,
            self.name_of(alias),
            import.span,
        ))
    }

    /// Read one declaration form's pieces into its slot in `container`.
    ///
    /// # Specification
    /// - requires: `pieces` is the reading of the form `declaration`, a
    ///   top-level declaration or a definition member of the module `container`
    ///   names.
    /// - ensures: as [`Self::declaration`], the name admitted in `container`.
    /// - provides: the reading half of [`Self::declaration`] and of a module's
    ///   definition members, over a borrowed reading.
    /// - fails: as [`Self::declaration`].
    /// - panics: none.
    ///
    /// # Errors
    /// As [`Self::declaration`].
    fn read_declaration(
        &mut self,
        container: Container,
        declaration: Placed,
        pieces: &Pieces,
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
        let attributed = self.read_attributes(
            Cursor::new(before, declaration.span),
            declaration.node,
            &mut attributes,
        );
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
        let tail = if let Maybe::Present(repaired) = pieces.repair {
            Tail::Refused(LoweringRefusal::MalformedForm {
                span: repaired.span,
                form: FormName::DECLARATION,
                fault: FormFault::Repaired(repaired.repair),
            })
        }
        else if let Err(refusal) = attributed {
            Tail::Refused(refusal)
        }
        else if let Maybe::Present(_) = recursive {
            Tail::Refused(unadmitted(declaration, FormName::RECURSIVE))
        }
        else {
            read_tail(&mut header, declaration)
        };
        self.file(slot, declaration, tail, attributes);

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
    fn unnamed(
        &self,
        pieces: &Pieces,
        declaration: Placed,
        header: &Cursor<'_>,
    ) -> LoweringRefusal<'source>
    {
        if let Maybe::Present(repaired) = pieces.repair {
            return LoweringRefusal::MalformedForm {
                span: repaired.span,
                form: FormName::DECLARATION,
                fault: FormFault::Repaired(repaired.repair),
            };
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
            | Maybe::Present(_) => header.here(),
            | Maybe::Absent(_) => declaration.span,
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
    fn read_block(
        &self,
        cursor: &mut Cursor<'_>,
        declaration: NodeIndex,
        attributes: &mut Vec<WrittenAttribute<'source>>,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        loop {
            attributes.push(self.read_attribute(cursor, declaration)?);
            if let Maybe::Present(_) = cursor.tile(TileName::COMMA) {
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
                | Run::Empty(_) => Payload::Unwritten,
                | Run::One(payload) => Payload::Written(payload),
                | Run::Several { extra, .. } => {
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
            | Run::Empty(_) => Ok(written),
            | Run::One(stray) | Run::Several { first: stray, .. } => {
                Err(extra_operand(FormName::ATTRIBUTE, stray))
            },
        }
    }

    /// File one read declaration form into its slot.
    ///
    /// # Specification
    /// - requires: `slot` names a live slot; `declaration` is the form read.
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
    /// - hypothesis: L3 — a written signature before a signed function tail and
    ///   after one, and two written signatures, each asserted as the exact
    ///   declared type, witness or refusal.
    /// - witness: `modules::modules::member_signature_attaches_and_wins_over_derived_function_type`
    /// - witness: `modules::modules::signatures_attach_to_their_defs`
    /// - witness: `module::tests::a_second_signature_is_refused`
    fn file(
        &mut self,
        slot: SlotIndex,
        declaration: Placed,
        tail: Tail<'source>,
        attributes: Vec<WrittenAttribute<'source>>,
    )
    {
        let Some(entry) = self.collected.slots.get_mut(slot.0)
        else {
            return;
        };
        let (operand, kinds): (Operand, &[HalfKind]) = match tail {
            | Tail::Wrote(HalfKind::Signature, operand) => {
                (Operand::Written(operand), &[HalfKind::Signature])
            },
            | Tail::Wrote(HalfKind::Definition, operand) => {
                (Operand::Written(operand), &[HalfKind::Definition])
            },
            | Tail::Function(Signing::Signed) => (Operand::Function, &[
                HalfKind::Signature,
                HalfKind::Definition,
            ]),
            | Tail::Function(Signing::Unsigned) => (Operand::Function, &[HalfKind::Definition]),
            | Tail::Refused(refusal) => {
                entry.refuse(declaration.node, refusal);
                return;
            },
        };
        let incoming = Half {
            declaration,
            operand,
        };
        let mut derived = Maybe::Absent(declaration_half::Absent::Unwritten);
        for &kind in kinds {
            let held = match kind {
                | HalfKind::Signature => entry.signature,
                | HalfKind::Definition => entry.definition,
            };
            let Maybe::Present(first) = held
            else {
                continue;
            };
            if kind == HalfKind::Signature {
                match (first.operand, operand) {
                    | (Operand::Written(_), Operand::Function) => {
                        derived = Maybe::Present(incoming);
                        continue;
                    },
                    | (Operand::Function, Operand::Written(_)) => {
                        derived = Maybe::Present(first);
                        continue;
                    },
                    | _ => {},
                }
            }
            let (span, name, first) = (declaration.span, entry.name, first.declaration.span);
            let refusal = match kind {
                | HalfKind::Signature => LoweringRefusal::DuplicateSignature { span, name, first },
                | HalfKind::Definition => {
                    LoweringRefusal::DuplicateDefinition { span, name, first }
                },
            };
            entry.refuse(declaration.node, refusal);
            return;
        }
        for &kind in kinds {
            match kind {
                | HalfKind::Signature => {
                    if derived != Maybe::Present(incoming) {
                        entry.signature = Maybe::Present(incoming);
                    }
                },
                | HalfKind::Definition => entry.definition = Maybe::Present(incoming),
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
                operand: Operand::Member(target),
            }),
            attributes: Vec::new(),
            refusal: Maybe::Absent(slot_refusal::Absent::Unrefused),
        };
        self.collected.slots.push(witness);

        minted
    }

    /// The identifier the tile `tile` spells.
    ///
    /// # Specification
    /// trivial.
    fn name_of(
        &self,
        tile: Placed,
    ) -> SurfaceName<'source>
    {
        self.tree
            .fragment(tile.node)
            .map_or_else(|| SurfaceName::from(""), SurfaceName::from)
    }
}

/// The kind a record type is written as, the only form a signature states a
/// nested module's components with.
const RECORD_TYPE: &str = "record_type";

/// A module form's header, read.
#[derive(Clone, Debug)]
struct Opened<'source>
{
    /// The module's name.
    name: SurfaceName<'source>,
    /// The name's tile.
    named: Placed,
    /// The inline signature's components, when ascribed transparently.
    ascription: Maybe<Vec<Component<'source>>, ascription::Absent>,
    /// The body's member forms, in source order.
    members: Vec<Placed>,
}

/// What reading a module form's header found.
#[derive(Clone, Debug)]
enum Header<'source>
{
    /// A module whose body is read.
    Opened(Opened<'source>),
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
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct Carried(bool);

/// Whether an operand is a bare name.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct BareName(bool);

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
    /// - provides: the module half of [`collect`].
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
    /// - hypothesis: L3 — nesting separated by depth one and depth eight, and
    ///   the refusals of the module as a whole by an unread body, an empty
    ///   body, a sealed module, a lowercase name and a malformed member, each
    ///   asserted as the exact declaration list.
    /// - witness: `modules::modules::modules_lower_to_named_member_declarations`
    /// - witness: `modules::modules::deeply_nested_modules_lower_and_resolve_at_every_depth`
    /// - witness: `modules::modules::an_unread_module_body_is_refused_not_emptied`
    /// - witness: `modules::modules::an_empty_module_is_not_an_unread_one`
    /// - witness: `modules::modules::opaque_module_ascription_is_declined_not_read_as_transparent`
    /// - witness: `modules::modules::module_name_case_boundary_covers_single_and_multi_names`
    /// - witness: `modules::modules::an_unread_member_keeps_its_own_report`
    /// - witness: `modules::modules::a_readable_module_keeps_its_members_and_its_successor`
    /// - witness: `modules::modules::a_nested_module_declares_under_either_case_spelling`
    /// - witness: `modules::modules::a_repaired_container_keeps_its_member`
    /// - witness: `modules::modules::a_malformed_member_is_repaired_and_its_siblings_kept`
    /// - witness: `modules::modules::duplicate_module_member_definition_is_rejected`
    /// - witness: `modules::modules::module_members_admit_in_source_order`
    /// - witness: `modules::modules::computation_signed_module_member_origin_mirrors_ascription_encoding`
    fn module(
        &mut self,
        module: Placed,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let mut pieces = Pieces::new();
        read_pieces(self.pbg, self.tree, module.node, &mut pieces)?;
        let mut stack = Vec::new();
        match self.header(module, &pieces, Container::TopLevel)? {
            | Header::Opened(opened) => self.open(Container::TopLevel, module, opened, &mut stack),
            | Header::Refused {
                name,
                named,
                refusal,
            } => {
                let _held = self.refuse_held(Container::TopLevel, name, module, named, refusal);
            },
            | Header::Unnamed(refusal) => return Err(refusal),
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

        Ok(())
    }

    /// Read a module form's header: its name, its signature and its body's
    /// member forms.
    ///
    /// # Specification
    /// - requires: `pieces` is the reading of the module form `form`, declared
    ///   in `container`.
    /// - ensures: the opened module when its tiles read `module Name (: #{ …
    ///   })? { members }`, a top-level name taking the uppercase spelling and a
    ///   nested one either; a top-level module named in lowercase, a repair no
    ///   operand carries, opaque ascription, or a signature or body out of
    ///   shape refuses the module under its name; a form with no name is
    ///   unnamed.
    /// - provides: the per-module reading of [`Self::module`] and
    ///   [`Self::member`].
    /// - fails: [`LoweringRefusal::UnknownMold`] for a foreign mold; every
    ///   fault of the form itself is yielded rather than raised.
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoweringRefusal::UnknownMold`].
    fn header(
        &self,
        form: Placed,
        pieces: &Pieces,
        container: Container,
    ) -> Result<Header<'source>, LoweringRefusal<'source>>
    {
        let mut cursor = Cursor::new(&pieces.pieces, form.span);
        let unnamed = |cursor: &Cursor<'_>| match pieces.repair {
            | Maybe::Present(repaired) => {
                Header::Unnamed(repaired_module(repaired.span, repaired.repair))
            },
            | Maybe::Absent(_) => Header::Unnamed(misplaced_in(FormName::MODULE, cursor.here())),
        };
        if let Maybe::Absent(_) = cursor.tile(TileName::MODULE) {
            return Ok(unnamed(&cursor));
        }
        let named = match cursor.peek() {
            | Maybe::Present(Piece::Tile { label, at })
                if label == TileName::TYPE_IDENTIFIER
                    || (label == TileName::IDENTIFIER && container != Container::TopLevel) =>
            {
                let _name = cursor.read();
                at
            },
            | Maybe::Present(Piece::Operand(standing))
                if container == Container::TopLevel && self.is_name(standing)?.0 =>
            {
                let name = self.name_of(standing);
                return Ok(Header::Refused {
                    name,
                    named: standing,
                    refusal: LoweringRefusal::LowercaseModuleName {
                        span: form.span,
                        name,
                    },
                });
            },
            | Maybe::Present(_) | Maybe::Absent(_) => return Ok(unnamed(&cursor)),
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
            return refused(repaired_module(repaired.span, repaired.repair));
        }
        let ascription = if let Maybe::Present(seal) = cursor.tile(TileName::SEAL) {
            return refused(LoweringRefusal::UnreadAscription {
                span: seal.span,
                name,
                form: AscriptionForm::Opaque,
            });
        }
        else if let Maybe::Present(_) = cursor.tile(TileName::COLON) {
            match self.signature(&mut cursor) {
                | Ok(components) => Maybe::Present(components),
                | Err(refusal) => return refused(refusal),
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
            members,
        }))
    }

    /// Whether `standing` is a bare name: a top-level module's lowercase name,
    /// which the grammar reads as an operand where the name tile belongs.
    ///
    /// # Specification
    /// trivial.
    fn is_name(
        &self,
        standing: Placed,
    ) -> Result<BareName, LoweringRefusal<'source>>
    {
        let Some(node) = self.tree.node(standing.node)
        else {
            return Ok(BareName(false));
        };
        let shape = shape_of(self.pbg, node)?;

        Ok(BareName(matches!(shape, Shape::Form {
            former: Former::Name,
            ..
        })))
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
            | Piece::Operand(operand) => repaired(operand),
            | Piece::Tile { .. } => false,
        }))
    }

    /// Read a module signature, `#{ components }`, after its `:`.
    ///
    /// # Specification
    /// - requires: `cursor` stands just past the ascription's `:`.
    /// - ensures: every component in signature order, the cursor past the
    ///   closing `}`: `x : T` a value component; `type T = τ` a manifest one;
    ///   `type T`, `type T : κ` and a type component binding parameters, each
    ///   kept as a form the fragment does not read.
    /// - provides: the signature half of [`Self::header`].
    /// - fails: yields a misplaced-tile refusal for a signature out of shape
    ///   and the hole's refusal for a type not written as one form.
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoweringRefusal::MalformedForm`] naming the module form.
    fn signature(
        &self,
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
                }
            }
            else if let Maybe::Present(_) = cursor.tile(TileName::TYPE) {
                let Maybe::Present(named) = cursor.tile(TileName::TYPE_IDENTIFIER)
                else {
                    return Err(misplaced_in(FormName::MODULE, cursor.here()));
                };
                Component {
                    name: self.name_of(named),
                    named,
                    form: type_component(cursor)?,
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
    ///   enclosing module's members and its body is pushed.
    /// - provides: the recording half of [`Self::module`].
    /// - fails: never.
    /// - panics: none.
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
        self.collected.structures.push(Structure {
            name: opened.name,
            container,
            declared_by: form,
            named: opened.named,
            ascription: opened.ascription,
            members: Vec::new(),
            exports: Vec::new(),
            types: Vec::new(),
            coerced: Coerced(false),
        });
        self.collected.modules.insert(key, structure);
        if let Container::Module(parent) = container
            && let Some(entry) = self.collected.structures.get_mut(parent.0)
        {
            entry.members.push(Member::Module(structure));
        }
        stack.push(Open {
            structure,
            members: opened.members,
            next: 0_usize,
        });
    }

    /// Read one member form of `structure`'s body.
    ///
    /// # Specification
    /// - requires: `pieces` is the reading of `member`, a member form of the
    ///   module at `structure`.
    /// - ensures: a form holding a `def` tile is a definition member, read as a
    ///   declaration in the module; a form opening on `module` is a nested
    ///   module, opened onto `stack` or refused as a whole under its name;
    ///   every other form is a malformed member, refused under the module's
    ///   name at the member, and the module's other members are kept.
    /// - provides: the per-member half of [`Self::module`].
    /// - fails: [`LoweringRefusal::UnknownMold`] for a foreign mold.
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoweringRefusal::UnknownMold`].
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
            | Shape::Form {
                former: Former::Module | Former::Declaration,
                name,
            } => name,
            | Shape::Form { name, .. } => {
                self.fault_at(structure, member, LoweringRefusal::OutOfFragment {
                    span: member.span,
                    form: name,
                    sort: FragmentSort::Declaration,
                    boundary: FragmentBoundary::WrongSort,
                });
                return Ok(());
            },
            | Shape::Root | Shape::Repair(_) | Shape::Layout => return Ok(()),
        };
        let defines = pieces
            .pieces
            .iter()
            .any(|piece| matches!(*piece, Piece::Tile { label, .. } if label == TileName::DEF));
        if defines {
            if let Err(refusal) = self.read_declaration(container, member, pieces) {
                self.fault_at(structure, member, refusal);
            }
            return Ok(());
        }
        let cursor = Cursor::new(&pieces.pieces, member.span);
        if let Maybe::Absent(_) = cursor.at(TileName::MODULE) {
            self.fault_at(structure, member, misplaced_in(form, cursor.here()));
            return Ok(());
        }
        match self.header(member, pieces, container)? {
            | Header::Opened(opened) => self.open(container, member, opened, stack),
            | Header::Refused {
                name,
                named,
                refusal,
            } => {
                let _held = self.refuse_held(container, name, member, named, refusal);
            },
            | Header::Unnamed(refusal) => self.fault_at(structure, member, refusal),
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
            refusal: Maybe::Absent(slot_refusal::Absent::Unrefused),
        });

        minted
    }

    /// A held slot carrying `refusal`, at the form `introduced_by`.
    ///
    /// # Specification
    /// trivial.
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
    /// trivial.
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
    ///   module's own, deepest last, by an explicit queue.
    /// - provides: coercive matching.
    /// - fails: [`LoweringRefusal::UnknownMold`] and
    ///   [`LoweringRefusal::BudgetExceeded`].
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoweringRefusal::UnknownMold`] and
    /// [`LoweringRefusal::BudgetExceeded`].
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
                        | Member::Module(nested) => Some(nested),
                        | Member::Slot(_) => None,
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
                && self.form_name(record)?.as_ref() == RECORD_TYPE
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
    ///   held slot owning its type; every type sees the manifest components
    ///   before it. A component no member supplies, a nested module stated a
    ///   type other than a record, and a type component the fragment does not
    ///   read each file a held slot carrying the refusal under the component's
    ///   name; members the signature omits stay admitted and are not exported.
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
    ///   one, and each unread type component; hiding by a member the signature
    ///   omits; order by a reordered signature, each asserted as the exact
    ///   exports, declared types or refusal.
    /// - witness: `modules::modules::a_reordered_signature_matches_and_canonicalizes`
    /// - witness: `modules::modules::module_signature_matching_hides_extra_members`
    /// - witness: `modules::modules::a_missing_signature_component_is_rejected_at_the_signature`
    /// - witness: `modules::modules::a_manifest_type_component_expands_in_later_components`
    /// - witness: `modules::modules::a_kinded_type_component_is_declined_by_name_and_a_manifest_one_is_not`
    /// - witness: `modules::modules::a_bare_type_component_declines_and_keeps_its_siblings`
    /// - witness: `modules::modules::a_nonempty_ascription_checks_each_component_at_its_member`
    /// - witness: `modules::modules::a_dangling_member_signature_is_an_obligation`
    /// - witness: `modules::modules::an_abstract_component_under_transparent_ascription_points_at_seal`
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
        let module = entry.name;
        let Maybe::Present(components) = entry.ascription.clone()
        else {
            let exports = entry
                .members
                .iter()
                .copied()
                .filter(|member| match *member {
                    | Member::Slot(slot) => self
                        .collected
                        .slots
                        .get(slot.0)
                        .is_some_and(|held| held.role == Role::Declared),
                    | Member::Module(_) => true,
                })
                .collect();
            if let Some(opened) = self.collected.structures.get_mut(structure.0) {
                opened.exports = exports;
            }
            return Ok(());
        };
        let mut exports = Vec::new();
        let mut types = Vec::new();
        for component in components {
            self.fuel.spend()?;
            let scope = ComponentScope {
                structure,
                before: types.len(),
            };
            let stated = match component.form {
                | ComponentForm::Value(stated) => stated,
                | ComponentForm::Manifest(defined) => {
                    let held =
                        self.held(container, component.name, component.named, component.named);
                    self.collected.own(defined.node, held);
                    self.collected.scopes.push((defined.node, scope));
                    types.push(TypeComponent {
                        name: component.name,
                        defined,
                        held,
                    });
                    continue;
                },
                | ComponentForm::Unread(form) => {
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
                && !exports.contains(&found)
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
            | Maybe::Present(Member::Slot(slot)) => {
                self.state(slot, stated, component.named, Maybe::Present(scope));
            },
            | Maybe::Present(Member::Module(nested)) => {
                let form = self.form_name(stated)?;
                if form.as_ref() != RECORD_TYPE {
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
            | Maybe::Absent(_) => {
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

    /// The member `container`'s body declares under `name`.
    ///
    /// # Specification
    /// trivial.
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
            | Some(&nested) => Maybe::Present(Member::Module(nested)),
            | None => Maybe::Absent(declared_member::Absent::Undeclared),
        }
    }

    /// State `stated`, a type written at `at`, for the definition member at
    /// `member`.
    ///
    /// # Specification
    /// - requires: `member` names a live slot.
    /// - ensures: a member with no signature, or with only the one a function
    ///   tail derives, takes `stated` as its signature, the derived one filed
    ///   as a witness; a member with a written signature keeps it and `stated`
    ///   is filed as a witness. The slot `stated` lands on owns it, and it sees
    ///   `scope`'s manifest type components.
    /// - provides: the one way a signature types a member.
    /// - fails: never.
    /// - panics: none.
    fn state(
        &mut self,
        member: SlotIndex,
        stated: Placed,
        at: Placed,
        scope: Maybe<ComponentScope, component_scope::Absent>,
    )
    {
        let half = Half {
            declaration: at,
            operand: Operand::Written(stated),
        };
        let Some(entry) = self.collected.slots.get_mut(member.0)
        else {
            return;
        };
        let owner = match entry.signature {
            | Maybe::Absent(_) => {
                entry.signature = Maybe::Present(half);
                member
            },
            | Maybe::Present(
                derived @ Half {
                    operand: Operand::Function,
                    ..
                },
            ) => {
                entry.signature = Maybe::Present(half);
                let _witness = self.witness(member, derived);
                member
            },
            | Maybe::Present(_) => self.witness(member, half),
        };
        self.collected.own(stated.node, owner);
        if let Maybe::Present(seen) = scope {
            self.collected.scopes.push((stated.node, seen));
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
    ///   name; a record out of shape files one under the module's name.
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
    ///   each asserted as the exact exports and the checker's verdict.
    /// - witness: `modules::modules::nested_modules_lower_as_parent_members_and_project`
    /// - witness: `modules::modules::nested_member_signature_constrains_the_parent_binding`
    fn layer(
        &mut self,
        layer: Layer,
        queue: &mut Vec<Layer>,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let mut pieces = Pieces::new();
        read_pieces(self.pbg, self.tree, layer.record.node, &mut pieces)?;
        let fields = match self.fields(layer.record, &pieces) {
            | Ok(fields) => fields,
            | Err(refusal) => {
                self.fault_at(layer.structure, layer.record, refusal);
                return Ok(());
            },
        };
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
        for field in fields {
            let found = exports
                .iter()
                .copied()
                .find(|export| self.member_name(*export) == field.name);
            match found {
                | Some(Member::Slot(slot)) => {
                    self.state(slot, field.stated, field.named, layer.scope);
                },
                | Some(Member::Module(nested)) => {
                    let form = self.form_name(field.stated)?;
                    if form.as_ref() != RECORD_TYPE {
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
                | None => {
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
                && !kept.contains(&export)
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

    /// Read a record type's fields, `#{ name : T, … }`.
    ///
    /// # Specification
    /// - requires: `pieces` is the reading of the record type `record`.
    /// - ensures: every field in order, when the tiles read `#{`, fields
    ///   separated by `,`, and `}` with nothing after.
    /// - provides: the reading half of [`Self::layer`].
    /// - fails: yields the repair the record holds, a misplaced tile, or the
    ///   hole's refusal for a field type not written as one form, each naming
    ///   the record form.
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoweringRefusal::MalformedForm`].
    fn fields(
        &self,
        record: Placed,
        pieces: &Pieces,
    ) -> Result<Vec<Field<'source>>, LoweringRefusal<'source>>
    {
        let form = self.form_name(record)?;
        if let Maybe::Present(repaired) = pieces.repair {
            return Err(LoweringRefusal::MalformedForm {
                span: repaired.span,
                form,
                fault: FormFault::Repaired(repaired.repair),
            });
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
            let Maybe::Present(named) = cursor.tile(TileName::IDENTIFIER)
            else {
                return Err(misplaced_in(form, cursor.here()));
            };
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
    /// trivial.
    fn member_name(
        &self,
        member: Member,
    ) -> SurfaceName<'source>
    {
        match member {
            | Member::Slot(slot) => self
                .collected
                .slots
                .get(slot.0)
                .map_or_else(|| SurfaceName::from(""), |entry| entry.name),
            | Member::Module(nested) => self
                .collected
                .structures
                .get(nested.0)
                .map_or_else(|| SurfaceName::from(""), |entry| entry.name),
        }
    }

    /// The name of the form `placed` stands for.
    ///
    /// # Specification
    /// trivial.
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
            | Shape::Form { name, .. } => name,
            | Shape::Root | Shape::Repair(_) | Shape::Layout => FormName::ROOT,
        })
    }
}

/// What a type component written `type T` states after its name.
///
/// # Specification
/// - requires: `cursor` stands just past the component's name.
/// - ensures: `= τ` a manifest component; `: κ` a kinded one; a parameter list,
///   skipped to its closing `)`, a parameterized one whatever follows; nothing
///   an abstract one. The cursor stands past the component.
/// - provides: the type-component half of a module signature.
/// - fails: yields a misplaced-tile refusal for a parameter list that does not
///   close, and the hole's refusal for a type not written as one form.
/// - panics: none.
///
/// # Errors
/// [`LoweringRefusal::MalformedForm`] naming the module form.
fn type_component<'source>(
    cursor: &mut Cursor<'_>
) -> Result<ComponentForm, LoweringRefusal<'source>>
{
    let parameterized = cursor.tile(TileName::PAREN_OPEN);
    if let Maybe::Present(_) = parameterized {
        let mut depth = 1_usize;
        while depth > 0_usize {
            depth = match cursor.read() {
                | Maybe::Present(Piece::Tile { label, .. }) if label == TileName::PAREN_OPEN => {
                    depth.saturating_add(1_usize)
                },
                | Maybe::Present(Piece::Tile { label, .. }) if label == TileName::PAREN_CLOSE => {
                    depth.saturating_sub(1_usize)
                },
                | Maybe::Present(_) => depth,
                | Maybe::Absent(_) => {
                    return Err(misplaced_in(FormName::MODULE, cursor.here()));
                },
            };
        }
    }
    let form = if let Maybe::Present(_) = cursor.tile(TileName::EQUALS) {
        let defined = one_in(FormName::MODULE, cursor.operands())?;
        ComponentForm::Manifest(defined)
    }
    else if let Maybe::Present(_) = cursor.tile(TileName::COLON) {
        let _kind = one_in(FormName::MODULE, cursor.operands())?;
        ComponentForm::Unread(AscriptionForm::Kinded)
    }
    else {
        ComponentForm::Unread(AscriptionForm::Abstract)
    };

    Ok(match parameterized {
        | Maybe::Present(_) => ComponentForm::Unread(AscriptionForm::Parameterized),
        | Maybe::Absent(_) => form,
    })
}

/// The operand a one-operand hole of `form` holds, or the fault its run
/// earns.
///
/// # Specification
/// trivial.
const fn one_in<'source>(
    form: FormName,
    run: Run,
) -> Result<Placed, LoweringRefusal<'source>>
{
    match run {
        | Run::One(operand) => Ok(operand),
        | Run::Empty(gap) => Err(LoweringRefusal::MalformedForm {
            span: gap,
            form,
            fault: FormFault::MissingOperand,
        }),
        | Run::Several { extra, .. } => Err(extra_operand(form, extra)),
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

/// The refusal a module whose own pieces hold `repair` at `span` earns.
///
/// # Specification
/// trivial.
const fn repaired_module<'source>(
    span: ByteSpan,
    repair: Repair,
) -> LoweringRefusal<'source>
{
    LoweringRefusal::MalformedForm {
        span,
        form: FormName::MODULE,
        fault: FormFault::Repaired(repair),
    }
}

/// Read a declaration form's tail, after its name.
///
/// # Specification
/// - requires: `header` stands just past the form's name.
/// - ensures: the half the tail writes, when it is a signature or a definition
///   whose hole holds exactly one form and which closes with `;` and nothing
///   after it; a function tail, opening on `(`, with whether it is signed;
///   every other tail yields its first fault — an implicit telescope declined
///   by the folded form's own name, an empty or overfull hole, or a tile out of
///   place.
/// - provides: the tail half of a declaration form.
/// - fails: never; a fault is yielded rather than raised.
/// - panics: none.
fn read_tail<'source>(
    header: &mut Cursor<'_>,
    declaration: Placed,
) -> Tail<'source>
{
    if let Maybe::Present(_) = header.at(TileName::PAREN_OPEN) {
        return Tail::Function(signing(header.clone()));
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
        | Run::One(operand) => operand,
        | Run::Empty(gap) => {
            return Tail::Refused(LoweringRefusal::MalformedForm {
                span: gap,
                form: FormName::DECLARATION,
                fault: FormFault::MissingOperand,
            });
        },
        | Run::Several { extra, .. } => {
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
fn signing(mut header: Cursor<'_>) -> Signing
{
    let _open = header.tile(TileName::PAREN_OPEN);
    loop {
        match header.read() {
            | Maybe::Present(Piece::Tile { label, .. }) if label == TileName::PAREN_CLOSE => break,
            | Maybe::Present(Piece::Tile { label, .. }) if TileName::BINDERS.contains(&label) => {
                if let Maybe::Absent(_) = header.at(TileName::COLON) {
                    return Signing::Unsigned;
                }
            },
            | Maybe::Present(Piece::Tile { .. } | Piece::Operand(_)) => {},
            | Maybe::Absent(_) => return Signing::Unsigned,
        }
    }
    match header.at(TileName::ARROW) {
        | Maybe::Present(_) => Signing::Signed,
        | Maybe::Absent(_) => Signing::Unsigned,
    }
}

/// The refusal a tail that is neither a signature, a definition nor a function
/// earns.
///
/// # Specification
/// - requires: `header` stands just past the form's name, at no `:`, `=` or
///   `(`.
/// - ensures: an implicit telescope is declined as a form the fragment does not
///   admit, by the folded form's own name; an operand is one the form does not
///   take; every other piece is a misplaced tile.
/// - provides: the decline of the declaration tails the fragment does not read.
/// - fails: never.
/// - panics: none.
fn unadmitted_tail<'source>(
    header: &Cursor<'_>,
    declaration: Placed,
) -> LoweringRefusal<'source>
{
    if let Maybe::Present(_) = header.at(TileName::ATTRIBUTES) {
        return unadmitted(declaration, FormName::PARAMETERS);
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

/// The refusal a declaration tail the fragment does not admit earns.
///
/// # Specification
/// trivial.
const fn unadmitted<'source>(
    declaration: Placed,
    form: FormName,
) -> LoweringRefusal<'source>
{
    LoweringRefusal::OutOfFragment {
        span: declaration.span,
        form,
        sort: FragmentSort::Declaration,
        boundary: FragmentBoundary::Unadmitted,
    }
}

/// What a name's declarations amount to once the module has been walked.
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
    /// The declaration's first refusal.
    Refused(LoweringRefusal<'source>),
}

/// The parts of one lowered declaration, as the pass that assembles a module
/// gathers them.
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
    /// The opaque handle a checker echoes back in place of that span.
    pub origin: OriginToken,
    /// The content identity of this name's signature form.
    pub signature: Maybe<NodeDigest, declaration_half::Absent>,
    /// The content identity of this name's definition form.
    pub definition: Maybe<NodeDigest, declaration_half::Absent>,
    /// What the name's declarations amount to.
    pub outcome: DeclarationOutcome<'source>,
}

/// One declared name, lowered.
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

    /// The content identity of this name's signature form, the key its
    /// attributes are filed under.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub const fn signature(&self) -> Maybe<NodeDigest, declaration_half::Absent>
    {
        self.parts.signature
    }

    /// The content identity of this name's definition form, the key its
    /// attributes are filed under.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub const fn definition(&self) -> Maybe<NodeDigest, declaration_half::Absent>
    {
        self.parts.definition
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
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct ValueComponent<'source>
{
    /// The component's name.
    pub name: SurfaceName<'source>,
    /// The admission position of the member it resolves to.
    pub constant: ConstantIndex,
}

/// One manifest type component of a lowered module.
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
    /// The manifest type components, in signature order.
    types: Vec<ManifestComponent<'source>>,
    /// Whether matching against a signature coerced the body.
    coerced: Coerced,
}

impl<'source> LoweredStructure<'source>
{
    /// The stratum item holding these parts.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn new(
        path: Vec<SurfaceName<'source>>,
        span: ByteSpan,
        values: Vec<ValueComponent<'source>>,
        modules: Vec<SurfaceName<'source>>,
        types: Vec<ManifestComponent<'source>>,
        coerced: Coerced,
    ) -> Self
    {
        Self {
            path,
            span,
            values,
            modules,
            types,
            coerced,
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

    /// The manifest type components, in signature order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn types(&self) -> &[ManifestComponent<'source>]
    {
        &self.types
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
}

/// One module, lowered: its declarations, its attributes, its origins, its
/// imports, and the outermost scope its names were declared in.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct LoweredModule<'source>
{
    /// The declarations, in admission order.
    declarations: Vec<LoweredDeclaration<'source>>,
    /// The modules, in pre-order: a module before every module nested in it.
    structures: Vec<LoweredStructure<'source>>,
    /// The attribute side table, keyed by declaration content identity.
    attributes: AttributeTable,
    /// Every minted core node's origin, and the declarations' own.
    origins: OriginTable,
    /// The imports, in source order, with their aliases bound.
    imports: ModuleImports<'source>,
    /// The outermost scope, with every declared name declared in it.
    recognition: Recognition,
}

impl<'source> LoweredModule<'source>
{
    /// The module holding these parts, for the pass that assembles one.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn new(
        declarations: Vec<LoweredDeclaration<'source>>,
        structures: Vec<LoweredStructure<'source>>,
        attributes: AttributeTable,
        origins: OriginTable,
        imports: ModuleImports<'source>,
        recognition: Recognition,
    ) -> Self
    {
        Self {
            declarations,
            structures,
            attributes,
            origins,
            imports,
            recognition,
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
    #[inline]
    #[must_use]
    pub fn path_of(
        &self,
        declaration: &LoweredDeclaration<'source>,
    ) -> Vec<SurfaceName<'source>>
    {
        let mut path = match declaration.container() {
            | Container::TopLevel => Vec::new(),
            | Container::Module(structure) => self
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
    /// - ensures: one entry per declaration whose role is [`Role::Declared`],
    ///   at its admission position, holding [`Self::path_of`] segment for
    ///   segment; a witness and a held declaration declare no name and take no
    ///   entry.
    /// - provides: the name each flattened member is exported under, while
    ///   every reference still reads the admission position.
    /// - fails: never; a surface name never holds the segment separator.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a module nesting a member five segments deep beside a
    ///   witness and a top-level declaration, exported through the checker and
    ///   decoded, each declaration asserted at its exact name.
    /// - witness: `modules::modules::modules_lower_to_named_member_declarations`
    #[inline]
    #[must_use]
    pub fn structured_names(&self) -> BTreeMap<ConstantIndex, StructuredName>
    {
        let mut names = BTreeMap::new();
        for declaration in &self.declarations {
            if declaration.role() != Role::Declared {
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

    /// The scope the imports' aliases are bound in: each alias resolves to
    /// its import's position, tagged with the import's bytes, and the export
    /// is empty.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn import_scope(&self) -> &Scope<ImportIndex, ByteSpan>
    {
        self.imports.scope()
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

    use gandr_kernel_term::ConstantIndex;
    use gandr_surface_grammar::NamedKind;
    use gandr_surface_syntax::ByteOffset;
    use gandr_surface_syntax::NodeIndex;
    use gandr_surface_syntax::SourceText;
    use quenchant_shape::shape::Maybe;

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
    use crate::fixture::span;
    use crate::form::FormName;
    use crate::form::Placed;
    use crate::lower::Fuel;
    use crate::lower::LoweringBudget;
    use crate::resolve::SurfaceName;

    /// A tank generous enough for a fixture-sized module.
    ///
    /// # Specification
    /// trivial.
    fn tank() -> Fuel
    {
        Fuel::new(LoweringBudget::DEFAULT)
    }

    #[test]
    fn a_signature_pairs_with_its_definition()
    {
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));
        let pbg = grammar();
        let tree = parsed(&pbg, SourceText::from("def x : Integer ; def x = 3 ;"));
        let collected = collect(&pbg, &tree, &mut tank()).unwrap();

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
        let collected = collect(&pbg, &tree, &mut tank()).unwrap();

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
        let collected = collect(&pbg, &tree, &mut tank()).unwrap();
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
        let collected = collect(&pbg, &tree, &mut tank()).unwrap();
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
            collect(&pbg, &tree, &mut tank()).unwrap_err(),
            LoweringRefusal::OutOfFragment {
                span: span(ByteOffset::from(0_usize), ByteOffset::from(1_usize)),
                form: FormName::from(NamedKind("number")),
                sort: FragmentSort::Declaration,
                boundary: FragmentBoundary::WrongSort,
            },
            "a module child that is not a declaration refuses the module"
        );
    }

    #[test]
    fn a_declaration_missing_its_body_is_refused()
    {
        let pbg = grammar();
        let tree = parsed(&pbg, SourceText::from("def x = ;"));
        let collected = collect(&pbg, &tree, &mut tank()).unwrap();
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
            collect(&pbg, &tree, &mut tank()).unwrap_err(),
            LoweringRefusal::OutOfFragment {
                span: at(4_usize, 5_usize),
                form: FormName::from(NamedKind("number")),
                sort: FragmentSort::Declaration,
                boundary: FragmentBoundary::WrongSort,
            },
            "a declaration's name is an identifier tile, and nothing can be filed without one"
        );
    }

    #[test]
    fn a_trailing_attribute_block_refuses_the_module()
    {
        let pbg = grammar();
        let tree = parsed(&pbg, SourceText::from("def x = 3 ; @[ checks ]"));

        assert_eq!(
            collect(&pbg, &tree, &mut tank()).unwrap_err(),
            LoweringRefusal::OutOfFragment {
                span: span(ByteOffset::from(12_usize), ByteOffset::from(23_usize)),
                form: FormName::from(NamedKind("attribute_block")),
                sort: FragmentSort::Declaration,
                boundary: FragmentBoundary::WrongSort,
            },
            "an attribute block decorates the declaration after it, so a trailing one decorates \
             nothing"
        );
    }

    #[test]
    fn an_attribute_block_decorates_the_declaration_after_it()
    {
        let pbg = grammar();
        let tree = parsed(&pbg, SourceText::from("@[ checks ] @[ owes ] def x = 3 ;"));
        let collected = collect(&pbg, &tree, &mut tank()).unwrap();
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
            container: Container::TopLevel,
            role: Role::Declared,
            constant: ConstantIndex::from(0_usize),
            introduced_by: introduced,
            named: introduced,
            signature: Maybe::<Half, _>::Absent(declaration_half::Absent::Unwritten),
            definition: Maybe::Absent(declaration_half::Absent::Unwritten),
            attributes: Vec::new(),
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
