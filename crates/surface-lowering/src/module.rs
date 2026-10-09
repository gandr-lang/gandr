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
use gandr_surface_grammar::Pbg;
use gandr_surface_syntax::ByteSpan;
use gandr_surface_syntax::NodeDigest;
use gandr_surface_syntax::NodeIndex;
use gandr_surface_syntax::SourceFragment;
use gandr_surface_syntax::SyntaxTree;
use quenchant_shape::shape::Maybe;

use crate::attribute::AttributeTable;
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

/// What one half of a declared name lowers from.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Operand
{
    /// The one form written in the hole of `: T ;` or `= e ;`.
    Written(Placed),
    /// The function tail `(params) -> T? { … }`, lowered at the declaration
    /// form itself.
    Function,
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
    /// Each declared name's slot, for the term-name resolution table.
    pub by_name: BTreeMap<SurfaceName<'source>, SlotIndex>,
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
        collected: Collected {
            slots: Vec::new(),
            owner,
            by_name: BTreeMap::new(),
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
        fuel.spend()?;
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
    /// - ensures: a declaration form is collected into its slot and an import
    ///   into the import list; every other form refuses the module as a form of
    ///   the wrong sort.
    /// - provides: the module-shape half of [`collect`].
    /// - fails: [`LoweringRefusal::OutOfFragment`] for a child that is neither
    ///   a declaration nor an import, and every module-level fault
    ///   [`Self::declaration`] and [`Self::import`] raise.
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
        let outcome = self.read_declaration(declaration, &pieces);
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

    /// Read one declaration form's pieces into its slot.
    ///
    /// # Specification
    /// - requires: `pieces` is the reading of the form `declaration`.
    /// - ensures: as [`Self::declaration`].
    /// - provides: the reading half of [`Self::declaration`], over a borrowed
    ///   reading.
    /// - fails: as [`Self::declaration`].
    /// - panics: none.
    ///
    /// # Errors
    /// As [`Self::declaration`].
    fn read_declaration(
        &mut self,
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
        let slot = self.admit(name, declaration, named);
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
    ///   of them; a clean form's attributes join the slot's in source order,
    ///   once whatever the halves it writes.
    /// - provides: the filing half of [`Self::declaration`].
    /// - fails: never.
    /// - panics: none.
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
        for &kind in kinds {
            let held = match kind {
                | HalfKind::Signature => entry.signature,
                | HalfKind::Definition => entry.definition,
            };
            if let Maybe::Present(first) = held {
                let (span, name, first) = (declaration.span, entry.name, first.declaration.span);
                let refusal = match kind {
                    | HalfKind::Signature => {
                        LoweringRefusal::DuplicateSignature { span, name, first }
                    },
                    | HalfKind::Definition => {
                        LoweringRefusal::DuplicateDefinition { span, name, first }
                    },
                };
                entry.refuse(declaration.node, refusal);
                return;
            }
        }
        for &kind in kinds {
            let held = match kind {
                | HalfKind::Signature => &mut entry.signature,
                | HalfKind::Definition => &mut entry.definition,
            };
            *held = Maybe::Present(Half {
                declaration,
                operand,
            });
        }
        entry.attributes.extend(attributes);
    }

    /// The slot `name` occupies, creating it at the next admission position
    /// when this is the name's first declaration, written by the tile `named`
    /// of the form `declaration`.
    ///
    /// # Specification
    /// - requires: the collection's slots and name table describe the same
    ///   collection so far.
    /// - ensures: a name already declared keeps its admission position, and a
    ///   fresh name takes the next one; the returned index always names a live
    ///   slot.
    /// - provides: the collect-by-name half of the pass.
    /// - fails: never.
    /// - panics: none.
    fn admit(
        &mut self,
        name: SurfaceName<'source>,
        declaration: Placed,
        named: Placed,
    ) -> SlotIndex
    {
        if let Some(&existing) = self.collected.by_name.get(&name) {
            return existing;
        }
        let minted = SlotIndex(self.collected.slots.len());
        self.collected.slots.push(DeclarationSlot {
            name,
            constant: ConstantIndex::from(minted.0),
            introduced_by: declaration,
            named,
            signature: Maybe::Absent(declaration_half::Absent::Unwritten),
            definition: Maybe::Absent(declaration_half::Absent::Unwritten),
            attributes: Vec::new(),
            refusal: Maybe::Absent(slot_refusal::Absent::Unrefused),
        });
        self.collected.by_name.insert(name, minted);

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

/// One module, lowered: its declarations, its attributes, its origins, its
/// imports, and the outermost scope its names were declared in.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct LoweredModule<'source>
{
    /// The declarations, in admission order.
    declarations: Vec<LoweredDeclaration<'source>>,
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
        attributes: AttributeTable,
        origins: OriginTable,
        imports: ModuleImports<'source>,
        recognition: Recognition,
    ) -> Self
    {
        Self {
            declarations,
            attributes,
            origins,
            imports,
            recognition,
        }
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

    use super::DeclarationSlot;
    use super::Half;
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
