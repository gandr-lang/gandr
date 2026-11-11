//! A path between two signatures, as the collection pass reads it: `path p :
//! V1 <~> V2 where { into where { … } from where { … } }`, two flows, one each
//! way, whose round trips conversion decides. The minting half lives with the
//! lowering (`crate::lower::path`).
//!
//! # A path is a module of two functions and their round trips
//!
//! The path `p` is collected as a module of its name. Each body is collected
//! as a flow's body is, a functor template whose parameter is its domain's
//! model and whose body reads the domain's members by name
//! ([`BodyScope::Path`]). The template never reaches the kernel, and no import
//! and no application names it. The module declares one function for each
//! body, `p.into : (s : Model(V1)) -> Model(V2)` and `p.from : (s :
//! Model(V2)) -> Model(V1)`: the lowering mints each as the template's
//! members, each a definition over the bound model `s`, packed as a model of
//! the codomain. The module also holds one round trip for each sort and each
//! value member of each signature, a witness that enters no name table: for
//! a member `m` of `V1`, `(s : Model(V1)) -> Path(p.from(p.into(s)).m,
//! s.m)`, checked as `Path.here(s.m)`. Conversion decides each over the bound
//! variable.
//!
//! - Choice: a body is a function between packed models, and a round trip a
//!   definition over the bound model, so the checker decides a round trip at a
//!   definition it already checks. Alternatives: an instance of the template at
//!   an abstract model, a new kind of instance. Reversal: none foreseen; the
//!   function is the template's substitution of the bound model.
//! - Choice: a round trip is stated for each sort without indices, each
//!   operation and each constant; a sort's is a path between codes. A law is
//!   carried by the operations it relates. Alternatives: no round trip for a
//!   sort, which accepts a path that loses a sort no operation reads. Reversal:
//!   a law whose proofs differ, which waits on the authored homotopy (#3462),
//!   and a family sort, which waits on its code's path.
//!
//! # References
//!
//! - `vault:01a178ab-289d-7702-b010-1c47ae9fd427` — lineage: the univalence
//!   design (§ The trust story) — a path between signatures is supplied, its
//!   two round trips its evidence.
//! - `vault:01a178aa-9a6d-7c20-a9c5-131d35beda06` — lineage: the
//!   directed-univalence design (§ The surface family) — a flow is a function
//!   between the models of two signatures, and a path two of them.

use alloc::collections::BTreeMap;
use alloc::vec::Vec;

use anodized::spec;
use gandr_kernel_term::ConstantIndex;
use quenchant_shape::shape::Maybe;

use super::Coerced;
use super::Collector;
use super::ComponentPlace;
use super::Container;
use super::DeclarationSlot;
use super::Header;
use super::Open;
use super::Opened;
use super::Role;
use super::Sealed;
use super::SlotIndex;
use super::Structure;
use super::StructureIndex;
use super::ascription;
use super::declaration_half;
use super::derived;
use super::functor::BodyScope;
use super::functor::FunctorIndex;
use super::functor::Stratum;
use super::functor::TheoryPath;
use super::functor::WrittenParameter;
use super::misplaced_in;
use super::slot_refusal;
use crate::error::LoweringRefusal;
use crate::form::Cursor;
use crate::form::FormName;
use crate::form::Piece;
use crate::form::Pieces;
use crate::form::Placed;
use crate::form::TileName;
use crate::model::ModelForm;
use crate::resolve::SurfaceName;

/// Which body of a path a part of it belongs to.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Side
{
    /// `into`, from the domain's models to the codomain's.
    Into,
    /// `from`, from the codomain's models back to the domain's.
    From,
}

/// One round trip of a path: the witness that a member comes back to itself
/// through both bodies.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct RoundTrip<'source>
{
    /// The body the trip ends with: `from` for a member of the domain, `into`
    /// for a member of the codomain.
    pub side: Side,
    /// The member's name.
    pub name: SurfaceName<'source>,
    /// The member's place in its signature.
    pub component: ComponentPlace,
    /// The witness.
    pub slot: SlotIndex,
}

/// A path as the collection found it.
///
/// # Specification
/// - requires: nothing to construct this data; the collection produces it.
/// - ensures: the module holds the two functions and the round trips; each body
///   is a functor whose scope is [`BodyScope::Path`].
/// - fails: not applicable to the data item.
/// - panics: not applicable to the data item.
/// - executable: none — the indices are not checked against a collection.
///
/// # Adequacy
/// - hypothesis: L3 — a path declares its two functions and one round trip for
///   each value member of its two signatures, and a second path of one name is
///   refused at it.
/// - witness: `tests::modules::paths::a_path_lowers_to_its_functions_and_its_round_trips_3487`
/// - witness: `tests::modules::paths::a_path_named_twice_is_refused_3487`
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PathDeclaration<'source>
{
    /// The path's name.
    pub name: SurfaceName<'source>,
    /// The path form.
    pub declared_by: Placed,
    /// The module the path declares.
    pub structure: StructureIndex,
    /// The body `into` and the function it lowers to.
    pub into: (FunctorIndex, SlotIndex),
    /// The body `from` and the function it lowers to.
    pub from: (FunctorIndex, SlotIndex),
    /// The round trips, the domain's members first.
    pub trips: Vec<RoundTrip<'source>>,
}

impl PathDeclaration<'_>
{
    /// The body on `side` and the function it lowers to.
    ///
    /// # Specification
    /// trivial.
    #[must_use]
    pub const fn body(
        &self,
        side: Side,
    ) -> (FunctorIndex, SlotIndex)
    {
        match side {
            Side::Into => self.into,
            Side::From => self.from,
        }
    }
}

/// A path's header and its two bodies, as [`Collector::path_header`] reads
/// them.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug)]
pub(super) struct PathHeader<'source>
{
    /// The path's name.
    name: SurfaceName<'source>,
    /// The name's tile.
    named: Placed,
    /// The body `into`, read as a flow's header from `V1` to `V2`.
    into: Opened<'source>,
    /// The body `from`, read as a flow's header from `V2` to `V1`.
    from: Opened<'source>,
}

impl PathHeader<'_>
{
    /// The tile naming the path.
    ///
    /// # Specification
    /// trivial.
    pub(super) const fn named(&self) -> Placed
    {
        self.named
    }
}

impl<'source> Collector<'_, 'source>
{
    /// Read a path's header past its `path` keyword: its name, its two
    /// signatures and its two bodies.
    ///
    /// # Specification
    /// - requires: `cursor` stands just past the `path` keyword of the form
    ///   `form`, whose reading is `pieces`.
    /// - ensures: the path when its tiles read `path name : V1 ≃ V2 { into {
    ///   members } from { members } }`, each body opened as a flow's is, its
    ///   parameter named by its domain's last name with the model its domain
    ///   derives and [`BodyScope::Path`], its ascription the model its codomain
    ///   derives; a repair no operand carries, a tile out of place, or a
    ///   signature [`Self::presented_model`] refuses refuses the path under its
    ///   name; a path with no name is unnamed.
    /// - provides: the path half of [`Self::header`].
    /// - fails: never; every fault of the form is yielded.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a path whose bodies read their domains' members by
    ///   name checks, and one whose domain names no theory is refused under its
    ///   name.
    /// - witness: `tests::modules::paths::a_path_lowers_to_its_functions_and_its_round_trips_3487`
    /// - witness: `tests::modules::paths::a_path_from_no_theory_is_refused_under_its_name_3487`
    #[spec(ensures: |ret| match ret {
        | Header::Path(ref path) => matches!(path.into.parameter, Maybe::Present(ref parameter) if matches!(parameter.scope, BodyScope::Path { .. }))
            && matches!(path.from.parameter, Maybe::Present(ref parameter) if matches!(parameter.scope, BodyScope::Path { .. })),
        | Header::Refused { .. } | Header::Unnamed(_) => true,
        | Header::Opened(_) | Header::Applied(_) => false,
    })]
    pub(super) fn path_header(
        &mut self,
        form: Placed,
        cursor: &mut Cursor<'_>,
        pieces: &Pieces,
    ) -> Header<'source>
    {
        let Maybe::Present(named) = cursor.tile(TileName::IDENTIFIER)
        else {
            return Header::Unnamed(match pieces.repair {
                Maybe::Present(repaired) => repaired.refusal(FormName::PATH),
                Maybe::Absent(_) => misplaced_in(FormName::PATH, cursor.here()),
            });
        };
        let name = self.name_of(named);
        let refused = |refusal| Header::Refused {
            name,
            named,
            refusal,
        };
        if let Maybe::Present(repaired) = pieces.repair
            && !self.carried(pieces).0
        {
            return refused(repaired.refusal(FormName::PATH));
        }
        if let Maybe::Absent(_) = cursor.tile(TileName::COLON) {
            return refused(misplaced_in(FormName::PATH, cursor.here()));
        }
        let (domain, domain_prefix) = match self.theory_path(cursor, FormName::PATH) {
            Ok(path) => path,
            Err(refusal) => return refused(refusal),
        };
        if let Maybe::Absent(_) = cursor.tile(TileName::EQUIVALENCE) {
            return refused(misplaced_in(FormName::PATH, cursor.here()));
        }
        let (codomain, codomain_prefix) = match self.theory_path(cursor, FormName::PATH) {
            Ok(path) => path,
            Err(refusal) => return refused(refusal),
        };
        if let Maybe::Absent(_) = cursor.tile(TileName::WHERE) {
            return refused(misplaced_in(FormName::PATH, cursor.here()));
        }
        if let Maybe::Absent(_) = cursor.tile(TileName::BRACE_OPEN) {
            return refused(misplaced_in(FormName::PATH, cursor.here()));
        }
        let Maybe::Present((into, into_members)) = Self::path_body(cursor, TileName::INTO)
        else {
            return refused(misplaced_in(FormName::PATH, cursor.here()));
        };
        let Maybe::Present((from, from_members)) = Self::path_body(cursor, TileName::FROM)
        else {
            return refused(misplaced_in(FormName::PATH, cursor.here()));
        };
        if let Maybe::Absent(_) = cursor.tile(TileName::BRACE_CLOSE) {
            return refused(misplaced_in(FormName::PATH, cursor.here()));
        }
        if let Maybe::Present(_) = cursor.peek() {
            return refused(misplaced_in(FormName::PATH, cursor.here()));
        }
        let (domain_components, domain_model, domain_used) =
            match self.presented_model(form, FormName::PATH, domain, &domain_prefix, &[]) {
                Ok(read) => read,
                Err(refusal) => return refused(refusal),
            };
        let (codomain_components, codomain_model, codomain_used) =
            match self.presented_model(form, FormName::PATH, codomain, &codomain_prefix, &[]) {
                Ok(read) => read,
                Err(refusal) => return refused(refusal),
            };
        self.collected.declared_uses.push(domain_used);
        self.collected.declared_uses.push(codomain_used);
        let domain_path = TheoryPath {
            prefix: domain_prefix,
            named: domain,
        };
        let codomain_path = TheoryPath {
            prefix: codomain_prefix,
            named: codomain,
        };

        Header::Path(alloc::boxed::Box::new(PathHeader {
            name,
            named,
            into: Opened {
                name: self.name_of(into),
                named: into,
                ascription: Maybe::Present(codomain_components.clone()),
                model: Maybe::Present((codomain_model.clone(), codomain_used.1)),
                sealed: Sealed(false),
                members: into_members,
                parameter: Maybe::Present(WrittenParameter {
                    name: self.name_of(domain),
                    named: domain,
                    components: domain_components.clone(),
                    model: Maybe::Present(domain_model.clone()),
                    scope: BodyScope::Path {
                        domain: domain_path.clone(),
                        codomain: codomain_path.clone(),
                    },
                }),
            },
            from: Opened {
                name: self.name_of(from),
                named: from,
                ascription: Maybe::Present(domain_components),
                model: Maybe::Present((domain_model, domain_used.1)),
                sealed: Sealed(false),
                members: from_members,
                parameter: Maybe::Present(WrittenParameter {
                    name: self.name_of(codomain),
                    named: codomain,
                    components: codomain_components,
                    model: Maybe::Present(codomain_model),
                    scope: BodyScope::Path {
                        domain: codomain_path,
                        codomain: domain_path,
                    },
                }),
            },
        }))
    }

    /// Read one body of a path, `keyword where { members }`, past its last
    /// brace.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the keyword's tile and the body's member forms when the tiles
    ///   read `keyword where { members }`; absent, the cursor at the first tile
    ///   out of place, otherwise.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the cursor exposes no tile it has read.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::path_header`].
    /// - witness: `tests::modules::paths::a_path_lowers_to_its_functions_and_its_round_trips_3487`
    fn path_body(
        cursor: &mut Cursor<'_>,
        keyword: TileName,
    ) -> Maybe<(Placed, Vec<Placed>), declaration_half::Absent>
    {
        let unwritten = Maybe::Absent(declaration_half::Absent::Unwritten);
        let Maybe::Present(at) = cursor.tile(keyword)
        else {
            return unwritten;
        };
        if let Maybe::Absent(_) = cursor.tile(TileName::WHERE) {
            return unwritten;
        }
        if let Maybe::Absent(_) = cursor.tile(TileName::BRACE_OPEN) {
            return unwritten;
        }
        let mut members = Vec::new();
        while let Maybe::Present(Piece::Operand(member)) = cursor.peek() {
            let _member = cursor.read();
            members.push(member);
        }
        if let Maybe::Absent(_) = cursor.tile(TileName::BRACE_CLOSE) {
            return unwritten;
        }

        Maybe::Present((at, members))
    }

    /// Collect the path `path`, written by the top-level form `form` in
    /// `container`: its module, its two bodies, its two functions and its
    /// round trips.
    ///
    /// # Specification
    /// - requires: `path` is the header [`Self::path_header`] read off `form`.
    /// - ensures: a path whose name a module already takes refuses a held slot
    ///   under its name; otherwise the path's module is the next module, under
    ///   its name, then each body is collected whole as a flow's body is,
    ///   `into` first, then the module admits the functions `into` and `from`
    ///   under their keywords' names and one round trip, a witness entered in
    ///   no name table, for each sort without indices, each operation and each
    ///   constant of each signature, the domain's first; the path is recorded.
    /// - provides: the path half of [`Self::module`].
    /// - fails: the refusals reading a body's members raises:
    ///   [`LoweringRefusal::UnknownMold`] and
    ///   [`LoweringRefusal::BudgetExceeded`].
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoweringRefusal::UnknownMold`] and
    /// [`LoweringRefusal::BudgetExceeded`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`PathDeclaration`].
    /// - witness: `tests::modules::paths::a_path_lowers_to_its_functions_and_its_round_trips_3487`
    /// - witness: `tests::modules::paths::a_path_named_twice_is_refused_3487`
    #[spec(
        captures: before = self.collected.paths.len(),
        ensures: |ret| ret.is_err() || self.collected.paths.len() <= before.saturating_add(1),
    )]
    pub(super) fn path(
        &mut self,
        container: Container,
        form: Placed,
        path: &PathHeader<'source>,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        if let Some(&first) = self.collected.modules.get(&(container, path.name)) {
            let first = self
                .collected
                .structures
                .get(first.0)
                .map_or(form.span, |earlier| earlier.named.span);
            let refusal = LoweringRefusal::DuplicateDefinition {
                span: path.named.span,
                name: path.name,
                first,
            };
            let _held = self.refuse_held(container, path.name, form, path.named, refusal);
            return Ok(());
        }
        let structure = StructureIndex(self.collected.structures.len());
        self.collected.structures.push(Structure {
            name: path.name,
            container,
            declared_by: form,
            named: path.named,
            ascription: Maybe::Absent(ascription::Absent::Unascribed),
            model: Maybe::Absent(derived::Absent::Written),
            sealed: Sealed(false),
            members: Vec::new(),
            exports: Vec::new(),
            types: Vec::new(),
            type_members: Vec::new(),
            exported_as: BTreeMap::new(),
            stated_at: Vec::new(),
            coerced: Coerced(false),
            stratum: Stratum::Module,
        });
        self.collected
            .modules
            .insert((container, path.name), structure);
        self.document_module(form.node, path.named.span.start(), form.node);
        let within = Container::Module(structure);
        let into = self.path_side(within, form, path.into.clone())?;
        let from = self.path_side(within, form, path.from.clone())?;
        let into_slot = self.admit(within, path.into.name, form, path.into.named);
        let from_slot = self.admit(within, path.from.name, form, path.from.named);
        let mut trips = Vec::new();
        for (side, body, opened) in [
            (Side::From, from, &path.into),
            (Side::Into, into, &path.from),
        ] {
            let Maybe::Present(ref parameter) = opened.parameter
            else {
                continue;
            };
            let Maybe::Present(ref model) = parameter.model
            else {
                continue;
            };
            for (component, derived) in model.components.iter().enumerate() {
                let tripped = match derived.form {
                    Ok(ModelForm::Operation { .. } | ModelForm::Constant(_)) => true,
                    Ok(ModelForm::Sort { ref indices, .. }) => indices.is_empty(),
                    Ok(ModelForm::Law { .. } | ModelForm::Nested(_)) | Err(_) => false,
                };
                if !tripped {
                    continue;
                }
                let name = self.name_of(derived.named);
                // The member's expectation states what its round trip settles
                // to: the template yields no declaration to read it.
                let (named, attributes) = match self
                    .defined_in(body, name)
                    .and_then(|defining| self.collected.slots.get_mut(defining.0))
                {
                    Some(member) => (
                        member.introduced_by,
                        core::mem::take(&mut member.attributes),
                    ),
                    None => (form, Vec::new()),
                };
                let slot = SlotIndex(self.collected.slots.len());
                self.collected.slots.push(DeclarationSlot {
                    name,
                    container: within,
                    role: Role::Witness,
                    constant: ConstantIndex::from(slot.0),
                    introduced_by: named,
                    named,
                    signature: Maybe::Absent(declaration_half::Absent::Unwritten),
                    definition: Maybe::Absent(declaration_half::Absent::Unwritten),
                    attributes,
                    docs: Vec::new(),
                    refusal: Maybe::Absent(slot_refusal::Absent::Unrefused),
                });
                trips.push(RoundTrip {
                    side,
                    name,
                    component: ComponentPlace(component),
                    slot,
                });
            }
        }
        self.close(structure, &[])?;
        self.collected.paths.push(PathDeclaration {
            name: path.name,
            declared_by: form,
            structure,
            into: (into, into_slot),
            from: (from, from_slot),
            trips,
        });

        Ok(())
    }

    /// Collect one body of a path, `opened`, as a flow's body in `container`:
    /// a functor whose body enters no name table and no module's members.
    ///
    /// # Specification
    /// - requires: `opened` carries its parameter, as [`Self::path_header`]
    ///   reads it.
    /// - ensures: the body is the next module, its parameter after it, and
    ///   every member of the body and of the modules it nests is read before
    ///   the functor closes; the functor is returned.
    /// - fails: as [`Self::path`].
    /// - panics: none.
    ///
    /// # Errors
    /// As [`Self::path`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::path`].
    /// - witness: `tests::modules::paths::a_path_lowers_to_its_functions_and_its_round_trips_3487`
    #[spec(
        captures: before = self.collected.functors.len(),
        ensures: |ret| ret.as_ref().map_or(true, |functor| functor.0 == before),
    )]
    fn path_side(
        &mut self,
        container: Container,
        form: Placed,
        opened: Opened<'source>,
    ) -> Result<FunctorIndex, LoweringRefusal<'source>>
    {
        let functor = FunctorIndex(self.collected.functors.len());
        let body = StructureIndex(self.collected.structures.len());
        let model = opened.model.map(|(derived, theory)| {
            let index = super::ModelIndex(self.collected.models.count().0);
            self.collected.models.insert(index, derived);
            let _fresh = self.collected.model_theories.insert(index, theory);
            index
        });
        self.collected.structures.push(Structure {
            name: opened.name,
            container,
            declared_by: form,
            named: opened.named,
            ascription: opened.ascription,
            model,
            sealed: Sealed(false),
            members: Vec::new(),
            exports: Vec::new(),
            types: Vec::new(),
            type_members: Vec::new(),
            exported_as: BTreeMap::new(),
            stated_at: Vec::new(),
            coerced: Coerced(false),
            stratum: Stratum::Module,
        });
        if let Maybe::Present(parameter) = opened.parameter {
            self.declare_parameter(body, parameter);
        }
        let mut stack = alloc::vec![Open {
            structure: body,
            members: opened.members,
            next: 0_usize,
            includes: Vec::new(),
            first: SlotIndex(self.collected.slots.len()),
            inner: Vec::new(),
            blocks: Vec::new(),
            leading: super::Leading(true),
        }];
        self.drain(&mut stack)?;
        self.close_functor(body);

        Ok(functor)
    }

    /// The slot of the member `name` the body `body` of a path defines, a
    /// value member or a type member, when it defines one: its round trip is
    /// placed at it and carries its attributes.
    ///
    /// # Specification
    /// trivial.
    fn defined_in(
        &self,
        functor: FunctorIndex,
        name: SurfaceName<'source>,
    ) -> Option<SlotIndex>
    {
        let body = self.collected.functors.get(functor.0)?.body;
        self.collected
            .by_name
            .get(&(Container::Module(body), name))
            .copied()
            .or_else(|| {
                self.collected
                    .structures
                    .get(body.0)?
                    .types
                    .iter()
                    .find(|component| component.name == name)
                    .map(|component| component.held)
            })
    }
}
