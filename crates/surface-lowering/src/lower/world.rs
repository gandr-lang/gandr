//! Located forms in the lowering: the handle type `A at w`, the hold `hold
//! v`, the opening statement `let x at w = v ;` and the migration
//! `migrate [w] { t }`.
//!
//! # A world is named by its declaration
//!
//! Every position that reads a world — a handle type's, an opening's, a
//! migration's and an entry's — reads a name, resolved as any name is: the
//! innermost binder carrying it, else an earlier declaration. A declaration
//! is the world its admission position names, `World::Declared`; whether that
//! declaration declares a world is the checker's to decide, so a name that
//! resolves to a function is refused there, by the checker's own name for it,
//! at the form that wrote it. A binder names no world, and a name nothing
//! binds is [`LoweringRefusal::UnresolvedName`], as an unbound capability
//! region's is.
//! `T at c` reads its name first: a capability scope binding `c` keeps the
//! capability region reading, so the two at types share their spelling.
//!
//! # Each form lowers to its world form
//!
//! `hold v` is a computation returning the handle, read as a value where a
//! value stands by the nesting every computation there takes.
//! `let x at w = v ;` opens the handle over the rest of its block, binding `x`
//! intuitionistically as `let x = c ;` does, so the rest's indices shift as a
//! bind's do. The opening writes the world it opens at, and the checker
//! refuses one whose handle stands at another. Any other pattern under `at`
//! stays refused. `migrate [w] { t }` reads its block where the migration
//! stands, its last computation the result returned to the world it left.
//! The capability a migration spends is no term: the checker's entry
//! introduces it.
//!
//! - Alternatives: a keyword of its own, `leta x = v ;`, which spent a word on
//!   a binder that `let` already reads; the opening's world left unwritten and
//!   read off the handle, which hides where the binder lives; a world named by
//!   a binder, which presupposes world variables no consumer needs yet.
//! - Reversal: world variables — the name resolves to a binder as well.
//!
//! A handle made at a block's tail is written in parentheses, `(hold v)`. A
//! handle bound for the rest of a block is written `var x : A at w = v ;`: the
//! stated handle type tells it from a held slot.
//!
//! # The mark and the entry are written where the source already decides
//!
//! `mobile type T` marks an abstract component of a sealed signature, which
//! is where its representation is hidden, so the claim that the
//! representation crosses sits beside the seal it is checked against; it
//! lowers to [`crate::module::Mark`] on the component's sealing. An entry is
//! the attribute `@[ entry((home, w, …)) ]`, its home first and then the
//! world of each capability, filed as constants under the declaration's keys
//! ([`crate::LoweredModule::worlds`]); a host's own entry is named by the
//! driver and bounds every stated one.
//!
//! - Alternatives: the mark as an attribute, `@[ mobile ]`, which would sit on
//!   the member rather than the signature that seals it; an entry written as a
//!   declaration form, which would need a keyword for what only a host grants.
//! - Reversal: an attribute on signature components, or entries inferred from
//!   the migrations a body makes.
//!
//! # A world's requirement is a row
//!
//! `world w requires [ … ] ;` files its entries as a labelled row writes them
//! ([`crate::LoweredModule::requirement`]). Each interface the requirement
//! names whole also mints into the world's row, held
//! ([`crate::LoweredModule::world_row`]). The checker checks a migration's
//! body under that row, as it checks a definition's body under its declared
//! row. A labelled entry mints no instance yet: the label binders that place
//! it are #6546's.

use alloc::collections::BTreeMap;
use alloc::vec::Vec;

use anodized::spec;
use gandr_core_term::effect::EffectName;
use gandr_core_term::effect::EffectRow;
use gandr_core_term::effect::capability::Region;
use gandr_core_term::world::World;
use gandr_core_term::world::WorldForm;
use gandr_core_term::world::WorldType;
use gandr_kernel_term::ConstantIndex;
pub(super) use gandr_surface_lowering_base::lower::world::Worlded;
use gandr_surface_syntax::ByteSpan;
use quenchant_shape::shape::Maybe;

use super::Lowered;
use super::Lowerer;
use super::Plan;
use super::Produced;
use super::Reading;
use super::Resolved;
use super::Sink;
use super::Site;
use super::Statement;
use super::StatementBinding;
use super::capability::CapabilityRef;
use super::capability::Interface;
use super::capability::Standing;
use super::closed;
use super::exhausted;
use super::exits;
use super::lowered;
use super::unopened;
use crate::error::FormFault;
use crate::error::LoweringRefusal;
use crate::form::Cursor;
use crate::form::FormName;
use crate::form::Former;
use crate::form::Piece;
use crate::form::Pieces;
use crate::form::Placed;
use crate::form::TileName;
use crate::module::RequiredEntry;
use crate::origin::Origin;
use crate::resolve::Frame;
use crate::resolve::SurfaceName;

#[cfg(test)]
mod tests;

impl<'source> Lowerer<'_, 'source>
{
    /// Classify a located computation: `hold v` or `migrate [w] { t }`.
    ///
    /// # Specification
    /// - requires: `site` is a hold or a migration.
    /// - ensures: the form stands as a computation; a hold's value is read as a
    ///   value under the form's frame; a migration's world is the one its name
    ///   resolves to and its block is read under the form's frame, the block's
    ///   last computation its result.
    /// - fails: the wrong-sort refusal where no computation is read;
    ///   [`LoweringRefusal::UnresolvedName`] for a world name no earlier
    ///   declaration answers; a misplaced-tile fault for a form out of shape;
    ///   the hole's and the block's own refusals.
    /// - panics: none.
    ///
    /// # Errors
    /// The form's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a hold and a migration lower to their world forms,
    ///   and a migration to a name nothing declares is refused at the name.
    /// - witness: `lower::world::tests::the_located_forms_lower_to_their_world_forms`
    /// - witness: `lower::world::tests::a_world_named_where_none_is_declared_is_unresolved`
    #[spec(ensures: |ret| ret.is_err() || matches!(self.cx().plans.get(site.at.node), Some(&Plan::World(Worlded::Hold { .. } | Worlded::Migrate { .. }))))]
    #[inline]
    pub fn world_form(
        &mut self,
        site: Site,
        pieces: &Pieces,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let frame = self.require(site, Produced::Computation)?;
        let mut cursor = Cursor::new(&pieces.pieces, site.at.span);
        let Maybe::Present(Piece::Tile { label: keyword, .. }) = cursor.read()
        else {
            return Err(site.fault(cursor.here(), FormFault::MisplacedTile));
        };
        let worlded = if keyword == TileName::HOLD {
            let value = site.one(cursor.operands())?;
            exhausted(site, &cursor)?;
            self.read(value.node, Reading::Value(frame));
            Worlded::Hold { value: value.node }
        }
        else if keyword == TileName::MIGRATE {
            closed(site, &mut cursor, TileName::BRACKET_OPEN)?;
            let Maybe::Present(written) = cursor.tile(TileName::IDENTIFIER)
            else {
                return Err(site.fault(cursor.here(), FormFault::MisplacedTile));
            };
            closed(site, &mut cursor, TileName::BRACKET_CLOSE)?;
            let world = self.world_named(site, frame, written)?;
            let body = self.block(site, &mut cursor, frame)?;
            let _result = self.cx_mut().results.insert(body.last);
            Worlded::Migrate { world, body }
        }
        else {
            return Err(site.fault(site.at.span, FormFault::MisplacedTile));
        };
        self.plan(site, Plan::World(worlded));

        Ok(())
    }

    /// Classify the handle type `T at w`, `w` resolved to the declaration at
    /// `constant`.
    ///
    /// # Specification
    /// - requires: `site` is an at type read as a value type; `operand` is its
    ///   held type.
    /// - ensures: the type stands as the handle to a value of the operand at
    ///   the world the declaration names, the operand read where the at type
    ///   stands.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Errors
    /// None; the result is the shape
    /// [`crate::lower::capability::Capability::at_type`] returns.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a handle at a declared world mints the handle type.
    /// - witness: `lower::world::tests::the_located_forms_lower_to_their_world_forms`
    #[spec(ensures: |ret| ret.is_ok() && matches!(self.cx().plans.get(site.at.node), Some(&Plan::World(Worlded::At { inner, world: World::Declared(declared) })) if inner == operand.node && declared == constant))]
    #[expect(
        clippy::same_name_method,
        reason = "the host's `Families` method of this name calls it"
    )]
    #[inline]
    pub fn located_type(
        &mut self,
        site: Site,
        operand: Placed,
        constant: ConstantIndex,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        self.read(operand.node, site.reading);
        self.plan(
            site,
            Plan::World(Worlded::At {
                inner: operand.node,
                world: World::Declared(constant),
            }),
        );

        Ok(())
    }

    /// The world the name written at `written` names, read under `frame` by
    /// the form at `site`.
    ///
    /// # Specification
    /// - requires: `written` is an identifier tile of the form at `site`.
    /// - ensures: the world an earlier declaration of the name declares, by its
    ///   admission position.
    /// - fails: [`LoweringRefusal::UnresolvedName`] at the name for a name
    ///   nothing binds or a binder carries; the name's own refusals.
    /// - panics: none.
    ///
    /// # Errors
    /// The name's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a declared world resolves to its position and an
    ///   undeclared name is refused at its span.
    /// - witness: `lower::world::tests::the_located_forms_lower_to_their_world_forms`
    /// - witness: `lower::world::tests::a_world_named_where_none_is_declared_is_unresolved`
    #[spec(ensures: |ret| match ret {
        | Err(LoweringRefusal::UnresolvedName { span, .. }) => span == written.span,
        | Ok(World::Declared(_)) | Err(_) => true,
        | Ok(World::Host) => false,
    })]
    fn world_named(
        &mut self,
        site: Site,
        frame: Frame,
        written: Placed,
    ) -> Result<World, LoweringRefusal<'source>>
    {
        let name = self.cx().name_at(written);
        match self.resolve_name(site, frame, name)? {
            Maybe::Present(Resolved::Declaration { constant, .. }) => Ok(World::Declared(constant)),
            Maybe::Present(Resolved::Binder(_)) | Maybe::Absent(_) => {
                Err(LoweringRefusal::UnresolvedName {
                    span: written.span,
                    name,
                })
            },
        }
    }

    /// Read the `let x at w = v ;` statement at `statement`, whose pattern is
    /// the at pattern `pattern` and whose value is `value`, its tiles already
    /// read.
    ///
    /// # Specification
    /// - requires: `pattern` is an at pattern standing as the statement's
    ///   binder; `frame` is the frame the statement reads under.
    /// - ensures: for a name `x`, `w` is resolved as a world and `v` read as a
    ///   value under `frame`; the statement is recorded as the opening of `v`
    ///   at `w` over the rest of the block, and the frame binding `x`
    ///   intuitionistically over `frame` is returned. Any other pattern under
    ///   `at` is absent, so the caller reads it as every other pattern.
    /// - fails: a fault naming the pattern for a tile out of shape, the world
    ///   name's refusal and the binder's own refusal.
    /// - panics: none.
    ///
    /// # Errors
    /// The statement's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a `let x at w` binds its name over the rest of its
    ///   block, which reads it as the innermost variable, and opens the handle
    ///   at the world written.
    /// - witness: `lower::world::tests::the_located_forms_lower_to_their_world_forms`
    #[spec(
        captures: before = self.cx().statements.mark(),
        ensures: |ret| match ret {
            | Ok(Maybe::Present(_)) => self.cx().statements.mark() == before.next()
                && self.cx().statements.last().is_some_and(|last| last.origin == statement.at.node && matches!(last.binding, StatementBinding::Opened { .. })),
            | Ok(Maybe::Absent(_)) | Err(_) => self.cx().statements.mark() == before,
        },
    )]
    #[inline]
    pub fn opened(
        &mut self,
        statement: Site,
        pattern: Placed,
        value: Placed,
        frame: Frame,
    ) -> Result<Maybe<Frame, unopened::Absent>, LoweringRefusal<'source>>
    {
        let mut pieces = Pieces::new();
        super::read_pieces(self.cx().pbg, self.cx().tree, pattern.node, &mut pieces)?;
        if let Maybe::Present(repaired) = pieces.repair {
            return Err(repaired.refusal(FormName::LET_STATEMENT));
        }
        let mut cursor = Cursor::new(&pieces.pieces, pattern.span);
        let binder = statement.one(cursor.operands())?;
        if !matches!(self.cx().form_at(binder)?, Some((_, Former::Name))) {
            return Ok(Maybe::Absent(unopened::Absent::OtherPattern));
        }
        closed(statement, &mut cursor, TileName::AT)?;
        let Maybe::Present(written) = cursor.tile(TileName::IDENTIFIER)
        else {
            return Err(statement.fault(cursor.here(), FormFault::MisplacedTile));
        };
        exhausted(statement, &cursor)?;
        let world = self.world_named(statement, frame, written)?;
        let name = self.shared().binder_name(statement, binder)?;
        self.note_binder(binder, frame, name)?;
        self.read(value.node, Reading::Value(frame));
        self.cx_mut().statements.push(Statement {
            origin: statement.at.node,
            bound: statement.at.node,
            binding: StatementBinding::Opened {
                value: value.node,
                name: binder.node,
                world,
            },
            rest: exits::Rest::Bound,
        });

        Ok(Maybe::Present(Frame::Inner(self.cx_mut().scope.extend(
            frame,
            name,
            Maybe::Present(binder.span),
        ))))
    }

    /// Mint the located form or type `worlded` plans.
    ///
    /// # Specification
    /// - requires: every node the plan names is already minted or absent.
    /// - ensures: the world type or form over its children's lowered nodes at
    ///   `origin`, a migration's block minted as a block; the first absence
    ///   among the children otherwise.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a handle type, a hold and a migration, each minted at
    ///   its own origin.
    /// - witness: `lower::world::tests::the_located_forms_lower_to_their_world_forms`
    #[spec(ensures: |ret| match (worlded, ret) {
        | (Worlded::At { .. }, Maybe::Present(Lowered::ValueType(id))) => sink.origins.value_type(id) == Maybe::Present(origin),
        | (Worlded::Hold { .. } | Worlded::Migrate { .. }, Maybe::Present(Lowered::Computation(id))) => sink.origins.computation(id) == Maybe::Present(origin),
        | (_, Maybe::Present(_)) => false,
        | (_, Maybe::Absent(_)) => true,
    })]
    #[inline]
    pub fn mint_world(
        &self,
        worlded: Worlded,
        sink: &mut Sink<'_>,
        origin: Origin,
    ) -> Maybe<Lowered, lowered::Absent>
    {
        let form = match worlded {
            Worlded::At { inner, world } => {
                return self.cx().value_type_at(inner).map(|inner| {
                    let id = sink.arena.value_type_world(WorldType::At { inner, world });
                    sink.origins.record_value_type(id, origin);
                    Lowered::ValueType(id)
                });
            },
            Worlded::Hold { value } => match self.cx().value_at(value) {
                Maybe::Present(value) => WorldForm::Hold { value },
                Maybe::Absent(reason) => return Maybe::Absent(reason),
            },
            Worlded::Migrate { world, body } => match self.mint_block(body, sink) {
                Maybe::Present(body) => WorldForm::Migrate { world, body },
                Maybe::Absent(reason) => return Maybe::Absent(reason),
            },
        };
        let id = sink.arena.computation_world(form);

        Maybe::Present(sink.computation(id, origin))
    }

    /// Refuse each world of the current source whose requirement row, `world
    /// w requires [ … ] ;`, holds an entry no row admits.
    ///
    /// # Specification
    /// - requires: the current source's collection has run.
    /// - ensures: each world of the current source written with a requirement
    ///   holds, as a fault, the first refusal among its entries in written
    ///   order: an entry's interface resolved as a row resolves it
    ///   ([`crate::lower::capability::CapabilityRef::handled`]), a label read
    ///   as a row reads it, an effect theory under no label
    ///   [`LoweringRefusal::UnlabelledRequirement`], and a label or an
    ///   interface named whole written again
    ///   [`LoweringRefusal::DuplicateDefinition`] at the second. A slot already
    ///   refused, or already faulted, keeps its own.
    /// - fails: never; a refusal is carried by the world.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a world requiring a host interface and a labelled
    ///   theory at its sorts settles; an unlabelled theory, a model theory, a
    ///   sort left unfixed, a name nothing declares and a label written twice
    ///   are each refused at the entry.
    /// - witness: `lower::world::tests::a_world_s_requirement_is_a_row_3523`
    #[spec(
        captures: before = self.cx().collected.slots.len(),
        ensures: self.cx().collected.slots.len() == before,
    )]
    #[inline]
    pub fn check_requirements(&mut self)
    {
        let source = self.cx().current.source;
        let mut refusals = Vec::new();
        let mut hosts = Vec::new();
        for (&slot, entries) in &self.cx().collected.requirements {
            let Some(entry) = self.cx().collected.slots.get(usize::from(slot))
            else {
                continue;
            };
            let Maybe::Present(half) = entry.definition
            else {
                continue;
            };
            if self.cx().collected.unit.source_at(entry.named.span.start()) != source
                || matches!(entry.refusal, Maybe::Present(_))
            {
                continue;
            }
            let site = Site {
                at: half.declaration,
                name: FormName::WORLD_DECLARATION,
                reading: Reading::Unread,
            };
            match self.shared().required(site, entries) {
                Ok(()) => hosts.extend(entries.iter().map(|required| {
                    (
                        required.interface.span().start(),
                        EffectName::from(required.interface.name(self.cx().tree).as_ref()),
                    )
                })),
                Err(refusal) => refusals.push((slot, refusal)),
            }
        }
        // Each host interface a requirement names reaches the import of its
        // module (#4523).
        for (at, named) in hosts {
            self.cx_mut().collected.reach_host(at, &named);
        }
        for (slot, refusal) in refusals {
            let _first = self.cx_mut().faults.entry(slot).or_insert(refusal);
        }
    }

    /// Mint the row each world of the current source requires: its
    /// interfaces named whole, each held.
    ///
    /// # Specification
    /// - requires: [`Self::check_requirements`] has run over the current
    ///   source.
    /// - ensures: each world of the current source written with a requirement,
    ///   neither refused nor faulted, holds in `world_rows` the row of its
    ///   unlabelled entries. Each entry gives its interface
    ///   ([`crate::lower::capability::CapabilityRef::handled`]) at its
    ///   signature ([`crate::lower::capability::CapabilityRef::interface_signature`]),
    ///   held. A labelled entry adds nothing: its instance waits on the label
    ///   binders of #6546. A world with no unlabelled entry holds no row.
    /// - fails: never; a world with an entry that mints no signature holds no
    ///   row, and the requirement check rules that out.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a world requiring a host interface whole holds a row
    ///   of its signature, held; a world requiring nothing and a labelled entry
    ///   add none.
    /// - witness: `lower::world::tests::a_world_s_requirement_mints_its_row_3545`
    #[spec(
        captures: before = self.cx().world_rows.len(),
        ensures: self.cx().world_rows.len() >= before,
    )]
    #[inline]
    pub fn mint_requirements(
        &mut self,
        sink: &mut Sink<'_>,
    )
    {
        let source = self.cx().current.source;
        let mut rows = Vec::new();
        let mut placed = Vec::new();
        for (&slot, entries) in &self.cx().collected.requirements {
            let Some(entry) = self.cx().collected.slots.get(usize::from(slot))
            else {
                continue;
            };
            let Maybe::Present(half) = entry.definition
            else {
                continue;
            };
            if self.cx().collected.unit.source_at(entry.named.span.start()) != source
                || matches!(entry.refusal, Maybe::Present(_))
                || self.cx().faults.contains_key(&slot)
            {
                continue;
            }
            let site = Site {
                at: half.declaration,
                name: FormName::WORLD_DECLARATION,
                reading: Reading::Unread,
            };
            placed.clear();
            let mut minted = true;
            for required in entries {
                if let Maybe::Present(_) = required.label {
                    continue;
                }
                let signature = match (
                    CapabilityRef::new(self.host_ref()).handled(
                        site,
                        &required.interface,
                        required.interface.last.node,
                        &required.manifest,
                    ),
                    self.cx().origin_at(required.interface.last.node),
                ) {
                    (Ok(interface), Maybe::Present(origin)) => CapabilityRef::new(self.host_ref())
                        .interface_signature(&interface, Standing::Read, sink, origin),
                    (Err(_), _) | (_, Maybe::Absent(_)) => Maybe::Absent(lowered::Absent::Unminted),
                };
                let Maybe::Present(signature) = signature
                else {
                    minted = false;
                    break;
                };
                placed.push((signature, Region::Held));
            }
            if !minted || placed.is_empty() {
                continue;
            }
            if let Ok(row) = EffectRow::from_placed(placed.iter().cloned()) {
                rows.push((entry.constant, row));
            }
        }
        self.cx_mut().world_rows.extend(rows);
    }

    /// Read the entries of a requirement row written at `site` as a labelled
    /// row reads its own.
    ///
    /// # Specification
    /// - requires: `entries` are the row's, read off the world declaration
    ///   `site` stands at.
    /// - ensures: nothing, when every entry resolves to an interface, every
    ///   theory stands under a label, and no label and no interface named whole
    ///   is written twice.
    /// - fails: the first refusal in written order.
    /// - panics: none.
    ///
    /// # Errors
    /// The refusals of [`crate::lower::capability::CapabilityRef::handled`] and
    /// [`crate::lower::capability::CapabilityRef::label_of`];
    /// [`LoweringRefusal::UnlabelledRequirement`] at a theory under no label;
    /// [`LoweringRefusal::DuplicateDefinition`] at a name written again.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::check_requirements`].
    /// - witness: `lower::world::tests::a_world_s_requirement_is_a_row_3523`
    #[spec(ensures: |ret| ret.is_ok() || !entries.is_empty())]
    fn required(
        &self,
        site: Site,
        entries: &[RequiredEntry],
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let mut labelled: BTreeMap<SurfaceName<'source>, ByteSpan> = BTreeMap::new();
        let mut whole: BTreeMap<SurfaceName<'source>, ByteSpan> = BTreeMap::new();
        for entry in entries {
            let interface = CapabilityRef::new(self.host_ref()).handled(
                site,
                &entry.interface,
                entry.interface.last.node,
                &entry.manifest,
            )?;
            let (span, name, seen) = match entry.label {
                Maybe::Present(written) => {
                    let named = CapabilityRef::new(self.host_ref()).label_of(site, written)?;
                    (named.span, self.cx().name_at(named), &mut labelled)
                },
                Maybe::Absent(_) => {
                    let name = entry.interface.name(self.cx().tree);
                    if let Interface::Theory(_) = interface {
                        return Err(LoweringRefusal::UnlabelledRequirement {
                            span: entry.interface.span(),
                            name,
                        });
                    }
                    (entry.interface.span(), name, &mut whole)
                },
            };
            if let Some(&first) = seen.get(&name) {
                return Err(LoweringRefusal::DuplicateDefinition { span, name, first });
            }
            let _first = seen.insert(name, span);
        }

        Ok(())
    }
}
