//! The block statement `import P ;`, which opens the module `P` names over
//! the rest of its block: a name no binder answers there reads the member
//! the module exports under it, as `P.x` would. The module is one the source
//! declares, found from the declaration's own module outward to the top
//! level, each later link a module the one before it exports. A member an
//! opaque ascription seals is read through its witness, as the qualified
//! path reads it, so opening a module shows no more than naming it does.
//!
//! An opened name binds nothing in the core: it lowers to the constant its
//! qualified spelling lowers to, so the checker and the kernel see the
//! program the qualified spelling writes. A binder wins over an opened
//! member, as a local does in Lean. A name both an opened module and an
//! enclosing declaration answer, or two opened modules, is refused at its
//! use as two unqualified imports binding one name are.

use alloc::vec::Vec;

use anodized::spec;
use gandr_surface_syntax::ByteSpan;
use quenchant_shape::shape::Maybe;

use super::Lowerer;
use super::Resolved;
use super::Site;
use super::named;
use crate::error::FormFault;
use crate::error::LoweringRefusal;
use crate::form::Cursor;
use crate::form::Placed;
use crate::form::TileName;
use crate::module::Container;
use crate::module::Half;
use crate::module::Member;
use crate::module::Operand;
use crate::module::SlotIndex;
use crate::module::StructureIndex;
use crate::resolve::SurfaceName;
use crate::resolve::binder_type;

#[cfg(test)]
mod tests;

/// A module a block statement opens, and the bytes it is open over.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: each value was read by [`Lowerer::open`].
/// - executable: none — the carrier holds no collection to check the module
///   against.
///
/// # Adequacy
/// - hypothesis: L3 — as [`Lowerer::open`].
/// - witness: `lower::opening::tests::an_opened_module_answers_the_rest_of_its_block`
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct Opened
{
    /// The bytes the module is open over: from the statement's `;` to the
    /// end of its block.
    scope: ByteSpan,
    /// The module.
    module: StructureIndex,
}

impl<'source> Lowerer<'_, 'source>
{
    /// Read the block statement `import P ;`, its `import` tile `keyword`
    /// already read, in the block `site` reads.
    ///
    /// # Specification
    /// - requires: `cursor` stands just past `keyword`, in a block whose form
    ///   `site` names and whose last piece closes it.
    /// - ensures: the module the path names is open over the bytes from the
    ///   statement's `;` to the end of `site`, keyed by the statement's bytes,
    ///   so reading the statement again opens nothing twice; the cursor is past
    ///   the `;`.
    /// - fails: a fault naming the block for a path or a `;` out of place;
    ///   [`LoweringRefusal::UnresolvedName`] for a head no enclosing container
    ///   declares a module of; [`LoweringRefusal::UnknownMember`] for a link
    ///   the module before it exports no module of.
    /// - panics: none.
    ///
    /// # Errors
    /// As `- fails:`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a top-level module and a nested one by its dotted
    ///   path each open, and a head nothing declares and a link no module
    ///   exports each refuse.
    /// - witness: `lower::opening::tests::an_opened_module_answers_the_rest_of_its_block`
    /// - witness: `lower::opening::tests::an_unknown_module_is_refused_at_its_path`
    #[spec(
        captures: before = self.opened.len(),
        ensures: |ret| ret.is_err() || self.opened.len() <= before.saturating_add(1),
    )]
    pub(super) fn open(
        &mut self,
        site: Site,
        cursor: &mut Cursor<'_>,
        keyword: Placed,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let Maybe::Present(head) = segment(cursor)
        else {
            return Err(site.fault(cursor.here(), FormFault::MisplacedTile));
        };
        let mut links = Vec::new();
        while let Maybe::Present(_) = cursor.tile(TileName::DOT) {
            let Maybe::Present(link) = segment(cursor)
            else {
                return Err(site.fault(cursor.here(), FormFault::MisplacedTile));
            };
            links.push(link);
        }
        let Maybe::Present(semicolon) = cursor.tile(TileName::SEMICOLON)
        else {
            return Err(site.fault(cursor.here(), FormFault::MisplacedTile));
        };
        let module = self.opened_module(site, head, &links)?;
        let scope = ByteSpan::new(semicolon.span.end(), site.at.span.end())
            .map_err(|_inverted| site.fault(semicolon.span, FormFault::MisplacedTile))?;
        let _first = self
            .opened
            .entry(keyword.span.join(semicolon.span))
            .or_insert(Opened { scope, module });

        Ok(())
    }

    /// The module the path `head` then `links` names from the declaration
    /// owning `site`.
    ///
    /// # Specification
    /// - requires: `head` and `links` are the path's name tiles, in order.
    /// - ensures: the module the nearest container outward from the owning
    ///   declaration's — its module, each module enclosing it, then its
    ///   source's top level — declares under `head`'s name, then each link a
    ///   module the one before it exports under the link's name.
    /// - fails: as [`Self::open`]; [`LoweringRefusal::BudgetExceeded`] when the
    ///   walk outruns the allowance.
    /// - panics: none.
    ///
    /// # Errors
    /// As `- fails:`.
    ///
    /// # Termination
    /// The walk outward visits each enclosing container once and the walk down
    /// each link once, each spending one step of the allowance.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::open`].
    /// - witness: `lower::opening::tests::an_opened_module_answers_the_rest_of_its_block`
    /// - witness: `lower::opening::tests::an_unknown_module_is_refused_at_its_path`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |module| self.collected.structures.get(usize::from(*module)).is_some()))]
    pub(super) fn opened_module(
        &mut self,
        site: Site,
        head: Placed,
        links: &[Placed],
    ) -> Result<StructureIndex, LoweringRefusal<'source>>
    {
        let name = self.name_at(head);
        let unresolved = LoweringRefusal::UnresolvedName {
            span: head.span,
            name,
        };
        let Maybe::Present(own) = self.collected.owner_of(site.at.node)
        else {
            return Err(unresolved);
        };
        let mut container = self.collected.slots.get(usize::from(own)).map_or_else(
            || self.collected.top(site.at.span.start()),
            |slot| slot.container,
        );
        let mut module = loop {
            self.fuel.spend()?;
            if let Some(&found) = self.collected.modules.get(&(container, name)) {
                break found;
            }
            let Container::Module(enclosing) = container
            else {
                return Err(unresolved);
            };
            container = self
                .collected
                .structures
                .get(usize::from(enclosing))
                .map_or_else(
                    || self.collected.top(site.at.span.start()),
                    |structure| structure.container,
                );
        };
        let mut spelled = name;
        for &link in links {
            self.fuel.spend()?;
            let member = self.name_at(link);
            let inner = self
                .collected
                .structures
                .get(usize::from(module))
                .and_then(|structure| {
                    structure.exports.iter().find_map(|export| match *export {
                        Member::Module(inner) => self
                            .collected
                            .structures
                            .get(usize::from(inner))
                            .is_some_and(|held| held.name == member)
                            .then_some(inner),
                        Member::Slot(_) => None,
                    })
                });
            let Some(inner) = inner
            else {
                return Err(LoweringRefusal::UnknownMember {
                    span: link.span,
                    module: spelled,
                    member,
                });
            };
            (module, spelled) = (inner, member);
        }

        Ok(module)
    }

    /// What the modules open at `site` answer `name` with, the declaration
    /// owning `site` being `own`.
    ///
    /// # Specification
    /// - requires: no binder answers `name` at `site`.
    /// - ensures: the absence when no module open at `site` exports `name`;
    ///   otherwise the member one exports, read through its witness past a
    ///   seal, with its constant and its signature's written type, as the
    ///   qualified path reads it.
    /// - fails: [`LoweringRefusal::ImportShadows`] at the use when two open
    ///   modules export distinct members of the name, or when an enclosing
    ///   declaration also answers it, naming the statement and the other
    ///   binding; [`LoweringRefusal::ForwardMemberReference`] for a member
    ///   admitted at or after `own`; and the refusal reading the enclosing
    ///   declarations raises.
    /// - panics: none.
    ///
    /// # Errors
    /// As `- fails:`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an opened member read in the rest of its block, a
    ///   binder winning over one, a name an enclosing declaration and an opened
    ///   module both answer, and a module opened after the use.
    /// - witness: `lower::opening::tests::an_opened_module_answers_the_rest_of_its_block`
    /// - witness: `lower::opening::tests::a_name_two_scopes_answer_is_refused_at_its_use`
    #[spec(ensures: |ret| match ret {
        | Ok(Maybe::Present(Resolved::Declaration { constant, .. })) => usize::from(constant) < usize::from(own),
        | Ok(Maybe::Present(Resolved::Binder(_))) => false,
        | Err(LoweringRefusal::ImportShadows { span, name: refused, .. } | LoweringRefusal::ForwardMemberReference { span, name: refused, .. }) => span == site.at.span && refused == name,
        | Ok(Maybe::Absent(_)) | Err(_) => true,
    })]
    pub(super) fn opened_name(
        &mut self,
        site: Site,
        own: SlotIndex,
        name: SurfaceName<'source>,
    ) -> Result<Maybe<Resolved, named::Absent>, LoweringRefusal<'source>>
    {
        let at = site.at.span.start();
        let mut found: Option<(SlotIndex, ByteSpan)> = None;
        for (&statement, opened) in &self.opened {
            if at < opened.scope.start() || at >= opened.scope.end() {
                continue;
            }
            let Some(structure) = self.collected.structures.get(usize::from(opened.module))
            else {
                continue;
            };
            let exported = structure.exports.iter().find_map(|export| match *export {
                Member::Slot(slot) => self
                    .collected
                    .slots
                    .get(usize::from(slot))
                    .is_some_and(|held| held.name == name)
                    .then(|| structure.exported_as.get(&slot).copied().unwrap_or(slot)),
                Member::Module(_) => None,
            });
            match (exported, found) {
                (Some(slot), Some((first, import))) if slot != first => {
                    return Err(LoweringRefusal::ImportShadows {
                        span: site.at.span,
                        name,
                        import,
                        other: statement,
                    });
                },
                (Some(slot), None) => found = Some((slot, statement)),
                (Some(_) | None, _) => {},
            }
        }
        let Some((slot, import)) = found
        else {
            return Ok(Maybe::Absent(named::Absent::Unresolved));
        };
        let Some(entry) = self.collected.slots.get(usize::from(slot))
        else {
            return Ok(Maybe::Absent(named::Absent::Unresolved));
        };
        let (constant, named_at, signature) = (entry.constant, entry.named.span, entry.signature);
        match self.declared_name(site, own, name) {
            Ok(Maybe::Absent(_) | Maybe::Present(Resolved::Binder(_))) => {},
            Ok(Maybe::Present(Resolved::Declaration {
                constant: other, ..
            })) if other == constant => {},
            Ok(Maybe::Present(Resolved::Declaration {
                constant: other, ..
            })) => {
                let other = self
                    .collected
                    .slots
                    .get(usize::from(other))
                    .map_or(site.at.span, |held| held.named.span);
                return Err(LoweringRefusal::ImportShadows {
                    span: site.at.span,
                    name,
                    import,
                    other,
                });
            },
            Err(LoweringRefusal::ForwardMemberReference { declared, .. }) => {
                return Err(LoweringRefusal::ImportShadows {
                    span: site.at.span,
                    name,
                    import,
                    other: declared,
                });
            },
            Err(refusal) => return Err(refusal),
        }
        if slot >= own {
            return Err(LoweringRefusal::ForwardMemberReference {
                span: site.at.span,
                name,
                declared: named_at,
            });
        }
        let declared = match signature {
            Maybe::Present(Half {
                operand: Operand::Written(written),
                ..
            }) => Maybe::Present(written.node),
            Maybe::Present(_) | Maybe::Absent(_) => Maybe::Absent(binder_type::Absent::Untyped),
        };

        Ok(Maybe::Present(Resolved::Declaration { constant, declared }))
    }
}

/// The name tile a module path writes at `cursor`, an identifier or a type
/// identifier, read past.
///
/// # Specification
/// trivial.
fn segment(cursor: &mut Cursor<'_>) -> Maybe<Placed, crate::form::cursor::Absent>
{
    match cursor.tile(TileName::IDENTIFIER) {
        Maybe::Present(name) => Maybe::Present(name),
        Maybe::Absent(_) => cursor.tile(TileName::TYPE_IDENTIFIER),
    }
}
