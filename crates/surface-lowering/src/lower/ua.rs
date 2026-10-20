//! Univalence at a stratum in the lowering: `ua[n, k](a, b, f, g)`, the path
//! in the universe between two `theory` descriptions that an equivalence of
//! their species at a certified stratum derives.
//!
//! # The spelling
//!
//! `ua[n, k](a, b, f, g)` is a call whose head instantiates `ua` at two
//! number literals. `n` is the degree the statement is made at and `k` the
//! catalogue's bound, the largest shape the conditions are checked over. `a`
//! and `b` name `theory` blocks, each read as the graphical species its
//! generators present ([`gandr_core_term::ua::Description::read`]). `f` and
//! `g` are records keyed by generator labels, `f` by `a`'s and `g` by `b`'s:
//! the label names the corolla its generator stands at, and the field is the
//! translator that moves every element of that corolla, all generators at
//! that profile in written order. The form stands as a value, as `equiv` does,
//! and lowers to [`gandr_core_term::Value::Ua`]; `gandr_core_checker`'s `ua`
//! module certifies the stratum, checks the translators and derives the path.
//!
//! # Decisions
//!
//! - **The stratum is written in the head.** A statement of univalence at a
//!   stratum fixes its alphabet and its quantifier range, so `n` and `k` are
//!   part of what is written, in the instantiation brackets the grammar already
//!   parses after a name, and a statement at another stratum is a different
//!   statement. The alternatives were a bound read off the largest profile
//!   either description inhabits, which hides what the statement quantifies
//!   over, and attributes on the declaration, which put the statement's meaning
//!   outside the term. Reversal: a catalogue cheap enough at every bound a
//!   program meets lets `k` be inferred and written only to narrow it.
//! - **Descriptions are named, translators keyed by generator.** `a` and `b`
//!   are resolved as any name is, in the source's own top level and then its
//!   imports — a block's name also defines the block's value at `Theory`, but
//!   the species is read off the block's description — and the record labels
//!   are the generator names a reader already sees in the block. The
//!   alternative, translators listed positionally in corolla order, makes the
//!   reader recompute the corolla catalogue to see which translator moves which
//!   generator. Reversal: a species read off a `Theory` value lets `a` and `b`
//!   be any term that normalises to a presentation.
//! - **The lowering reads, the checker decides.** The lowering refuses only
//!   what it can see in the syntax: a head that is not `ua` at two literals, an
//!   operand count other than four, a name no `theory` block declares, a block
//!   with a refused member, and a block that is no graphical species. Degree,
//!   condition, bound and the translators themselves are the checker's, so one
//!   set of refusals names every defect a statement can have once it is
//!   written.

use alloc::sync::Arc;

use anodized::spec;
use gandr_core_term::ua::Description;
use gandr_core_term::ua::Sides;
use gandr_core_term::ua::Stratum;
use gandr_core_term::ua::Unread;
use gandr_surface_syntax::NodeIndex;
use quenchant_shape::shape::Maybe;

use super::Former;
use super::Lowerer;
use super::Plan;
use super::Produced;
use super::Reading;
use super::Site;
use super::arguments;
use super::closed;
use super::exhausted;
use super::identity::spelled;
use crate::error::FragmentBoundary;
use crate::error::LoweringRefusal;
use crate::form::Cursor;
use crate::form::Placed;
use crate::form::Shape;
use crate::form::TileName;
use crate::form::read_pieces;
use crate::form::shape_of;
use crate::origin::Origin;
use crate::resolve::OperandCount;

#[cfg(test)]
mod tests;

/// The name the head of a univalence statement instantiates.
const UA: &str = "ua";

impl<'source> Lowerer<'_, 'source>
{
    /// The stratum a call's head writes, when it is `ua[n, k]`.
    ///
    /// # Specification
    /// - requires: `head` is the head operand of the call at `site`.
    /// - ensures: present for an instantiation whose head is the name `ua`,
    ///   free at the call, with two number literals between its brackets: `n`
    ///   the degree and `k` the bound; absent for any other head, so a descent
    ///   claim `f[<]` and a binder named `ua` read as before.
    /// - fails: an instantiation of `ua` with other than two residents, a
    ///   resident that is no decimal number, and the name resolution's own
    ///   refusals.
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoweringRefusal::OutOfFragment`] with the arity boundary for the
    /// resident count and the unadmitted boundary at a resident that is no
    /// number; a misplaced tile for brackets out of shape.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a statement at degree one and bound four lowers to
    ///   that stratum; a resident that is a type and a single resident are
    ///   refused by their own boundaries; a later member named `ua` is a
    ///   forward reference at the name.
    /// - witness: `lower::ua::tests::a_statement_lowers_to_univalence_at_its_stratum`
    /// - witness: `lower::ua::tests::a_statement_the_syntax_cannot_read_is_refused`
    /// - witness: `lower::ua::tests::a_later_member_named_ua_is_a_forward_reference`
    #[spec(ensures: |ret| !matches!(ret, Ok(Maybe::Present(_))) || self.tree.node(head.node).is_some())]
    pub(super) fn ua_head(
        &mut self,
        site: Site,
        head: Placed,
    ) -> Result<Maybe<Stratum, spelled::Absent>, LoweringRefusal<'source>>
    {
        let unspelled = Ok(Maybe::Absent(spelled::Absent::Unspelled));
        let Some(node) = self.tree.node(head.node)
        else {
            return unspelled;
        };
        let Shape::Form {
            former: Former::Instantiation,
            ..
        } = shape_of(self.pbg, node)?
        else {
            return unspelled;
        };
        let instantiated = Site { at: head, ..site };
        let mut scratch = core::mem::take(&mut self.scratch);
        let read = read_pieces(self.pbg, self.tree, head.node, &mut scratch);
        let mut cursor = Cursor::new(&scratch.pieces, head.span);
        let written = read.and_then(|()| {
            let named = instantiated.one(cursor.operands())?;
            closed(instantiated, &mut cursor, TileName::BRACKET_OPEN)?;
            let mut residents = alloc::vec::Vec::new();
            loop {
                residents.push(instantiated.one(cursor.operands())?);
                if let Maybe::Absent(_) = cursor.at(TileName::COMMA) {
                    break;
                }
                closed(instantiated, &mut cursor, TileName::COMMA)?;
            }
            closed(instantiated, &mut cursor, TileName::BRACKET_CLOSE)?;
            exhausted(instantiated, &cursor)?;
            Ok((named, residents))
        });
        self.scratch = scratch;
        let (named, residents) = written?;
        let is_name = self.tree.node(named.node).is_some_and(|node| {
            matches!(
                shape_of(self.pbg, node),
                Ok(Shape::Form {
                    former: Former::Name,
                    ..
                })
            )
        });
        let name = self.name_at(named);
        if !is_name || name.as_ref() != UA {
            return unspelled;
        }
        // The name inside the instantiation is owned by no declaration until
        // the call around it is read, so it resolves at the call's node, at
        // its own bytes: a later member named `ua` is then a forward
        // reference, as for the identity heads (#633).
        let at_name = Site {
            at: Placed {
                node: site.at.node,
                span: named.span,
            },
            ..site
        };
        if let Maybe::Present(_shadowed) = self.resolve_name(at_name, site.reading.frame(), name)? {
            return unspelled;
        }
        let &[degree, bound] = residents.as_slice()
        else {
            return Err(
                instantiated.out(FragmentBoundary::Arity(OperandCount::from(residents.len())))
            );
        };
        Ok(Maybe::Present(Stratum {
            degree: self.resident(site, degree)?,
            bound: self.resident(site, bound)?,
        }))
    }

    /// The count a resident of `ua[n, k]` writes: a degree or a catalogue
    /// bound.
    ///
    /// A resident is read in the instantiation sort, which holds a type where
    /// a literal is written; a resident whose whole text is decimal digits is
    /// the literal, since no name or type is spelled with digits alone.
    ///
    /// # Specification
    /// - ensures: the count of a resident written as decimal digits.
    /// - fails: a resident written otherwise, or digits past the machine word.
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoweringRefusal::OutOfFragment`] with the unadmitted boundary at the
    /// resident.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the witnesses' literals read as their values and a
    ///   name in their place is refused.
    /// - witness: `lower::ua::tests::a_statement_the_syntax_cannot_read_is_refused`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |value| self.text_at(resident).as_ref().parse::<usize>().map(Count::from).as_ref() == Ok(value)))]
    fn resident<Count>(
        &self,
        site: Site,
        resident: Placed,
    ) -> Result<Count, LoweringRefusal<'source>>
    where
        Count: From<usize> + PartialEq,
    {
        let written = Site {
            at: resident,
            ..site
        };
        let text = self.text_at(resident);
        let spelled: &str = text.as_ref();
        match spelled.parse::<usize>() {
            Ok(value) if spelled.bytes().all(|byte| byte.is_ascii_digit()) => {
                Ok(Count::from(value))
            },
            Ok(_) | Err(_) => Err(written.out(FragmentBoundary::Unadmitted)),
        }
    }

    /// Classify `ua[n, k](a, b, f, g)` at `site`, its stratum read off the
    /// head, the cursor at its arguments.
    ///
    /// # Specification
    /// - requires: [`Self::ua_head`] read `stratum` off the call's head.
    /// - ensures: plans univalence at `stratum` between the descriptions `a`
    ///   and `b` name, the records `f` and `g` read as values.
    /// - fails: other than four arguments; a description refused as
    ///   [`Self::description`] refuses it; a position that reads no value.
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoweringRefusal::OutOfFragment`] with the arity boundary at the call,
    /// and the description's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a statement between two magmas lowers to its
    ///   descriptions and records in written order, and one argument short is
    ///   refused by its count.
    /// - witness: `lower::ua::tests::a_statement_lowers_to_univalence_at_its_stratum`
    /// - witness: `lower::ua::tests::a_statement_the_syntax_cannot_read_is_refused`
    #[spec(ensures: |ret| ret.is_err() || matches!(self.plans.get(usize::from(site.at.node)), Some(&Plan::Ua { .. })))]
    pub(super) fn ua_call(
        &mut self,
        site: Site,
        stratum: Stratum,
        mut cursor: Cursor<'_>,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let frame = self.require(site, Produced::Value)?;
        let start = self.operands.len();
        let read = arguments(site, &mut cursor, &mut self.operands);
        let count = self.operands.len().saturating_sub(start);
        let written = [0_usize, 1_usize, 2_usize, 3_usize]
            .map(|offset| self.operands.get(start.saturating_add(offset)).copied());
        self.operands.truncate(start);
        read?;
        let (4_usize, [Some(source), Some(target), Some(forward), Some(backward)]) =
            (count, written)
        else {
            return Err(site.out(FragmentBoundary::Arity(OperandCount::from(count))));
        };
        let sides = Sides {
            source: self.description(site, source)?,
            target: self.description(site, target)?,
        };
        let named = [source, target].map(|operand| {
            self.tree.node(operand).map_or_else(
                || Origin::new(operand, site.at.span),
                |node| Origin::new(operand, node.span()),
            )
        });
        self.read(forward, Reading::Value(frame));
        self.read(backward, Reading::Value(frame));
        self.plan(site, Plan::Ua {
            stratum,
            sides: Arc::new(sides),
            named,
            forward,
            backward,
        });
        Ok(())
    }

    /// The description the `theory` block `operand` names reads as, a graphical
    /// species.
    ///
    /// # Specification
    /// - requires: `operand` is an argument of the call at `site`.
    /// - ensures: the description of the `theory` block the name `operand`
    ///   spells declares, resolved in the call's own source and then in the
    ///   sources it imports unqualified, so a block another source of the unit
    ///   declares answers only when an import reaches it.
    /// - fails: an operand that is no name; a name that resolves to no `theory`
    ///   block; a name two imports bind; a block with a member the description
    ///   route or the cell gate refused; a block [`Description::read`] refuses.
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoweringRefusal::UnresolvedName`] for a name that resolves to no
    /// `theory` block; [`LoweringRefusal::ImportShadows`] for a name two
    /// imports bind; [`LoweringRefusal::OutOfFragment`] at the operand
    /// otherwise, with the indexed boundary for an indexed sort and the
    /// unadmitted one for every other refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a magma reads at its two corollas; a name no block
    ///   declares, a block with two sorts and an indexed block are refused at
    ///   the operand; a block of another source answers through an import of it
    ///   and not without one.
    /// - witness: `lower::ua::tests::a_statement_lowers_to_univalence_at_its_stratum`
    /// - witness: `lower::ua::tests::a_description_outside_the_stratum_is_refused_at_its_name`
    /// - witness: `tests::namespace::a_univalence_statement_reads_only_the_blocks_its_source_sees_1078`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |description| !description.name.as_ref().is_empty()))]
    fn description(
        &self,
        site: Site,
        operand: NodeIndex,
    ) -> Result<Description, LoweringRefusal<'source>>
    {
        let Some(node) = self.tree.node(operand)
        else {
            return Err(site.out(FragmentBoundary::Unadmitted));
        };
        let at = Placed::of(operand, node);
        let written = Site { at, ..site };
        let Shape::Form {
            former: Former::Name | Former::Constructor,
            ..
        } = shape_of(self.pbg, node)?
        else {
            return Err(written.out(FragmentBoundary::Unadmitted));
        };
        let name = self.name_at(at);
        let local = self
            .collected
            .by_name
            .get(&(self.collected.top(at.span.start()), name))
            .copied();
        let position = match local {
            Some(position) => Some(position),
            None => {
                match self
                    .collected
                    .imported_slot(self.collected.unit.source_at(at.span.start()), name)
                {
                    Ok(Maybe::Present((position, _import))) => Some(position),
                    Ok(Maybe::Absent(_)) => None,
                    Err(ambiguity) => {
                        return Err(LoweringRefusal::ImportShadows {
                            span: at.span,
                            name,
                            import: ambiguity.import,
                            other: ambiguity.other,
                        });
                    },
                }
            },
        };
        let Some(entry) = position
            .and_then(|position| self.collected.slots.get(usize::from(position)))
            .and_then(|slot| self.collected.descriptions.get(&slot.introduced_by.node))
            .filter(|entry| matches!(entry.classifier, Maybe::Absent(_)))
        else {
            return Err(LoweringRefusal::UnresolvedName {
                span: at.span,
                name,
            });
        };
        let block = entry.at.span;
        let inside = |span: gandr_surface_syntax::ByteSpan| {
            span.start() >= block.start() && span.end() <= block.end()
        };
        let refused = self
            .collected
            .description_diagnostics
            .iter()
            .any(|diagnostic| inside(diagnostic.span))
            || self
                .collected
                .cells
                .diagnostics
                .iter()
                .any(|diagnostic| inside(diagnostic.span));
        if refused {
            return Err(written.out(FragmentBoundary::Unadmitted));
        }
        Description::read(&entry.description).map_err(|unread| {
            written.out(match unread {
                Unread::Indexed => FragmentBoundary::Indexed,
                Unread::Sorts
                | Unread::Parameters
                | Unread::Constructors
                | Unread::Rules
                | Unread::Leg { .. } => FragmentBoundary::Unadmitted,
            })
        })
    }
}
