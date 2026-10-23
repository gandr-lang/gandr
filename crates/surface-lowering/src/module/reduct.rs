//! Reducts and forgetting maps, as the collection pass reads them.
//!
//! A `theory` block that includes another keeps the inclusion beside its
//! presentation, and a model of the block restricts along it to a model of
//! the theory it includes. Each theory the block includes, directly or through
//! a theory it includes, takes one slot after the block's, [`Role::Derived`]
//! with the definition half [`Operand::Derived`]: the reduct
//! `Model(T') -> Model(T)` the lowering mints along the composed inclusion
//! ([`ReductSlot`]). A theory reached two ways round takes one slot, the first
//! way's; the ways compose to one inclusion. The slot is entered in no name
//! table; the lowering enters it under the block's path, `T'.T`.
//!
//! A model type a source writes with manifest sorts, `Model(T) with sort C₁ =
//! A₁ … with sort Cₙ = Aₙ`, takes one slot before the top-level form writing
//! it, the same way: the forgetting map from `T`'s models with those sorts
//! manifest to its models ([`ForgetSlot`]), `(x₁ : Type, …) -> Model(T) with
//! sort C₁ = x₁ … -> Model(T)`, which drops the cell each manifest fixes and
//! keeps every other sort a field. Beside it, each theory a reduct of `T`
//! restricts to takes one slot: the forgetting map followed by that reduct,
//! `… -> Model(T) with sort C₁ = x₁ … -> Model(S)`, so a manifest model of
//! an extension stands where an included theory's model is asked. One slot
//! serves every model type of the unit fixing the same sorts of the same
//! theory, so the maps a unit takes are as many as the sort sets it writes,
//! times the theories each restricts to, each judged before every
//! declaration that crosses by it. A slot carries the name of the theory it
//! returns a model of and is entered in no name table.

use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use alloc::vec::Vec;

use anodized::spec;
use gandr_kernel_term::ConstantIndex;
use gandr_surface_syntax::NodeIndex;
use gandr_surface_syntax::NodeLabel;
use gandr_theory_levitation::Name;
use gandr_theory_levitation::TheoryInclusion;
use quenchant_shape::shape::Maybe;

use super::Collected;
use super::Collector;
use super::DeclarationSlot;
use super::Half;
use super::Operand;
use super::Role;
use super::SlotIndex;
use super::declaration_half;
use super::slot_refusal;
use crate::error::LoweringRefusal;
use crate::form::Cursor;
use crate::form::Former;
use crate::form::Pieces;
use crate::form::Placed;
use crate::form::Run;
use crate::form::Shape;
use crate::form::TileName;
use crate::form::read_pieces;
use crate::form::shape_of;
use crate::model::Included;
use crate::model::ModelForm;
use crate::model::derive;

/// A slot a theory's reduct takes: the theory whose models it restricts, the
/// theory it restricts them to, and the inclusion it restricts along.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: `inclusion` places each member of the theory whose block holds
///   the slot `target` among the members of the one whose block holds the slot
///   `source`, composed along every `include` between them.
/// - executable: none — the record is data the lowering reads.
///
/// # Adequacy
/// - hypothesis: L3 — a monoid's model restricts to its semigroup's, and a
///   theory including two extensions of the semigroup restricts to it once.
/// - witness: `tests::modules::models::a_model_of_an_extension_stands_where_the_included_model_is_asked`
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ReductSlot
{
    /// The including theory's slot.
    pub source: SlotIndex,
    /// The included theory's slot.
    pub target: SlotIndex,
    /// Where each member of the included theory stands in the including one.
    pub inclusion: TheoryInclusion,
}

/// A slot a forgetting map takes: the theory whose models it forgets the
/// manifest sorts of, the sorts it puts back, and the theory it returns a
/// model of.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: `theory` is the slot of a `theory` block whose models bundle,
///   `fixed` names at least one unindexed sort of its presentation, and `onto`
///   is `theory` itself or the target of a reduct of `theory`.
/// - executable: none — the record is data the lowering reads.
///
/// # Adequacy
/// - hypothesis: L3 — a counter's models, its carrier manifest at the integers,
///   stand where a counter's are asked; a pairing's, one sort of two manifest,
///   stand where a pairing's are; a monoid's, its carrier manifest, where a
///   semigroup's are.
/// - witness: `tests::modules::models::a_manifest_model_stands_where_its_theory_s_model_is_asked`
/// - witness: `tests::modules::models::a_model_fixing_some_sorts_stands_where_its_theory_s_model_is_asked_2132`
/// - witness: `tests::modules::models::a_manifest_model_of_an_extension_stands_where_the_included_model_is_asked_2136`
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ForgetSlot
{
    /// The theory's slot.
    pub theory: SlotIndex,
    /// The sorts the map puts back.
    pub fixed: BTreeSet<Name>,
    /// The slot of the theory the map returns a model of: `theory`, or one a
    /// reduct of it restricts to, which the map restricts to after putting
    /// the sorts back.
    pub onto: SlotIndex,
}

/// Each theory and sort set a forgetting slot puts back.
pub(super) type Forgotten = BTreeSet<(SlotIndex, BTreeSet<Name>)>;

impl<'source> Collector<'_, 'source>
{
    /// Collect the reducts of the `theory` block `block`, which took the slot
    /// `theory` and includes `inclusions`.
    ///
    /// # Specification
    /// - requires: `theory` is the clean slot `block` took, and `inclusions`
    ///   its presentation's, in written order.
    /// - ensures: every theory an inclusion names, and every theory that one
    ///   includes as this pass recorded it, is recorded as one the block
    ///   includes, with the inclusion composed along the way it was first
    ///   reached. When the block's models are a bundled record, each such
    ///   theory whose models are one too takes one [`Role::Derived`] slot, in
    ///   that order, under the included theory's name, its definition the
    ///   reduct the lowering mints, named at the `include` it was reached
    ///   through. An inclusion naming no collected block is passed over.
    /// - provides: the reduct half of the theory collection.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a monoid's semigroup, an extension of the monoid
    ///   reaching the semigroup through it, and two extensions of the semigroup
    ///   included together, reaching it once.
    /// - witness: `tests::modules::models::a_model_of_an_extension_stands_where_the_included_model_is_asked`
    /// - witness: `description::theory::tests::the_include_subject_s_ways_round_compose_to_one_inclusion`
    #[spec(
        captures: before = self.collected.slots.len(),
        ensures: self.collected.slots.len() >= before
            && self.collected.slots.len().saturating_sub(before) <= self.collected.included.get(&theory).map_or(0, Vec::len),
    )]
    pub(super) fn reducts(
        &mut self,
        (theory, block): (SlotIndex, Placed),
        inclusions: &[Included],
    )
    {
        let mut reached: Vec<(SlotIndex, TheoryInclusion, Placed)> = Vec::new();
        let mut seen: BTreeSet<SlotIndex> = BTreeSet::new();
        for included in inclusions {
            let Maybe::Present(target) = self.collected.owner_of(included.block.node)
            else {
                continue;
            };
            let beyond = self
                .collected
                .included
                .get(&target)
                .cloned()
                .unwrap_or_default();
            let ways = core::iter::once((target, Some(included.inclusion.clone()))).chain(
                beyond
                    .into_iter()
                    .map(|(further, inner)| (further, inner.then(&included.inclusion))),
            );
            for (reaches, inclusion) in ways {
                if let Some(inclusion) = inclusion
                    && seen.insert(reaches)
                {
                    reached.push((reaches, inclusion, included.named));
                }
            }
        }
        let _first = self.collected.included.insert(
            theory,
            reached
                .iter()
                .map(|&(target, ref inclusion, _)| (target, inclusion.clone()))
                .collect(),
        );
        // A reduct is minted between two bundled records, so a theory whose
        // models no record states, a circuit rule's among them, takes none.
        let bundles = |collected: &Collected<'_>, node: NodeIndex| {
            collected
                .descriptions
                .get(&node)
                .and_then(|entry| match entry.presentation {
                    Maybe::Present(ref presentation) => derive(presentation).ok(),
                    Maybe::Absent(_) => None,
                })
                .filter(|signature| {
                    signature
                        .components
                        .iter()
                        .all(|component| component.form.is_ok())
                })
        };
        if bundles(self.collected, block.node).is_none() {
            return;
        }
        let container = self.collected.top(block.span.start());
        for (target, inclusion, through) in reached {
            let Some(included) = self.collected.slots.get(usize::from(target))
            else {
                continue;
            };
            let name = included.name;
            if bundles(self.collected, included.introduced_by.node).is_none() {
                continue;
            }
            let minted = SlotIndex(self.collected.slots.len());
            self.collected.slots.push(DeclarationSlot {
                name,
                container,
                role: Role::Derived,
                constant: ConstantIndex::from(minted.0),
                introduced_by: block,
                named: through,
                signature: Maybe::Absent(declaration_half::Absent::Unwritten),
                definition: Maybe::Present(Half {
                    declaration: block,
                    named: through,
                    operand: Operand::Derived,
                }),
                attributes: Vec::new(),
                docs: Vec::new(),
                refusal: Maybe::Absent(slot_refusal::Absent::Unrefused),
            });
            let _fresh = self.collected.reducts.insert(minted, ReductSlot {
                source: theory,
                target,
                inclusion,
            });
        }
    }

    /// The manifest types and the forgetting forms of the source, in the order
    /// their text starts.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: every node of the source's tree classified as a manifest type
    ///   or a forgetting form, once, ascending by the start of its span.
    /// - panics: none.
    /// - executable: none — the classification is the grammar's, which a
    ///   predicate would read again.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::forget`].
    /// - witness: `tests::modules::models::a_model_fixing_some_sorts_stands_where_its_theory_s_model_is_asked_2132`
    pub(super) fn manifest_types(&self) -> Vec<Placed>
    {
        // A form's mold decides its former, so each mold is classified once.
        let mut manifest_molds = BTreeMap::new();
        let mut found = Vec::new();
        for position in self.tree.positions() {
            let Some(node) = self.tree.node(position)
            else {
                continue;
            };
            let NodeLabel::Meld(mold) = node.label()
            else {
                continue;
            };
            let manifest = *manifest_molds.entry(mold).or_insert_with(|| {
                matches!(
                    shape_of(self.pbg, node),
                    Ok(Shape::Form {
                        former: Former::ManifestType | Former::ForgetModel,
                        ..
                    })
                )
            });
            if manifest {
                found.push(Placed::of(position, node));
            }
        }
        found.sort_by_key(|placed| placed.span.start());

        found
    }

    /// Each theory and sort set a forgetting slot of the unit already puts
    /// back.
    ///
    /// # Specification
    /// trivial.
    pub(super) fn forgotten(&self) -> Forgotten
    {
        self.collected
            .forgets
            .values()
            .map(|slot| (slot.theory, slot.fixed.clone()))
            .collect()
    }

    /// Collect the forgetting maps the manifest type or the forgetting form
    /// `at` asks for: `Model(T) with sort C₁ = A₁ … with sort Cₙ = Aₙ` and
    /// `forget[sort C₁ = A₁, …, sort Cₙ = Aₙ](m) at Model(T)` both put back
    /// the sorts `C₁ … Cₙ` of `T`.
    ///
    /// # Specification
    /// - requires: `at` is a manifest type or a forgetting form of the source;
    ///   `forgotten` holds each theory and sort set a forgetting slot of the
    ///   unit puts back.
    /// - ensures: when `at` applies `Model` to a theory
    ///   [`Collected::presented_theory`] resolves where the type is written,
    ///   whose models bundle, and its bindings fix distinct unindexed sorts of
    ///   it that no slot of `forgotten` puts back for the theory, one
    ///   [`Role::Derived`] slot under the theory's name, its definition the
    ///   forgetting map of those sorts the lowering mints, then one per theory
    ///   a reduct of the theory restricts to, in the reducts' order, under that
    ///   theory's name, its definition the forgetting map followed by the
    ///   reduct; each named at the theory's name in the type, and the sort set
    ///   entered in `forgotten`. Nothing otherwise, a manifest type of another
    ///   shape being the lowering's to refuse where it reads it. Every slot
    ///   taken is a forgetting slot.
    /// - provides: the forgetting half of the theory collection.
    /// - fails: [`LoweringRefusal::BudgetExceeded`] when the walk outruns the
    ///   allowance, before any slot is taken.
    /// - panics: none.
    ///
    /// # Errors
    /// As the fails clause.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a counter's carrier fixed at a type and at a
    ///   variable, one map between them; a pairing's sorts fixed one, the other
    ///   and both, a map each; a monoid's carrier fixed, a map to the monoids
    ///   and one to the semigroups; a theory no manifest type names, none.
    /// - witness: `tests::modules::models::a_manifest_model_stands_where_its_theory_s_model_is_asked`
    /// - witness: `tests::modules::models::a_model_fixing_some_sorts_stands_where_its_theory_s_model_is_asked_2132`
    /// - witness: `tests::modules::models::a_manifest_model_of_an_extension_stands_where_the_included_model_is_asked_2136`
    #[spec(
        captures: before = (self.collected.slots.len(), self.collected.forgets.len()),
        ensures: |ret| self.collected.slots.len().saturating_sub(before.0)
            == self.collected.forgets.len().saturating_sub(before.1)
            && (ret.is_ok() || self.collected.slots.len() == before.0),
    )]
    pub(super) fn forget(
        &mut self,
        at: Placed,
        forgotten: &mut Forgotten,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        self.fuel.spend()?;
        let forgetting = self.tree.node(at.node).is_some_and(|node| {
            matches!(
                shape_of(self.pbg, node),
                Ok(Shape::Form {
                    former: Former::ForgetModel,
                    ..
                })
            )
        });
        let mut pieces = core::mem::take(&mut self.pieces);
        let chain = if forgetting {
            self.forgetting_chain(at, &mut pieces)
        }
        else {
            self.manifest_chain(at, &mut pieces)
        };
        self.pieces = pieces;
        let Some((named, fixed)) = chain
        else {
            return Ok(());
        };
        let Ok((theory, presentation)) =
            self.collected
                .presented_theory(named.span.start(), named.span, self.name_of(named))
        else {
            return Ok(());
        };
        let Ok(signature) = derive(presentation)
        else {
            return Ok(());
        };
        if !signature
            .components
            .iter()
            .all(|component| component.form.is_ok())
        {
            return Ok(());
        }
        let unindexed: BTreeMap<&str, &Name> = signature
            .components
            .iter()
            .filter(|component| {
                matches!(component.form, Ok(ModelForm::Sort { ref indices }) if indices.is_empty())
            })
            .map(|component| (component.name.as_ref(), &component.name))
            .collect();
        let mut sorts = BTreeSet::new();
        let clean = fixed.iter().all(|&sort| {
            unindexed
                .get(self.name_of(sort).as_ref())
                .is_some_and(|&name| sorts.insert(name.clone()))
        });
        if !clean || !forgotten.insert((theory, sorts.clone())) {
            return Ok(());
        }
        // The map onto the theory's own models first, then one per theory a
        // reduct restricts them to.
        let reached: Vec<SlotIndex> = self
            .collected
            .reducts
            .values()
            .filter(|reduct| reduct.source == theory)
            .map(|reduct| reduct.target)
            .collect();
        let container = self.collected.top(at.span.start());
        for onto in core::iter::once(theory).chain(reached) {
            let Some(held) = self.collected.slots.get(usize::from(onto))
            else {
                continue;
            };
            let name = held.name;
            let minted = SlotIndex(self.collected.slots.len());
            self.collected.slots.push(DeclarationSlot {
                name,
                container,
                role: Role::Derived,
                constant: ConstantIndex::from(minted.0),
                introduced_by: at,
                named,
                signature: Maybe::Absent(declaration_half::Absent::Unwritten),
                definition: Maybe::Present(Half {
                    declaration: at,
                    named,
                    operand: Operand::Derived,
                }),
                attributes: Vec::new(),
                docs: Vec::new(),
                refusal: Maybe::Absent(slot_refusal::Absent::Unrefused),
            });
            let _first = self.collected.forgets.insert(minted, ForgetSlot {
                theory,
                fixed: sorts.clone(),
                onto,
            });
        }

        Ok(())
    }

    /// The theory's name tile and each fixed sort's name tile of the manifest
    /// type `at`, `Model(T) with sort C₁ = A₁ … with sort Cₙ = Aₙ`, read off
    /// its tiles with `pieces` as scratch; nothing for a manifest type whose
    /// left operand is no application of `Model` to one name, and for a chain
    /// out of shape.
    ///
    /// # Specification
    /// - requires: `at` is a manifest type of the source.
    /// - ensures: the name tile of `T` and the sort name tiles in written
    ///   order, at least one, when the type reads as above.
    /// - panics: none.
    /// - executable: none — the reading is the tiles', which a predicate would
    ///   read again.
    ///
    /// # Termination
    /// Every pass descends to the right operand of a `with`, a node strictly
    /// inside the one before it in the finite tree.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::forget`].
    /// - witness: `tests::modules::models::a_model_fixing_some_sorts_stands_where_its_theory_s_model_is_asked_2132`
    fn manifest_chain(
        &self,
        at: Placed,
        pieces: &mut Pieces,
    ) -> Option<(Placed, Vec<Placed>)>
    {
        let (applied, mut bound) = self.halves(at, pieces)?;
        let named = self.model_operand(applied, pieces)?;
        let mut sorts = Vec::new();
        loop {
            let node = self.tree.node(bound.node)?;
            let link = matches!(
                shape_of(self.pbg, node),
                Ok(Shape::Form {
                    former: Former::ManifestType,
                    ..
                })
            );
            let binding = if link {
                let (first, rest) = self.halves(bound, pieces)?;
                bound = rest;
                first
            }
            else {
                bound
            };
            read_pieces(self.pbg, self.tree, binding.node, pieces).ok()?;
            let mut cursor = Cursor::new(&pieces.pieces, binding.span);
            let Maybe::Present(_) = cursor.tile(TileName::SORT)
            else {
                return None;
            };
            let Maybe::Present(sort) = cursor.tile(TileName::TYPE_IDENTIFIER)
            else {
                return None;
            };
            sorts.push(sort);
            if !link {
                return Some((named, sorts));
            }
        }
    }

    /// The theory's name tile and each sort's name tile of the forgetting form
    /// `at`, `forget[sort C₁ = A₁, …, sort Cₙ = Aₙ](m) at Model(T)`, read off
    /// its tiles and its bracket's bindings with `pieces` as scratch; nothing
    /// for a form the parser repaired or out of that shape.
    ///
    /// # Specification
    /// - requires: `at` is a forgetting form of the source.
    /// - ensures: the name tile of `T` and the sort name tiles in written
    ///   order, at least one, when the form reads as above.
    /// - panics: none.
    /// - executable: none — as [`Self::manifest_chain`].
    ///
    /// # Termination
    /// Every pass of the bracket's loop reads an entry and the next separator
    /// off the finite pieces, or leaves; the second reads each of the entries
    /// the first collected once.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a counter's carrier put back by the written map,
    ///   whose slot no manifest type of the source asks for, as
    ///   [`Self::forget`].
    /// - witness: `tests::modules::models::a_written_forgetting_map_takes_the_slot_it_names_2130`
    fn forgetting_chain(
        &self,
        at: Placed,
        pieces: &mut Pieces,
    ) -> Option<(Placed, Vec<Placed>)>
    {
        read_pieces(self.pbg, self.tree, at.node, pieces).ok()?;
        if let Maybe::Present(_) = pieces.repair {
            return None;
        }
        let mut cursor = Cursor::new(&pieces.pieces, at.span);
        let Maybe::Present(_) = cursor.tile(TileName::FORGET)
        else {
            return None;
        };
        let Maybe::Present(_) = cursor.tile(TileName::BRACKET_OPEN)
        else {
            return None;
        };
        let mut entries = Vec::new();
        loop {
            let Run::One(entry) = cursor.operands()
            else {
                return None;
            };
            entries.push(entry);
            if let Maybe::Present(_) = cursor.tile(TileName::BRACKET_CLOSE) {
                break;
            }
            let Maybe::Present(_) = cursor.tile(TileName::COMMA)
            else {
                return None;
            };
            if let Maybe::Present(_) = cursor.tile(TileName::BRACKET_CLOSE) {
                break;
            }
        }
        let Maybe::Present(_) = cursor.tile(TileName::PAREN_OPEN)
        else {
            return None;
        };
        let Run::One(_) = cursor.operands()
        else {
            return None;
        };
        let Maybe::Present(_) = cursor.tile(TileName::PAREN_CLOSE)
        else {
            return None;
        };
        let Maybe::Present(_) = cursor.tile(TileName::AT)
        else {
            return None;
        };
        let Run::One(stated) = cursor.operands()
        else {
            return None;
        };
        let Maybe::Absent(_) = cursor.peek()
        else {
            return None;
        };
        let mut sorts = Vec::with_capacity(entries.len());
        for entry in entries {
            read_pieces(self.pbg, self.tree, entry.node, pieces).ok()?;
            let mut binding = Cursor::new(&pieces.pieces, entry.span);
            let Maybe::Present(_) = binding.tile(TileName::SORT)
            else {
                return None;
            };
            let Maybe::Present(sort) = binding.tile(TileName::TYPE_IDENTIFIER)
            else {
                return None;
            };
            let Maybe::Present(_) = binding.tile(TileName::EQUALS)
            else {
                return None;
            };
            let Run::One(_) = binding.operands()
            else {
                return None;
            };
            let Maybe::Absent(_) = binding.peek()
            else {
                return None;
            };
            sorts.push(sort);
        }
        let named = self.model_operand(stated, pieces)?;

        Some((named, sorts))
    }

    /// The operands either side of the `with` of the manifest type `at`.
    ///
    /// # Specification
    /// - requires: `at` is a manifest type of the source.
    /// - ensures: its one left operand and its one right operand, when the form
    ///   reads `L with R` unrepaired.
    /// - panics: none.
    /// - executable: none — as [`Self::manifest_chain`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a chain of two `with`s read link by link, as
    ///   [`Self::forget`].
    /// - witness: `tests::modules::models::a_model_fixing_some_sorts_stands_where_its_theory_s_model_is_asked_2132`
    fn halves(
        &self,
        at: Placed,
        pieces: &mut Pieces,
    ) -> Option<(Placed, Placed)>
    {
        read_pieces(self.pbg, self.tree, at.node, pieces).ok()?;
        if let Maybe::Present(_) = pieces.repair {
            return None;
        }
        let mut cursor = Cursor::new(&pieces.pieces, at.span);
        let Run::One(left) = cursor.operands()
        else {
            return None;
        };
        let Maybe::Present(_) = cursor.tile(TileName::WITH)
        else {
            return None;
        };
        let Run::One(right) = cursor.operands()
        else {
            return None;
        };
        let Maybe::Absent(_) = cursor.peek()
        else {
            return None;
        };

        Some((left, right))
    }

    /// The name tile of the theory the application `applied` writes, when it
    /// is `Model(T)` with `T` one name.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the name tile of `T` when `applied` reads `Model ( T )`.
    /// - panics: none.
    /// - executable: none — as [`Self::manifest_chain`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — `Model(Pairing)` read to its theory's name, as
    ///   [`Self::forget`].
    /// - witness: `tests::modules::models::a_model_fixing_some_sorts_stands_where_its_theory_s_model_is_asked_2132`
    fn model_operand(
        &self,
        applied: Placed,
        pieces: &mut Pieces,
    ) -> Option<Placed>
    {
        let node = self.tree.node(applied.node)?;
        let Ok(Shape::Form {
            former: Former::TypeApplication,
            ..
        }) = shape_of(self.pbg, node)
        else {
            return None;
        };
        read_pieces(self.pbg, self.tree, applied.node, pieces).ok()?;
        let mut cursor = Cursor::new(&pieces.pieces, applied.span);
        let Maybe::Present(head) = cursor.tile(TileName::TYPE_IDENTIFIER)
        else {
            return None;
        };
        if self.name_of(head).as_ref() != "Model" {
            return None;
        }
        let Maybe::Present(_) = cursor.tile(TileName::PAREN_OPEN)
        else {
            return None;
        };
        let Run::One(theory) = cursor.operands()
        else {
            return None;
        };
        let theory_node = self.tree.node(theory.node)?;
        if let NodeLabel::Tile(_) = theory_node.label() {
            return Some(theory);
        }
        read_pieces(self.pbg, self.tree, theory.node, pieces).ok()?;
        let mut inner = Cursor::new(&pieces.pieces, theory.span);
        let Maybe::Present(named) = inner.tile(TileName::TYPE_IDENTIFIER)
        else {
            return None;
        };
        let Maybe::Absent(_) = inner.peek()
        else {
            return None;
        };

        Some(named)
    }
}
