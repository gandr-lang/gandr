//! The reads of the lowering's context that each family shares: the text and
//! the name a node spells, the reading and the plan each node holds, what each
//! node lowered to, and the forms that the classification reads again.

use alloc::vec::Vec;

use anodized::spec;
use gandr_core_term::CompTypeId;
use gandr_core_term::ComputationId;
use gandr_core_term::ValueId;
use gandr_core_term::ValueTypeId;
use gandr_core_term::effect::EffectName;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::DeBruijnIndex;
use gandr_surface_syntax::ByteSpan;
use gandr_surface_syntax::LayoutBlock;
use gandr_surface_syntax::NodeIndex;
use gandr_surface_syntax::SourceFragment;
use quenchant_shape::shape::Maybe;

use super::Context;
use crate::by_form::At;
use crate::by_form::FormStretch;
use crate::error::FormFault;
use crate::error::LoweringRefusal;
use crate::form::Cursor;
use crate::form::FormName;
use crate::form::Former;
use crate::form::Piece;
use crate::form::Placed;
use crate::form::Shape;
use crate::form::TileName;
use crate::form::shape_of;
use crate::import::ImportResolution;
use crate::import::Opening;
use crate::lower::Lowered;
use crate::lower::Plan;
use crate::lower::Produced;
use crate::lower::Reading;
use crate::lower::Site;
use crate::lower::Stretch;
use crate::lower::arity;
use crate::lower::arity::Entry;
use crate::lower::arity::Held;
use crate::lower::arity::Key;
use crate::lower::arity::Place;
use crate::lower::arity::separated;
use crate::lower::closed;
use crate::lower::exhausted;
use crate::lower::identity::related;
use crate::lower::lowered;
use crate::lower::model::bundle_dependence;
use crate::lower::native::worded;
use crate::module::FamilyIndex;
use crate::module::Half;
use crate::module::Operand;
use crate::module::WordsForm;
use crate::origin::Origin;
use crate::resolve::Frame;
use crate::resolve::SurfaceName;
use crate::resolve::TypeFormer;
use crate::resolve::homed_former;
use crate::resolve::type_former;
use crate::resolve::type_head;
use crate::unit::ImportTarget;

impl<'source> Context<'_, 'source>
{
    /// The source text of `placed`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a node with a source fragment yields that fragment; an absent
    ///   fragment yields empty text.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — source literal text is interpreted at its own syntax
    ///   node and malformed lexemes retain their exact refusal span.
    /// - witness: `gandr-surface-lowering::lower::tests::a_malformed_integer_literal_is_refused`
    /// - witness: `gandr-surface-lowering::lower::tests::a_malformed_text_literal_is_refused`
    #[spec(
        ensures: |ret| {
            self.tree.fragment(placed.node).map_or_else(
                || ret.as_ref().is_empty(),
                |fragment| ret.as_ref() == fragment.as_ref(),
            )
        },
    )]
    #[must_use]
    #[inline]
    pub fn text_at(
        &self,
        placed: Placed,
    ) -> SourceFragment<'source>
    {
        self.tree
            .fragment(placed.node)
            .unwrap_or_else(|| SourceFragment::from(""))
    }

    /// The name `placed` spells.
    ///
    /// # Specification
    /// trivial.
    #[must_use]
    #[inline]
    pub fn name_at(
        &self,
        placed: Placed,
    ) -> SurfaceName<'source>
    {
        SurfaceName::from(self.text_at(placed))
    }

    /// The block naming the form `position` belongs to: its descendants' block
    /// for a top-level form, and its own block for any other node.
    ///
    /// # Specification
    /// - requires: nothing — a position the tree does not hold is admissible.
    /// - ensures: for a top-level form with descendants, the block they lie in;
    ///   otherwise `position`'s own block, which is its form's block for a node
    ///   below a top-level form.
    /// - provides: the form a frame is numbered in (`Lowerer::enter`).
    /// - fails: never.
    /// - panics: none.
    /// - intension: one read of the tree's form index.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a module's frames keep their coordinates when one
    ///   form before them takes another binder.
    /// - witness: `gandr-surface-lowering::tests::scopes::a_form_s_frames_keep_their_coordinates_when_another_form_changes_4457`
    #[spec(ensures: |ret| self.tree.descendants(position).is_some() || ret == position.block())]
    #[must_use]
    #[inline]
    pub fn form_of(
        &self,
        position: NodeIndex,
    ) -> LayoutBlock
    {
        self.tree
            .descendants(position)
            .and_then(|mut descendants| descendants.next())
            .map_or_else(|| position.block(), NodeIndex::block)
    }

    /// How `position` is read.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a live position yields its stored reading; an absent position
    ///   is unread.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — paired declarations and refused siblings retain
    ///   distinct readings through the ascending classification sweep.
    /// - witness: `gandr-surface-lowering::lower::tests::a_completed_declaration_lowers_both_halves`
    /// - witness: `gandr-surface-lowering::lower::tests::a_refused_declaration_leaves_the_others_lowered`
    #[spec(
        ensures: |ret| {
            ret == self
                .readings
                .get(position)
                .copied()
                .unwrap_or(Reading::Unread)
        },
    )]
    #[must_use]
    #[inline]
    pub fn reading(
        &self,
        position: NodeIndex,
    ) -> Reading
    {
        self.readings
            .get(position)
            .copied()
            .unwrap_or(Reading::Unread)
    }

    /// The key a plan keeps for the operands at the positions `written`
    /// names.
    ///
    /// # Specification
    /// trivial.
    #[must_use]
    #[inline]
    pub fn kept(
        &self,
        written: Stretch,
    ) -> FormStretch
    {
        self.operands
            .since_until(At::from(written.start), At::from(written.end))
    }

    /// What `position` lowered to.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a live position yields its stored lowering result; a missing
    ///   position is unminted.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — independently lowered children feed their parent and
    ///   a refused declaration does not prevent its sibling from lowering.
    /// - witness: `gandr-surface-lowering::lower::tests::force_and_application_lower_over_their_children`
    /// - witness: `gandr-surface-lowering::lower::tests::a_refused_declaration_leaves_the_others_lowered`
    #[spec(
        ensures: |ret| {
            ret == self
                .lowered
                .get(position)
                .copied()
                .unwrap_or(Maybe::Absent(lowered::Absent::Unminted))
        },
    )]
    #[inline]
    pub fn lowered_at(
        &self,
        position: NodeIndex,
    ) -> Maybe<Lowered, lowered::Absent>
    {
        self.lowered
            .get(position)
            .copied()
            .unwrap_or(Maybe::Absent(lowered::Absent::Unminted))
    }

    /// The value `position` lowered to.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: an unminted result preserves its reason, the requested family
    ///   yields its id, and every other family yields an other-sort reason.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — concrete value, computation and type operands are
    ///   read back in their own families while assembling completed
    ///   declarations.
    /// - witness: `gandr-surface-lowering::lower::tests::a_completed_declaration_lowers_both_halves`
    /// - witness: `gandr-surface-lowering::lower::tests::force_and_application_lower_over_their_children`
    #[spec(
        ensures: |ret| {
            ret == match self.lowered_at(position) {
                | Maybe::Absent(reason) => Maybe::Absent(reason),
                | Maybe::Present(Lowered::Value(id)) => Maybe::Present(id),
                | Maybe::Present(_) => Maybe::Absent(lowered::Absent::OtherSort),
            }
        },
    )]
    #[inline]
    pub fn value_at(
        &self,
        position: NodeIndex,
    ) -> Maybe<ValueId, lowered::Absent>
    {
        self.lowered_at(position).and_then(|held| match held {
            Lowered::Value(id) => Maybe::Present(id),
            Lowered::Computation(_)
            | Lowered::ValueType(_)
            | Lowered::CompType(_)
            | Lowered::Function { .. } => Maybe::Absent(lowered::Absent::OtherSort),
        })
    }

    /// The computation `position` lowered to.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: an unminted result preserves its reason, the requested family
    ///   yields its id, and every other family yields an other-sort reason.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — concrete value, computation and type operands are
    ///   read back in their own families while assembling completed
    ///   declarations.
    /// - witness: `gandr-surface-lowering::lower::tests::a_completed_declaration_lowers_both_halves`
    /// - witness: `gandr-surface-lowering::lower::tests::force_and_application_lower_over_their_children`
    #[spec(
        ensures: |ret| {
            ret == match self.lowered_at(position) {
                | Maybe::Absent(reason) => Maybe::Absent(reason),
                | Maybe::Present(Lowered::Computation(id)) => Maybe::Present(id),
                | Maybe::Present(_) => Maybe::Absent(lowered::Absent::OtherSort),
            }
        },
    )]
    #[inline]
    pub fn computation_at(
        &self,
        position: NodeIndex,
    ) -> Maybe<ComputationId, lowered::Absent>
    {
        self.lowered_at(position).and_then(|held| match held {
            Lowered::Computation(id) => Maybe::Present(id),
            Lowered::Value(_)
            | Lowered::ValueType(_)
            | Lowered::CompType(_)
            | Lowered::Function { .. } => Maybe::Absent(lowered::Absent::OtherSort),
        })
    }

    /// The value type `position` lowered to.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: an unminted result preserves its reason, the requested family
    ///   yields its id, and every other family yields an other-sort reason.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — concrete value, computation and type operands are
    ///   read back in their own families while assembling completed
    ///   declarations.
    /// - witness: `gandr-surface-lowering::lower::tests::a_completed_declaration_lowers_both_halves`
    /// - witness: `gandr-surface-lowering::lower::tests::force_and_application_lower_over_their_children`
    #[spec(
        ensures: |ret| {
            ret == match self.lowered_at(position) {
                | Maybe::Absent(reason) => Maybe::Absent(reason),
                | Maybe::Present(Lowered::ValueType(id)) => Maybe::Present(id),
                | Maybe::Present(_) => Maybe::Absent(lowered::Absent::OtherSort),
            }
        },
    )]
    #[inline]
    pub fn value_type_at(
        &self,
        position: NodeIndex,
    ) -> Maybe<ValueTypeId, lowered::Absent>
    {
        self.lowered_at(position).and_then(|held| match held {
            Lowered::ValueType(id) => Maybe::Present(id),
            Lowered::Value(_)
            | Lowered::Computation(_)
            | Lowered::CompType(_)
            | Lowered::Function { .. } => Maybe::Absent(lowered::Absent::OtherSort),
        })
    }

    /// The computation type `position` lowered to.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: an unminted result preserves its reason, the requested family
    ///   yields its id, and every other family yields an other-sort reason.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — concrete value, computation and type operands are
    ///   read back in their own families while assembling completed
    ///   declarations.
    /// - witness: `gandr-surface-lowering::lower::tests::a_completed_declaration_lowers_both_halves`
    /// - witness: `gandr-surface-lowering::lower::tests::force_and_application_lower_over_their_children`
    #[spec(
        ensures: |ret| {
            ret == match self.lowered_at(position) {
                | Maybe::Absent(reason) => Maybe::Absent(reason),
                | Maybe::Present(Lowered::CompType(id)) => Maybe::Present(id),
                | Maybe::Present(_) => Maybe::Absent(lowered::Absent::OtherSort),
            }
        },
    )]
    #[inline]
    pub fn comp_type_at(
        &self,
        position: NodeIndex,
    ) -> Maybe<CompTypeId, lowered::Absent>
    {
        self.lowered_at(position).and_then(|held| match held {
            Lowered::CompType(id) => Maybe::Present(id),
            Lowered::Value(_)
            | Lowered::Computation(_)
            | Lowered::ValueType(_)
            | Lowered::Function { .. } => Maybe::Absent(lowered::Absent::OtherSort),
        })
    }

    /// The declared type the function tail at `position` lowered to.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a function yields its stored signature result; an unminted
    ///   result preserves its reason and other families yield an other-sort
    ///   reason.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — signed and unsigned function tails preserve the body
    ///   while differing in whether they supply a derived signature.
    /// - witness: `gandr-surface-lowering::lower::tests::a_function_tail_lowers_to_a_thunked_lambda_chain`
    /// - witness: `gandr-surface-lowering::lower::tests::a_tail_missing_a_type_writes_its_definition_alone`
    #[spec(
        ensures: |ret| {
            ret == match self.lowered_at(position) {
                | Maybe::Absent(reason) => Maybe::Absent(reason),
                | Maybe::Present(Lowered::Function { signature, .. }) => signature,
                | Maybe::Present(_) => Maybe::Absent(lowered::Absent::OtherSort),
            }
        },
    )]
    #[inline]
    pub fn signature_at(
        &self,
        position: NodeIndex,
    ) -> Maybe<ValueTypeId, lowered::Absent>
    {
        self.lowered_at(position).and_then(|held| match held {
            Lowered::Function { signature, .. } => signature,
            Lowered::Value(_)
            | Lowered::Computation(_)
            | Lowered::ValueType(_)
            | Lowered::CompType(_) => Maybe::Absent(lowered::Absent::OtherSort),
        })
    }

    /// The body the function tail at `position` lowered to.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a function yields its body id; an unminted result preserves
    ///   its reason and other families yield an other-sort reason.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — signed and unsigned function tails preserve the body
    ///   while differing in whether they supply a derived signature.
    /// - witness: `gandr-surface-lowering::lower::tests::a_function_tail_lowers_to_a_thunked_lambda_chain`
    /// - witness: `gandr-surface-lowering::lower::tests::a_tail_missing_a_type_writes_its_definition_alone`
    #[spec(
        ensures: |ret| {
            ret == match self.lowered_at(position) {
                | Maybe::Absent(reason) => Maybe::Absent(reason),
                | Maybe::Present(Lowered::Function { body, .. }) => Maybe::Present(body),
                | Maybe::Present(_) => Maybe::Absent(lowered::Absent::OtherSort),
            }
        },
    )]
    #[inline]
    pub fn function_body_at(
        &self,
        position: NodeIndex,
    ) -> Maybe<ValueId, lowered::Absent>
    {
        self.lowered_at(position).and_then(|held| match held {
            Lowered::Function { body, .. } => Maybe::Present(body),
            Lowered::Value(_)
            | Lowered::Computation(_)
            | Lowered::ValueType(_)
            | Lowered::CompType(_) => Maybe::Absent(lowered::Absent::OtherSort),
        })
    }

    /// The origin of a core node the syntax node at `position` wrote.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a live syntax node yields its own position and span as
    ///   written provenance; a missing node is unminted.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — each minted family records the syntax origin that
    ///   produced it, independently of inserted bridges.
    /// - witness: `gandr-surface-lowering::lower::tests::every_minted_node_has_an_origin`
    /// - witness: `gandr-surface-lowering::lower::tests::an_author_written_force_is_not_marked_inserted`
    #[spec(
        ensures: |ret| {
            ret == self
                .tree
                .node(position)
                .map_or(Maybe::Absent(lowered::Absent::Unminted), |node| {
                    Maybe::Present(Origin::new(position, node.span()))
                })
        },
    )]
    #[inline]
    pub fn origin_at(
        &self,
        position: NodeIndex,
    ) -> Maybe<Origin, lowered::Absent>
    {
        self.tree
            .node(position)
            .map_or(Maybe::Absent(lowered::Absent::Unminted), |node| {
                Maybe::Present(Origin::new(position, node.span()))
            })
    }

    /// The named kind and former of the form at `at`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the form's kind and former; nothing for a node that is no
    ///   form.
    /// - fails: [`LoweringRefusal::UnknownMold`].
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoweringRefusal::UnknownMold`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a type entry's key is told from its type by kind.
    /// - witness: `gandr-surface-lowering::lower::arity::tests::a_telescope_type_lowers_by_its_arity`
    #[spec(ensures: |ret| ret.is_ok() || matches!(ret, Err(LoweringRefusal::UnknownMold { .. })))]
    #[inline]
    pub fn form_at(
        &self,
        at: Placed,
    ) -> Result<Option<(FormName, Former)>, LoweringRefusal<'source>>
    {
        let Some(node) = self.tree.node(at.node)
        else {
            return Ok(None);
        };

        Ok(match shape_of(self.pbg, node)? {
            Shape::Form { name, former } => Some((name, former)),
            Shape::Root | Shape::Repair(_) | Shape::Layout => None,
        })
    }

    /// Read a label after its dot: `.l` or `.i`.
    ///
    /// # Specification
    /// - requires: `cursor` stands at the label's `.`.
    /// - ensures: a name for an identifier, an index for a decimal number.
    /// - fails: a misplaced tile for anything else.
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoweringRefusal::MalformedForm`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — named and indexed labels each reach their former.
    /// - witness: `gandr-surface-lowering::lower::arity::tests::an_injection_takes_its_index_from_its_label`
    #[spec(ensures: |ret| !matches!(ret, Ok(Key::Positional)))]
    #[inline]
    pub fn dotted(
        &self,
        site: Site,
        cursor: &mut Cursor<'_>,
    ) -> Result<Key<'source>, LoweringRefusal<'source>>
    {
        closed(site, cursor, TileName::DOT)?;
        if let Maybe::Present(word) = cursor.tile(TileName::IDENTIFIER) {
            return Ok(Key::Label(self.name_at(word), word));
        }
        let Maybe::Present(number) = cursor.tile(TileName::NUMBER)
        else {
            return Err(site.fault(cursor.here(), FormFault::MisplacedTile));
        };
        let name = self.name_at(number);
        let spelled: &str = name.as_ref();

        spelled
            .parse::<usize>()
            .map(|index| Key::Index(index, name, number))
            .map_err(|_overflow| site.fault(number.span, FormFault::MisplacedTile))
    }

    /// Read the entries of a telescope pattern up to `}`: each a punned
    /// `.l`, a renamed `.l = p`, or a positional `p`.
    ///
    /// # Specification
    /// - requires: `cursor` stands just past the pattern's `#{`.
    /// - ensures: every entry in written order, the cursor exhausted; a punned
    ///   entry holds its label tile.
    /// - fails: a misplaced tile at an undotted key `k = p`, at a punned index,
    ///   and at a separator out of place; a hole's own fault.
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoweringRefusal::MalformedForm`].
    ///
    /// # Termination
    /// Every round consumes at least one piece of the finite cursor or
    /// refuses.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — punned, renamed and positional entries, and an
    ///   undotted key.
    /// - witness: `gandr-surface-lowering::lower::native::tests::telescope_patterns_split_and_project`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |entries| entries.iter().all(|entry| !matches!(entry.held, Held::Punned(_)) || matches!(entry.key, Key::Label(..)))))]
    #[inline]
    pub fn pattern_entries(
        &self,
        here: Site,
        cursor: &mut Cursor<'_>,
    ) -> Result<Vec<Entry<'source>>, LoweringRefusal<'source>>
    {
        let mut entries = Vec::new();
        while let Maybe::Absent(_) = cursor.tile(TileName::BRACE_CLOSE) {
            let entry = if let Maybe::Present(_) = cursor.at(TileName::DOT) {
                let key = self.dotted(here, cursor)?;
                let held = if let Maybe::Present(_) = cursor.tile(TileName::EQUALS) {
                    Held::Operand(here.one(cursor.operands())?)
                }
                else {
                    match key {
                        Key::Label(_, label) => Held::Punned(label),
                        Key::Index(_, _, written) => {
                            return Err(here.fault(written.span, FormFault::MisplacedTile));
                        },
                        Key::Positional => {
                            return Err(here.fault(cursor.here(), FormFault::MisplacedTile));
                        },
                    }
                };
                Entry { key, held }
            }
            else {
                let first = here.one(cursor.operands())?;
                if let Maybe::Present(equals) = cursor.at(TileName::EQUALS) {
                    return Err(here.fault(equals.span, FormFault::MisplacedTile));
                }
                Entry {
                    key: Key::Positional,
                    held: Held::Operand(first),
                }
            };
            entries.push(entry);
            separated(here, cursor, TileName::BRACE_CLOSE)?;
        }
        exhausted(here, cursor)?;

        Ok(entries)
    }

    /// The unary type former `name` spells in the source being lowered: an
    /// ambient former, or one a listed import of its home binds,
    /// `import std.list (List);` (#4520).
    ///
    /// # Specification
    /// - requires: nothing — every identifier is admissible input.
    /// - ensures: the ambient table's answer when it has one; else the former
    ///   that the home of a resolved listed import of the current source
    ///   answers under `name`; else the absence.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a list type in a source that lists `List` from
    ///   `std.list` lowers to the native list, and one in a source that does
    ///   not is an unresolved head.
    /// - witness: `gandr-surface-lowering::lower::tests::a_list_type_resolves_only_through_its_listing_4520`
    #[spec(
        ensures: |ret| match type_former(name) {
            | Maybe::Present(ambient) => ret == Maybe::Present(ambient),
            | Maybe::Absent(_) => true,
        },
    )]
    #[inline]
    pub fn former(
        &self,
        name: SurfaceName<'source>,
    ) -> Maybe<TypeFormer, type_head::Absent>
    {
        let ambient = type_former(name);
        if let Maybe::Present(_) = ambient {
            return ambient;
        }
        self.listed_head(name, homed_former)
            .map_or(ambient, Maybe::Present)
    }

    /// What `homed` answers for `name` at the module of the first resolved
    /// listed import of the current source that lists `name`.
    ///
    /// # Specification
    /// - requires: `homed` reads a home table by module and name.
    /// - ensures: the first answer `homed` gives over the current source's
    ///   resolved listings of `name`, in import order; none when no listing
    ///   names it or no home answers.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the clause restates the walk over the current
    ///   source's imports.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::former`] and `Lowerer::atom`.
    /// - witness: `gandr-surface-lowering::lower::tests::a_list_type_resolves_only_through_its_listing_4520`
    /// - witness: `gandr-surface-lowering::lower::tests::a_buffer_type_resolves_only_through_its_listing_4522`
    #[inline]
    pub fn listed_head<Head>(
        &self,
        name: SurfaceName<'source>,
        homed: fn(SurfaceName<'_>, SurfaceName<'_>) -> Maybe<Head, type_head::Absent>,
    ) -> Option<Head>
    {
        self.collected
            .imports
            .declarations()
            .iter()
            .filter(|import| {
                import.source() == self.current.source
                    && matches!(
                        import.resolution(),
                        ImportResolution::Path(ImportTarget::Source(_))
                    )
            })
            .find_map(|import| match (import.opening(), import.module()) {
                (&Opening::Listed(ref listed), Maybe::Present(module))
                    if listed
                        .iter()
                        .any(|&(held, _)| held.as_ref() == name.as_ref()) =>
                {
                    match homed(module, name) {
                        Maybe::Present(head) => Some(head),
                        Maybe::Absent(_) => None,
                    }
                },
                (&(Opening::Listed(_) | Opening::Every | Opening::Nothing), _) => None,
            })
    }

    /// The sort a family's applications stand at: [`Produced::CompType`] for a
    /// family whose definition is a computation type, and
    /// [`Produced::ValueType`] for any other.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the computation-type sort exactly when the family's
    ///   definition is among the lowerer's computation members; the value-type
    ///   sort otherwise, an unknown family too.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a family into returners and a family into value types
    ///   each stand at their own sort.
    /// - witness: `gandr-surface-lowering::tests::modules::a_type_member_names_a_computation_type_3080`
    #[spec(ensures: |ret| matches!(ret, Produced::CompType | Produced::ValueType))]
    #[must_use]
    #[inline]
    pub fn family_produced(
        &self,
        family: FamilyIndex,
    ) -> Produced
    {
        match self.collected.families.get(family.0) {
            Some(member) if self.computation_members.contains(&member.defined.node) => {
                Produced::CompType
            },
            Some(_) | None => Produced::ValueType,
        }
    }

    /// The fields a pattern splits at the type `stated`, when it is a
    /// theory's models and their record nests pairs.
    ///
    /// # Specification
    /// - requires: `stated` is a type's syntax node, already classified.
    /// - ensures: through the transparent plans of parentheses, for a type
    ///   planned as `Model(T)` whose outermost record has a field a later one
    ///   names, one entry per component of `T`'s signature in signature order,
    ///   labelled by the component's name and placed at `at`, beside whether
    ///   each but the last binds the ones after it, as `Lowerer::bundle_type`
    ///   nests them; the other-former absence for a bundle keyed by names,
    ///   which a pattern splits as the record it is, and for every other type.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Termination
    /// Each step follows a transparent plan to the child it stands for,
    /// strictly deeper in the finite tree.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a positional and a labelled pattern at a toggle's
    ///   models bind its carrier, its start, its step and its reading.
    /// - witness: `gandr-surface-lowering::tests::modules::models::a_pattern_at_a_model_type_splits_its_fields`
    #[spec(ensures: |ret| match ret {
        Maybe::Present((ref entries, ref links)) => links.len().saturating_add(1) == entries.len(),
        Maybe::Absent(_) => true,
    })]
    #[inline]
    pub fn stated_bundle(
        &self,
        stated: NodeIndex,
        at: Placed,
    ) -> Maybe<(Vec<arity::Entry<'source>>, Vec<arity::Dependent>), related::Absent>
    {
        let otherwise = Maybe::Absent(related::Absent::Otherwise);
        let mut node = stated;
        let bundled = loop {
            match self.plans.get(node) {
                Some(&Plan::Transparent(inner)) => node = inner,
                Some(&Plan::Bundle(ref bundled)) => break bundled,
                _ => return otherwise,
            }
        };
        let Some(theory) = bundled.theories.first()
        else {
            return otherwise;
        };
        let binds = bundle_dependence(&theory.signature);
        if !binds.iter().any(|binds| binds.0) {
            return otherwise;
        }
        let entries: Vec<arity::Entry<'source>> = theory
            .signature
            .components
            .iter()
            .map(|component| arity::Entry {
                key: arity::Key::Label(self.name_at(component.named), at),
                held: arity::Held::Operand(at),
            })
            .collect();
        let links = binds
            .iter()
            .take(entries.len().saturating_sub(1))
            .map(|binds| arity::Dependent(binds.0))
            .collect();

        Maybe::Present((entries, links))
    }

    /// The variable a call at `site`, read under `frame`, passes for the
    /// instance `entry` of `function` it omits: the one instance of the
    /// entry's interface standing in scope.
    ///
    /// # Specification
    /// - requires: `entry` is an instance of `function`'s merged telescope.
    /// - ensures: the index, where `frame` stands, of the one binder in scope
    ///   holding an instance of the entry's interface — a capability scope's
    ///   capability, or an instance a label of the caller's own row binds.
    /// - fails: [`LoweringRefusal::InstanceUnanswered`] when none stands;
    ///   [`LoweringRefusal::InstanceAmbiguous`] naming the innermost two when
    ///   several do; a fault at the call for an entry naming no interface.
    /// - panics: none.
    ///
    /// # Errors
    /// As `- fails:`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — one scope of the interface resolves the call to its
    ///   capability beneath a binder of each zone, none refuses the call as
    ///   unanswered and two as ambiguous, naming both.
    /// - witness: `gandr-surface-lowering::lower::implicit::tests::an_omitted_instance_is_the_one_handled_in_scope_2271`
    /// - witness: `gandr-surface-lowering::lower::implicit::tests::an_omitted_instance_is_refused_when_none_or_several_stand_2271`
    #[spec(ensures: |ret| ret.is_ok() || matches!(ret, Err(LoweringRefusal::InstanceUnanswered { .. } | LoweringRefusal::InstanceAmbiguous { .. } | LoweringRefusal::MalformedForm { .. })))]
    #[inline]
    pub fn resolved_instance(
        &self,
        site: Site,
        frame: Frame,
        function: SurfaceName<'source>,
        entry: crate::module::TelescopeEntry<'source>,
    ) -> Result<DeBruijnIndex, LoweringRefusal<'source>>
    {
        let Maybe::Present(path) = entry.interface
        else {
            return Err(site.fault(site.at.span, FormFault::MisplacedTile));
        };
        let named = self.instance_interface(path);
        let wanted = EffectName::from(named.as_ref());
        let mut standing = self.scope.bindings(frame).filter(|&(_, bound)| {
            self.answered.get(&bound.binder) == Some(&wanted)
                || self
                    .labelled
                    .get(&bound.binder)
                    .is_some_and(|&(ref interface, _)| *interface == wanted)
        });
        let Some((first, only)) = standing.next()
        else {
            return Err(LoweringRefusal::InstanceUnanswered {
                span: site.at.span,
                function,
                instance: entry.name,
                interface: named,
            });
        };
        if let Some((second, _)) = standing.next() {
            return Err(LoweringRefusal::InstanceAmbiguous {
                span: site.at.span,
                function,
                instance: entry.name,
                interface: named,
                first,
                second,
            });
        }

        Ok(only.index)
    }

    /// The interface an instance's row label names, as the bytes `path` of its
    /// whole path spell it: `std.io.Console.Eff`.
    ///
    /// # Specification
    /// trivial.
    #[must_use]
    #[inline]
    pub fn instance_interface(
        &self,
        path: ByteSpan,
    ) -> SurfaceName<'source>
    {
        SurfaceName::from(
            self.tree
                .spanned(path)
                .unwrap_or_else(|| SourceFragment::from("")),
        )
    }

    /// The target and the selected name of one link of a type path, and the
    /// module names the link passes, read from its pieces.
    ///
    /// # Specification
    /// - requires: `pieces` is the reading of a type path covering `span`.
    /// - ensures: the operand the type is selected from; the pieces between the
    ///   link's first dot and its selected name, each module name it passes and
    ///   the dot after it, `inner .` in `Sealed.inner.T` and `b . c .` in
    ///   `a.b.c.T`, empty for a link that passes none; and the selected name
    ///   after its last dot: a type name, or a value name the link applies,
    ///   `ext` in `Standard.ext(a, b)` (#5213).
    /// - provides: the link half of `Lowerer::type_path`, one link through a
    ///   module path of any length.
    /// - fails: yields the misplaced-tile refusal when the pieces are not an
    ///   operand, a dot, module names each followed by a dot, and a type name
    ///   or a value name.
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoweringRefusal::MalformedForm`] for a malformed link.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a one-link and a two-link path preserve their targets
    ///   and selected names, a link through a nested module keeps the module,
    ///   and a link through a module path of three names keeps each.
    /// - witness: `gandr-surface-lowering::tests::modules::a_qualified_type_reference_resolves_through_the_namespace`
    /// - witness: `gandr-surface-lowering::tests::modules::models::a_sealed_nested_model_s_sort_is_spelled_by_its_path_1311`
    /// - witness: `gandr-surface-lowering::tests::namespace::a_type_reads_through_a_module_path_of_any_length_2874`
    #[spec(
        ensures: |ret| {
            ret.as_ref().map_or(true, |&(target, modules, selected)| {
                pieces.first() == Some(&Piece::Operand(target))
                    && matches!(pieces.get(1), Some(&Piece::Tile { label: TileName::DOT, .. }))
                    && modules.len() % 2 == 0
                    && matches!(pieces.get(modules.len().saturating_add(2)), Some(&Piece::Tile {
                        label: TileName::TYPE_IDENTIFIER | TileName::TYPE_VARIABLE,
                        at,
                    }) if at == selected)
            })
        },
    )]
    #[inline]
    pub fn type_link<'pieces>(
        site: Site,
        pieces: &'pieces [Piece],
        span: ByteSpan,
    ) -> Result<(Placed, &'pieces [Piece], Placed), LoweringRefusal<'source>>
    {
        let mut cursor = Cursor::new(pieces, span);
        let Maybe::Present(Piece::Operand(target)) = cursor.read()
        else {
            return Err(site.fault(cursor.here(), FormFault::MisplacedTile));
        };
        let Maybe::Present(_dot) = cursor.tile(TileName::DOT)
        else {
            return Err(site.fault(cursor.here(), FormFault::MisplacedTile));
        };
        let mut passed = 0_usize;
        let selected = loop {
            if let Maybe::Present(name) = cursor.tile(TileName::TYPE_VARIABLE) {
                if let Maybe::Present(_dot) = cursor.tile(TileName::DOT) {
                    passed = passed.saturating_add(2_usize);
                    continue;
                }
                // A value name the link ends at, which its argument list
                // applies (#5213).
                break name;
            }
            let Maybe::Present(selected) = cursor.tile(TileName::TYPE_IDENTIFIER)
            else {
                return Err(site.fault(cursor.here(), FormFault::MisplacedTile));
            };
            break selected;
        };
        let modules = pieces
            .get(2_usize .. passed.saturating_add(2_usize))
            .unwrap_or_default();

        Ok((target, modules, selected))
    }

    /// The target and the selected name of one selection, read from its
    /// pieces.
    ///
    /// # Specification
    /// - requires: `pieces` is the reading of a projection covering `span`.
    /// - ensures: the operand the selection is taken from and the name tile
    ///   after its dot.
    /// - provides: the one-link half of `Lowerer::projection`.
    /// - fails: yields the misplaced-tile refusal when the pieces are not an
    ///   operand, a dot and a name.
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoweringRefusal::MalformedForm`] for a malformed selection.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — single and deeply nested selections preserve their
    ///   target and own member positions, which locate an unknown member at its
    ///   depth.
    /// - witness: `gandr-surface-lowering::tests::modules::nested_modules_lower_as_parent_members_and_project`
    /// - witness: `gandr-surface-lowering::tests::modules::a_deep_module_path_is_governed_at_the_depth_that_binds_it`
    #[spec(
        ensures: |ret| {
            ret.as_ref().map_or(true, |&(target, selected)| {
                pieces.first() == Some(&Piece::Operand(target))
                    && matches!(
                        pieces.get(1),
                        Some(&Piece::Tile {
                            label: TileName::DOT,
                            ..
                        })
                    )
                    && matches!(
                        pieces.get(2),
                        Some(&Piece::Tile {
                            label: TileName::IDENTIFIER | TileName::CONSTRUCTOR,
                            at,
                        }) if at == selected
                    )
            })
        },
    )]
    #[inline]
    pub fn link(
        site: Site,
        pieces: &[Piece],
        span: ByteSpan,
    ) -> Result<(Placed, Placed), LoweringRefusal<'source>>
    {
        let mut cursor = Cursor::new(pieces, span);
        let Maybe::Present(Piece::Operand(target)) = cursor.read()
        else {
            return Err(site.fault(cursor.here(), FormFault::MisplacedTile));
        };
        let Maybe::Present(_dot) = cursor.tile(TileName::DOT)
        else {
            return Err(site.fault(cursor.here(), FormFault::MisplacedTile));
        };
        let selected = match cursor.tile(TileName::IDENTIFIER) {
            Maybe::Present(selected) => selected,
            Maybe::Absent(_) => match cursor.tile(TileName::CONSTRUCTOR) {
                Maybe::Present(selected) => selected,
                Maybe::Absent(_) => {
                    return Err(site.fault(cursor.here(), FormFault::MisplacedTile));
                },
            },
        };
        Ok((target, selected))
    }

    /// Read the entries of a tuple pattern up to `)`, each positional.
    ///
    /// # Specification
    /// - requires: `cursor` stands just past the pattern's `(`.
    /// - ensures: every entry in written order, the cursor exhausted.
    /// - fails: a misplaced tile, and a hole's own fault.
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoweringRefusal::MalformedForm`].
    ///
    /// # Termination
    /// Every round consumes at least one piece of the finite cursor or
    /// refuses.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a tuple pattern splits as the telescope does.
    /// - witness: `gandr-surface-lowering::lower::native::tests::telescope_patterns_split_and_project`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |entries| entries.iter().all(|entry| matches!(entry.key, Key::Positional))))]
    #[inline]
    pub fn tuple_entries(
        here: Site,
        cursor: &mut Cursor<'_>,
    ) -> Result<Vec<Entry<'source>>, LoweringRefusal<'source>>
    {
        let mut entries = Vec::new();
        while let Maybe::Absent(_) = cursor.tile(TileName::PAREN_CLOSE) {
            entries.push(Entry {
                key: Key::Positional,
                held: Held::Operand(here.one(cursor.operands())?),
            });
            separated(here, cursor, TileName::PAREN_CLOSE)?;
        }
        exhausted(here, cursor)?;

        Ok(entries)
    }

    /// The index and the entry the label `name`, written at `written`, names
    /// among `stated`.
    ///
    /// # Specification
    /// - requires: `stated` are a stated type's entries.
    /// - ensures: the first entry so labelled, with its index.
    /// - fails: the unresolved-name refusal at `written` when none is.
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoweringRefusal::UnresolvedName`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a label the stated type has and one it lacks.
    /// - witness: `gandr-surface-lowering::lower::arity::tests::an_injection_takes_its_index_from_its_label`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |&(place, _)| place.0 < stated.len()))]
    #[inline]
    pub fn labelled_in(
        stated: &[Entry<'source>],
        name: SurfaceName<'source>,
        written: Placed,
    ) -> Result<(Place, Entry<'source>), LoweringRefusal<'source>>
    {
        stated
            .iter()
            .enumerate()
            .find(|&(_, entry)| matches!(entry.key, Key::Label(held, _) if held == name))
            .map(|(index, &entry)| (Place(index), entry))
            .ok_or(LoweringRefusal::UnresolvedName {
                span: written.span,
                name,
            })
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
    /// - witness: `gandr-surface-lowering::lower::identity::tests::a_derived_operation_synthesises_its_path_at_the_words`
    #[spec(ensures: |ret| matches!(ret, Maybe::Absent(_)) || matches!(
        self.collected.slots.get(usize::from(constant)).map(|slot| slot.definition),
        Some(Maybe::Present(Half { operand: Operand::Loop { .. } | Operand::Words(_), .. }))
    ))]
    #[inline]
    pub fn words_at(
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
}
