//! Implicit parameters in the lowering: a function whose telescope `@[a :
//! Type]` binds a value binds every parameter in its merged telescope's order
//! ([`crate::module::Plicity`]), and a call supplies the implicits by name,
//! `f[a = T](x)`, or omits them, `f(x)`.
//!
//! # Supply by name
//!
//! A call whose head instantiates a function with every resident written `a
//! = e` is that function applied to one argument per parameter of its merged
//! telescope: an implicit's argument is the resident naming it, in any
//! order, and an explicit one's the next argument the parentheses write. The
//! core sees an ordinary application: plicity is the declaration's metadata,
//! never type structure, so the declared type and the application are the
//! ones the function written with every parameter explicit would give.
//!
//! A supply where no call applies it, `apply(same[a = Integer], 3)`, is the
//! function applied to its implicits alone, a function of the rest: the
//! declaration taken as a value has every implicit determined where it is
//! taken.
//!
//! # Nomination
//!
//! A call that omits an implicit, `same(3)`, passes in its place a hole the
//! call nominates ([`gandr_core_term::hole::HoleId::nominated`]), apart from
//! every hole the text writes, and the application is otherwise the one the
//! supply by name gives. The checker solves each nominated hole from the
//! comparisons the call's explicit arguments force and supplies the
//! solution, so the body it accepts is the one `same[a = Integer](3)` lowers
//! to; the lowering keeps which call nominated each hole, and for which
//! implicit ([`Nomination`]), so a refusal names it.
//!
//! A wildcard `_` written where a value is read is the same hole the text
//! asks for: the lowering nominates one for it, recorded as a wildcard, and
//! the checker solves it as it solves an omitted implicit, from the
//! comparisons that force it, `idAt(_, 3)` lowering to the body
//! `idAt(Integer, 3)` lowers to. Where a computation is read the wildcard
//! leaves the fragment: the solver binds values.
//!
//! # Boundaries
//!
//! - A use of a function with implicits standing as a value supplies all of
//!   them: [`LoweringRefusal::ImplicitUnsupplied`] names the first one it
//!   leaves out, and a bare name of the function leaves out all. A call
//!   nominates every implicit it leaves out.
//! - A call writing one argument per parameter in its parentheses, the
//!   implicits among them, is [`LoweringRefusal::ImplicitInParentheses`].
//! - A resident naming no implicit of the function is
//!   [`LoweringRefusal::UnresolvedName`] at the name, unless it names one of
//!   the function's stage binders: that resident supplies a stage, which
//!   crosses beside the declaration rather than as an argument
//!   ([`super::staged`]).
//! - A supply standing as a value whose merged telescope places an implicit
//!   after an explicit parameter, whose type mentions it, opens a lambda for
//!   each explicit parameter before the last implicit and applies the function
//!   to their variables: `chosen[x = 7]`, for `chosen @[x : t] (t : Type)`,
//!   lowers to `λ t. chosen(t)[x = 7]`. A supplied value is read where the
//!   supply stands and raised past those lambdas, so it names none of them.
//! - A stage crosses only at a call's head, so a supply of one standing as a
//!   value opens a lambda for every explicit parameter and stands as the call.
//! - The grammar writes no telescope after `def rec`, so a recursive function
//!   has no implicits.

use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use alloc::vec::Vec;

use anodized::spec;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::DeBruijnIndex;
use gandr_surface_syntax::NodeIndex;
use quenchant_shape::shape::Maybe;

use super::Lowerer;
use super::Parameter;
use super::Plan;
use super::Produced;
use super::Reading;
use super::Resolved;
use super::Site;
use super::Stretch;
use super::arguments;
use super::arity;
use super::stated;
use crate::error::FormFault;
use crate::error::FragmentBoundary;
use crate::error::LoweringRefusal;
use crate::form::Cursor;
use crate::form::Former;
use crate::form::Piece;
use crate::form::Placed;
use crate::form::Run;
use crate::form::Shape;
use crate::form::TileName;
use crate::form::read_pieces;
use crate::form::shape_of;
use crate::module::Plicity;
use crate::module::SlotIndex;
use crate::module::TelescopeEntry;
use crate::module::merged;
use crate::resolve::Frame;
use crate::resolve::SurfaceName;
use crate::unbuilt::Unbuilt;

#[cfg(test)]
mod tests;

/// How a supply's function is applied.
enum Use<'cursor>
{
    /// The head of a call, whose parentheses, at the cursor, write the
    /// explicit arguments.
    Called(Cursor<'cursor>),
    /// Standing where no call applies it, passed or returned as a value.
    Standing,
}

/// What a nominated hole stands for: an implicit a call omits, or a wildcard
/// the text writes.
///
/// # Specification
/// - requires: nothing.
/// - ensures: an omitted implicit keeps the function's name and the implicit's.
/// - provides: what the origin table records for the hole once it is minted,
///   and a refusal of the hole names.
/// - panics: none.
/// - executable: none — a record of names, holding no tree to check them
///   against.
///
/// # Adequacy
/// - hypothesis: L3 — a call omitting both implicits of `first` nominates one
///   hole per implicit, each naming it; a wildcard beside them nominates its
///   own.
/// - witness: `lower::implicit::tests::an_omitted_implicit_is_a_nominated_hole`
/// - witness: `lower::implicit::tests::a_wildcard_is_a_nominated_hole_of_its_own`
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum Nomination<'source>
{
    /// The implicit `implicit` of `function`, which a call omits.
    Omitted
    {
        /// The function the call applies.
        function: SurfaceName<'source>,
        /// The implicit the call omits.
        implicit: SurfaceName<'source>,
    },
    /// A wildcard `_` written where a value is read.
    Wildcard,
}

impl<'source> Lowerer<'_, 'source>
{
    /// The merged telescope of the function whose declaration holds `node`,
    /// when its telescope binds a value.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the entries the collection merged for the declaration owning
    ///   `node`; absent for a node no declaration owns and a declaration with
    ///   no implicit.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a function with an implicit and one without separate
    ///   the answers.
    /// - witness: `lower::implicit::tests::plicity_is_metadata_not_type_structure`
    #[spec(ensures: |ret| match ret {
        Maybe::Present(entries) => entries.iter().any(|entry| entry.plicity == Plicity::Implicit),
        Maybe::Absent(_) => true,
    })]
    pub(super) fn merged_at(
        &self,
        node: NodeIndex,
    ) -> Maybe<&[TelescopeEntry<'source>], merged::Absent>
    {
        let entries = match self.collected.owner_of(node) {
            Maybe::Present(slot) => self.collected.plicities.get(&slot),
            Maybe::Absent(_) => None,
        };
        if let Some(&Ok(ref entries)) = entries {
            Maybe::Present(entries.as_slice())
        }
        else {
            Maybe::Absent(merged::Absent::NoImplicit)
        }
    }

    /// The refusal the merge of the telescope of the function whose
    /// declaration holds `node` met, when it met one.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: `Ok` for a declaration whose telescope merged or binds no
    ///   value.
    /// - fails: the merge's own refusal, [`LoweringRefusal::TelescopeCycle`]
    ///   for parameters whose types mention each other.
    /// - panics: none.
    ///
    /// # Errors
    /// As `- fails:`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a telescope in a cycle and one that merges separate
    ///   the answers.
    /// - witness: `lower::implicit::tests::a_telescope_cycle_is_refused_naming_the_cycle`
    #[spec(ensures: |ret| ret.is_ok() || matches!(self.merged_at(node), Maybe::Absent(_)))]
    pub(super) fn merge_refusal(
        &self,
        node: NodeIndex,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let merged = match self.collected.owner_of(node) {
            Maybe::Present(slot) => self.collected.plicities.get(&slot),
            Maybe::Absent(_) => None,
        };
        match merged {
            Some(&Err(refusal)) => Err(refusal),
            Some(&Ok(_)) | None => Ok(()),
        }
    }

    /// Bind the parameters of the function `site` declares in its merged
    /// telescope's order, when it has one, under `frame`.
    ///
    /// # Specification
    /// - requires: `cursor` stands just past the parameter list's `(`;
    ///   `function` is the function tail's site.
    /// - ensures: for a function with a merged telescope, each entry is bound
    ///   in a frame extending the one before it, its type, when written, read
    ///   as a value type under that frame and recorded on its parameter; the
    ///   cursor then stands at the list's `)`, and the frame the last entry
    ///   bound is returned. Otherwise nothing changes and `frame` is returned.
    /// - fails: a binder's own refusal; a fault at the parameter list when it
    ///   ends before its `)`.
    /// - panics: none.
    ///
    /// # Errors
    /// As `- fails:`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an implicit whose type names a later explicit
    ///   parameter binds after it, and its declared type equals the one the
    ///   function written with every parameter explicit, in that order, gives.
    /// - witness: `lower::implicit::tests::plicity_is_metadata_not_type_structure`
    /// - witness: `lower::implicit::tests::a_forward_reference_from_the_prefix_binds_after_its_target`
    #[spec(
        captures: before = self.parameters.len(),
        ensures: |ret| ret.is_err() || self.parameters.len() >= before,
    )]
    pub(super) fn merged_parameters(
        &mut self,
        site: Site,
        function: Site,
        cursor: &mut Cursor<'_>,
        frame: Frame,
    ) -> Result<Frame, LoweringRefusal<'source>>
    {
        let Maybe::Present(entries) = self.merged_at(site.at.node)
        else {
            return Ok(frame);
        };
        let entries = entries.to_vec();
        let mut frame = frame;
        for entry in entries {
            let declared = match entry.declared {
                Maybe::Present(declared) => {
                    self.read(declared.node, Reading::ValueType(frame));
                    Maybe::Present(declared.node)
                },
                Maybe::Absent(_) => Maybe::Absent(stated::Absent::Unstated),
            };
            self.note_binder(entry.binder, entry.name)?;
            let written = Maybe::Present(entry.binder.span);
            let bound = match declared {
                Maybe::Present(declared) => self
                    .scope
                    .extend_typed(frame, entry.name, declared, written),
                Maybe::Absent(_) => self.scope.extend(frame, entry.name, written),
            };
            self.parameters.push(Parameter {
                binder: entry.binder.node,
                frame: bound,
                declared,
            });
            frame = Frame::Inner(bound);
        }
        while let Maybe::Absent(_) = cursor.at(TileName::PAREN_CLOSE) {
            if let Maybe::Absent(_) = cursor.read() {
                return Err(function.fault(cursor.here(), FormFault::MisplacedTile));
            }
        }

        Ok(frame)
    }

    /// Refuse the use at `site` of the declaration `constant` when the
    /// declaration has implicits and the use supplies none.
    ///
    /// # Specification
    /// - requires: the name at `site` resolved to `constant`.
    /// - ensures: `Ok` for a declaration with no implicit and for the head of a
    ///   call that supplies them.
    /// - fails: [`LoweringRefusal::ImplicitUnsupplied`] at `site`, naming the
    ///   declaration's first implicit, otherwise.
    /// - panics: none.
    ///
    /// # Errors
    /// As `- fails:`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a bare use and a supplied call separate the answers.
    /// - witness: `lower::implicit::tests::an_unsupplied_implicit_is_refused_with_its_slot_spelling`
    #[spec(ensures: |ret| ret.is_ok() || matches!(ret, Err(LoweringRefusal::ImplicitUnsupplied { .. })))]
    pub(super) fn supplied_or_refused(
        &self,
        site: Site,
        constant: ConstantIndex,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let slot = SlotIndex::from(usize::from(constant));
        let Some(&Ok(ref entries)) = self.collected.plicities.get(&slot)
        else {
            return Ok(());
        };
        if self.supplied.contains(&site.at.node) {
            return Ok(());
        }
        let Some(first) = entries
            .iter()
            .find(|entry| entry.plicity == Plicity::Implicit)
        else {
            return Ok(());
        };
        let function = self
            .collected
            .slots
            .get(usize::from(slot))
            .map_or(first.name, |declared| declared.name);

        Err(LoweringRefusal::ImplicitUnsupplied {
            span: site.at.span,
            function,
            implicit: first.name,
        })
    }

    /// Plan the call at `site` whose head names a function with implicits:
    /// each supplied by name or nominated where the call omits it, the
    /// function applied in its merged telescope's order; otherwise refused.
    ///
    /// # Specification
    /// - requires: `site` is a call read as a computation under `frame`;
    ///   `cursor` stands at its head.
    /// - ensures: [`arity::Planned`] true exactly when the head is a bare name
    ///   or an instantiation of a declaration with implicits or stage binders,
    ///   every resident `a = e` naming one, the call then planned as the
    ///   declaration applied to one argument per merged entry, an implicit's
    ///   the resident naming it or, where none does, the hole the call
    ///   nominates for it ([`Self::nominate`]), and an explicit one's the next
    ///   written argument, each written argument read as a value under `frame`
    ///   and the declaration's name as the head; a resident naming a stage
    ///   binder is no argument but a stage the head carries
    ///   ([`Self::stage_supplies`]); the head is recorded as supplied. False,
    ///   with nothing changed, for any other head.
    /// - fails: [`LoweringRefusal::ImplicitInParentheses`] for a call writing
    ///   one argument per parameter and omitting an implicit;
    ///   [`LoweringRefusal::UnresolvedName`] at a resident naming no implicit
    ///   or stage binder, and at a stage supplied by a name the caller binds no
    ///   stage to; a fault at a resident written twice; the reserved refusal
    ///   for a resident other than `a = e` beside one that is; the budget
    ///   refusal once no hole can be nominated; a form fault reading the head.
    /// - panics: none.
    ///
    /// # Errors
    /// As `- fails:`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — residents in either order apply alike; an omitted
    ///   implicit is a nominated hole; an implicit among the parentheses and a
    ///   resident naming nothing each refuse by their own name.
    /// - witness: `lower::implicit::tests::supply_by_name_is_order_free`
    /// - witness: `lower::implicit::tests::an_omitted_implicit_is_a_nominated_hole`
    /// - witness: `lower::implicit::tests::an_implicit_in_the_parentheses_is_refused`
    /// - witness: `lower::implicit::tests::a_resident_naming_no_implicit_is_unresolved`
    /// - witness: `lower::staged::tests::a_supplied_stage_crosses_at_the_call_s_head_1227`
    #[spec(
        captures: start = self.operands.len(),
        ensures: |ret| match ret {
            Ok(arity::Planned(true)) => matches!(
                self.plans.get(site.at.node),
                Some(&Plan::Application(_, arguments)) if arguments.start == start && arguments.end == self.operands.len()
            ),
            Ok(arity::Planned(false)) => self.operands.len() == start,
            Err(_) => true,
        },
    )]
    pub(super) fn supplied_call(
        &mut self,
        site: Site,
        frame: Frame,
        cursor: &Cursor<'_>,
    ) -> Result<arity::Planned, LoweringRefusal<'source>>
    {
        let mut rest = cursor.clone();
        let Run::One(head) = rest.operands()
        else {
            return Ok(arity::Planned(false));
        };
        self.supply(site, frame, head, Use::Called(rest))
    }

    /// Plan the instantiation at `site` that supplies a function's implicits
    /// or stages where no call applies it: the function applied to its
    /// implicits under a lambda for each explicit parameter before the last of
    /// them, a function of the rest; or, a stage supplied, the call of the
    /// function under a lambda for each explicit parameter.
    ///
    /// # Specification
    /// - requires: `site` is an instantiation.
    /// - ensures: [`arity::Planned`] true exactly when the instantiation's head
    ///   names a declaration with implicits or stages and every resident `a =
    ///   e` names one, the instantiation then planned as the declaration
    ///   applied in its merged telescope's order to the residents, each read as
    ///   a value, and to the variable of a lambda the supply opens
    ///   ([`Self::abstracted`]) for each explicit parameter the telescope
    ///   places before its last implicit, or for every explicit parameter when
    ///   a stage is supplied, bridged as a computation read where it stands.
    ///   False, with nothing changed, for any other instantiation, a
    ///   recursion's claim among them.
    /// - fails: [`LoweringRefusal::ImplicitUnsupplied`] for a supply leaving an
    ///   implicit out; the wrong-sort refusal where no computation can stand;
    ///   the refusals of [`Self::supplied_call`] at a resident.
    /// - panics: none.
    ///
    /// # Errors
    /// As `- fails:`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a supplied function passed as a value applies to its
    ///   leading implicits alone, and runs once applied; one whose implicit
    ///   follows an explicit parameter abstracts that parameter; one supplied a
    ///   stage stands as its call under a lambda per parameter.
    /// - witness: `lower::implicit::tests::a_supplied_function_stands_as_a_value`
    /// - witness: `lower::implicit::tests::a_standing_supply_opens_a_lambda_per_explicit_before_it_1498`
    /// - witness: `lower::implicit::tests::a_standing_stage_supply_stands_as_its_call_1498`
    #[spec(
        captures: start = self.operands.len(),
        ensures: |ret| match ret {
            Ok(arity::Planned(true)) => matches!(
                self.plans.get(site.at.node),
                Some(&Plan::Application(_, arguments)) if arguments.start == start && arguments.end == self.operands.len()
            ),
            Ok(arity::Planned(false)) => self.operands.len() == start,
            Err(_) => true,
        },
    )]
    pub(super) fn supplied_value(
        &mut self,
        site: Site,
    ) -> Result<arity::Planned, LoweringRefusal<'source>>
    {
        self.supply(site, site.reading.frame(), site.at, Use::Standing)
    }

    /// Plan `site`, whose head is `head`, as the supply its residents write,
    /// applied as `used` says.
    ///
    /// # Specification
    /// - requires: `head` is the call's head or, standing, `site` itself.
    /// - ensures: as [`Self::supplied_call`] for [`Use::Called`] and
    ///   [`Self::supplied_value`] for [`Use::Standing`].
    /// - fails: as theirs.
    /// - panics: none.
    ///
    /// # Errors
    /// As `- fails:`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — exercised through both callers.
    /// - witness: `lower::implicit::tests::supply_by_name_is_order_free`
    /// - witness: `lower::implicit::tests::a_supplied_function_stands_as_a_value`
    #[spec(
        captures: start = self.operands.len(),
        ensures: |ret| match ret {
            Ok(arity::Planned(false)) => self.operands.len() == start,
            Ok(arity::Planned(true)) | Err(_) => true,
        },
    )]
    fn supply(
        &mut self,
        site: Site,
        frame: Frame,
        head: Placed,
        used: Use<'_>,
    ) -> Result<arity::Planned, LoweringRefusal<'source>>
    {
        let former_of = |node: NodeIndex| {
            let shape = shape_of(self.pbg, self.tree.node(node)?).ok()?;
            if let Shape::Form { former, .. } = shape {
                Some(former)
            }
            else {
                None
            }
        };
        let former = former_of(head.node);
        let mut scratch = core::mem::take(&mut self.scratch);
        let read = read_pieces(self.pbg, self.tree, head.node, &mut scratch);
        let pieces = scratch.pieces.clone();
        self.scratch = scratch;
        read?;
        let called = matches!(used, Use::Called(_));
        let (inner, residents) = match (former, pieces.as_slice()) {
            (Some(Former::Instantiation), &[Piece::Operand(inner), ref rest @ ..]) => (inner, rest),
            (Some(Former::Name), _) if called => (head, &[][..]),
            (Some(_) | None, _) => return Ok(arity::Planned(false)),
        };
        if former_of(inner.node) != Some(Former::Name) {
            return Ok(arity::Planned(false));
        }
        // The head and its residents are never read as forms of their own:
        // the name and each supplied value are. Each takes its owner here, as
        // reading a form gives its children theirs.
        self.inherit_owner(head.node);
        // The residents are read before the head resolves: a recursive
        // call's claim, `f[<]`, is no supply, and its head names a binder.
        let mut supplied: BTreeMap<SurfaceName<'source>, (Placed, NodeIndex)> = BTreeMap::new();
        let mut scratch = core::mem::take(&mut self.scratch);
        let mut outcome = Ok(arity::Planned(true));
        for piece in residents {
            let Piece::Operand(resident) = *piece
            else {
                continue;
            };
            if let Err(refusal) = read_pieces(self.pbg, self.tree, resident.node, &mut scratch) {
                outcome = Err(refusal);
                break;
            }
            self.inherit_owner(resident.node);
            let reserved = Site {
                at: resident,
                ..site
            }
            .out(FragmentBoundary::Reserved(Unbuilt::CombinedSupply));
            let [
                Piece::Tile { label, at: written },
                Piece::Tile { label: equals, .. },
                Piece::Operand(value),
            ] = *scratch.pieces.as_slice()
            else {
                outcome = if supplied.is_empty() {
                    Ok(arity::Planned(false))
                }
                else {
                    Err(reserved)
                };
                break;
            };
            if label != TileName::IDENTIFIER || equals != TileName::EQUALS {
                outcome = Err(reserved);
                break;
            }
            let implicit = self.name_at(written);
            if supplied.insert(implicit, (written, value.node)).is_some() {
                outcome = Err(site.fault(written.span, FormFault::MisplacedTile));
                break;
            }
        }
        self.scratch = scratch;
        if outcome? == arity::Planned(false) {
            return Ok(arity::Planned(false));
        }
        let name = self.name_at(inner);
        if let Maybe::Present(_) = self.scope.resolve(frame, name, &mut self.fuel)? {
            return Ok(arity::Planned(false));
        }
        let named_site = Site { at: inner, ..site };
        let resolved = self.resolve_name(named_site, frame, name)?;
        let Maybe::Present(Resolved::Declaration { constant, .. }) = resolved
        else {
            return Ok(arity::Planned(false));
        };
        let slot = SlotIndex::from(usize::from(constant));
        let staged = self.stage_supplies(site, slot, &mut supplied)?;
        let stage_supplied = !staged.is_empty();
        let entries = match self.collected.plicities.get(&slot).cloned() {
            Some(Ok(entries)) => entries,
            None if !staged.is_empty() => Vec::new(),
            Some(Err(_)) | None => return Ok(arity::Planned(false)),
        };
        if !staged.is_empty() {
            let caller = match self.collected.owner_of(site.at.node) {
                Maybe::Present(owner) => self
                    .collected
                    .slots
                    .get(usize::from(owner))
                    .map(|slot| slot.constant),
                Maybe::Absent(_) => None,
            };
            let Some(caller) = caller
            else {
                return Err(site.out(FragmentBoundary::Unadmitted(Unbuilt::UnownedSupply)));
            };
            let _first = self.planned_supplies.insert(inner.node, (caller, staged));
        }
        let implicits: BTreeSet<SurfaceName<'source>> = entries
            .iter()
            .filter(|entry| entry.plicity == Plicity::Implicit)
            .map(|entry| entry.name)
            .collect();
        if let Some((&unknown, &(written, _))) = supplied
            .iter()
            .find(|&(supplied_name, _)| !implicits.contains(supplied_name))
        {
            return Err(LoweringRefusal::UnresolvedName {
                span: written.span,
                name: unknown,
            });
        }
        let mut written = Vec::new();
        let standing = match used {
            Use::Called(mut rest) => {
                arguments(site, &mut rest, &mut written)?;
                false
            },
            Use::Standing => true,
        };
        let explicit = entries
            .iter()
            .filter(|entry| entry.plicity == Plicity::Explicit)
            .count();
        let function = self
            .collected
            .slots
            .get(usize::from(slot))
            .map_or(name, |declared| declared.name);
        if let Some(missing) = entries
            .iter()
            .find(|entry| entry.plicity == Plicity::Implicit && !supplied.contains_key(&entry.name))
        {
            if written.len() == entries.len() && written.len() > explicit {
                return Err(LoweringRefusal::ImplicitInParentheses {
                    span: site.at.span,
                    function,
                    implicit: missing.name,
                });
            }
            if standing {
                return Err(LoweringRefusal::ImplicitUnsupplied {
                    span: site.at.span,
                    function,
                    implicit: missing.name,
                });
            }
        }
        // Standing, the supply applies the function to its implicits and opens
        // a lambda for each explicit parameter the merged telescope places
        // before the last of them, whose types those implicits mention:
        // `chosen[x = 7]` is `λ t. chosen(t)[x = 7]`, a function of the rest.
        // A supplied stage crosses only at a call's head, so a supply of one
        // opens a lambda for every explicit parameter and stands as the call:
        // `applyAt[i = k]` is `λ f. λ x. applyAt[i = k](f, x)`.
        let mut opened = 0_usize;
        if standing {
            let _frame = self.require(site, Produced::Computation)?;
            opened = if stage_supplied {
                self.collected.parameters.get(&slot).map_or(0, Vec::len)
            }
            else {
                entries
                    .iter()
                    .rposition(|entry| entry.plicity == Plicity::Implicit)
                    .map_or(0, |last| {
                        entries
                            .iter()
                            .take(last)
                            .filter(|entry| entry.plicity == Plicity::Explicit)
                            .count()
                    })
            };
        }
        // A function quantified over stages alone has no merged telescope: its
        // explicit parameters are known here only by their count.
        let unlisted = if entries.is_empty() { opened } else { 0 };
        let mut bound = 0_usize;
        let start = self.operands.len();
        let mut positional = written.iter();
        for entry in entries
            .iter()
            .map(Some)
            .chain(core::iter::repeat_n(None, unlisted))
        {
            let plicity = entry.map_or(Plicity::Explicit, |entry| entry.plicity);
            let argument = match (plicity, entry) {
                (Plicity::Implicit, Some(entry)) => {
                    if let Some(&(_, value)) = supplied.get(&entry.name) {
                        Some(value)
                    }
                    else {
                        let hole = self.nominate(Nomination::Omitted {
                            function,
                            implicit: entry.name,
                        })?;
                        let _first = self.nominated.insert(self.operands.len(), hole);
                        Some(site.at.node)
                    }
                },
                (Plicity::Explicit, _) if bound < opened => {
                    // The outermost lambda binds the first explicit: its
                    // variable is the furthest under the application.
                    let index = opened.saturating_sub(bound).saturating_sub(1);
                    bound = bound.saturating_add(1);
                    let _first = self.abstracted.insert(
                        self.operands.len(),
                        DeBruijnIndex::from(u32::try_from(index).unwrap_or(u32::MAX)),
                    );
                    Some(site.at.node)
                },
                (Plicity::Explicit | Plicity::Implicit, _) => positional.next().copied(),
            };
            if let Some(argument) = argument {
                self.operands.push(argument);
            }
        }
        self.operands.extend(positional.copied());
        let applied = Stretch {
            start,
            end: self.operands.len(),
        };
        let _fresh = self.supplied.insert(inner.node);
        if applied.start == applied.end {
            let _first = self.nullary.insert(inner.node, site.at.node);
        }
        self.read(inner.node, Reading::Head(frame));
        for position in applied.start .. applied.end {
            if self.nominated.contains_key(&position) || self.abstracted.contains_key(&position) {
                continue;
            }
            if let Some(&argument) = self.operands.get(position) {
                self.read(argument, Reading::Value(frame));
            }
        }
        self.plan(site, Plan::Application(inner.node, applied));

        Ok(arity::Planned(true))
    }

    /// Nominate a hole for `nomination`, an implicit a call omits or a
    /// wildcard the text writes, the next nominated name of its kind.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a name no hole before it carries, kept beside `nomination`: a
    ///   wildcard's name for a wildcard, so the printer writes it back as `_`,
    ///   and a nominated one for an omitted implicit, which it leaves out.
    /// - fails: the budget refusal once the kind's quarter has no more names.
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoweringRefusal::BudgetExceeded`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — two implicits a call omits are two distinct holes,
    ///   each kept with its implicit's name, and a wildcard beside them a
    ///   third, named as a wildcard.
    /// - witness: `lower::implicit::tests::an_omitted_implicit_is_a_nominated_hole`
    /// - witness: `lower::implicit::tests::a_wildcard_is_a_nominated_hole_of_its_own`
    #[spec(
        captures: before = self.nominations.len(),
        ensures: |ret| match ret {
            Ok(hole) => matches!(
                (hole.origin(), nomination),
                (gandr_core_term::hole::HoleOrigin::Wildcard, Nomination::Wildcard)
                    | (gandr_core_term::hole::HoleOrigin::Nominated, Nomination::Omitted { .. })
            ) && self.nominations.len() == before.saturating_add(1)
                && self.nominations.get(&hole) == Some(&nomination),
            Err(_) => self.nominations.len() == before,
        },
    )]
    pub(super) fn nominate(
        &mut self,
        nomination: Nomination<'source>,
    ) -> Result<gandr_core_term::hole::HoleId, LoweringRefusal<'source>>
    {
        let named = match nomination {
            Nomination::Wildcard => gandr_core_term::hole::HoleId::wildcard,
            Nomination::Omitted { .. } => gandr_core_term::hole::HoleId::nominated,
        };
        let hole = u32::try_from(self.nominations.len())
            .ok()
            .map(gandr_core_term::hole::NominationIndex::from)
            .and_then(named)
            .ok_or(LoweringRefusal::BudgetExceeded {
                budget: self.fuel.budget,
            })?;
        let _first = self.nominations.insert(hole, nomination);
        Ok(hole)
    }
}
