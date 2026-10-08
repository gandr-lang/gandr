//! The definition chain and the per-scope definitional environment: what a
//! definition *is*, and where it is *manifest*.
//!
//! # The chain carries content ids, not pointers and not arena ids
//!
//! The prototype carried definition bodies as syntax behind reference-counted
//! pointers, and it did so for a real reason: an arena id is meaningful only in
//! the arena that minted it, while a context is cloned into whatever normalizer
//! a conversion mints, so compiled ids would dangle silently.
//!
//! The property is kept and the pointer is dropped. A [`DefinitionEntry`]
//! carries a **content id** — an entry index in the artifact's canonical
//! subterm table — which is arena-independent by construction, because the
//! table is canonical: the same content is the same entry, in every arena that
//! decodes it. A normalizer lowers the chain into its own arena in one pass;
//! the chain itself owns no node, borrows no arena, and clones flat.
//!
//! # Heights are computed in admission order
//!
//! A definition's height is one above the tallest definition it mentions, and a
//! declaration with no body — an axiom, a sealed atom — is height zero and is
//! not in the chain at all. Admission order is what makes the height one
//! forward pass rather than a fixed point: every mention names a strictly
//! earlier admission position, so its height is already recorded when the
//! mentioning entry is appended. Both halves are enforced —
//! [`DefinitionChain::define`] refuses an entry out of admission order and
//! refuses a mention at or above its own position — so the height is a
//! computed fact rather than a producer's claim.
//!
//! Heights are a scheduling prior, never a gate: they weight which side of a
//! conversion is cheaper to unfold and they never decide which unfoldings are
//! attempted.
//!
//! # The definitional environment is per-scope from the start
//!
//! Transparent ascription forces it: the same atom is manifest inside a sealed
//! module and opaque outside it, so a single global transparency table is
//! simply wrong. The environment is a flat, id-addressed forest of scopes whose
//! parent link always points at a strictly earlier scope, and a lookup walks
//! outward taking the innermost override.
//!
//! The empty environment degenerates to the flat one at no cost — one root
//! scope, no overrides, one scan that finds nothing and answers with the
//! declaration's own stance — which is why the shape is paid before the sealing
//! feature that needs it lands rather than after.

use alloc::vec::Vec;

use anodized::spec;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::GlobalIndex;

/// A definition's height: one above the tallest definition its body mentions.
///
/// Zero is the floor and it names **not unfoldable**: an axiom, a sealed
/// abstract type, a bound variable. Nothing in the chain sits there, because
/// every entry in the chain has a body and can therefore be unfolded at least
/// once — a definition mentioning no other definition has height one, not zero.
/// Reading a height of zero as "a definition that costs nothing to unfold"
/// would collapse exactly the distinction the height exists to weight.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct DefinitionHeight(u32);

impl From<u32> for DefinitionHeight
{
    /// Wraps a raw count as an unfolding height.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(height: u32) -> Self
    {
        Self(height)
    }
}

impl From<DefinitionHeight> for u32
{
    /// Unwraps an unfolding height to its raw count.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(height: DefinitionHeight) -> Self
    {
        height.0
    }
}

/// Whether a definition's body may be unfolded where it is being read.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Transparency
{
    /// The body may be unfolded here.
    Manifest,
    /// The body may not be unfolded here; the definition behaves as an atom.
    Opaque,
}

/// One definition of the chain.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct DefinitionEntry
{
    /// The admission position this definition was admitted at.
    constant: ConstantIndex,
    /// The body, as a canonical subterm-table entry index. Arena-independent by
    /// construction, which is the whole reason the chain carries this rather
    /// than a node.
    body: GlobalIndex,
    /// The height, computed when the entry was appended.
    height: DefinitionHeight,
    /// The stance the declaration itself carries, before any scope overrides
    /// it.
    declared: Transparency,
}

impl DefinitionEntry
{
    /// The admission position this definition was admitted at.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn constant(&self) -> ConstantIndex
    {
        self.constant
    }

    /// The body's canonical subterm-table entry index.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn body(&self) -> GlobalIndex
    {
        self.body
    }

    /// The height computed for this definition.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn height(&self) -> DefinitionHeight
    {
        self.height
    }

    /// The stance the declaration itself carries.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn declared(&self) -> Transparency
    {
        self.declared
    }
}

/// A scope of the definitional environment.
///
/// The id is the frame's own offset, so it is exactly as wide as the frame
/// vector can be. That is what leaves [`DefinitionalEnvironment::open_scope`]
/// with one failure mode rather than two: there is no id space to exhaust
/// separately from the memory the frames already occupy.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ScopeId(usize);

impl From<usize> for ScopeId
{
    /// Wraps a frame offset as a scope identifier.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(scope: usize) -> Self
    {
        Self(scope)
    }
}

impl From<ScopeId> for usize
{
    /// Unwraps a scope identifier to its frame offset.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(scope: ScopeId) -> Self
    {
        scope.0
    }
}

/// One transparency override recorded in a scope.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
struct Override
{
    /// The definition the override is about.
    constant: ConstantIndex,
    /// The stance this scope gives it.
    stance: Transparency,
}

/// One scope frame: its parent link and its local overrides.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
struct ScopeFrame
{
    /// The enclosing scope, absent only for the root. Always a strictly smaller
    /// id than this frame's own, which is what makes an outward walk finite.
    parent: Option<ScopeId>,
    /// The overrides this scope states, innermost-wins over its parents'.
    overrides: Vec<Override>,
}

/// Why a chain or environment operation was refused.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum DefinitionError
{
    /// The admission position is already in the chain.
    AlreadyDefined
    {
        /// The position offered twice.
        constant: ConstantIndex,
    },
    /// The admission position does not follow every position already in the
    /// chain, so the chain would stop being in admission order and the
    /// one-pass height computation would stop being sound.
    OutOfAdmissionOrder
    {
        /// The position offered.
        constant: ConstantIndex,
        /// The last position the chain holds.
        latest: ConstantIndex,
    },
    /// A body mentions a position at or above its own, which admission order
    /// rules out and which would make the height depend on an entry that does
    /// not exist yet.
    ForwardReference
    {
        /// The position being defined.
        constant: ConstantIndex,
        /// The mention that does not precede it.
        mention: ConstantIndex,
    },
    /// The scope id names no frame of this environment.
    UnknownScope
    {
        /// The unresolvable scope.
        scope: ScopeId,
    },
}

/// The definition chain: every definition's body and height, in admission
/// order.
///
/// The chain owns no term node and borrows no arena; it is a flat vector of
/// admission positions, table indices and heights, so cloning it into a
/// normalizer costs a vector copy and carries nothing that can dangle.
#[repr(transparent)]
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct DefinitionChain
{
    /// The entries, strictly increasing in admission position.
    entries: Vec<DefinitionEntry>,
}

impl DefinitionChain
{
    /// The empty chain.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn new() -> Self
    {
        Self::default()
    }

    /// Every entry, in admission order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn entries(&self) -> &[DefinitionEntry]
    {
        &self.entries
    }

    /// The entry for an admission position, or `None` when the position holds
    /// no definitional body.
    ///
    /// # Specification
    /// - requires: nothing — an unknown position is admissible input.
    /// - ensures: `|ret| ret == self.entries.iter().find(|held| held.constant()
    ///   == constant)` — the entry whose position is `constant`, found by
    ///   binary search over the strictly increasing positions the chain
    ///   maintains; `None` for an axiom, a sealed atom, or a position never
    ///   admitted. The clause scans linearly, so it is an independent reading
    ///   of the same chain rather than the search read back.
    /// - provides: the lookup a normalizer's unfolding step and the height
    ///   computation both run.
    /// - fails: never; absence is `None` rather than an error, because "this
    ///   position has no body" is an ordinary answer.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the decision surface is the binary search, separated
    ///   by the first, a middle and the last position of a three-entry chain,
    ///   plus a position between two entries and one past the end, each
    ///   asserted exactly.
    /// - witness: `definition::tests::a_chain_resolves_only_the_positions_it_holds`
    #[inline]
    #[must_use]
    #[spec(ensures: |ret| ret == self.entries.iter().find(|held| held.constant() == constant))]
    pub fn entry(
        &self,
        constant: ConstantIndex,
    ) -> Option<&DefinitionEntry>
    {
        let found = self
            .entries
            .binary_search_by_key(&constant, DefinitionEntry::constant)
            .ok()?;
        self.entries.get(found)
    }

    /// Append a definition, computing its height from the definitions it
    /// mentions.
    ///
    /// # Specification
    /// - requires: `mentions` lists every admission position the body names. A
    ///   short list yields a height that under-states the body's depth, which
    ///   costs scheduling quality and never soundness, because a height is a
    ///   share and never a gate.
    /// - ensures: `|ret| ret.is_err() || (Some(self.entries.len()) ==
    ///   entry_count.checked_add(1_usize) &&
    ///   self.entries.last().map(DefinitionEntry::constant) == Some(constant)
    ///   && ret.ok().map(u32::from) ==
    ///   Some(mentions.iter().filter_map(|mention|
    ///   self.entry(*mention)).map(|held|
    ///   u32::from(held.height())).max().unwrap_or(0_u32)
    ///   .saturating_add(1_u32)))` — on success the chain holds one more entry,
    ///   its position is the chain's greatest, and its height is **one above
    ///   the tallest mentioned entry**, counting an absent mention — an axiom,
    ///   a sealed atom — as the floor. Every entry therefore has height at
    ///   least one, which is the reading that makes zero mean "not unfoldable"
    ///   rather than "unfoldable for free".
    /// - provides: the one-pass height computation the admission order makes
    ///   possible, and the chain the normalizer lowers. The requirement stays
    ///   prose: the body is a subterm-table index, so which positions it names
    ///   is not an observation this call can make.
    /// - fails: [`DefinitionError::AlreadyDefined`],
    ///   [`DefinitionError::OutOfAdmissionOrder`] and
    ///   [`DefinitionError::ForwardReference`], each leaving the chain exactly
    ///   as it was, so a refused definition is not half-recorded.
    /// - panics: none — the height's increment saturates rather than
    ///   overflowing, at a ceiling four billion definitions deep.
    ///
    /// # Errors
    /// - [`DefinitionError::AlreadyDefined`] — the position is already
    ///   recorded.
    /// - [`DefinitionError::OutOfAdmissionOrder`] — the position does not
    ///   follow the chain's last.
    /// - [`DefinitionError::ForwardReference`] — a mention does not precede the
    ///   position being defined.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the decision surfaces are the order guard, the
    ///   mention guard and the height maximum, separated by a re-offered
    ///   position, a position below the chain's last, a self-mention, a forward
    ///   mention, and a body mentioning two definitions of different heights
    ///   whose result is asserted exactly against the taller.
    /// - witness: `definition::tests::heights_rise_one_above_the_tallest_mention`
    /// - witness: `definition::tests::a_definition_out_of_admission_order_is_refused`
    /// - witness: `definition::tests::a_forward_mention_is_refused`
    #[inline]
    #[spec(
        captures: entry_count = self.entries.len(),
        ensures: |ret| ret.is_err()
            || (Some(self.entries.len()) == entry_count.checked_add(1_usize)
                && self.entries.last().map(DefinitionEntry::constant) == Some(constant)
                && ret.ok().map(u32::from)
                    == Some(
                        mentions
                            .iter()
                            .filter_map(|mention| self.entry(*mention))
                            .map(|held| u32::from(held.height()))
                            .max()
                            .unwrap_or(0_u32)
                            .saturating_add(1_u32),
                    )),
    )]
    pub fn define(
        &mut self,
        constant: ConstantIndex,
        body: GlobalIndex,
        declared: Transparency,
        mentions: &[ConstantIndex],
    ) -> Result<DefinitionHeight, DefinitionError>
    {
        if self.entry(constant).is_some() {
            return Err(DefinitionError::AlreadyDefined { constant });
        }
        if let Some(latest) = self.entries.last().map(DefinitionEntry::constant)
            && constant < latest
        {
            return Err(DefinitionError::OutOfAdmissionOrder { constant, latest });
        }
        let mut tallest = DefinitionHeight::default();
        for &mention in mentions {
            if mention >= constant {
                return Err(DefinitionError::ForwardReference { constant, mention });
            }
            if let Some(entry) = self.entry(mention) {
                tallest = tallest.max(entry.height);
            }
        }
        let height = DefinitionHeight(tallest.0.saturating_add(1_u32));
        self.entries.push(DefinitionEntry {
            constant,
            body,
            height,
            declared,
        });
        Ok(height)
    }
}

/// The offset of one scope frame within the environment's flat vector.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct FrameOffset(usize);

/// The per-scope definitional environment: which definitions are manifest
/// where.
///
/// A flat forest of scope frames behind [`ScopeId`]s, each frame naming its
/// parent and its own overrides. A lookup walks outward and takes the innermost
/// override, so a definition sealed by an enclosing scope is opaque in every
/// scope beneath it that does not re-open it.
#[repr(transparent)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct DefinitionalEnvironment
{
    /// The frames, in creation order. A frame's parent id is strictly smaller
    /// than its own, which is the invariant the outward walk's bound rests on.
    frames: Vec<ScopeFrame>,
}

impl Default for DefinitionalEnvironment
{
    /// The environment holding the root scope alone.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn default() -> Self
    {
        Self::new()
    }
}

impl DefinitionalEnvironment
{
    /// The environment holding the root scope alone.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn new() -> Self
    {
        Self {
            frames: Vec::from([ScopeFrame::default()]),
        }
    }

    /// The root scope, which every other scope descends from.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn root(&self) -> ScopeId
    {
        ScopeId(0_usize)
    }

    /// Resolve a scope to its frame offset.
    ///
    /// # Specification
    /// - requires: nothing — an unknown scope is admissible input.
    /// - ensures: `|ret| ret == self.frames.get(usize::from(scope)).map(|_|
    ///   FrameOffset(usize::from(scope)))` — the offset of the frame the scope
    ///   names, when it names one.
    /// - provides: the single narrowing both the writer and the reader go
    ///   through, so the two cannot disagree about which frame an id names.
    /// - fails: returns `None` for a scope this environment never opened.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the single decision surface is the bound comparison,
    ///   separated by the root scope, the newest scope, and an id past the
    ///   frame count, each observed through the callers that report on it.
    /// - witness: `definition::tests::a_scope_inherits_until_it_seals`
    /// - witness: `definition::tests::an_unknown_scope_is_refused`
    #[inline]
    #[spec(ensures: |ret| ret
        == self.frames.get(usize::from(scope)).map(|_| FrameOffset(usize::from(scope))))]
    fn frame_offset(
        &self,
        scope: ScopeId,
    ) -> Option<FrameOffset>
    {
        if scope.0 < self.frames.len() {
            return Some(FrameOffset(scope.0));
        }
        None
    }

    /// Open a scope inside `parent`.
    ///
    /// # Specification
    /// - requires: nothing — an unknown parent is admissible input and is
    ///   refused.
    /// - ensures: `|ret| ret.is_err() || ret.is_ok_and(|fresh|
    ///   usize::from(fresh) > usize::from(parent) &&
    ///   self.frames.get(usize::from(fresh)).is_some_and(|frame|
    ///   frame.overrides.is_empty()))` — on success a fresh scope whose id is
    ///   strictly greater than `parent`'s, holding no overrides of its own, so
    ///   it reads exactly what its parent reads until something is sealed in
    ///   it.
    /// - provides: the nesting a sealed module introduces, and the strictly
    ///   increasing id the outward walk's finiteness rests on.
    /// - fails: [`DefinitionError::UnknownScope`] when `parent` names no frame.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`DefinitionError::UnknownScope`] — `parent` names no frame of this
    ///   environment.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the decision surfaces are the parent guard and the
    ///   fresh id, separated by opening under the root, opening under a scope
    ///   opened that way, and opening under an id past the frame count, with
    ///   the inherited reading asserted at each.
    /// - witness: `definition::tests::a_scope_inherits_until_it_seals`
    /// - witness: `definition::tests::an_inner_scope_reopens_what_its_parent_sealed`
    /// - witness: `definition::tests::an_unknown_scope_is_refused`
    #[inline]
    #[spec(ensures: |ret| ret.is_err()
        || ret.is_ok_and(|fresh| {
            usize::from(fresh) > usize::from(parent)
                && self
                    .frames
                    .get(usize::from(fresh))
                    .is_some_and(|frame| frame.overrides.is_empty())
        }))]
    pub fn open_scope(
        &mut self,
        parent: ScopeId,
    ) -> Result<ScopeId, DefinitionError>
    {
        if self.frame_offset(parent).is_none() {
            return Err(DefinitionError::UnknownScope { scope: parent });
        }
        let fresh = ScopeId(self.frames.len());
        self.frames.push(ScopeFrame {
            parent: Some(parent),
            overrides: Vec::new(),
        });
        Ok(fresh)
    }

    /// State a definition's transparency in one scope, replacing whatever that
    /// scope said before.
    ///
    /// # Specification
    /// - requires: nothing — an unknown scope is admissible input and is
    ///   refused.
    /// - ensures: `|ret| ret.is_err() || (self.transparency(scope, constant,
    ///   Transparency::Manifest) == Ok(stance) && self.transparency(scope,
    ///   constant, Transparency::Opaque) == Ok(stance))` — on success the scope
    ///   reads `stance` for `constant`, whichever stance the declaration itself
    ///   carries.
    /// - provides: the sealing and the transparent-ascription moves, which are
    ///   the same operation at two stances. That every scope beneath this one
    ///   which states nothing reads the same stance is [`Self::transparency`]'s
    ///   outward walk rather than a second observation here.
    /// - fails: [`DefinitionError::UnknownScope`] when `scope` names no frame.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`DefinitionError::UnknownScope`] — `scope` names no frame of this
    ///   environment.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the decision surfaces are the scope guard and the
    ///   replace-versus-append branch, separated by sealing a definition,
    ///   re-stating it at the other stance in the same scope, and sealing in an
    ///   unknown scope, each with the resulting reading asserted exactly.
    /// - witness: `definition::tests::a_scope_inherits_until_it_seals`
    /// - witness: `definition::tests::restating_a_stance_replaces_it`
    /// - witness: `definition::tests::an_unknown_scope_is_refused`
    #[inline]
    #[spec(ensures: |ret| ret.is_err()
        || (self.transparency(scope, constant, Transparency::Manifest) == Ok(stance)
            && self.transparency(scope, constant, Transparency::Opaque) == Ok(stance)))]
    pub fn state(
        &mut self,
        scope: ScopeId,
        constant: ConstantIndex,
        stance: Transparency,
    ) -> Result<(), DefinitionError>
    {
        let Some(offset) = self.frame_offset(scope)
        else {
            return Err(DefinitionError::UnknownScope { scope });
        };
        let Some(frame) = self.frames.get_mut(offset.0)
        else {
            return Err(DefinitionError::UnknownScope { scope });
        };
        for recorded in &mut frame.overrides {
            if recorded.constant == constant {
                recorded.stance = stance;
                return Ok(());
            }
        }
        frame.overrides.push(Override { constant, stance });
        Ok(())
    }

    /// The transparency a definition has in a scope.
    ///
    /// The walk runs outward from `scope` and stops at the innermost scope
    /// stating anything about `constant`; a chain that states nothing answers
    /// with `declared`, the stance the declaration itself carries.
    ///
    /// # Specification
    /// - requires: nothing — an unknown scope is admissible input and is
    ///   refused.
    /// - ensures: `|ret| ret.is_err() || ret ==
    ///   Ok(core::iter::successors(Some(scope), |held| { let frame =
    ///   self.frames.get(usize::from(*held))?; frame.parent
    ///   }).take(self.frames.len()).find_map(|held| { let frame =
    ///   self.frames.get(usize::from(held))?;
    ///   frame.overrides.iter().find(|recorded| recorded.constant ==
    ///   constant).map(|recorded| recorded.stance) }).unwrap_or(declared))` —
    ///   the stance of the innermost enclosing scope that states one, and
    ///   `declared` when none does. The clause walks the parent chain as an
    ///   iterator bounded by the frame count, so it is an independent walk
    ///   rather than the body's own loop read back.
    /// - provides: the unfolding permission a normalizer asks before it expands
    ///   a definition, which is per-scope because transparent ascription makes
    ///   the same atom manifest inside a seal and opaque outside it.
    /// - fails: [`DefinitionError::UnknownScope`] when `scope` names no frame.
    /// - panics: none.
    /// - intension: the walk visits each enclosing scope at most once and is
    ///   bounded by the environment's frame count, because a frame's parent id
    ///   is strictly smaller than its own. It is iterative, so its cost is
    ///   observable as scope depth rather than as stack depth.
    ///
    /// # Errors
    /// - [`DefinitionError::UnknownScope`] — `scope` names no frame of this
    ///   environment.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the decision surfaces are the parent walk, the
    ///   innermost-wins tie-break and the `declared` fallback, separated by a
    ///   two-deep nest where the outer scope seals and the inner re-opens, a
    ///   nest that states nothing, and a lookup in an unknown scope.
    /// - witness: `definition::tests::a_scope_inherits_until_it_seals`
    /// - witness: `definition::tests::an_inner_scope_reopens_what_its_parent_sealed`
    /// - witness: `definition::tests::an_unknown_scope_is_refused`
    #[inline]
    #[spec(ensures: |ret| ret.is_err()
        || ret
            == Ok(core::iter::successors(Some(scope), |held| {
                let frame = self.frames.get(usize::from(*held))?;
                frame.parent
            })
            .take(self.frames.len())
            .find_map(|held| {
                let frame = self.frames.get(usize::from(held))?;
                frame
                    .overrides
                    .iter()
                    .find(|recorded| recorded.constant == constant)
                    .map(|recorded| recorded.stance)
            })
            .unwrap_or(declared)))]
    pub fn transparency(
        &self,
        scope: ScopeId,
        constant: ConstantIndex,
        declared: Transparency,
    ) -> Result<Transparency, DefinitionError>
    {
        if self.frame_offset(scope).is_none() {
            return Err(DefinitionError::UnknownScope { scope });
        }
        let mut current = Some(scope);
        for _ in 0 .. self.frames.len() {
            let Some(here) = current
            else {
                return Ok(declared);
            };
            let Some(offset) = self.frame_offset(here)
            else {
                return Ok(declared);
            };
            let Some(frame) = self.frames.get(offset.0)
            else {
                return Ok(declared);
            };
            if let Some(found) = frame
                .overrides
                .iter()
                .find(|recorded| recorded.constant == constant)
            {
                return Ok(found.stance);
            }
            current = frame.parent;
        }
        Ok(declared)
    }
}

#[cfg(test)]
mod tests
{
    use gandr_kernel_term::ConstantIndex;
    use gandr_kernel_term::GlobalIndex;

    use super::DefinitionChain;
    use super::DefinitionEntry;
    use super::DefinitionError;
    use super::DefinitionHeight;
    use super::DefinitionalEnvironment;
    use super::ScopeId;
    use super::Transparency;

    #[test]
    fn heights_rise_one_above_the_tallest_mention()
    {
        let mut chain = DefinitionChain::new();
        let ground = chain.define(
            ConstantIndex::from(0_usize),
            GlobalIndex::from(0_u32),
            Transparency::Manifest,
            &[],
        );
        assert_eq!(
            Ok(DefinitionHeight::from(1_u32)),
            ground,
            "a definition mentioning nothing still unfolds once, so it is one above the floor"
        );
        let short = chain.define(
            ConstantIndex::from(1_usize),
            GlobalIndex::from(1_u32),
            Transparency::Manifest,
            &[ConstantIndex::from(0_usize)],
        );
        assert_eq!(
            Ok(DefinitionHeight::from(2_u32)),
            short,
            "one above the definition it mentions"
        );
        let tall = chain.define(
            ConstantIndex::from(2_usize),
            GlobalIndex::from(2_u32),
            Transparency::Manifest,
            &[ConstantIndex::from(1_usize)],
        );
        assert_eq!(Ok(DefinitionHeight::from(3_u32)), tall);
        let joined = chain.define(
            ConstantIndex::from(3_usize),
            GlobalIndex::from(3_u32),
            Transparency::Manifest,
            &[ConstantIndex::from(0_usize), ConstantIndex::from(2_usize)],
        );
        assert_eq!(
            Ok(DefinitionHeight::from(4_u32)),
            joined,
            "the maximum decides, not the first or the last mention"
        );
        let axiomatic = chain.define(
            ConstantIndex::from(5_usize),
            GlobalIndex::from(4_u32),
            Transparency::Opaque,
            &[ConstantIndex::from(4_usize)],
        );
        assert_eq!(
            Ok(DefinitionHeight::from(1_u32)),
            axiomatic,
            "a mention with no body — an axiom — sits on the floor and raises nothing, so \
             a definition over axioms alone is one above it like any other leaf definition"
        );
        assert!(
            chain
                .entries()
                .iter()
                .all(|entry| entry.height() > DefinitionHeight::default()),
            "no entry of the chain sits on the floor: the floor names what cannot unfold"
        );
    }

    #[test]
    fn a_definition_out_of_admission_order_is_refused()
    {
        let mut chain = DefinitionChain::new();
        let defined = chain.define(
            ConstantIndex::from(4_usize),
            GlobalIndex::from(0_u32),
            Transparency::Manifest,
            &[],
        );
        assert!(defined.is_ok());
        assert_eq!(
            Err(DefinitionError::AlreadyDefined {
                constant: ConstantIndex::from(4_usize)
            }),
            chain.define(
                ConstantIndex::from(4_usize),
                GlobalIndex::from(1_u32),
                Transparency::Manifest,
                &[]
            ),
            "the same position twice is refused by name"
        );
        assert_eq!(
            Err(DefinitionError::OutOfAdmissionOrder {
                constant: ConstantIndex::from(3_usize),
                latest: ConstantIndex::from(4_usize),
            }),
            chain.define(
                ConstantIndex::from(3_usize),
                GlobalIndex::from(1_u32),
                Transparency::Manifest,
                &[]
            ),
            "a position below the chain's last would break the one-pass height computation"
        );
        let later = chain.define(
            ConstantIndex::from(6_usize),
            GlobalIndex::from(2_u32),
            Transparency::Manifest,
            &[],
        );
        assert!(later.is_ok());
        assert_eq!(
            Err(DefinitionError::AlreadyDefined {
                constant: ConstantIndex::from(4_usize)
            }),
            chain.define(
                ConstantIndex::from(4_usize),
                GlobalIndex::from(3_u32),
                Transparency::Manifest,
                &[]
            ),
            "a position already in the chain is refused as a duplicate, not as an ordering \
             fault, however far back it sits"
        );
        assert_eq!(
            2_usize,
            chain.entries().len(),
            "a refused definition is not half-recorded"
        );
    }

    #[test]
    fn a_forward_mention_is_refused()
    {
        let mut chain = DefinitionChain::new();
        assert_eq!(
            Err(DefinitionError::ForwardReference {
                constant: ConstantIndex::from(1_usize),
                mention: ConstantIndex::from(1_usize),
            }),
            chain.define(
                ConstantIndex::from(1_usize),
                GlobalIndex::from(0_u32),
                Transparency::Manifest,
                &[ConstantIndex::from(1_usize)]
            ),
            "a body mentioning its own position is refused"
        );
        assert_eq!(
            Err(DefinitionError::ForwardReference {
                constant: ConstantIndex::from(1_usize),
                mention: ConstantIndex::from(2_usize),
            }),
            chain.define(
                ConstantIndex::from(1_usize),
                GlobalIndex::from(0_u32),
                Transparency::Manifest,
                &[ConstantIndex::from(2_usize)]
            ),
            "a body mentioning a later position is refused"
        );
        assert!(
            chain.entries().is_empty(),
            "neither refusal recorded anything"
        );
    }

    #[test]
    fn a_chain_resolves_only_the_positions_it_holds()
    {
        let mut chain = DefinitionChain::new();
        let recorded = [
            (ConstantIndex::from(0_usize), GlobalIndex::from(10_u32)),
            (ConstantIndex::from(2_usize), GlobalIndex::from(11_u32)),
            (ConstantIndex::from(4_usize), GlobalIndex::from(12_u32)),
        ];
        for (position, index) in recorded {
            let defined = chain.define(position, index, Transparency::Manifest, &[]);
            assert!(defined.is_ok());
        }
        for (position, index) in recorded {
            assert_eq!(
                Some(index),
                chain.entry(position).map(DefinitionEntry::body),
                "each recorded position resolves to its own body"
            );
        }
        assert!(
            chain.entry(ConstantIndex::from(1_usize)).is_none(),
            "a gap between two entries holds nothing"
        );
        assert!(
            chain.entry(ConstantIndex::from(9_usize)).is_none(),
            "a position past the chain holds nothing"
        );
    }

    #[test]
    fn a_chain_carries_no_arena_and_clones_flat()
    {
        let mut chain = DefinitionChain::new();
        let defined = chain.define(
            ConstantIndex::from(0_usize),
            GlobalIndex::from(7_u32),
            Transparency::Manifest,
            &[],
        );
        assert!(defined.is_ok());
        let copied = chain.clone();
        assert_eq!(chain, copied, "the clone is the chain");
        assert_eq!(
            chain
                .entry(ConstantIndex::from(0_usize))
                .map(DefinitionEntry::body),
            copied
                .entry(ConstantIndex::from(0_usize))
                .map(DefinitionEntry::body),
            "a content id means the same thing in the copy, because it names a canonical \
             table entry rather than a node"
        );
    }

    #[test]
    fn a_scope_inherits_until_it_seals()
    {
        let mut environment = DefinitionalEnvironment::new();
        let root = environment.root();
        let inner = environment.open_scope(root).expect("the root resolves");
        assert_eq!(
            Ok(Transparency::Manifest),
            environment.transparency(inner, ConstantIndex::from(0_usize), Transparency::Manifest),
            "a scope that states nothing answers with the declaration's own stance"
        );
        let sealed = environment.state(root, ConstantIndex::from(0_usize), Transparency::Opaque);
        assert_eq!(Ok(()), sealed);
        assert_eq!(
            Ok(Transparency::Opaque),
            environment.transparency(inner, ConstantIndex::from(0_usize), Transparency::Manifest),
            "an enclosing seal reaches the scopes beneath it"
        );
        assert_eq!(
            Ok(Transparency::Manifest),
            environment.transparency(inner, ConstantIndex::from(1_usize), Transparency::Manifest),
            "and it reaches only the definition it named"
        );
    }

    #[test]
    fn an_inner_scope_reopens_what_its_parent_sealed()
    {
        let mut environment = DefinitionalEnvironment::new();
        let root = environment.root();
        let inner = environment.open_scope(root).expect("the root resolves");
        let deeper = environment
            .open_scope(inner)
            .expect("the inner scope resolves");
        let sealed = environment.state(root, ConstantIndex::from(0_usize), Transparency::Opaque);
        assert_eq!(Ok(()), sealed);
        let reopened =
            environment.state(inner, ConstantIndex::from(0_usize), Transparency::Manifest);
        assert_eq!(Ok(()), reopened);
        assert_eq!(
            Ok(Transparency::Manifest),
            environment.transparency(deeper, ConstantIndex::from(0_usize), Transparency::Opaque),
            "the innermost statement wins, two scopes down"
        );
        assert_eq!(
            Ok(Transparency::Opaque),
            environment.transparency(root, ConstantIndex::from(0_usize), Transparency::Manifest),
            "and the outer scope still reads its own seal"
        );
    }

    #[test]
    fn restating_a_stance_replaces_it()
    {
        let mut environment = DefinitionalEnvironment::new();
        let root = environment.root();
        let sealed = environment.state(root, ConstantIndex::from(0_usize), Transparency::Opaque);
        assert_eq!(Ok(()), sealed);
        let reopened =
            environment.state(root, ConstantIndex::from(0_usize), Transparency::Manifest);
        assert_eq!(Ok(()), reopened);
        assert_eq!(
            Ok(Transparency::Manifest),
            environment.transparency(root, ConstantIndex::from(0_usize), Transparency::Opaque),
            "a scope states one stance per definition, not a stack of them"
        );
    }

    #[test]
    fn an_unknown_scope_is_refused()
    {
        let mut environment = DefinitionalEnvironment::new();
        let absent = ScopeId::from(7_usize);
        assert_eq!(
            Err(DefinitionError::UnknownScope { scope: absent }),
            environment.open_scope(absent)
        );
        assert_eq!(
            Err(DefinitionError::UnknownScope { scope: absent }),
            environment.state(absent, ConstantIndex::from(0_usize), Transparency::Opaque)
        );
        assert_eq!(
            Err(DefinitionError::UnknownScope { scope: absent }),
            environment.transparency(absent, ConstantIndex::from(0_usize), Transparency::Opaque)
        );
    }
}
