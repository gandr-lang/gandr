//! A function's implicit parameters, as the collection pass reads them: each
//! entry `a : T` of the telescope `@[ … ]` after the function's name whose
//! sort is not `Size`. A stage binder `i : Size` and a bound `i < n` are the
//! signature's quantifier and bind no value ([`crate::lower`]'s staged half).
//!
//! # One telescope, merged
//!
//! The implicit and the explicit parameters merge into one telescope by a
//! stable topological sort: each parameter stands after every parameter its
//! type mentions, and ties keep the written order, the telescope's entries
//! before the parentheses'. An implicit's type may name an explicit parameter
//! written after it, `@[i : Fin(n)] (n : Nat)`, which places the implicit
//! after it; an explicit parameter's type reads the parameters before it as
//! it always has, so a later explicit name it mentions orders nothing. A
//! name a type binds itself — the key of a group's entry, `x` in `(x : A) =>
//! B`, over the entries after it and an arrow's codomain — mentions no
//! parameter, whatever its spelling. A cycle through the telescope is
//! refused, naming two of its parameters.
//!
//! Which parameters are implicit is the declaration's metadata
//! ([`super::Collected::plicities`]), never type structure: the declared type
//! is the merged telescope's ordinary function type, so `def f @[a : Type] (x
//! : a) -> -F a` and `def f(a : Type, x : a) -> -F a` declare one type. A use
//! supplies the implicits by name in the instantiation slot, `f[a = T](x)`,
//! in any order.
//!
//! # Boundaries
//!
//! - A telescope entry is a lower-case name; a capitalised binder is the
//!   lowering's [`LoweringRefusal::ImplicitTelescope`].
//! - Only a function's telescope binds implicits: a signature or a definition
//!   half that is not a function tail refuses its telescope at the declaration.

use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use alloc::vec::Vec;

use anodized::spec;
use gandr_surface_syntax::NodeIndex;
use quenchant_shape::shape::Maybe;

use super::Collector;
use crate::error::LoweringRefusal;
use crate::form::Cursor;
use crate::form::Piece;
use crate::form::Pieces;
use crate::form::Placed;
use crate::form::TileName;
use crate::form::read_pieces;
use crate::resolve::SurfaceName;

#[cfg(test)]
mod tests;

/// Where a function's parameter is written.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: two distinct placements.
/// - executable: none — a plain tag.
///
/// # Adequacy
/// - hypothesis: L3 — a use supplies an implicit by name and an explicit
///   parameter in the parentheses.
/// - witness: `lower::implicit::tests::supply_by_name_is_order_free`
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Plicity
{
    /// In the telescope `@[ … ]`, supplied by name.
    Implicit,
    /// In the parentheses, supplied in place.
    Explicit,
}

quenchant_shape::reason_enum! {
    /// Why a parameter carries no written type.
    pub mod unstated {
        /// The reason the type is missing.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The parameter is written as its name alone.
            Unwritten,
        }
    }
}

quenchant_shape::reason_enum! {
    /// Why a parameter's type classifies no argument written for it.
    pub mod unclosed {
        /// The reason the type classifies nothing.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The parameter is written as its name alone.
            Unwritten,
            /// The type names an entry of the implicit telescope, which no
            /// argument written in the parentheses supplies.
            Dependent,
        }
    }
}

quenchant_shape::reason_enum! {
    /// Why a declaration has no merged telescope.
    pub mod merged {
        /// The reason nothing merges.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The declaration's telescope binds no value: it is absent, or
            /// every entry of it is a stage binder or a bound.
            NoImplicit,
        }
    }
}

/// One parameter of a function whose telescope binds a value, as the merged
/// telescope places it.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: the binder tile is the one the source writes for `name`.
/// - executable: none — a record of written tiles.
///
/// # Adequacy
/// - hypothesis: L3 — as [`Collector::merged_telescope`].
/// - witness: `lower::implicit::tests::a_forward_reference_from_the_prefix_binds_after_its_target`
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct TelescopeEntry<'source>
{
    /// The parameter's name.
    pub name: SurfaceName<'source>,
    /// The tile the name is written at.
    pub binder: Placed,
    /// The type it is written with, when it is.
    pub declared: Maybe<Placed, unstated::Absent>,
    /// Where it is written.
    pub plicity: Plicity,
}

/// One explicit parameter of a function written with a parameter list, as a
/// call's arguments read it.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: `binder` is the tile the source writes the parameter's name at,
///   and `declared` the type written for it, unless it is written bare or its
///   type names an entry of the implicit telescope.
/// - executable: none — a record of written tiles.
///
/// # Adequacy
/// - hypothesis: L3 — as [`Collector::explicit_parameters`].
/// - witness: `lower::native::tests::a_constructor_argument_takes_its_parameter_s_type_1833`
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct ExplicitParameter
{
    /// The tile the parameter's name is written at.
    pub binder: Placed,
    /// The type it is written with, read under the parameters before it.
    pub declared: Maybe<Placed, unclosed::Absent>,
}

/// A parameter's position among a telescope's parameters as they are
/// written, the telescope's entries before the parentheses'.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
#[repr(transparent)]
pub struct TelescopePosition(usize);

impl From<usize> for TelescopePosition
{
    /// The position `position`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(position: usize) -> Self
    {
        Self(position)
    }
}

impl From<TelescopePosition> for usize
{
    /// The position as an index.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(position: TelescopePosition) -> Self
    {
        position.0
    }
}

/// That the parameter at `later` stands after the one at `earlier`, its type
/// mentioning it.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Precedence
{
    /// The parameter whose type mentions the other.
    pub later: TelescopePosition,
    /// The parameter it mentions.
    pub earlier: TelescopePosition,
}

/// Two parameters of a telescope standing in a cycle: each one's type
/// mentions the other, directly or through the telescope.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: both are positions of the telescope the cycle was found in.
/// - executable: none — two positions.
///
/// # Adequacy
/// - hypothesis: L3 — a two-entry cycle names both entries.
/// - witness: `lower::implicit::tests::a_telescope_cycle_is_refused_naming_the_cycle`
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Cycle
{
    /// The first parameter the sort could not place.
    pub first: TelescopePosition,
    /// A parameter its type waits on.
    pub second: TelescopePosition,
}

/// The merged order of the parameters below `end`, written in order, each
/// [`Precedence`] of `after` standing in it.
///
/// # Specification
/// - requires: every position `after` names is below `end`.
/// - ensures: a permutation of the positions below `end` in which every
///   precedence of `after` holds, and among the positions free to stand next
///   the lowest stands first; a [`Cycle`] when no order holds every precedence,
///   naming the lowest position left unplaced and a position it waits on.
/// - fails: the [`Cycle`] as stated.
/// - panics: none.
///
/// # Errors
/// As `- fails:`.
///
/// # Termination
/// - reason: each turn of the loop places one position, taken from the ready
///   set, which every position enters at most once.
/// - measure: the positions not yet placed.
///
/// # Adequacy
/// - hypothesis: L1 — every dependence relation over up to four positions, each
///   answer checked against a validator: a topological order whose ties keep
///   the written order, or a cycle exactly when the relation has one.
/// - witness: `module::plicity::tests::the_merged_telescope_places_each_parameter_after_what_its_type_mentions`
#[spec(ensures: |ret| ret.as_ref().map_or_else(
    |cycle| cycle.first < end && cycle.second < end,
    |order| order.len() == usize::from(end),
))]
pub fn merge_order(
    end: TelescopePosition,
    after: &mut [Precedence],
) -> Result<Vec<TelescopePosition>, Cycle>
{
    after.sort_unstable_by_key(|precedence| (precedence.earlier, precedence.later));
    let mut waiting = alloc::vec![0_usize; usize::from(end)];
    for precedence in after.iter() {
        if let Some(slot) = waiting.get_mut(usize::from(precedence.later)) {
            *slot = slot.saturating_add(1);
        }
    }
    let mut ready = alloc::collections::BTreeSet::new();
    for (position, &count) in waiting.iter().enumerate() {
        if count == 0 {
            let _fresh = ready.insert(TelescopePosition(position));
        }
    }
    let mut order = Vec::with_capacity(usize::from(end));
    while let Some(next) = ready.pop_first() {
        order.push(next);
        let first = after.partition_point(|precedence| precedence.earlier < next);
        let last = after.partition_point(|precedence| precedence.earlier <= next);
        for precedence in after.get(first .. last).unwrap_or_default() {
            if let Some(slot) = waiting.get_mut(usize::from(precedence.later)) {
                *slot = slot.saturating_sub(1);
                if *slot == 0 {
                    let _fresh = ready.insert(precedence.later);
                }
            }
        }
    }
    if order.len() == usize::from(end) {
        return Ok(order);
    }
    let first = TelescopePosition(
        waiting
            .iter()
            .position(|&count| count > 0)
            .unwrap_or_default(),
    );
    let second = after
        .iter()
        .find(|precedence| {
            precedence.later == first
                && waiting
                    .get(usize::from(precedence.earlier))
                    .is_some_and(|&count| count > 0)
        })
        .map_or(first, |precedence| precedence.earlier);

    Err(Cycle { first, second })
}

impl<'source> Collector<'_, 'source>
{
    /// The merged telescope of the function whose header `header` stands just
    /// past the name of.
    ///
    /// # Specification
    /// - requires: `header` stands just past a declaration's name.
    /// - ensures: when the header opens a telescope one of whose entries `a :
    ///   T` sorts other than by `Size`, and a parameter list follows it, every
    ///   such entry and every explicit parameter, in the order [`merge_order`]
    ///   gives over what each one's type mentions, a name the type binds itself
    ///   mentioning nothing; absent otherwise. `header` is left where it was.
    /// - provides: the plicity metadata of [`super::Collected::plicities`].
    /// - fails: [`LoweringRefusal::TelescopeCycle`] at the declaration, naming
    ///   two parameters standing in a cycle; a form fault reading a type's
    ///   pieces.
    /// - panics: none.
    ///
    /// # Errors
    /// As `- fails:`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an implicit before the parameter its type mentions is
    ///   placed after it, and one whose type binds a later parameter's name is
    ///   not; a cycle is refused naming both; a telescope of stage binders
    ///   alone merges nothing.
    /// - witness: `lower::implicit::tests::a_forward_reference_from_the_prefix_binds_after_its_target`
    /// - witness: `lower::implicit::tests::a_binder_of_an_implicit_s_type_mentions_no_parameter_1350`
    /// - witness: `lower::implicit::tests::a_telescope_cycle_is_refused_naming_the_cycle`
    /// - witness: `lower::implicit::tests::a_stage_telescope_merges_nothing`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |merged| match *merged {
        Maybe::Present(ref entries) => entries.iter().any(|entry| entry.plicity == Plicity::Implicit),
        Maybe::Absent(_) => true,
    }))]
    pub(super) fn merged_telescope(
        &self,
        header: &Cursor<'_>,
        declaration: Placed,
    ) -> Result<Maybe<Vec<TelescopeEntry<'source>>, merged::Absent>, LoweringRefusal<'source>>
    {
        let none = Maybe::Absent(merged::Absent::NoImplicit);
        let mut cursor = header.clone();
        if let Maybe::Absent(_) = cursor.tile(TileName::ATTRIBUTES) {
            return Ok(none);
        }
        let mut scratch = Pieces::new();
        let mut entries: Vec<TelescopeEntry<'source>> = Vec::new();
        while let Maybe::Present(written) = cursor.tile(TileName::IDENTIFIER) {
            if let Maybe::Present(_) = cursor.tile(TileName::COLON) {
                let Maybe::Present(Piece::Operand(sort)) = cursor.read()
                else {
                    return Ok(none);
                };
                if self.sort_of(sort, &mut scratch)? == EntrySort::Value {
                    entries.push(TelescopeEntry {
                        name: self.name_of(written),
                        binder: written,
                        declared: Maybe::Present(sort),
                        plicity: Plicity::Implicit,
                    });
                }
            }
            else if let Maybe::Present(_) = cursor.tile(TileName::LESS_THAN) {
                let _over = cursor.tile(TileName::IDENTIFIER);
            }
            let _comma = cursor.tile(TileName::COMMA);
        }
        if entries.is_empty() {
            return Ok(none);
        }
        if let Maybe::Absent(_) = cursor.tile(TileName::BRACKET_CLOSE) {
            return Ok(none);
        }
        if let Maybe::Absent(_) = cursor.tile(TileName::PAREN_OPEN) {
            return Ok(none);
        }
        while let Maybe::Present(written) = cursor.tile(TileName::IDENTIFIER) {
            let declared = match cursor.tile(TileName::COLON) {
                Maybe::Present(_) => {
                    // A receiver's mode word or mode variable: the receivers
                    // table keeps it, and the function's lowering refuses one
                    // off a receiver.
                    if let Maybe::Absent(_) = cursor.tile(TileName::SHARED)
                        && let Maybe::Absent(_) = cursor.tile(TileName::CONSUMED)
                    {
                        let _mode = cursor.tile(TileName::IDENTIFIER);
                    }
                    match cursor.read() {
                        Maybe::Present(Piece::Operand(typed)) => Maybe::Present(typed),
                        Maybe::Present(Piece::Tile { .. }) | Maybe::Absent(_) => return Ok(none),
                    }
                },
                Maybe::Absent(_) => Maybe::Absent(unstated::Absent::Unwritten),
            };
            entries.push(TelescopeEntry {
                name: self.name_of(written),
                binder: written,
                declared,
                plicity: Plicity::Explicit,
            });
            let _comma = cursor.tile(TileName::COMMA);
        }
        if let Maybe::Absent(_) = cursor.at(TileName::PAREN_CLOSE) {
            return Ok(none);
        }
        let positions: BTreeMap<SurfaceName<'source>, TelescopePosition> = entries
            .iter()
            .enumerate()
            .map(|(position, entry)| (entry.name, TelescopePosition(position)))
            .collect();
        let mut after = Vec::new();
        // Each node still to read, with the innermost binder of the type's
        // own around it: a type binds the keys of its groups, `(x : A) => B`,
        // and a name such a key binds mentions no parameter (#1350).
        let mut pending: Vec<(NodeIndex, Option<usize>)> = Vec::new();
        let mut binders: Vec<(SurfaceName<'source>, Option<usize>)> = Vec::new();
        let mut keyed = Pieces::new();
        let mut named = Pieces::new();
        for (later, entry) in entries.iter().enumerate() {
            let Maybe::Present(typed) = entry.declared
            else {
                continue;
            };
            let later = TelescopePosition(later);
            binders.clear();
            pending.push((typed.node, None));
            while let Some((node, mut scope)) = pending.pop() {
                read_pieces(self.pbg, self.tree, node, &mut scratch)?;
                let pieces = core::mem::take(&mut scratch.pieces);
                for (index, piece) in pieces.iter().enumerate() {
                    let next = pieces.get(index.saturating_add(1));
                    match *piece {
                        Piece::Operand(operand) => match next {
                            Some(&Piece::Tile { label, .. }) if label == TileName::COLON => {
                                if let Some(name) = self.key(operand.node, &mut named)? {
                                    binders.push((name, scope));
                                    scope = Some(binders.len().saturating_sub(1));
                                }
                            },
                            Some(&Piece::Tile { label, .. })
                                if label == TileName::ARROW || label == TileName::FAT_ARROW =>
                            {
                                pending.push((operand.node, scope));
                                read_pieces(self.pbg, self.tree, operand.node, &mut keyed)?;
                                for (at, held) in keyed.pieces.iter().enumerate() {
                                    if let (&Piece::Operand(key), Some(&Piece::Tile { label, .. })) =
                                        (held, keyed.pieces.get(at.saturating_add(1)))
                                        && label == TileName::COLON
                                        && let Some(name) = self.key(key.node, &mut named)?
                                    {
                                        binders.push((name, scope));
                                        scope = Some(binders.len().saturating_sub(1));
                                    }
                                }
                            },
                            _ => pending.push((operand.node, scope)),
                        },
                        Piece::Tile { label, at }
                            if label == TileName::IDENTIFIER
                                || label == TileName::TYPE_VARIABLE =>
                        {
                            let name = self.name_of(at);
                            let mut enclosing = scope;
                            let mut bound = false;
                            while let Some(binder) = enclosing
                                && let Some(&(held, outer)) = binders.get(binder)
                            {
                                if held == name {
                                    bound = true;
                                    break;
                                }
                                enclosing = outer;
                            }
                            let mentioned = positions.get(&name).copied().filter(|_| !bound);
                            if let Some(earlier) = mentioned
                                && earlier != later
                                && entries.get(usize::from(earlier)).is_some_and(|other| {
                                    other.plicity == Plicity::Implicit
                                        || entry.plicity == Plicity::Implicit
                                        || earlier < later
                                })
                            {
                                after.push(Precedence { later, earlier });
                            }
                        },
                        Piece::Tile { .. } => {},
                    }
                }
                scratch.pieces = pieces;
            }
        }
        let end = TelescopePosition(entries.len());
        let order = merge_order(end, &mut after).map_err(|cycle| {
            let name = |position: TelescopePosition| {
                entries
                    .get(usize::from(position))
                    .map_or_else(|| self.name_of(declaration), |entry| entry.name)
            };
            LoweringRefusal::TelescopeCycle {
                span: declaration.span,
                first: name(cycle.first),
                second: name(cycle.second),
            }
        })?;

        Ok(Maybe::Present(
            order
                .iter()
                .filter_map(|&position| entries.get(usize::from(position)).copied())
                .collect(),
        ))
    }

    /// Each explicit parameter of the function whose header `header` stands
    /// just past the name of, in written order, with its written type when
    /// the type names no entry of the implicit telescope.
    ///
    /// # Specification
    /// - requires: `header` stands just past a declaration's name.
    /// - ensures: past an implicit telescope `[ … ]` when one is written, one
    ///   entry per parameter of the parenthesised list, at its name's tile: `x
    ///   : T` its `T`, or [`unclosed::Absent::Dependent`] when `T` names an
    ///   entry of the telescope; a bare `x` [`unclosed::Absent::Unwritten`]; a
    ///   receiver's mode word skipped. None when no parameter list follows, or
    ///   one is out of shape. `header` is left where it was. A type naming a
    ///   parameter before its own is kept: the arguments written for those
    ///   replace them where the call is read.
    /// - provides: [`super::Collected::parameters`], the type each argument of
    ///   a call checks against.
    /// - fails: never: a type whose pieces do not read counts as naming one.
    /// - panics: none.
    /// - executable: none — the cursor offers no count of its pieces to bound
    ///   the result by.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a constructor argument takes its classifier from the
    ///   parameter at its place, closed or naming the one before it.
    /// - witness: `lower::native::tests::a_constructor_argument_takes_its_parameter_s_type_1833`
    /// - witness: `lower::native::tests::a_constructor_argument_reads_the_arguments_before_it_1876`
    pub(super) fn explicit_parameters(
        &self,
        header: &Cursor<'_>,
    ) -> Vec<ExplicitParameter>
    {
        let mut cursor = header.clone();
        let mut bound: BTreeSet<SurfaceName<'source>> = BTreeSet::new();
        if let Maybe::Present(_) = cursor.tile(TileName::ATTRIBUTES) {
            loop {
                match cursor.read() {
                    Maybe::Present(Piece::Tile { label, .. })
                        if label == TileName::BRACKET_CLOSE =>
                    {
                        break;
                    },
                    Maybe::Present(Piece::Tile { label, at }) if label == TileName::IDENTIFIER => {
                        let _fresh = bound.insert(self.name_of(at));
                    },
                    Maybe::Present(_) => {},
                    Maybe::Absent(_) => return Vec::new(),
                }
            }
        }
        if let Maybe::Absent(_) = cursor.tile(TileName::PAREN_OPEN) {
            return Vec::new();
        }
        let mut parameters = Vec::new();
        while let Maybe::Present(written) = cursor.tile(TileName::IDENTIFIER) {
            let declared = match cursor.tile(TileName::COLON) {
                Maybe::Present(_) => {
                    if let Maybe::Absent(_) = cursor.tile(TileName::SHARED)
                        && let Maybe::Absent(_) = cursor.tile(TileName::CONSUMED)
                    {
                        let _mode = cursor.tile(TileName::IDENTIFIER);
                    }
                    match cursor.read() {
                        Maybe::Present(Piece::Operand(typed)) => self.closed(typed, &bound),
                        Maybe::Present(Piece::Tile { .. }) | Maybe::Absent(_) => return Vec::new(),
                    }
                },
                Maybe::Absent(_) => Maybe::Absent(unclosed::Absent::Unwritten),
            };
            parameters.push(ExplicitParameter {
                binder: written,
                declared,
            });
            let _comma = cursor.tile(TileName::COMMA);
        }
        if let Maybe::Absent(_) = cursor.at(TileName::PAREN_CLOSE) {
            return Vec::new();
        }

        parameters
    }

    /// The type written at `typed`, when it names none of `names`, anywhere
    /// inside it.
    ///
    /// # Specification
    /// - ensures: `typed` at once for no names; otherwise
    ///   [`unclosed::Absent::Dependent`] when an identifier or a type variable
    ///   written in the form spells one of `names`, or a piece of it does not
    ///   read, and `typed` otherwise. A name the form binds itself counts as
    ///   named: the answer errs toward naming.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the tiles are read from the tree, which a predicate
    ///   over the answer would read again.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — `List(a)` names `a`; `List(Integer)` names nothing.
    /// - witness: `lower::native::tests::a_constructor_argument_takes_its_parameter_s_type_1833`
    fn closed(
        &self,
        typed: Placed,
        names: &BTreeSet<SurfaceName<'source>>,
    ) -> Maybe<Placed, unclosed::Absent>
    {
        if names.is_empty() {
            return Maybe::Present(typed);
        }
        let mut scratch = Pieces::new();
        let mut pending = alloc::vec![typed.node];
        while let Some(next) = pending.pop() {
            if read_pieces(self.pbg, self.tree, next, &mut scratch).is_err() {
                return Maybe::Absent(unclosed::Absent::Dependent);
            }
            for piece in &scratch.pieces {
                match *piece {
                    Piece::Operand(operand) => pending.push(operand.node),
                    Piece::Tile { label, at }
                        if (label == TileName::IDENTIFIER || label == TileName::TYPE_VARIABLE)
                            && names.contains(&self.name_of(at)) =>
                    {
                        return Maybe::Absent(unclosed::Absent::Dependent);
                    },
                    Piece::Tile { .. } => {},
                }
            }
        }

        Maybe::Present(typed)
    }

    /// The name the key `node` of a group's entry `k : T` binds, when the key
    /// is one name, read through `scratch`.
    ///
    /// # Specification
    /// - ensures: the name exactly when the key's one piece is an identifier or
    ///   a type variable.
    /// - fails: a form fault reading the key's pieces.
    /// - panics: none.
    /// - executable: none — the name is read from the key's own tile, which a
    ///   predicate over the answer would read again.
    ///
    /// # Errors
    /// As `- fails:`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a function type's binder in an implicit's type, named
    ///   as a later parameter, orders nothing.
    /// - witness: `lower::implicit::tests::a_binder_of_an_implicit_s_type_mentions_no_parameter_1350`
    fn key(
        &self,
        node: NodeIndex,
        scratch: &mut Pieces,
    ) -> Result<Option<SurfaceName<'source>>, LoweringRefusal<'source>>
    {
        read_pieces(self.pbg, self.tree, node, scratch)?;
        Ok(match *scratch.pieces.as_slice() {
            [Piece::Tile { label, at }]
                if label == TileName::IDENTIFIER || label == TileName::TYPE_VARIABLE =>
            {
                Some(self.name_of(at))
            },
            _ => None,
        })
    }

    /// The stage binders of the function whose header `header` stands just
    /// past the name of: each entry `i : Size` of its telescope, in written
    /// order, so a binder's position is the ordinal its stage is minted at.
    ///
    /// # Specification
    /// - requires: `header` stands just past a declaration's name.
    /// - ensures: the names of the telescope's entries sorted by `Size`, in
    ///   written order; empty without a telescope or with none. `header` is
    ///   left where it was.
    /// - provides: the stage binders of [`super::Collected::stage_binders`],
    ///   which a call's supply `f[i = s]` names.
    /// - fails: a form fault reading an entry's sort.
    /// - panics: none.
    /// - executable: none — each entry's sort is read off the tree, and a
    ///   postcondition would repeat that walk to state it.
    ///
    /// # Errors
    /// As `- fails:`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a call supplying a stage names the callee's binder,
    ///   declared after the call or before it.
    /// - witness: `lower::staged::tests::a_supplied_stage_crosses_at_the_call_s_head_1227`
    pub(super) fn stage_binders(
        &self,
        header: &Cursor<'_>,
    ) -> Result<Vec<SurfaceName<'source>>, LoweringRefusal<'source>>
    {
        let mut binders = Vec::new();
        let mut cursor = header.clone();
        if let Maybe::Absent(_) = cursor.tile(TileName::ATTRIBUTES) {
            return Ok(binders);
        }
        let mut scratch = Pieces::new();
        while let Maybe::Present(written) = cursor.tile(TileName::IDENTIFIER) {
            if let Maybe::Present(_) = cursor.tile(TileName::COLON) {
                let Maybe::Present(Piece::Operand(sort)) = cursor.read()
                else {
                    return Ok(binders);
                };
                if self.sort_of(sort, &mut scratch)? == EntrySort::Stage {
                    binders.push(self.name_of(written));
                }
            }
            else if let Maybe::Present(_) = cursor.tile(TileName::LESS_THAN) {
                let _over = cursor.tile(TileName::IDENTIFIER);
            }
            let _comma = cursor.tile(TileName::COMMA);
        }
        Ok(binders)
    }

    /// How a telescope entry's sort `sort` binds: a stage when it is the
    /// type head `Size`, a region when it is the type head `Region`, a mode
    /// when it is the type head `Mode`, a value otherwise.
    ///
    /// # Specification
    /// - requires: `scratch` is free for reading pieces.
    /// - ensures: [`EntrySort::Stage`] exactly when the sort reads as one tile
    ///   spelling `Size`, [`EntrySort::Region`] exactly when it reads as one
    ///   spelling `Region`, and [`EntrySort::Mode`] exactly when it reads as
    ///   one spelling `Mode`.
    /// - fails: a form fault reading the sort's pieces.
    /// - panics: none.
    ///
    /// # Errors
    /// As `- fails:`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a stage binder, a region binder, a mode binder and a
    ///   type entry separate the four answers.
    /// - witness: `lower::implicit::tests::a_stage_telescope_merges_nothing`
    /// - witness: `lower::capability::tests::a_kept_type_at_a_region_binder_is_bound_to_it_1221`
    /// - witness: `lower::method::tests::a_deduced_mode_is_erased_from_the_telescope`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |sorted| *sorted == EntrySort::Value || scratch.pieces.len() == 1))]
    fn sort_of(
        &self,
        sort: Placed,
        scratch: &mut Pieces,
    ) -> Result<EntrySort, LoweringRefusal<'source>>
    {
        read_pieces(self.pbg, self.tree, sort.node, scratch)?;
        let [Piece::Tile { at, .. }] = *scratch.pieces.as_slice()
        else {
            return Ok(EntrySort::Value);
        };

        Ok(match self.name_of(at).as_ref() {
            "Size" => EntrySort::Stage,
            "Region" => EntrySort::Region,
            "Mode" => EntrySort::Mode,
            _ => EntrySort::Value,
        })
    }
}

/// What a telescope entry `a : T` binds.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum EntrySort
{
    /// A stage, sorted by `Size`: the signature's quantifier.
    Stage,
    /// A region, sorted by `Region`: the caller's region the definition
    /// abstracts, erased.
    Region,
    /// A mode, sorted by `Mode`: the access mode a method's call asks of the
    /// place it answers, erased.
    Mode,
    /// A value of the sort: an implicit parameter.
    Value,
}
