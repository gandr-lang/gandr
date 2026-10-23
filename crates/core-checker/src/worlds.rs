//! Located judgements: a judgement stands at a world, every hypothesis
//! records the world it was bound at, and a value crosses between worlds only
//! when its type is mobile and open.
//!
//! The vocabulary — [`World`], the handle type `A at w`, the capability
//! `cap_w`, and the forms `hold`, `leta` and `migrate[w]` — is
//! `gandr-core-term`'s `world` module. This module states the rules the
//! judgement runs over it and holds the pieces that read no machine state:
//! the crossing decision, an entry's worlds and capabilities, and the
//! refusals.
//!
//! # The rules
//!
//! ```text
//!              Γ ⊢_w v ⇒ A    w named
//!   Hold      ───────────────────────────────
//!              Γ ⊢_w hold v ⇒ F (A at w)
//!
//!              Γ ⊢_w v ⇒ A at w′    Γ, x :_w′ A ⊢_w t ⇒ C
//!   Leta      ────────────────────────────────────────────────
//!              Γ ⊢_w leta x = v ; t ⇒ C
//!
//!              Γ; Σ ⊢_w′ t ⇒ F A    A mobile and open    t pure
//!   Migrate   ──────────────────────────────────────────────────
//!              Γ; Σ, cap_w′ :_w ⊢_w migrate[w′] { t } ⇒ F A
//!
//!              x :_w′ A ∈ Γ    w′ = w
//!   Var       ─────────────────────────
//!              Γ ⊢_w x ⇒ A
//! ```
//!
//! The judgement's world is the register of the context's binders: every
//! binder a rule opens is located at it, a `leta` opens its binder at the
//! handle's world, and a migration moves the register for its body and puts
//! it back once the body's result has crossed. A linear resident — an
//! endpoint, a held value, a view, a capability — is located the same way,
//! and an action, an access or an eliminator on one at another world is
//! [`LocatedDefect::Elsewhere`], as is a variable.
//!
//! # Two predicates decide a crossing
//!
//! A value crosses — returned by a migration, or a constant read at a world
//! other than its declaration's home — only when its type is **mobile**, so
//! nothing it holds carries authority, and **open**, so its representation
//! commits to a value the far world can read. Neither implies the other: a
//! handle `A at w` is mobile whatever `A` is, and open only when `A` is.
//!
//! |former|mobile|open|
//! |---|---|---|
//! |integer, string, unit|yes|yes|
//! |product, sum, record, list, lift, staged|when every component is|when every component is|
//! |datatype|when every field and every type argument is|as mobile|
//! |`A at w`|yes|when `A` is|
//! |abstract atom|when its signature marks it `mobile`|as mobile|
//! |the unknown type|yes|yes|
//! |thunk, stack|no|no|
//! |endpoint, `Cap E`, `cap_w`|no|no|
//! |universe, static Pi, path, flow, run|no|no|
//! |decode of a code the judgement cannot read|no|no|
//!
//! A crossing is refused as [`LocatedDefect::Immobile`], naming the former
//! that failed and which predicate: [`Predicate::Mobile`] for a former met
//! directly, [`Predicate::Open`] for one met under a handle.
//!
//! - **A datatype** is decided field by field: a field naming a parameter
//!   crosses when the argument does, which is checked at the type itself; a
//!   field naming an earlier field, as a dependent field does, does not, for
//!   its type is not known until the value is; the datatype's own recursive
//!   occurrence crosses, a value being a finite tree of fields.
//! - **The static content** — universes, static Pi, identity evidence and
//!   recorded runs — is judged where it stands and never ships. Reversal: the
//!   storage codec's datatype rule, which encodes certificates and receipts,
//!   makes their carriers' crossing the decision.
//! - **The unknown type** crosses: a hole's type is consistent with every type,
//!   and the hole owes the rest.
//!
//! # The mark is the signature's
//!
//! An abstract type crosses only as its signature says: `mobile type T` in a
//! module signature marks the atom mobile, and sealing refuses a mark whose
//! representation does not cross as [`LocatedDefect::MarkUnfounded`], so the
//! promise a client relies on is checked once, where the representation is
//! visible. An unmarked atom is immobile outside its seal whatever it stands
//! for. **Alternative.** An attribute `@[ mobile ]` on the signature field,
//! which reads as decoration while it changes what a client may do with the
//! type. **Reversal.** Attributes gaining semantic roles on signature fields.
//!
//! # The entry
//!
//! A declaration is judged at its entry: a home world and the capabilities
//! the host hands it. A source states one with `@[ entry((home, cap, …)) ]`,
//! the worlds named by their declarations, read by [`Entry::declared`]; a
//! host names one for every declaration of a run by the worlds' names
//! ([`crate::HostGrant::entering`], `gandr check --entry home,cap,…`), and
//! bounds the stated ones as a grant bounds a held capability: a stated entry
//! at another home, or claiming a capability the host's does not hold, is
//! [`LocatedDefect::EntryUngranted`].
//!
//! - **The capabilities open under the outermost thunk.** The host forces an
//!   entry once, so its capabilities are linear residents of the run that
//!   judges its body, located at its home; a migration under any other thunk, a
//!   fixpoint, a branch, a handler or a shift is
//!   [`LocatedDefect::CapabilityCaptured`], as an endpoint there is.
//! - **A capability is a token, not an obligation.** One left unspent is
//!   dropped when the run ends, no residue.
//! - **An entry is not a value.** A declaration that spent a capability is an
//!   entry, and naming its constant from another declaration is
//!   [`LocatedDefect::EntryNamed`]: forcing it twice would spend its
//!   capabilities twice. Reversal: a capability requirement on a declaration's
//!   signature is the next rung, composition, not this slice.
//! - **The host's world is no locus.** A declaration whose entry names no world
//!   stands at [`World::Host`], where a hold and a `leta` are
//!   [`LocatedDefect::Unlocated`]; it is then world-free, and its constant is
//!   valid at every world. A constant whose declaration has a home is valid
//!   there, and elsewhere only when its type crosses.
//!
//! # The capability
//!
//! `cap_w` is a value-type former of its own, the one-shot authority to
//! migrate to `w`, resident in the linear zone and introduced by no term.
//! **Alternative.** `Cap E` at the consumable grade, which names an
//! exercised operation's grant atoms while a migration exercises none, and
//! which formation refuses as [`CheckRefusal::CapabilityConsumable`] for a
//! term to hold. **Reversal.** Migration as a host operation exercised
//! through a capability.
//!
//! # What is unreachable
//!
//! A fork binds both ends at the world it stands at, and a migration refuses
//! a resident of another world, so a channel never spans two worlds: a
//! cross-world send is not a form the judgement meets. Reversal: a fork that
//! binds its ends at two worlds, with the payload's crossing checked at each
//! send.
//!
//! # References
//!
//! - Tom Murphy VII, Karl Crary and Robert Harper. "Type-Safe Distributed
//!   Programming with ML5." _Trustworthy Global Computing 2007_, LNCS 4912.
//!   <https://www.cs.cmu.edu/~rwh/papers> — located judgements, `hold`,
//!   `leta` and the mobility of a type.
//! - Tom Murphy VII. "Modal Types for Mobile Code." Doctoral thesis,
//!   CMU-CS-08-126, Carnegie Mellon University, 2008.
//!   <http://tom7.org/papers/modal-types-for-mobile-code.pdf> — the
//!   worlds, the validity of a world-free hypothesis, and mobility.

use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use alloc::sync::Arc;
use alloc::vec::Vec;

use anodized::spec;
use gandr_core_term::ComputationId;
use gandr_core_term::LinearZone;
use gandr_core_term::Value;
use gandr_core_term::ValueTypeId;
use gandr_core_term::Zone;
use gandr_core_term::world::World;
use gandr_core_term::world::WorldType;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::DeBruijnIndex;
use quenchant_shape::shape::Maybe;

use crate::context::CheckingContext;
use crate::refusal::CheckRefusal;
use crate::session::Capture;
use crate::view::ValueTypeView;
use crate::view::value_type_view;

/// A declaration's entry: the world it is judged at and the capabilities the
/// host hands it, one migration each.
#[derive(Clone, Debug, Default, Eq, Hash, PartialEq)]
pub struct Entry
{
    /// The world the body is judged at.
    home: World,
    /// The world each capability migrates to, in the order named.
    capabilities: Vec<World>,
}

/// Whether a stated entry lies within the host's.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Bound
{
    /// The same home, and no capability more often than the host's holds it.
    Within,
    /// Another home, or a capability more often than the host's holds it.
    Beyond,
}

impl Entry
{
    /// The entry at `home` holding one capability per world of
    /// `capabilities`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn new(
        home: World,
        capabilities: Vec<World>,
    ) -> Self
    {
        Self { home, capabilities }
    }

    /// The entry `worlds` names, as an `entry` attribute writes it: its home
    /// first, then the world of each capability, each a declared constant.
    ///
    /// # Specification
    /// - ensures: present exactly when `worlds` names at least one, at the
    ///   first as home and holding one capability per later name, in order;
    ///   [`entry::Absent::Unstated`](crate::declaration::entry::Absent::Unstated)
    ///   for no name at all.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — no name, one name and three names separate absence, a
    ///   bare home and a home holding capabilities in written order.
    /// - witness: `worlds::tests::an_entry_reads_its_home_then_its_capabilities`
    #[spec(ensures: |ref ret| match *ret {
        Maybe::Present(ref entry) => worlds.first().is_some_and(|&home| entry.home == World::Declared(home))
            && entry.capabilities.len() == worlds.len().saturating_sub(1),
        Maybe::Absent(_) => worlds.is_empty(),
    })]
    #[inline]
    pub fn declared(worlds: &[ConstantIndex]) -> Maybe<Self, crate::declaration::entry::Absent>
    {
        let Some((&home, capabilities)) = worlds.split_first()
        else {
            return Maybe::Absent(crate::declaration::entry::Absent::Unstated);
        };
        Maybe::Present(Self::new(
            World::Declared(home),
            capabilities.iter().copied().map(World::Declared).collect(),
        ))
    }

    /// The world the body is judged at.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn home(&self) -> World
    {
        self.home
    }

    /// The world each capability migrates to.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn capabilities(&self) -> &[World]
    {
        &self.capabilities
    }

    /// Whether this entry lies within `host`: the same home, and no
    /// capability more often than the host's holds it.
    ///
    /// # Specification
    /// - ensures: [`Bound::Within`] exactly when the homes are equal and every
    ///   world is named at most as often here as in `host`.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a stated entry at the host's home with fewer
    ///   capabilities checks; one at another home, and one naming a capability
    ///   twice where the host names it once, are refused.
    /// - witness: `worlds::tests::a_stated_entry_is_bounded_by_the_host_s`
    #[spec(ensures: |ret| ret == Bound::Beyond || self.home == host.home)]
    #[inline]
    #[must_use]
    pub fn within(
        &self,
        host: &Self,
    ) -> Bound
    {
        if self.home != host.home {
            return Bound::Beyond;
        }
        let mut held: BTreeMap<World, usize> = BTreeMap::new();
        for &world in &host.capabilities {
            let count = held.entry(world).or_default();
            *count = count.saturating_add(1);
        }
        let bounded = self.capabilities.iter().all(|world| {
            held.get_mut(world).is_some_and(|count| {
                let Some(left) = count.checked_sub(1)
                else {
                    return false;
                };
                *count = left;
                true
            })
        });
        if bounded {
            Bound::Within
        }
        else {
            Bound::Beyond
        }
    }
}

/// The entry the host names for every declaration of a run.
#[derive(Clone, Debug, Default, Eq, Hash, PartialEq)]
pub enum HostEntry
{
    /// The host names none: a declaration's own entry is taken as stated,
    /// and one stating none stands at the host's world with no capability.
    #[default]
    Unbounded,
    /// Every declaration stands at this entry, or within it as it states.
    Within(Entry),
    /// The host named a world the source declares nowhere.
    Undeclared,
}

/// The name of a world, as a host names one before any source declares it.
#[repr(transparent)]
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct WorldName(Arc<str>);

impl From<&str> for WorldName
{
    /// Copy a world name into shared storage.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(name: &str) -> Self
    {
        Self(Arc::from(name))
    }
}

impl AsRef<str> for WorldName
{
    /// Borrow the world's spelling.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn as_ref(&self) -> &str
    {
        &self.0
    }
}

/// Whether a sealed abstract type crosses outside its seal.
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Mobility
{
    /// The signature does not mark it: it stays where it was made.
    #[default]
    Immobile,
    /// The signature marks it `mobile`: its representation crosses.
    Mobile,
}

/// Which of the two crossing predicates a former fails.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Predicate
{
    /// Authority: a value of the type may hold what is meaningful only where
    /// it was made.
    Mobile,
    /// Representation: a handle to it does not commit to a value the far
    /// world can read.
    Open,
}

/// The decision on whether a type crosses.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Crossing
{
    /// The type is mobile and open.
    Crosses,
    /// The type stays: `former` fails `predicate`.
    Stays
    {
        /// The former that failed, as it stands in the type.
        former: ValueTypeId,
        /// The predicate it failed.
        predicate: Predicate,
    },
}

/// What crosses at a refused crossing. The world it crosses to is where the
/// refusal stands: the innermost migration around it, or the entry's home.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Crossed
{
    /// A migration's result, returned to the world it left.
    Result,
    /// A constant, the refusal's node, read at a world other than its
    /// declaration's home.
    Constant,
}

/// How a located judgement breaks.
///
/// A defect names what the judgement cannot recover from the refusal's node:
/// the world a migration or a read stands at is the innermost migration
/// around the node, or the entry's home, and is left to the reader.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum LocatedDefect
{
    /// A value crosses to a world where its type does not.
    Immobile
    {
        /// What crosses.
        crossed: Crossed,
        /// Its type.
        ty: ValueTypeId,
        /// The former in `ty` that fails.
        former: ValueTypeId,
        /// The predicate it fails.
        predicate: Predicate,
    },
    /// A migration found no capability for its world where it stands.
    CapabilityMissing
    {
        /// The world migrated to.
        world: World,
    },
    /// A migration stands under a former that may run it other than once,
    /// or in a body that may perform an operation.
    CapabilityCaptured
    {
        /// The world migrated to.
        world: World,
        /// What may run it again.
        by: Capture,
    },
    /// A hypothesis or a linear resident used at a world other than the one
    /// it was bound at.
    Elsewhere
    {
        /// The world it was bound at.
        bound: World,
    },
    /// A hold checked against a handle at another world: a hold makes a
    /// handle only where it stands.
    HoldElsewhere
    {
        /// The world the handle was wanted at.
        wanted: World,
    },
    /// A hold or a `leta` at the host's world, which is no locus.
    Unlocated,
    /// A world position that holds no world declaration.
    UndeclaredWorld
    {
        /// The position named.
        world: ConstantIndex,
    },
    /// The host's entry names a world the source declares nowhere.
    HostWorldUndeclared,
    /// A `mobile` mark over a representation that does not cross.
    MarkUnfounded
    {
        /// The abstract type's atom.
        atom: ConstantIndex,
        /// The former in the representation that fails.
        former: ValueTypeId,
        /// The predicate it fails.
        predicate: Predicate,
    },
    /// A declaration that spent a capability named from another one.
    EntryNamed
    {
        /// The entry's constant.
        constant: ConstantIndex,
    },
    /// A stated entry the host's entry does not hold.
    EntryUngranted
    {
        /// The declaration stating it.
        constant: ConstantIndex,
    },
    /// A `leta` of a value whose type is no handle `A at w`.
    NotAHandle
    {
        /// The type the value synthesised.
        found: ValueTypeId,
    },
}

/// One move of the world register a typed run keeps: a migration's push,
/// with the linear zone before and after its capability was spent, and its
/// pop.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum WorldMove
{
    /// A migration spent a capability and moved the register.
    Migrated
    {
        /// The migration.
        at: ComputationId,
        /// The world it left.
        from: World,
        /// The world it moved to.
        to: World,
        /// The linear zone before the capability was spent.
        before: LinearZone,
        /// The linear zone after.
        after: LinearZone,
    },
    /// A migration's result crossed and the register was put back.
    Returned
    {
        /// The migration.
        at: ComputationId,
        /// The world the register was put back at.
        to: World,
    },
}

/// Whether a run spent a capability of its entry.
#[derive(Clone, Copy, Debug, Default, Eq, Hash, PartialEq)]
pub(crate) enum Spending
{
    /// No capability was spent.
    #[default]
    Unspent,
    /// At least one was.
    Spent,
}

quenchant_shape::reason_enum! {
    /// Why no entry is under way.
    pub mod entered {
        /// The reason no entry is under way.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// No declaration's body is being judged.
            Idle,
        }
    }
}

/// The located state of a checking context: the worlds declared, each
/// declaration's home, the entries, the host's entry and the entry of the
/// declaration under way.
#[derive(Clone, Debug)]
pub(crate) struct Worlds
{
    /// The positions of the world declarations admitted.
    declared: BTreeSet<ConstantIndex>,
    /// The home of each declaration judged at a declared world.
    homes: BTreeMap<ConstantIndex, World>,
    /// The declarations that spent a capability.
    entries: BTreeSet<ConstantIndex>,
    /// The entry the host names.
    host: HostEntry,
    /// The entry of the declaration whose body is being judged.
    entered: Maybe<Entry, entered::Absent>,
    /// Whether a run of the body under way spent a capability.
    spending: Spending,
}

impl Default for Worlds
{
    /// No world declared, no home, no entry, the host naming none and no
    /// entry under way.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn default() -> Self
    {
        Self {
            declared: BTreeSet::new(),
            homes: BTreeMap::new(),
            entries: BTreeSet::new(),
            host: HostEntry::Unbounded,
            entered: Maybe::Absent(entered::Absent::Idle),
            spending: Spending::Unspent,
        }
    }
}

impl Worlds
{
    /// Admit the world declaration at `constant`.
    ///
    /// # Specification
    /// trivial.
    pub(crate) fn declare(
        &mut self,
        constant: ConstantIndex,
    )
    {
        let _fresh = self.declared.insert(constant);
    }

    /// The positions of the world declarations admitted.
    ///
    /// # Specification
    /// trivial.
    pub(crate) const fn declared(&self) -> &BTreeSet<ConstantIndex>
    {
        &self.declared
    }

    /// Whether `world` is the host's or one a world declaration declared.
    ///
    /// # Specification
    /// - ensures: success for the host's world and a declared one.
    /// - fails: [`LocatedDefect::UndeclaredWorld`] for a world no world
    ///   declaration declares.
    /// - panics: none.
    ///
    /// # Errors
    /// As above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a handle, a migration and an entry naming a position
    ///   no world declaration holds are refused; the declared worlds are not.
    /// - witness: `worlds::tests::an_undeclared_world_is_refused`
    #[spec(ensures: |ret| ret.is_ok() || matches!(world, World::Declared(_)))]
    pub(crate) fn named(
        &self,
        world: World,
    ) -> Result<(), LocatedDefect>
    {
        match world {
            World::Host => Ok(()),
            World::Declared(constant) if self.declared.contains(&constant) => Ok(()),
            World::Declared(constant) => Err(LocatedDefect::UndeclaredWorld { world: constant }),
        }
    }

    /// Bound every declaration's entry by `host`.
    ///
    /// # Specification
    /// trivial.
    pub(crate) fn host(
        &mut self,
        host: HostEntry,
    )
    {
        self.host = host;
    }

    /// The entry of the declaration under way, when one is.
    ///
    /// # Specification
    /// trivial.
    pub(crate) const fn entered(&self) -> &Maybe<Entry, entered::Absent>
    {
        &self.entered
    }

    /// Begin judging a body at `entry`, nothing spent yet.
    ///
    /// # Specification
    /// trivial.
    pub(crate) fn enter(
        &mut self,
        entry: Entry,
    )
    {
        self.entered = Maybe::Present(entry);
        self.spending = Spending::Unspent;
    }

    /// Finish judging a body: whether a run of it spent a capability.
    ///
    /// # Specification
    /// trivial.
    pub(crate) fn leave(&mut self) -> Spending
    {
        self.entered = Maybe::Absent(entered::Absent::Idle);
        core::mem::take(&mut self.spending)
    }

    /// Note that a run of the body under way spent a capability.
    ///
    /// # Specification
    /// trivial.
    pub(crate) fn spend(&mut self)
    {
        self.spending = Spending::Spent;
    }

    /// Record `constant`'s home, and whether it is an entry.
    ///
    /// # Specification
    /// trivial.
    pub(crate) fn settle(
        &mut self,
        constant: ConstantIndex,
        home: World,
        spending: Spending,
    )
    {
        if home != World::Host {
            let _previous = self.homes.insert(constant, home);
        }
        if spending == Spending::Spent {
            let _fresh = self.entries.insert(constant);
        }
    }

    /// The home of `constant`'s declaration: the host's world when it was
    /// judged at none.
    ///
    /// # Specification
    /// trivial.
    pub(crate) fn home(
        &self,
        constant: ConstantIndex,
    ) -> World
    {
        self.homes.get(&constant).copied().unwrap_or_default()
    }

    /// Whether `constant` may be named: it is not an entry, a declaration
    /// that spent a capability.
    ///
    /// # Specification
    /// - ensures: success exactly when `constant`'s judgement spent no
    ///   capability.
    /// - fails: [`LocatedDefect::EntryNamed`] for an entry.
    /// - panics: none.
    ///
    /// # Errors
    /// As above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an entry forced from a later declaration is refused;
    ///   an owed declaration forced the same way is named freely.
    /// - witness: `worlds::tests::a_second_migration_without_a_capability_is_refused`
    #[spec(ensures: |ret| ret.is_err() == self.entries.contains(&constant))]
    pub(crate) fn nameable(
        &self,
        constant: ConstantIndex,
    ) -> Result<(), LocatedDefect>
    {
        if self.entries.contains(&constant) {
            return Err(LocatedDefect::EntryNamed { constant });
        }
        Ok(())
    }

    /// The entry `constant`'s declaration is judged at: its own as it states
    /// it, within the host's, or the host's when it states none.
    ///
    /// # Specification
    /// - ensures: under no host entry, the stated entry or the host's world
    ///   with no capability; under a host entry, the stated entry when it lies
    ///   within the host's, the host's when none is stated.
    /// - fails: [`LocatedDefect::EntryUngranted`] for a stated entry outside
    ///   the host's; [`LocatedDefect::HostWorldUndeclared`] when the host named
    ///   a world the source does not declare;
    ///   [`LocatedDefect::UndeclaredWorld`] for a world the stated entry names
    ///   that no declaration declares.
    /// - panics: none.
    ///
    /// # Errors
    /// As above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the three host entries against a stated entry and
    ///   none, each answer asserted.
    /// - witness: `worlds::tests::a_stated_entry_is_bounded_by_the_host_s`
    #[spec(ensures: |ret| ret.is_err() || matches!(self.host, HostEntry::Unbounded | HostEntry::Within(_)))]
    pub(crate) fn resolve(
        &self,
        constant: ConstantIndex,
        stated: Maybe<&Entry, crate::declaration::entry::Absent>,
    ) -> Result<Entry, LocatedDefect>
    {
        if let Maybe::Present(entry) = stated {
            for &world in core::iter::once(&entry.home).chain(&entry.capabilities) {
                self.named(world)?;
            }
        }
        match (&self.host, stated) {
            (&HostEntry::Undeclared, _) => Err(LocatedDefect::HostWorldUndeclared),
            (&HostEntry::Unbounded, Maybe::Present(entry)) => Ok(entry.clone()),
            (&HostEntry::Unbounded, Maybe::Absent(_)) => Ok(Entry::default()),
            (&HostEntry::Within(ref host), Maybe::Present(entry)) => match entry.within(host) {
                Bound::Within => Ok(entry.clone()),
                Bound::Beyond => Err(LocatedDefect::EntryUngranted { constant }),
            },
            (&HostEntry::Within(ref host), Maybe::Absent(_)) => Ok(host.clone()),
        }
    }
}

/// One type the crossing decision still has to read: the type, the
/// predicate it answers to, and where its variables point.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Pending
{
    /// The type.
    ty: ValueTypeId,
    /// The predicate a failure here fails: [`Predicate::Open`] under a
    /// handle.
    predicate: Predicate,
    /// Where its variables point.
    scope: Scope,
}

/// Where the variables of a type the crossing decision reads point.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Scope
{
    /// A type the judgement stands at: a decoded variable is a code the
    /// judgement cannot read.
    Standing
    {
        /// The binders opened inside the type since its root.
        depth: u32,
    },
    /// A datatype's field: a decoded variable names a parameter, which
    /// crosses when its argument does, or an earlier field, which does not.
    Field
    {
        /// The fields before this one.
        position: u32,
        /// The binders opened inside the field since its root.
        depth: u32,
    },
}

impl Scope
{
    /// The same scope one binder deeper.
    ///
    /// # Specification
    /// trivial.
    const fn deeper(self) -> Self
    {
        match self {
            Self::Standing { depth } => Self::Standing {
                depth: depth.saturating_add(1),
            },
            Self::Field { position, depth } => Self::Field {
                position,
                depth: depth.saturating_add(1),
            },
        }
    }

    /// What the decode of the variable at `index` names, as a crossing reads
    /// it.
    ///
    /// # Specification
    /// trivial.
    fn decoded(
        self,
        index: DeBruijnIndex,
    ) -> Decoded
    {
        match self {
            Self::Standing { .. } => Decoded::Opaque,
            Self::Field { position, depth } => match u32::from(index).checked_sub(depth) {
                Some(outer) if outer >= position => Decoded::Parameter,
                Some(_) | None => Decoded::Opaque,
            },
        }
    }
}

/// What a decoded variable names, as a crossing reads it.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Decoded
{
    /// A datatype's parameter: it crosses on its own, its argument checked at
    /// the type.
    Parameter,
    /// A code the judgement cannot read: a variable the type stands under, or
    /// an earlier field.
    Opaque,
}

/// Decide whether `ty` crosses: whether it is mobile and open, as the table
/// in this module's documentation states it for every value-type former.
///
/// # Specification
/// - requires: `ty` is formed in `context`.
/// - ensures: [`Crossing::Crosses`] when every former `ty` reaches crosses;
///   otherwise the first former met that does not, with the predicate it fails,
///   [`Predicate::Open`] when it was reached under a handle.
/// - fails: as the weak-head reading of a type; a former outside the fragment
///   as the view refuses it.
/// - panics: none.
///
/// # Errors
/// As above.
///
/// # Termination
/// - reason: the `while let` loop over an explicit worklist, not recursion.
/// - measure: a type is replaced by its children; a datatype's fields are read
///   once per declaration, its own and every other's, so a recursive datatype
///   adds its fields once.
///
/// # Adequacy
/// - hypothesis: L3 — one type of every value-type former, each asserted to
///   cross or to stay with its predicate, plus a handle over an endpoint, a
///   datatype over a parameter at a thunk and an abstract atom marked and
///   unmarked.
/// - witness: `worlds::tests::mobility_is_decided_on_every_former`
#[spec(ensures: |ret| match ret {
    | Ok(Crossing::Stays { former, .. }) => context.arena().value_type(former).is_some(),
    | Ok(Crossing::Crosses) | Err(_) => true,
})]
pub(crate) fn crosses(
    context: &mut CheckingContext<'_>,
    ty: ValueTypeId,
) -> Result<Crossing, CheckRefusal>
{
    let mut pending = Vec::from([Pending {
        ty,
        predicate: Predicate::Mobile,
        scope: Scope::Standing { depth: 0 },
    }]);
    let mut fields_read: BTreeSet<ConstantIndex> = BTreeSet::new();
    // A data type's arguments, copied out of the arena while it grows; one
    // buffer refilled per data type met.
    let mut arguments_held = Vec::new();
    while let Some(Pending {
        ty,
        predicate,
        scope,
    }) = pending.pop()
    {
        let head = context.whnf_value_type(ty)?;
        let stays = Crossing::Stays {
            former: head,
            predicate,
        };
        let below = |child| Pending {
            ty: child,
            predicate,
            scope,
        };
        match value_type_view(context.arena(), head)? {
            ValueTypeView::Integer
            | ValueTypeView::String
            | ValueTypeView::Character
            | ValueTypeView::Float64
            | ValueTypeView::Fixed(_)
            | ValueTypeView::Unit
            | ValueTypeView::Unknown => {},
            ValueTypeView::Product(parts) | ValueTypeView::Sum(parts) => {
                pending.extend(parts.iter().map(|&part| below(part)));
            },
            ValueTypeView::Record(fields) => {
                pending.extend(fields.values().map(|&field| below(field)));
            },
            ValueTypeView::List(inner)
            | ValueTypeView::Lift { inner, .. }
            | ValueTypeView::Staged { base: inner, .. }
            | ValueTypeView::Kept { value: inner, .. } => pending.push(below(inner)),
            ValueTypeView::Sigma { first, second } => {
                pending.push(below(first));
                pending.push(Pending {
                    ty: second,
                    predicate,
                    scope: scope.deeper(),
                });
            },
            ValueTypeView::World(WorldType::At { inner, .. }) => pending.push(Pending {
                ty: inner,
                predicate: Predicate::Open,
                scope,
            }),
            ValueTypeView::Abstract(atom) => {
                if context.abstract_mobility(atom)? == Mobility::Immobile {
                    return Ok(stays);
                }
            },
            ValueTypeView::Element { code, .. } => {
                let parameter = matches!(
                    *context.arena().value(code).ok_or(CheckRefusal::DanglingNode {
                        node: crate::refusal::CoreNode::Term(crate::refusal::TermNode::Value(code)),
                    })?,
                    Value::Variable { zone: Zone::Intuitionistic, index }
                        if scope.decoded(index) == Decoded::Parameter
                );
                if !parameter {
                    return Ok(stays);
                }
            },
            ValueTypeView::Data {
                declaration,
                arguments,
            } => {
                arguments_held.clear();
                arguments_held.extend_from_slice(arguments);
                let Some(signature) = context.consult_data(declaration)
                else {
                    return Ok(stays);
                };
                for (&argument, &classifier) in arguments_held.iter().zip(signature.parameters()) {
                    let ValueTypeView::Universe { level, .. } =
                        value_type_view(context.arena(), classifier)?
                    else {
                        continue;
                    };
                    let level = level.clone();
                    let decoded = context.arena_mut().value_type_element(argument, level);
                    pending.push(below(decoded));
                }
                if fields_read.insert(declaration) {
                    for fields in signature.constructors() {
                        for (position, &field) in (0_u32 ..).zip(fields) {
                            pending.push(Pending {
                                ty: field,
                                predicate,
                                scope: Scope::Field { position, depth: 0 },
                            });
                        }
                    }
                }
            },
            ValueTypeView::Thunk(_)
            | ValueTypeView::Stack { .. }
            | ValueTypeView::Session(_)
            | ValueTypeView::Capability { .. }
            | ValueTypeView::Buffer
            | ValueTypeView::World(WorldType::Capability(_))
            | ValueTypeView::Universe { .. }
            | ValueTypeView::StaticPi { .. }
            | ValueTypeView::PathUniverse(..)
            | ValueTypeView::Path { .. }
            | ValueTypeView::Flow { .. }
            | ValueTypeView::Run(_)
            | ValueTypeView::Prefix(_)
            | ValueTypeView::Dialogue(_)
            | ValueTypeView::Web => return Ok(stays),
        }
    }
    Ok(Crossing::Crosses)
}

#[cfg(test)]
mod tests;
