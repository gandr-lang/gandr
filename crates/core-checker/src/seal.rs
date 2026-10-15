//! Site-keyed minting: one atom per abstract component per sealing site, in
//! source order, and the record that makes the atoms' freshness checkable.
//!
//! # Why a table at all
//!
//! Opaque ascription `module M :> Σ { … }` mints one nominal atom for each
//! abstract type component of `Σ` and gives the module's exports their types
//! at the atoms. An abstract type could instead be introduced by quantifying
//! existentially over its identity, packing the representation at the
//! ascription and opening the package at every use (Mitchell and Plotkin's
//! reading, and the one *F-ing modules* elaborates to). The two presentations
//! translate into each other in the first-order fragment sealing admits; what
//! differs is what an admission point can verify. A package offers an importer
//! nothing to check, because the packing already happened elsewhere. Minting
//! against a table offers a check, because the identity minted is a function
//! of the sealing site and the site is recorded: re-elaborate, re-mint, and
//! require the result to equal the record.
//!
//! - Choice: generative atoms keyed by site, in the line of Harper and
//!   Lillibridge's translucent sums and Leroy's manifest types, where an
//!   opaquely ascribed component is a new type name rather than a bound
//!   variable.
//! - Alternatives: existential packages, which give no recorded identity to
//!   recheck; a counter with no site, which mints deterministic serials but
//!   cannot refuse a program that seals one component twice.
//! - Reversal: a sealing whose identity must survive across separately
//!   elaborated programs — two programs both start their serials at zero, so
//!   serials are deterministic but not globally unique. That widening belongs
//!   to the package boundary, where a sealed value first crosses a process.
//!
//! # What a site is
//!
//! A [`SealSite`] names one opaque ascription and one abstract component of
//! its signature, both by numbers the producer issues: the checker is
//! name-free, so a site carries no module or component name. Sealing is
//! declaration-granular, so a site always has its sealing ascription in scope,
//! and two ascriptions sealing a component of the same name are two sites.
//! Elaborating one program meets one sequence of sites in one order, so the
//! serials are a function of the program rather than of the run, and
//! [`SealTable::verify_reminting`] refutes a recorded sequence a
//! re-elaboration does not reproduce.
//!
//! The serial orders the minting; the atom's identity in the core and the
//! kernel is its admission position, which the sealing declaration takes and
//! the kernel bridge carries across unchanged. The kernel's export format has
//! the other half of the check: its minted-atom table refutes an artifact
//! whose recorded atoms are not the abstract-type declarations it holds, where
//! this table refutes a program that seals one component twice.
//!
//! # References
//!
//! - Robert Harper and Mark Lillibridge. "A Type-Theoretic Approach to
//!   Higher-Order Modules with Sharing." _POPL 1994_.
//!   <https://doi.org/10.1145/174675.176927>
//! - Xavier Leroy. "Manifest Types, Modules, and Separate Compilation." _POPL
//!   1994_. <https://doi.org/10.1145/174675.176926>
//! - Derek Dreyer, Karl Crary and Robert Harper. "A Type System for
//!   Higher-Order Modules." _POPL 2003_. <https://doi.org/10.1145/604131.604151>
//! - Andreas Rossberg, Claudio Russo and Derek Dreyer. "F-ing Modules."
//!   _Journal of Functional Programming_ 24(5) (2014).
//!   <https://doi.org/10.1017/S0956796814000264>

use alloc::collections::BTreeMap;
use alloc::vec::Vec;
use core::fmt;

use anodized::spec;
use quenchant_shape::shape::Maybe;

quenchant_shape::reason_enum! {
    /// Why a table holds no atom for a site.
    pub mod minted_site {
        /// The reason no atom is held.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// No minting claimed the site.
            Unminted,
        }
    }
}

/// The opaque ascription a site belongs to, as its producer numbers it.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct SealingSite(usize);

impl From<usize> for SealingSite
{
    /// The ascription numbered `index`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(index: usize) -> Self
    {
        Self(index)
    }
}

impl From<SealingSite> for usize
{
    /// The number the ascription carries.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(sealing: SealingSite) -> Self
    {
        sealing.0
    }
}

/// An abstract component's place among its signature's components.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ComponentOrdinal(usize);

impl From<usize> for ComponentOrdinal
{
    /// The component at place `index`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(index: usize) -> Self
    {
        Self(index)
    }
}

impl From<ComponentOrdinal> for usize
{
    /// The component's place.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(component: ComponentOrdinal) -> Self
    {
        component.0
    }
}

/// One sealing site: an opaque ascription and the abstract component of its
/// signature it seals.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct SealSite
{
    /// The ascription.
    sealing: SealingSite,
    /// The component it seals.
    component: ComponentOrdinal,
}

impl SealSite
{
    /// The site sealing `component` at the ascription `sealing`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn new(
        sealing: SealingSite,
        component: ComponentOrdinal,
    ) -> Self
    {
        Self { sealing, component }
    }

    /// The ascription.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn sealing(&self) -> SealingSite
    {
        self.sealing
    }

    /// The component sealed.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn component(&self) -> ComponentOrdinal
    {
        self.component
    }
}

impl fmt::Display for SealSite
{
    /// Writes the site as the ascription's and the component's numbers.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        write!(
            f,
            "ascription {} component {}",
            self.sealing.0, self.component.0
        )
    }
}

/// A minted atom's place in minting order.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct SealSerial(usize);

impl From<usize> for SealSerial
{
    /// The serial `index`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(index: usize) -> Self
    {
        Self(index)
    }
}

impl From<SealSerial> for usize
{
    /// The place the serial names.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(serial: SealSerial) -> Self
    {
        serial.0
    }
}

/// One minted atom: its serial and the site that minted it.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct SealId
{
    /// The place in minting order.
    serial: SealSerial,
    /// The site that minted it.
    site: SealSite,
}

impl SealId
{
    /// The place in minting order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn serial(&self) -> SealSerial
    {
        self.serial
    }

    /// The site that minted it.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn site(&self) -> SealSite
    {
        self.site
    }
}

/// Why a minting or a re-minting check failed.
///
/// Both refuse a claim about freshness: one a program sealing one component
/// twice, the other a recorded sequence re-elaboration does not reproduce.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum SealError
{
    /// Two sealings claimed one site.
    ///
    /// Minting the second would give one component two atoms, and the second
    /// would shadow the first in every later reference — silent where it is
    /// made, and observable only as a type error at a use far away.
    SiteAlreadyMinted
    {
        /// The site claimed twice.
        site: SealSite,
    },
    /// A re-elaboration did not reproduce a recorded minting: the sites
    /// differ, or the same sites came in another order and so at other
    /// serials.
    RemintingDiverged
    {
        /// The first serial at which the two sequences disagree.
        serial: SealSerial,
    },
    /// A re-elaboration minted another number of atoms than was recorded.
    RemintingCountDiverged
    {
        /// How many atoms the record holds.
        recorded: usize,
        /// How many this table minted.
        minted: usize,
    },
}

impl fmt::Display for SealError
{
    /// Writes the refused claim with its site, serial or counts.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        match *self {
            Self::SiteAlreadyMinted { site } => {
                write!(f, "the sealing site at {site} was already minted")
            },
            Self::RemintingDiverged { serial } => {
                write!(
                    f,
                    "re-minting diverged from the recorded sealing at serial {}",
                    serial.0
                )
            },
            Self::RemintingCountDiverged { recorded, minted } => {
                write!(
                    f,
                    "re-minting produced {minted} atoms where {recorded} were recorded"
                )
            },
        }
    }
}

impl core::error::Error for SealError
{
}

/// The atoms one elaboration minted, in minting order, with the sites that
/// minted them.
#[derive(Clone, Debug, Default, Eq, Hash, PartialEq)]
pub struct SealTable
{
    /// The sites minted, in minting order; a site's index is its serial.
    order: Vec<SealSite>,
    /// Each minted site's serial, for the duplicate refusal.
    minted: BTreeMap<SealSite, SealSerial>,
}

impl SealTable
{
    /// A table that has minted nothing.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn new() -> Self
    {
        Self::default()
    }

    /// Mint one atom for `site`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: when `site` was not minted, the atom at the next serial in
    ///   minting order, recorded against `site`; on refusal the table is
    ///   unchanged.
    /// - provides: the one way an abstract component acquires an identity.
    /// - fails: [`SealError::SiteAlreadyMinted`] when `site` was minted before,
    ///   refused where the program does it rather than at a use later.
    /// - panics: none.
    ///
    /// # Errors
    /// [`SealError::SiteAlreadyMinted`].
    ///
    /// # Adequacy
    /// - hypothesis: L2 — minting order is serial order and each site mints
    ///   once; the L3 residue is the duplicate refusal.
    /// - witness: `seal::tests::minting_is_ordered_and_each_site_mints_once`
    /// - witness: `seal::tests::a_repeated_site_is_refused`
    /// - witness: `seal::tests::two_declarations_sealing_one_component_name_stay_distinct`
    #[spec(
        captures: before = (self.order.len(), self.minted.contains_key(&site)),
        ensures: |ret| match ret {
            | Ok(id) => !before.1 && id.site == site && usize::from(id.serial) == before.0
                && self.order.len() == before.0.saturating_add(1)
                && self.minted.get(&site) == Some(&id.serial),
            | Err(SealError::SiteAlreadyMinted { site: refused }) => before.1 && refused == site
                && self.order.len() == before.0,
            | Err(_) => false,
        },
    )]
    #[inline]
    pub fn mint(
        &mut self,
        site: SealSite,
    ) -> Result<SealId, SealError>
    {
        if self.minted.contains_key(&site) {
            return Err(SealError::SiteAlreadyMinted { site });
        }
        let serial = SealSerial(self.order.len());
        let _prior = self.minted.insert(site, serial);
        self.order.push(site);
        Ok(SealId { serial, site })
    }

    /// The sites minted, in minting order: a site's index is its serial.
    ///
    /// Every entry names an ascription that was in scope when it minted, so a
    /// minted atom with no sealing occurrence to anchor it cannot appear here.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn sites(&self) -> &[SealSite]
    {
        &self.order
    }

    /// The atom `site` minted, or why there is none.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the atom at the serial `site` was minted at, when it was.
    /// - fails: never; an unminted site is [`minted_site::Absent::Unminted`].
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a minted and an unminted site separate the answer.
    /// - witness: `seal::tests::minting_is_ordered_and_each_site_mints_once`
    #[spec(ensures: |ret| match ret {
        | Maybe::Present(id) => id.site == site && self.minted.get(&site) == Some(&id.serial),
        | Maybe::Absent(_) => !self.minted.contains_key(&site),
    })]
    #[inline]
    pub fn lookup(
        &self,
        site: SealSite,
    ) -> Maybe<SealId, minted_site::Absent>
    {
        match self.minted.get(&site) {
            Some(&serial) => Maybe::Present(SealId { serial, site }),
            None => Maybe::Absent(minted_site::Absent::Unminted),
        }
    }

    /// Refute a recorded minting against this one: the freshness check.
    ///
    /// A recorded sequence of sites is compared with the sequence this
    /// elaboration minted — the same sites in the same order, so at the same
    /// serials, or the record is refused. Order is compared, not membership,
    /// because the serial is the place: two programs minting the same two
    /// sites in opposite orders mint different atoms.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: `Ok(())` exactly when `recorded` is this table's minting
    ///   order, element for element.
    /// - provides: the elaborator's re-minting check, beside the export
    ///   format's minted-atom table.
    /// - fails: [`SealError::RemintingCountDiverged`] on a length disagreement,
    ///   [`SealError::RemintingDiverged`] at the first differing serial.
    /// - panics: none.
    ///
    /// # Errors
    /// [`SealError::RemintingCountDiverged`],
    /// [`SealError::RemintingDiverged`].
    ///
    /// # Adequacy
    /// - hypothesis: L2 — a re-elaboration of one program verifies against its
    ///   own record; the L3 residues are the two divergences, each pinned by a
    ///   perturbed record.
    /// - witness: `seal::tests::re_minting_the_same_sites_verifies`
    /// - witness: `seal::tests::a_reordered_record_is_refused`
    /// - witness: `seal::tests::a_truncated_record_is_refused`
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            spec_clause_traversal,
            reason = "parity: the body compares the record with the minting order site by site once; the check compares them once more"
        )
    )]
    #[spec(ensures: |ret| match ret {
        | Ok(()) => recorded == self.order.as_slice(),
        | Err(SealError::RemintingCountDiverged { recorded: count, minted }) => count == recorded.len()
            && minted == self.order.len() && count != minted,
        | Err(SealError::RemintingDiverged { serial }) => recorded.len() == self.order.len()
            && recorded.iter().zip(&self.order).position(|(left, right)| left != right) == Some(usize::from(serial)),
        | Err(SealError::SiteAlreadyMinted { .. }) => false,
    })]
    #[inline]
    pub fn verify_reminting(
        &self,
        recorded: &[SealSite],
    ) -> Result<(), SealError>
    {
        if recorded.len() != self.order.len() {
            return Err(SealError::RemintingCountDiverged {
                recorded: recorded.len(),
                minted: self.order.len(),
            });
        }
        recorded
            .iter()
            .zip(&self.order)
            .position(|(left, right)| left != right)
            .map_or(Ok(()), |position| {
                Err(SealError::RemintingDiverged {
                    serial: SealSerial(position),
                })
            })
    }
}

#[cfg(test)]
mod tests
{
    use alloc::string::ToString as _;
    use alloc::vec::Vec;

    use quenchant_shape::shape::Maybe;

    use super::ComponentOrdinal;
    use super::SealError;
    use super::SealSerial;
    use super::SealSite;
    use super::SealTable;
    use super::SealingSite;
    use super::minted_site;

    /// The site sealing component `component` at ascription `sealing`.
    ///
    /// # Specification
    /// trivial.
    fn site(
        sealing: SealingSite,
        component: ComponentOrdinal,
    ) -> SealSite
    {
        SealSite::new(sealing, component)
    }

    /// A two-component sealing: one ascription sealing its first two
    /// components.
    ///
    /// # Specification
    /// trivial.
    fn counter_sites() -> [SealSite; 2]
    {
        [
            site(0_usize.into(), 0_usize.into()),
            site(0_usize.into(), 1_usize.into()),
        ]
    }

    #[test]
    fn minting_is_ordered_and_each_site_mints_once()
    {
        let mut table = SealTable::new();
        let [first_site, second_site] = counter_sites();
        let first = table.mint(first_site).unwrap();
        let second = table.mint(second_site).unwrap();
        assert_eq!(
            (SealSerial::from(0_usize), SealSerial::from(1_usize)),
            (first.serial(), second.serial()),
            "serials follow minting order from zero"
        );
        assert_ne!(first, second, "two components mint two distinct atoms");
        assert_eq!(
            [first_site, second_site].as_slice(),
            table.sites(),
            "the table records the minting order"
        );
        assert_eq!(
            (
                Maybe::Present(first),
                Maybe::Absent(minted_site::Absent::Unminted)
            ),
            (
                table.lookup(first_site),
                table.lookup(site(1_usize.into(), 0_usize.into()))
            ),
            "a minted site finds its atom and an unminted one finds none"
        );
    }

    /// Two sealings of one component are refused where they happen.
    #[test]
    fn a_repeated_site_is_refused()
    {
        let mut table = SealTable::new();
        let repeated = site(0_usize.into(), 0_usize.into());
        let _first = table.mint(repeated).unwrap();
        let refused = table.mint(repeated);
        assert_eq!(
            Err(SealError::SiteAlreadyMinted { site: repeated }),
            refused,
            "one component may be sealed once"
        );
        assert_eq!(
            1,
            table.sites().len(),
            "the refused mint left the table unchanged"
        );
        assert_eq!(
            "the sealing site at ascription 0 component 0 was already minted",
            refused.unwrap_err().to_string()
        );
    }

    /// Two ascriptions sealing a component at the same place mint distinct
    /// atoms: sealing is generative and declaration-granular.
    #[test]
    fn two_declarations_sealing_one_component_name_stay_distinct()
    {
        let mut table = SealTable::new();
        let first = table.mint(site(0_usize.into(), 0_usize.into())).unwrap();
        let second = table.mint(site(1_usize.into(), 0_usize.into())).unwrap();
        assert_ne!(
            first, second,
            "structurally identical sealings in two ascriptions do not interchange"
        );
    }

    /// Re-elaborating one program meets the same sites in the same order, so
    /// its record verifies.
    #[test]
    fn re_minting_the_same_sites_verifies()
    {
        let mut first_run = SealTable::new();
        let mut second_run = SealTable::new();
        for minted in counter_sites() {
            let _first = first_run.mint(minted).unwrap();
            let _second = second_run.mint(minted).unwrap();
        }
        let recorded: Vec<SealSite> = first_run.sites().to_vec();
        assert_eq!(
            Ok(()),
            second_run.verify_reminting(&recorded),
            "re-minting one program reproduces its recorded atoms"
        );
    }

    /// A record in another order is refused: the serial is the place, so the
    /// same sites in another order name other atoms.
    #[test]
    fn a_reordered_record_is_refused()
    {
        let [first, second] = counter_sites();
        let mut table = SealTable::new();
        let _one = table.mint(first).unwrap();
        let _two = table.mint(second).unwrap();
        let refused = table.verify_reminting(&[second, first]);
        assert_eq!(
            Err(SealError::RemintingDiverged {
                serial: SealSerial::from(0_usize),
            }),
            refused,
            "a reordered record names other atoms and is refused"
        );
        assert_eq!(
            "re-minting diverged from the recorded sealing at serial 0",
            refused.unwrap_err().to_string()
        );
    }

    /// A record missing an atom is refused, so no minted atom goes
    /// unrecorded.
    #[test]
    fn a_truncated_record_is_refused()
    {
        let [first, second] = counter_sites();
        let mut table = SealTable::new();
        let _one = table.mint(first).unwrap();
        let _two = table.mint(second).unwrap();
        let refused = table.verify_reminting(&[first]);
        assert_eq!(
            Err(SealError::RemintingCountDiverged {
                recorded: 1,
                minted: 2,
            }),
            refused,
            "a record short of the minting is refused"
        );
        assert_eq!(
            "re-minting produced 2 atoms where 1 were recorded",
            refused.unwrap_err().to_string()
        );
    }
}
