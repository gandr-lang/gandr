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
