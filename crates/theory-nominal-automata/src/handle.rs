//! Register stores, symbolic transfers, and their shared validation.

use alloc::collections::BTreeSet;
use alloc::vec::Vec;

use anodized::spec;
use quenchant_shape::shape::Maybe;

/// An index into the control table.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Control(usize);

impl Control
{
    /// The zero value.
    pub const ZERO: Self = Self(0);
}

impl From<usize> for Control
{
    /// Wrap a machine-sized count or index without truncation.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: usize) -> Self
    {
        Self(value)
    }
}

impl From<Control> for usize
{
    /// Unwrap the count or index.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: Control) -> Self
    {
        value.0
    }
}

/// An index into a register store.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Register(usize);

impl Register
{
    /// The zero value.
    pub const ZERO: Self = Self(0);
}

impl From<usize> for Register
{
    /// Wrap a machine-sized count or index without truncation.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: usize) -> Self
    {
        Self(value)
    }
}

impl From<Register> for usize
{
    /// Unwrap the count or index.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: Register) -> Self
    {
        value.0
    }
}

/// The number of registers at a control point.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Arity(usize);

impl Arity
{
    /// The zero value.
    pub const ZERO: Self = Self(0);
}

impl From<usize> for Arity
{
    /// Wrap a machine-sized count or index without truncation.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: usize) -> Self
    {
        Self(value)
    }
}

impl From<Arity> for usize
{
    /// Unwrap the count or index.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: Arity) -> Self
    {
        value.0
    }
}

/// The number of control points.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Controls(usize);

impl Controls
{
    /// The zero value.
    pub const ZERO: Self = Self(0);
}

impl From<usize> for Controls
{
    /// Wrap a machine-sized count or index without truncation.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: usize) -> Self
    {
        Self(value)
    }
}

impl From<Controls> for usize
{
    /// Unwrap the count or index.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: Controls) -> Self
    {
        value.0
    }
}

/// The maximum register arity of an automaton.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Degree(usize);

impl Degree
{
    /// The zero value.
    pub const ZERO: Self = Self(0);
}

impl From<usize> for Degree
{
    /// Wrap a machine-sized count or index without truncation.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: usize) -> Self
    {
        Self(value)
    }
}

impl From<Degree> for usize
{
    /// Unwrap the count or index.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: Degree) -> Self
    {
        value.0
    }
}

/// Why a register lookup has no name.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum RegisterAbsent
{
    /// The register exists but holds no name.
    Empty,
    /// The register is outside the store.
    OutOfRange,
}

/// An empty slot in a partial store.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum EmptyRegister
{
    /// No name occupies this slot.
    Empty,
}

/// A partial injective assignment of caller-owned names to registers.
///
/// # Specification
/// - ensures: occupied registers hold pairwise distinct names.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 duplicate rejection and exact partial lookup distinguish
///   loss of injectivity and confusion between empty and missing registers.
/// - witness: `tests::handle::duplicate_assignment_is_rejected`
/// - witness: `tests::handle::injective_partial_store_is_accepted`
#[repr(transparent)]
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Store<A>
{
    /// Internal slots; absence is exposed with a site-specific reason.
    slots: Vec<Option<A>>,
}

/// A duplicate name prevented store construction.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct StoreError<A>
{
    /// The name assigned to more than one register.
    pub atom: A,
}

impl<A: core::fmt::Debug> core::fmt::Display for StoreError<A>
{
    /// Describe a duplicate assignment without rendering a caller's name.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result
    {
        f.write_str("register store assigns one name twice")
    }
}
impl<A: core::fmt::Debug> core::error::Error for StoreError<A>
{
}

impl<A: Copy + Ord> Store<A>
{
    /// Validate an explicit partial assignment.
    ///
    /// # Specification
    /// - ensures: success preserves slot order and rejects repeated occupied
    ///   names.
    /// - fails: returns the duplicated name in `StoreError`.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns `StoreError` if any name occurs twice.
    ///
    /// # Adequacy
    /// - hypothesis: L3 an occupied duplicate separated by an empty slot is
    ///   rejected, while distinct names and empty slots preserve their
    ///   positions.
    /// - witness: `tests::handle::duplicate_assignment_is_rejected`
    /// - witness: `tests::handle::injective_partial_store_is_accepted`
    #[inline]
    #[spec(ensures: |ref result| result.as_ref().map_or(true, |store| store.slots.iter().flatten().collect::<BTreeSet<_>>().len() == store.slots.iter().flatten().count()))]
    pub fn try_new(slots: Vec<Maybe<A, EmptyRegister>>) -> Result<Self, StoreError<A>>
    {
        let mut seen = BTreeSet::new();
        let mut values = Vec::with_capacity(slots.len());
        for slot in slots {
            match slot {
                | Maybe::Present(atom) => {
                    if !seen.insert(atom) {
                        return Err(StoreError { atom });
                    }
                    values.push(Some(atom));
                },
                | Maybe::Absent(EmptyRegister::Empty) => values.push(None),
            }
        }
        Ok(Self { slots: values })
    }

    /// Build a store containing only empty registers.
    ///
    /// # Specification
    /// - ensures: exactly `arity` registers exist and every register is empty.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 empty-store reads distinguish empty slots from names
    ///   and from the first out-of-range register.
    /// - witness: `tests::handle::empty_store_has_only_empty_registers`
    #[inline]
    #[must_use]
    #[spec(ensures: |ref result| result.slots.len() == arity.0 && result.slots.iter().all(Option::is_none))]
    pub fn empty(arity: Arity) -> Self
    {
        Self {
            slots: alloc::vec![None; arity.0],
        }
    }

    /// The store's register count.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn arity(&self) -> Arity
    {
        Arity(self.slots.len())
    }

    /// Read a name, distinguishing an empty register from an unknown one.
    ///
    /// # Specification
    /// - provides: the occupied name, or `RegisterAbsent::Empty` for an
    ///   existing vacancy, or `RegisterAbsent::OutOfRange` beyond the store.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 occupied, empty and boundary reads select distinct
    ///   results.
    /// - witness: `tests::handle::injective_partial_store_is_accepted`
    #[inline]
    #[spec(ensures: |result| match result {
        Maybe::Present(atom) => self.slots.get(register.0) == Some(&Some(atom)),
        Maybe::Absent(RegisterAbsent::Empty) => self.slots.get(register.0) == Some(&None),
        Maybe::Absent(RegisterAbsent::OutOfRange) => register.0 >= self.slots.len(),
    })]
    pub fn name(
        &self,
        register: Register,
    ) -> Maybe<A, RegisterAbsent>
    {
        match self.slots.get(register.0).copied() {
            | Some(Some(atom)) => Maybe::Present(atom),
            | Some(None) => Maybe::Absent(RegisterAbsent::Empty),
            | None => Maybe::Absent(RegisterAbsent::OutOfRange),
        }
    }

    /// Test whether a name is absent from every register.
    ///
    /// # Specification
    /// - ensures: freshness holds exactly when no register contains `atom`.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 occupied and absent names separate both freshness
    ///   answers.
    /// - witness: `tests::handle::injective_partial_store_is_accepted`
    #[inline]
    #[must_use]
    #[spec(ensures: |result| (result == Freshness::Fresh) != self.slots.contains(&Some(atom)))]
    pub fn freshness(
        &self,
        atom: A,
    ) -> Freshness
    {
        if self.slots.contains(&Some(atom)) {
            Freshness::Remembered
        }
        else {
            Freshness::Fresh
        }
    }

    /// Apply an already-validated injective transfer.
    ///
    /// # Specification
    /// - requires: retained registers are in range and pairwise distinct; an
    ///   allocated name, if present, is fresh and used at most once.
    /// - ensures: each target slot follows its transfer entry.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 the lifecycle and dropping witnesses distinguish
    ///   retention, allocation and erasure through accepted words.
    /// - witness: `tests::nda::session_monitor_accepts_drained_log`
    /// - witness: `tests::dropping::name_dropping_closes_language_under_alpha`
    #[spec(ensures: |ref result| result.slots.len() == transfer.len())]
    pub(crate) fn transfer(
        &self,
        transfer: &[Transfer],
        allocated: Maybe<A, EmptyRegister>,
    ) -> Self
    {
        let allocated = match allocated {
            | Maybe::Present(atom) => Some(atom),
            | Maybe::Absent(EmptyRegister::Empty) => None,
        };
        let slots = transfer
            .iter()
            .map(|entry| match *entry {
                | Transfer::Keep(register) => self.slots.get(register.0).copied().flatten(),
                | Transfer::Allocated => allocated,
                | Transfer::Empty => None,
            })
            .collect();
        Self { slots }
    }
}

/// A name's membership in a store's support.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Freshness
{
    /// No register holds the name.
    Fresh,
    /// A register already holds the name.
    Remembered,
}

/// The result of literal word membership.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Membership
{
    /// At least one run ends at a final control.
    Accepted,
    /// No run ends at a final control.
    Rejected,
}

/// A control point paired with its register assignment.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Configuration<A>
{
    /// The control point.
    control: Control,
    /// Its partial injective assignment.
    store: Store<A>,
}
impl<A> Configuration<A>
{
    /// Pair a control with a store; automaton construction validates its arity.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn new(
        control: Control,
        store: Store<A>,
    ) -> Self
    {
        Self { control, store }
    }
    /// The control point.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn control(&self) -> Control
    {
        self.control
    }
    /// The register assignment.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn store(&self) -> &Store<A>
    {
        &self.store
    }
}

/// The source of a target register's value.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Transfer
{
    /// Retain a source register, including its vacancy.
    Keep(Register),
    /// Store the freshly allocated name.
    Allocated,
    /// Leave the target register empty.
    Empty,
}

/// A structural error in an automaton handle.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum AutomatonError
{
    /// A referenced control is absent from the table.
    InvalidControl
    {
        /// The referenced control.
        control: Control,
        /// The size of the table.
        controls: Controls,
    },
    /// Store or transfer length differs from the control's arity.
    ArityMismatch
    {
        /// The target control.
        control: Control,
        /// Its declared arity.
        expected: Arity,
        /// The supplied length.
        actual: Arity,
    },
    /// A read or transfer names an unknown register.
    UnknownRegister
    {
        /// The source control.
        control: Control,
        /// The invalid register.
        register: Register,
    },
    /// A transfer repeats a source register and can violate injectivity.
    RepeatedRegister
    {
        /// The source control.
        control: Control,
        /// The repeated register.
        register: Register,
    },
    /// An allocation appears in a non-allocating rule or more than once.
    MisplacedAllocatedName
    {
        /// The source control.
        control: Control,
    },
    /// A close or drop rule retains the name it erases.
    KeptDeallocatedName
    {
        /// The source control.
        control: Control,
        /// The retained register.
        register: Register,
    },
}
impl core::fmt::Display for AutomatonError
{
    /// Render the violated structural invariant.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result
    {
        match *self {
            | Self::InvalidControl { control, controls } => write!(
                f,
                "control {} is outside {} controls",
                control.0, controls.0
            ),
            | Self::ArityMismatch {
                control,
                expected,
                actual,
            } => write!(
                f,
                "control {} requires {} registers, received {}",
                control.0, expected.0, actual.0
            ),
            | Self::UnknownRegister { control, register } => {
                write!(f, "control {} has no register {}", control.0, register.0)
            },
            | Self::RepeatedRegister { control, register } => {
                write!(f, "control {} repeats register {}", control.0, register.0)
            },
            | Self::MisplacedAllocatedName { control } => {
                write!(f, "control {} misplaces an allocated name", control.0)
            },
            | Self::KeptDeallocatedName { control, register } => write!(
                f,
                "control {} keeps erased register {}",
                control.0, register.0
            ),
        }
    }
}
impl core::error::Error for AutomatonError
{
}

/// Look up a control's declared arity.
///
/// # Specification
/// - ensures: success returns the control's table entry.
/// - fails: unknown controls report their index and the table size.
/// - panics: none.
///
/// # Errors
/// Returns `AutomatonError::InvalidControl` outside the table.
///
/// # Adequacy
/// - hypothesis: L3 unknown source, target, initial and final controls are
///   refused.
/// - witness: `tests::nda::construction_rejects_invalid_control`
#[spec(ensures: |result| result.map_or(control.0 >= arities.len(), |arity| arities.get(control.0) == Some(&arity)))]
pub(crate) fn arity_at(
    arities: &[Arity],
    control: Control,
) -> Result<Arity, AutomatonError>
{
    arities
        .get(control.0)
        .copied()
        .ok_or(AutomatonError::InvalidControl {
            control,
            controls: Controls(arities.len()),
        })
}

/// Validate the initial configuration against the control table.
///
/// # Specification
/// - ensures: success means the initial control exists and its store fits.
/// - fails: invalid control or mismatching arity.
/// - panics: none.
///
/// # Errors
/// Returns `InvalidControl` or `ArityMismatch` from `AutomatonError`.
///
/// # Adequacy
/// - hypothesis: L3 the initial store's boundary arity distinguishes rejection.
/// - witness: `tests::nda::construction_rejects_arity_mismatch`
#[spec(ensures: |ref result| result.is_err() || arities.get(initial.control.0) == Some(&initial.store.arity()))]
pub(crate) fn validate_initial<A>(
    arities: &[Arity],
    initial: &Configuration<A>,
) -> Result<(), AutomatonError>
where
    A: Copy + Ord,
{
    let expected = arity_at(arities, initial.control)?;
    let actual = initial.store.arity();
    if expected != actual {
        return Err(AutomatonError::ArityMismatch {
            control: initial.control,
            expected,
            actual,
        });
    }
    Ok(())
}

/// Whether a rule supplies a newly allocated name.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum Allocation
{
    /// Allocation is permitted.
    Allowed,
    /// No name is allocated.
    Forbidden,
}

/// Validate one target's injective transfer from a source control.
///
/// # Specification
/// - ensures: success means all retained registers exist and are distinct,
///   allocation is permitted at most once, and target arity matches.
/// - fails: invalid control, arity, register, repetition or allocation.
/// - panics: none.
///
/// # Errors
/// Returns the corresponding `AutomatonError` with source or target evidence.
///
/// # Adequacy
/// - hypothesis: L3 boundary reads, duplicate retention and allocation
///   placement distinguish violations of the partial-injection invariant.
/// - witness: `tests::validation::transfers_preserve_partial_injections`
#[spec(ensures: |ref result| result.is_err() || arities.get(target.0) == Some(&Arity(transfer.len())))]
pub(crate) fn validate_transfer(
    arities: &[Arity],
    source: Control,
    target: Control,
    transfer: &[Transfer],
    allocation: Allocation,
) -> Result<(), AutomatonError>
{
    let source_arity = arity_at(arities, source)?;
    let expected = arity_at(arities, target)?;
    let actual = Arity(transfer.len());
    if expected != actual {
        return Err(AutomatonError::ArityMismatch {
            control: target,
            expected,
            actual,
        });
    }
    let mut seen = BTreeSet::new();
    let mut allocated = false;
    for entry in transfer {
        match *entry {
            | Transfer::Keep(register) => {
                if register.0 >= source_arity.0 {
                    return Err(AutomatonError::UnknownRegister {
                        control: source,
                        register,
                    });
                }
                if !seen.insert(register) {
                    return Err(AutomatonError::RepeatedRegister {
                        control: source,
                        register,
                    });
                }
            },
            | Transfer::Allocated => {
                if allocation == Allocation::Forbidden || allocated {
                    return Err(AutomatonError::MisplacedAllocatedName { control: source });
                }
                allocated = true;
            },
            | Transfer::Empty => {},
        }
    }
    Ok(())
}
