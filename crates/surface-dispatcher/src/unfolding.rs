//! Probe-only reports of global body reads during surface checking.

use alloc::collections::BTreeMap;
use alloc::string::String;
use alloc::vec::Vec;
use core::cell::RefCell;

use gandr_core_checker::CheckingContext;
use gandr_core_nbe::UnfoldingProbe;
use gandr_kernel_term::ConstantIndex;
use gandr_surface_lowering::LoweredModule;

std::thread_local! {
    static ACTIVE: RefCell<Vec<Vec<ObservedModule>>> = const { RefCell::new(Vec::new()) };
}

/// The distinct global-body pairs one subject reads.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
#[must_use]
pub struct UnfoldingPairs(usize);

/// The global-body read events one subject performs.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
#[must_use]
pub struct UnfoldingEvents(usize);

/// The global-body reads made while one subject is checked.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
#[must_use]
pub struct UnfoldingReport
{
    /// The fully qualified subject name.
    subject: String,
    /// The subject's distinct body pairs.
    pairs: UnfoldingPairs,
    /// The subject's body-read events.
    events: UnfoldingEvents,
}

/// The output and reports of one observed operation.
#[derive(Debug)]
#[must_use]
pub struct UnfoldingObservation<Output>
{
    /// The operation output.
    output: Output,
    /// The body-read reports.
    reports: Vec<UnfoldingReport>,
}

/// The names and body-read probe of one lowered module.
#[derive(Debug)]
struct ObservedModule
{
    /// The names of declarations in the lowered module.
    names: BTreeMap<ConstantIndex, String>,
    /// The module's body-read probe.
    probe: UnfoldingProbe,
}

/// The counts collected for one subject.
#[derive(Default)]
struct SubjectTotals
{
    /// The subject and global pairs.
    pairs: usize,
    /// The total body-read events.
    events: usize,
}

/// Removes one active observation when its operation unwinds.
struct ObservationGuard
{
    /// Whether the observer already returned its reports.
    closed: bool,
}

impl ObservationGuard
{
    /// Start an empty observation on this thread.
    ///
    /// # Specification
    /// trivial.
    fn open() -> Self
    {
        ACTIVE.with(|active| active.borrow_mut().push(Vec::new()));
        Self { closed: false }
    }

    /// Return this observation's modules.
    ///
    /// # Specification
    /// trivial.
    fn close(&mut self) -> Vec<ObservedModule>
    {
        self.closed = true;
        ACTIVE.with(|active| active.borrow_mut().pop().unwrap_or_default())
    }
}

impl Drop for ObservationGuard
{
    fn drop(&mut self)
    {
        if !self.closed {
            ACTIVE.with(|active| {
                let _observed = active.borrow_mut().pop();
            });
        }
    }
}

impl From<UnfoldingPairs> for usize
{
    /// The pair count as a machine word.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(count: UnfoldingPairs) -> Self
    {
        count.0
    }
}

impl From<UnfoldingEvents> for usize
{
    /// The event count as a machine word.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(count: UnfoldingEvents) -> Self
    {
        count.0
    }
}

impl UnfoldingReport
{
    /// The fully qualified subject name.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn subject(&self) -> &str
    {
        self.subject.as_str()
    }

    /// The distinct global-body pairs the subject reads.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub const fn pairs(&self) -> UnfoldingPairs
    {
        self.pairs
    }

    /// The global-body read events the subject performs.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub const fn events(&self) -> UnfoldingEvents
    {
        self.events
    }
}

impl<Output> UnfoldingObservation<Output>
{
    /// The observed operation's output.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn output(&self) -> &Output
    {
        &self.output
    }

    /// The reports ordered by subject name.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn reports(&self) -> &[UnfoldingReport]
    {
        self.reports.as_slice()
    }

    /// Split the observed operation's output from its reports.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn into_parts(self) -> (Output, Vec<UnfoldingReport>)
    {
        (self.output, self.reports)
    }
}

/// Observe the global-body reads made by `run`.
///
/// # Specification
/// trivial.
#[inline]
pub fn observe_unfoldings<Output, Run>(run: Run) -> UnfoldingObservation<Output>
where
    Run: FnOnce() -> Output,
{
    let mut guard = ObservationGuard::open();
    let output = run();
    let observed = guard.close();
    let reports = summarize(observed);
    UnfoldingObservation { output, reports }
}

/// Attach a fresh module probe to `context` during an observation, which
/// reports each read by the module's `names`.
///
/// # Specification
/// trivial.
pub fn attach(
    context: &mut CheckingContext<'_>,
    names: &BTreeMap<ConstantIndex, String>,
)
{
    ACTIVE.with(|active| {
        let mut active = active.borrow_mut();
        let Some(observed) = active.last_mut()
        else {
            return;
        };
        let probe = UnfoldingProbe::new();
        context.observe_unfoldings(probe.clone());
        observed.push(ObservedModule {
            names: names.clone(),
            probe,
        });
    });
}

/// Copy the declaration names from `module`.
///
/// # Specification
/// trivial.
pub fn names(module: &LoweredModule<'_>) -> BTreeMap<ConstantIndex, String>
{
    let mut names: BTreeMap<ConstantIndex, String> = module
        .structured_names()
        .into_iter()
        .map(|(constant, name)| (constant, spell(&name)))
        .collect();
    for declaration in module.declarations() {
        let mut name = String::new();
        for (index, segment) in module.path_of(declaration).into_iter().enumerate() {
            if index > 0_usize {
                name.push('.');
            }
            name.push_str(segment.as_ref());
        }
        if !name.is_empty() {
            let _replaced = names.insert(declaration.constant(), name);
        }
    }
    names
}

/// Spell one structured declaration name.
///
/// # Specification
/// trivial.
fn spell(name: &gandr_kernel_term::StructuredName) -> String
{
    let mut text = String::new();
    for (index, segment) in name.segments().iter().enumerate() {
        if index > 0_usize {
            text.push('.');
        }
        text.push_str(segment.as_ref());
    }
    text
}

/// Summarize the pairs and events for each observed subject.
///
/// # Specification
/// trivial.
fn summarize(observed: Vec<ObservedModule>) -> Vec<UnfoldingReport>
{
    let mut totals = BTreeMap::<String, SubjectTotals>::new();
    for observed in observed {
        for record in observed.probe.records() {
            let subject = observed
                .names
                .get(&record.subject())
                .cloned()
                .unwrap_or_else(|| format!("{:?}", record.subject()));
            let total = totals.entry(subject).or_default();
            total.pairs = total.pairs.saturating_add(1_usize);
            total.events = total.events.saturating_add(usize::from(record.events()));
        }
    }
    totals
        .into_iter()
        .map(|(subject, total)| UnfoldingReport {
            subject,
            pairs: UnfoldingPairs(total.pairs),
            events: UnfoldingEvents(total.events),
        })
        .collect()
}
