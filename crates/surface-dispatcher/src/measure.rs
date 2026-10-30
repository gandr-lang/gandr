//! Each declaration a settled source writes, measured in the kernel artifact
//! its component's admission exported, and in the tally of that admission.
//!
//! # A row is a segment of the kernel's artifact
//!
//! The kernel exports one artifact per component: its declarations in
//! admission order, each a segment over one maximally shared subterm table.
//! A row reads three sizes off that artifact for one declaration the source
//! writes: its segment's bytes, the table entries its segment adds and the
//! expanded work of its roots. The entries are its shared size, a subterm an
//! earlier segment holds counted there. The expanded work is its unshared
//! size, the tree its roots stand for. A reference to an earlier declaration
//! is one node, so a row measures the declaration as written over the
//! definitions it names, never unfolded.
//!
//! A row also reads what the admission tallied: the census the kernel's check
//! charged, goal by goal, and the time the kernel took to admit it. The census
//! counts each goal the check expanded, each its memo recalled and each an
//! earlier admission's kept outcome answered. A declaration a recorded verdict
//! admitted ran no check, and its row says so rather than counting nothing. A
//! resumed declaration carries the tally of the run that admitted it.
//!
//! # Measuring reads and never checks
//!
//! [`measure`] decodes the artifact the admission already exported and
//! changes no verdict. It reads each declaration at the position its
//! admission recorded, which only a walk asked to measure records
//! ([`crate::Walk::measuring`]), so a check that measures nothing records,
//! times and decodes nothing more.
//!
//! # References
//!
//! - `vault:01a18572-6e13-7412-bc74-aa6a24d157c4` — background: Example 1.4 and
//!   § 6 give the artifact sizes in bytes that a row's bytes stand beside.
//! - `vault:01a178aa-655f-72f2-97ee-298c0647e1e5` — background: the sharing
//!   ratio of iterated composites grows with dimension, which a row's shared
//!   and unshared sizes measure.
//! - `vault:01a051fd-25fd-7f24-a5d4-a72eca18a687` — lineage: the sharing
//!   format's one table per artifact and its expanded-work budget, the shared
//!   and unshared sizes a row reads.

use anodized::spec;
use gandr_core_checker::bridge::AdmissionTime;
use gandr_kernel_core::ExpansionCensus;
use gandr_kernel_core::tallied;
use gandr_kernel_term::ByteCount;
use gandr_kernel_term::DecodeError;
use gandr_kernel_term::ExpandedWork;
use gandr_kernel_term::TableEntryCount;
use gandr_kernel_term::decode_measured;
use gandr_surface_lowering::SurfaceName;
use quenchant_shape::shape::Maybe;

use crate::compose::Composed;

/// One declaration a source writes, measured in its component's kernel
/// artifact and in its admission's tally.
///
/// # Specification
/// - requires: built by [`measure`].
/// - ensures: the declaration's name, its segment's bytes, the table entries
///   its segment adds, the expanded work of its roots, the census its check
///   charged and the time its admission took.
/// - panics: none.
/// - executable: none — the fields are private and set only by [`measure`],
///   whose specification states them.
///
/// # Adequacy
/// - hypothesis: L2 — as [`measure`]'s.
/// - witness: `tests::measure::a_source_measures_the_declarations_it_writes_and_none_it_imports`
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Measure<'source>
{
    /// The declaration's name, as the source spells it.
    name: SurfaceName<'source>,
    /// The bytes its segment takes.
    bytes: ByteCount,
    /// The table entries its segment adds: its shared size.
    shared: TableEntryCount,
    /// The expanded work of its roots: its unshared size.
    unshared: ExpandedWork,
    /// What the kernel's check of it charged, goal by goal, or why no check
    /// was tallied.
    census: Maybe<ExpansionCensus, tallied::Absent>,
    /// How long the kernel took to admit it, or why no time was read.
    took: AdmissionTime,
}

impl<'source> Measure<'source>
{
    /// The declaration's name, as the source spells it.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn name(&self) -> SurfaceName<'source>
    {
        self.name
    }

    /// The bytes the declaration's segment takes in the kernel's artifact.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn bytes(&self) -> ByteCount
    {
        self.bytes
    }

    /// The table entries the declaration's segment adds: its shared size.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn shared(&self) -> TableEntryCount
    {
        self.shared
    }

    /// The expanded work of the declaration's roots: its unshared size.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn unshared(&self) -> ExpandedWork
    {
        self.unshared
    }

    /// What the kernel's check of the declaration charged: each goal it
    /// expanded, each its memo recalled and each an earlier admission's kept
    /// outcome answered. A declaration a recorded verdict admitted ran no
    /// check here.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub const fn census(&self) -> Maybe<ExpansionCensus, tallied::Absent>
    {
        self.census
    }

    /// How long the kernel took to admit the declaration, or why no time was
    /// read.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub const fn took(&self) -> AdmissionTime
    {
        self.took
    }
}

quenchant_shape::reason_enum! {
    /// Why a composition has no rows to measure.
    pub mod measured {
        /// The reason none is measured.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The lowering refused the source as a whole, so it declares
            /// nothing.
            Refused,
            /// The module's admission has not run, so no artifact exists.
            Pending,
            /// The admission recorded no artifact positions: the walk was
            /// not asked to measure.
            Unpositioned,
        }
    }
}

/// Measure each declaration `composed` writes in its component's kernel
/// artifact.
///
/// # Specification
/// - requires: nothing.
/// - ensures: absent as [`measured::Absent::Refused`] for a source refused as a
///   whole, as [`measured::Absent::Pending`] before its admission ran, and as
///   [`measured::Absent::Unpositioned`] when its admission recorded no
///   positions. Otherwise one row per declaration the source's report names
///   that crossed into the kernel, in the report's order, read at the artifact
///   position the admission gave it: its name, its segment's bytes, the table
///   entries its segment adds, the expanded work of its roots, the census the
///   kernel's check of it charged and the time its admission took. No row names
///   a declaration of the source's import closure.
/// - provides: the sizes and the tally `gandr check --measure` prints for each
///   declaration.
/// - fails: [`DecodeError`] when the exported artifact does not decode, which
///   the kernel's own export never meets.
/// - panics: none.
///
/// # Errors
/// [`DecodeError`] from [`decode_measured`].
///
/// # Adequacy
/// - hypothesis: L2 — over `library/math`, whose `math.cylinder` imports
///   `math.path` and the prelude, each source's rows are the declarations it
///   writes, in order, and none its closure holds. Each row reads the segment
///   of the artifact's declaration of its name, which a row read at its module
///   position does not. A shared size never passes its unshared size, which
///   separates the two columns swapped. Each row's census charges at least one
///   goal and its admission is timed, which a row read from an untimed or
///   unchecked admission is not. A walk not asked to measure answers that it
///   recorded no positions, rather than no rows.
/// - witness: `tests::measure::a_source_measures_the_declarations_it_writes_and_none_it_imports`
#[inline]
#[spec(ensures: |ret| match (composed, ret.as_ref()) {
    (&Composed::Settled { ref report, .. }, Ok(&Maybe::Present(ref rows))) => rows.len() <= report.declarations().len(),
    (&Composed::Refused(_), Ok(&Maybe::Absent(measured::Absent::Refused)))
    | (&Composed::Settled { .. }, Ok(&Maybe::Absent(measured::Absent::Pending | measured::Absent::Unpositioned)) | Err(_)) => true,
    _ => false,
})]
pub fn measure<'source>(
    composed: &Composed<'source>
) -> Result<Maybe<Vec<Measure<'source>>, measured::Absent>, DecodeError>
{
    let Composed::Settled {
        ref report,
        ref kernel,
        ref positions,
        ..
    } = *composed
    else {
        return Ok(Maybe::Absent(measured::Absent::Refused));
    };
    let Maybe::Present(ref kernel) = *kernel
    else {
        return Ok(Maybe::Absent(measured::Absent::Pending));
    };
    let Maybe::Present(ref positions) = *positions
    else {
        return Ok(Maybe::Absent(measured::Absent::Unpositioned));
    };
    let (artifact, measures) = decode_measured(kernel.as_image())?;
    let layout = artifact.segments();
    let rows = report
        .declarations()
        .iter()
        .filter_map(|declaration| {
            let Maybe::Present(placed) = positions.placed(declaration.constant())
            else {
                return None;
            };
            let position = placed.position();
            let measure = measures.get(usize::from(position))?;
            let span = layout.declaration_segment(position)?;
            Some(Measure {
                name: declaration.name(),
                bytes: ByteCount::from(
                    usize::from(span.end).saturating_sub(usize::from(span.start)),
                ),
                shared: measure.entries(),
                unshared: measure.expanded_work(),
                census: placed.census(),
                took: placed.took(),
            })
        })
        .collect();
    Ok(Maybe::Present(rows))
}
