//! The `run` statements the sugared form writes away, as the source's lowering
//! lists them.
//!
//! A `run x <- c ;` whose binder the next step reads once, as the first thing
//! that step runs or reads, only sequences the call `c`: written at the read,
//! the checker runs `c` there, at the same point. Which statements stand so is
//! the lowering's to say (`gandr_surface_lowering::LinearRun`); this module
//! carries their spans into the formatted source. The two spellings lower to
//! different cores — a bind, and a nested call the checker elaborates to that
//! bind — so a source rewritten this way is checked by the bodies the checker
//! elaborates ([`crate::Elaborate`]). Without a checker no statement is written
//! away, nor in a declaration the checker refuses as written: there is no
//! elaboration to compare, and the declaration keeps its other rewrites.

use alloc::vec::Vec;

use gandr_surface_lowering::LoweredModule;
use gandr_surface_syntax::ByteOffset;
use gandr_surface_syntax::ByteSpan;

use crate::composite::within;

/// The `run` statements the sugared form writes away: each one's call and the
/// read the call is written at.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Runs
{
    /// The calls' spans, in the source's own offsets, sorted.
    bound: Vec<ByteSpan>,
    /// Each read's span beside its call's, sorted by the read.
    reads: Vec<(ByteSpan, ByteSpan)>,
}

impl Runs
{
    /// The linear runs `module` lists outside `unchecked` — the spans, in the
    /// source's own offsets, of the top-level forms holding a declaration the
    /// checker elaborates no body for — of which the formatted source starts
    /// at `base` in the unit's text.
    ///
    /// # Specification
    /// trivial.
    pub fn of(
        module: &LoweredModule<'_>,
        base: ByteOffset,
        mut unchecked: Vec<ByteSpan>,
    ) -> Self
    {
        // Top-level forms are disjoint, so the last to start at or before a
        // call is the only one that may hold it.
        unchecked.sort_unstable();
        let mut bound = Vec::new();
        let mut reads = Vec::new();
        for run in module.linear_runs() {
            let (Some(call), Some(read)) = (within(run.bound, base), within(run.read, base))
            else {
                continue;
            };
            let opened = unchecked.partition_point(|span| span.start() <= call.start());
            let held = opened
                .checked_sub(1)
                .and_then(|last| unchecked.get(last))
                .is_some_and(|&form| form.start() <= call.start() && call.end() <= form.end());
            if !held {
                bound.push(call);
                reads.push((read, call));
            }
        }
        bound.sort_unstable();
        reads.sort_unstable();
        Self { bound, reads }
    }

    /// The calls of the statements written away, in the source's own
    /// offsets, sorted.
    ///
    /// # Specification
    /// trivial.
    pub fn calls(&self) -> &[ByteSpan]
    {
        &self.bound
    }

    /// The span of the call written at the read spanning exactly `span`.
    ///
    /// # Specification
    /// trivial.
    pub fn read(
        &self,
        span: ByteSpan,
    ) -> Option<ByteSpan>
    {
        self.reads
            .binary_search_by_key(&span, |&(read, _)| read)
            .ok()
            .and_then(|at| self.reads.get(at))
            .map(|&(_, call)| call)
    }
}
