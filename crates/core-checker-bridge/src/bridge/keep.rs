//! A readmission that keeps each entry an edit leaves. The declarations of
//! the edited source are matched in order to the declarations of a record by
//! their content keys. The readmission retires the reach of each declaration
//! that the match leaves out. Each other entry takes the rank of its place in
//! the edited source, and the walk keeps it in place at its own key.
//!
//! The reach holds more than the kernel's reverse index gives. A decode or an
//! instance of a definition crosses as the definition's body, so the entry of
//! its reader holds that body and names no kernel position for it. The
//! certificates of the reader record the unfolding, and each declaration
//! that unfolds an edited one is edited too.
//!
//! A seed is an entry that the bridge admits for the first declaration that
//! reads it: a native signature, a free model or an assumption. It stands just
//! below that reader. A seed whose first reader the readmission does not keep
//! retires with each entry that reads it, and the crossing of its first reader
//! in the edited source seeds it again.
//!
//! # References
//!
//! - `vault:01a178aa-6917-7983-b5cd-86e2af86b3ec` — anchor: a kept entry stands
//!   by its own key, computed again in place, and the rank, not the position,
//!   gives precedence.

use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use alloc::collections::VecDeque;
use alloc::vec::Vec;

use anodized::spec;
use gandr_kernel_check_memo::ContentDigest;
use gandr_kernel_core::CheckedId;
use gandr_kernel_core::Environment;
use gandr_kernel_core::KeptKeys;
use gandr_kernel_core::KernelError;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::SourceRank;
use quenchant_shape::shape::Maybe;

use super::CodeDefinitions;
use super::Crossed;
use super::DeclarationKey;
use super::Outcome;
use super::Positions;
use super::Readmitted;
use super::Replayed;
use super::timed;
use crate::code::Unfolded;
use crate::report::Judged;
use crate::report::ModuleReport;
use crate::report::Verdict;

/// How far apart the ranks of two neighbouring places of the edited source
/// stand. The seeds and the members a declaration admits take the ranks
/// from its place's on, so a crossing fits between two kept entries.
pub(super) const STRIDE: usize = 1 << 20_u32;

/// Where in the ranks of its place a crossing starts: past the kept seeds
/// of the place, so that a crossing after a refused keep reads them below
/// itself, as a fresh admission reads a seed its first reader admitted.
pub(super) const CROSSING: usize = STRIDE >> 1_u32;

/// The most places that one run of kept units holds ([`run_firsts`]).
const RUN: usize = 4096;

quenchant_shape::reason_enum! {
    /// Why a readmission keeps nothing of a record and crosses each
    /// declaration.
    pub(super) mod keeping {
        /// The reason nothing is kept.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The record or the report has no content key for each of its
            /// declarations.
            Unkeyed,
            /// The record holds the witnesses of a formation, whose readers
            /// find them by content and not by position.
            Formed,
            /// The report seals an abstract type, whose scope the walk
            /// closes as it crosses.
            Sealed,
            /// The kernel refused to retire the reach or to rewrite the
            /// ranks.
            Unranked,
        }
    }
}

quenchant_shape::reason_enum! {
    /// Why an outcome holds no kernel entry.
    pub(super) mod entry {
        /// The reason no entry is held.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The kernel admitted nothing for the declaration: it is
            /// static, or it was marked, suspended, refused or rejected.
            Unadmitted,
            /// The places keep no whole mutual block of the record: a place
            /// keeps nothing, or keeps an entry that the block did not admit
            /// at the next position.
            Unwhole,
        }
    }
}

/// Whether a verdict is of the kind a record's outcome crossed under.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Agreement
{
    /// The kinds agree: the outcome may be kept for the verdict.
    Agrees,
    /// The kinds differ: the declaration crosses again.
    Differs,
}

/// What a readmission keeps of a record: the environment with the reach of
/// the edit retired and each other entry at the rank of its place in the
/// edited source, the positions with each retired seed taken out, and the
/// record's entry that each place keeps.
#[derive(Debug)]
pub(super) struct Kept<'record>
{
    /// The record's environment, the reach retired and the rest reranked.
    pub environment: Environment,
    /// The record's positions, with no module position, no core body and no
    /// retired seed.
    pub positions: Positions,
    /// The record's entry each place of the edited source keeps, by place;
    /// none for a place the walk crosses.
    pub held: Vec<Option<&'record Readmitted>>,
    /// The module position in the edited source of each record declaration
    /// the readmission keeps, by its module position in the record.
    pub renames: BTreeMap<ConstantIndex, ConstantIndex>,
}

/// The kernel position an outcome took, when the kernel admitted it.
///
/// # Specification
/// trivial.
pub(super) const fn position_of(outcome: &Outcome) -> Maybe<ConstantIndex, entry::Absent>
{
    match *outcome {
        Outcome::Defined { admitted, .. }
        | Outcome::Data { admitted, .. }
        | Outcome::Assumed { admitted, .. } => Maybe::Present(admitted.position()),
        Outcome::Marked(_)
        | Outcome::Suspended
        | Outcome::Static
        | Outcome::Refused(_)
        | Outcome::Rejected(_) => Maybe::Absent(entry::Absent::Unadmitted),
    }
}

/// The kernel position of each entry that `held` keeps before the first
/// place that the walk crosses, over [`RUN`] places at most. `held` holds the
/// entries that the record keeps, from one place of the walk on.
///
/// # Specification
/// trivial.
fn run_firsts(held: &[Option<&Readmitted>]) -> Vec<ConstantIndex>
{
    held.iter()
        .take(RUN)
        .map_while(|entry| *entry)
        .filter_map(|entry| match position_of(&entry.outcome) {
            Maybe::Present(position) => Some(position),
            Maybe::Absent(_) => None,
        })
        .collect()
}

/// Keep in place the unit whose first member stands at `first`, with the
/// key check that `checked` holds for it.
///
/// When the environment forks and `checked` holds no check of the unit at the
/// state that the environment is in, the walk first checks the keys of the
/// run from this place on through the fork. `held` holds the entries that the
/// record keeps from this place on. An environment that does not fork keeps
/// the unit as [`Environment::keep_in_place`] keeps it.
///
/// # Specification
/// - ensures: what [`Environment::keep_in_place`] at `first` gives.
/// - fails: as [`Environment::keep_in_place`].
/// - panics: none.
///
/// # Errors
/// As `- fails:`.
///
/// # Adequacy
/// - hypothesis: L3 — a kept readmission on a fork answers as on no fork.
/// - witness: `bridge::tests::a_forked_kept_readmission_answers_as_a_serial_one_7217`
pub(super) fn keep_in_run(
    environment: &mut Environment,
    checked: &mut KeptKeys,
    (held, first): (&[Option<&Readmitted>], ConstantIndex),
) -> Result<CheckedId, KernelError>
{
    if !environment.forks_kept_keys() {
        return environment.keep_in_place(first);
    }
    if !checked.covers(first) || !environment.holds_kept_keys(checked) {
        *checked = environment.check_kept_keys(&run_firsts(held));
    }
    environment.keep_checked_in_place(first, checked)
}

/// The first kernel position of the mutual block that `held`, the entries
/// kept at the places of a block of the edited source, keeps whole.
///
/// # Specification
/// - ensures: present when each place keeps an entry that a mutual block
///   admitted ([`timed::Absent::Block`]), at consecutive kernel positions from
///   the first; absent as [`entry::Absent::Unwhole`] otherwise, and as
///   [`entry::Absent::Unadmitted`] when `held` is empty. A member of the
///   record's block that the edit left out is retired with its unit, so no kept
///   block holds more members than the places.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a block is kept whole or crossed whole, as a fresh
///   admission admits it.
/// - witness: `bridge::tests::a_kept_readmission_answers_as_a_whole_one_6846`
#[spec(ensures: |ret| matches!(ret, Maybe::Absent(_)) || (!held.is_empty() && held.iter().all(Option::is_some)))]
pub(super) fn unit_of(held: &[Option<&Readmitted>]) -> Maybe<ConstantIndex, entry::Absent>
{
    let mut first = None;
    for (offset, entry) in held.iter().enumerate() {
        let Some(entry) = *entry
        else {
            return Maybe::Absent(entry::Absent::Unwhole);
        };
        let (Maybe::Absent(timed::Absent::Block), Maybe::Present(position)) =
            (entry.took, position_of(&entry.outcome))
        else {
            return Maybe::Absent(entry::Absent::Unwhole);
        };
        let start = *first.get_or_insert(position);
        if usize::from(position) != usize::from(start).saturating_add(offset) {
            return Maybe::Absent(entry::Absent::Unwhole);
        }
    }
    first.map_or(Maybe::Absent(entry::Absent::Unadmitted), Maybe::Present)
}

/// The entry of the declaration `judged`, kept in place from the record's
/// `entry`: the record's outcome and time at the declaration's module
/// position and origin, and the record's certificates with each definition
/// they unfold at its module position in the edited source (`renames`). Its
/// body is defined and its kernel position filed in `positions`, as its
/// crossing filed them.
///
/// # Specification
/// - requires: the verdict of `judged` agrees with the outcome of `entry`, and
///   `renames` holds each definition the certificates of `entry` unfold.
/// - ensures: as above; `positions` gains the module position of `judged` and
///   its body or signature, and nothing else.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — as [`Crossed::resume`], which carries each resumed entry
///   so, and the certificates of a kept entry name the definitions of the
///   edited source.
/// - witness: `bridge::tests::a_kept_readmission_answers_as_a_whole_one_6846`
#[spec(ensures: |ret| ret.constant == judged.constant() && ret.certificates.len() == entry.certificates.len())]
pub(super) fn keep_entry(
    positions: &mut Positions,
    report: &ModuleReport,
    (entry, judged): (&Readmitted, &Judged),
    renames: &BTreeMap<ConstantIndex, ConstantIndex>,
) -> Readmitted
{
    let constant = judged.constant();
    define(
        &mut positions.definitions,
        report,
        (constant, &entry.outcome, judged.verdict()),
    );
    if let Maybe::Present(position) = position_of(&entry.outcome) {
        positions.admitted.insert(constant, position);
    }
    Readmitted {
        constant,
        origin: judged.origin(),
        outcome: entry.outcome.clone(),
        certificates: entry
            .certificates
            .iter()
            .map(|replayed| match replayed.unfolded {
                Unfolded::Definition(at) => Replayed {
                    unfolded: Unfolded::Definition(renames.get(&at).copied().unwrap_or(at)),
                    ..*replayed
                },
                Unfolded::Abstraction(_) | Unfolded::Returned(_) => *replayed,
            })
            .collect(),
        took: entry.took,
    }
}

/// Retire the unit of the kernel entry `entry` holds, when it is live: what a
/// refused keep leaves, so that the place crosses again.
///
/// # Specification
/// - ensures: the unit of the entry's kernel position is retired when that
///   entry was live; nothing changes otherwise.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a refused keep retires the unit and the place crosses, as
///   a fresh admission crosses it.
/// - witness: `bridge::tests::a_kept_readmission_answers_as_a_whole_one_6846`
#[spec(captures: length = environment.entries().len(), ensures: environment.entries().len() == length)]
pub(super) fn retire_unit(
    environment: &mut Environment,
    entry: &Readmitted,
)
{
    if let Maybe::Present(position) = position_of(&entry.outcome)
        && environment.entries().get(usize::from(position)).is_some()
    {
        // A live entry retires: its position stands below the entries.
        let _retired = environment.retire(&[position]);
    }
}

/// Define in `definitions` the core body or the data signature that the
/// declaration at `constant` of `report` holds under `verdict`, as crossing
/// it under `outcome` did: what a decode or an instance of it reads.
///
/// # Specification
/// trivial.
fn define(
    definitions: &mut CodeDefinitions,
    report: &ModuleReport,
    (constant, outcome, verdict): (ConstantIndex, &Outcome, Verdict),
)
{
    match (outcome, verdict) {
        (
            &(Outcome::Defined { .. } | Outcome::Static),
            Verdict::Checked { body, .. } | Verdict::Synthesised { body, .. },
        ) => definitions.define(
            constant,
            report.definitions().get(&constant).copied().unwrap_or(body),
        ),
        (&Outcome::Data { .. }, Verdict::Data) => {
            if let Some(signature) = report.data_signatures().get(&constant) {
                definitions.present(constant, signature);
            }
        },
        _ => {},
    }
}

/// Whether `verdict` is of the kind the declaration at `constant` of
/// `report` crossed as `outcome` under: a body for a definition, a body or a
/// world for a static declaration, a nominal declaration for a data
/// declaration, a signed one for an assumption.
///
/// # Specification
/// trivial.
fn agrees(
    report: &ModuleReport,
    (constant, outcome, verdict): (ConstantIndex, &Outcome, Verdict),
) -> Agreement
{
    match (outcome, verdict) {
        (
            &(Outcome::Defined { .. } | Outcome::Static),
            Verdict::Checked { .. } | Verdict::Synthesised { .. },
        )
        | (&Outcome::Data { .. }, Verdict::Data)
        | (
            &Outcome::Assumed { .. },
            Verdict::Owed(_) | Verdict::Checked { .. } | Verdict::Synthesised { .. },
        ) => Agreement::Agrees,
        (&Outcome::Static, Verdict::Data) if report.worlds().contains(&constant) => {
            Agreement::Agrees
        },
        _ => Agreement::Differs,
    }
}

/// The longest run of `pairs` whose second positions ascend: the pairs a
/// readmission keeps. Each pair is the module position of a declaration of
/// the edited source and that of the record's declaration with its key.
///
/// # Specification
/// - requires: `pairs` ascend by their first positions.
/// - ensures: a longest subsequence of `pairs` that ascends by both positions,
///   in order.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a moved declaration is kept on one side of the move only,
///   so the kept entries keep their relative order and no rank rewrite reorders
///   them.
/// - witness: `bridge::tests::a_kept_readmission_answers_as_a_whole_one_6846`
#[spec(ensures: |ret| ret.len() <= pairs.len()
    && ret.windows(2).all(|pair| matches!(*pair, [(new, old), (later, older)] if new < later && old < older)))]
fn in_order(pairs: &[(ConstantIndex, ConstantIndex)]) -> Vec<(ConstantIndex, ConstantIndex)>
{
    // Patience sorting: `tails[k]` is the pair that ends the least run of
    // length `k + 1` found so far, and `before` links each pair to the one
    // before it in its run.
    let mut tails: Vec<usize> = Vec::new();
    let mut before: Vec<Option<usize>> = Vec::with_capacity(pairs.len());
    for (at, &(_, old)) in pairs.iter().enumerate() {
        let length = tails
            .partition_point(|&tail| pairs.get(tail).is_some_and(|&(_, earlier)| earlier < old));
        before.push(length.checked_sub(1).and_then(|k| tails.get(k).copied()));
        match tails.get_mut(length) {
            Some(tail) => *tail = at,
            None => tails.push(at),
        }
    }
    let mut run = Vec::with_capacity(tails.len());
    let mut cursor = tails.last().copied();
    while let Some(at) = cursor {
        if let Some(&pair) = pairs.get(at) {
            run.push(pair);
        }
        cursor = before.get(at).copied().flatten();
    }
    run.reverse();
    run
}

/// What a readmission of `report`, whose declarations carry `keys`, keeps
/// of `record`: [`Kept`], or why it keeps nothing.
///
/// # Specification
/// - requires: `keys` holds the content key of each declaration of `report`, in
///   order, as the record's keys hold those of its own.
/// - ensures: when present, the record's environment handed on
///   ([`Environment::handed_on`]) with the reach of the edit retired: the
///   entries of each record declaration that the in-order match leaves, of each
///   declaration whose certificates unfold an edited one, of each seed whose
///   first reader is edited, and of each entry that reads one of them. The
///   first reader of a seed is the record declaration whose entry ranks least
///   past the seed. Each kept place `p` holds the record's entry it keeps, and
///   that entry's kernel entry and the seeds below it, in their order of rank
///   in the record, take the ranks from `p × STRIDE` on. The positions hold no
///   module position, no core body and no retired seed. The record is
///   unchanged.
/// - fails: never; absent as [`keeping::Absent::Unkeyed`] without keys, as
///   [`keeping::Absent::Formed`] when the record holds a formation, as
///   [`keeping::Absent::Sealed`] when the report seals an abstract type, and as
///   [`keeping::Absent::Unranked`] when the kernel refuses the retirement or
///   the rank rewrite.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a readmission that retires the reach of an edit and keeps
///   the rest in place answers as a whole readmission of the edited source.
/// - witness: `bridge::tests::a_kept_readmission_answers_as_a_whole_one_6846`
/// - witness: `bridge::tests::a_seed_whose_first_reader_leaves_retires_6846`
/// - witness: `bridge::tests::a_crossing_that_reads_a_kept_seed_first_takes_it_below_itself_7196`
#[spec(ensures: |ret| match ret {
    Maybe::Present(ref kept) => kept.held.len() == keys.len(),
    Maybe::Absent(_) => true,
})]
pub(super) fn keeping<'record>(
    record: &'record Crossed,
    report: &ModuleReport,
    keys: &[DeclarationKey],
) -> Maybe<Kept<'record>, keeping::Absent>
{
    let judged = report.judged();
    if record.keys.len() != record.readmitted.len() || keys.len() != judged.len() {
        return Maybe::Absent(keeping::Absent::Unkeyed);
    }
    if !record.positions.formations.is_empty() {
        return Maybe::Absent(keeping::Absent::Formed);
    }
    if !report.abstract_types().is_empty() {
        return Maybe::Absent(keeping::Absent::Sealed);
    }
    // Each declaration of the edited source takes the first record
    // declaration with its key that no earlier one took, when the kinds of
    // their verdicts agree; the longest run of those in the order of both
    // sources is kept.
    let mut by_key: BTreeMap<ContentDigest, VecDeque<&Readmitted>> = BTreeMap::new();
    for (key, entry) in record.keys.iter().zip(&record.readmitted) {
        if let Maybe::Present(digest) = *key {
            by_key.entry(digest).or_default().push_back(entry);
        }
    }
    let mut pairs = Vec::new();
    for (key, declaration) in keys.iter().zip(judged) {
        if let Maybe::Present(digest) = *key
            && let Some(entry) = by_key.get_mut(&digest).and_then(VecDeque::pop_front)
            && agrees(
                report,
                (
                    declaration.constant(),
                    &entry.outcome,
                    declaration.verdict(),
                ),
            ) == Agreement::Agrees
        {
            pairs.push((declaration.constant(), entry.constant));
        }
    }
    let matched = in_order(&pairs);
    let kept_from: BTreeMap<ConstantIndex, ConstantIndex> =
        matched.iter().map(|&(new, old)| (old, new)).collect();
    // The record declaration at each kernel position, by its module position,
    // and the record declarations whose certificates unfold each one: a decode
    // or an instance of a definition crosses as its body, so its reader's
    // entry holds that body, and no kernel reference records the definition.
    let mut owner_at = BTreeMap::new();
    let mut position_at = BTreeMap::new();
    let mut unfolders: BTreeMap<ConstantIndex, Vec<ConstantIndex>> = BTreeMap::new();
    for entry in &record.readmitted {
        if let Maybe::Present(position) = position_of(&entry.outcome) {
            owner_at.insert(position, entry.constant);
            position_at.insert(entry.constant, position);
        }
        for replayed in &entry.certificates {
            if let Unfolded::Definition(at) = replayed.unfolded() {
                unfolders.entry(at).or_default().push(entry.constant);
            }
        }
    }
    // A seed stands just below its first reader: the record declaration whose
    // entry ranks least past it. A crossing that read a kept seed first took
    // it below itself, so the position of a seed no longer says where it
    // stands.
    let seeds: BTreeSet<ConstantIndex> = record
        .positions
        .native
        .values()
        .chain(record.positions.assumed.values())
        .copied()
        .chain(record.positions.models.iter().map(|model| model.position))
        .collect();
    let rank_in_record = |position: ConstantIndex| {
        record
            .environment
            .entries()
            .get(usize::from(position))
            .map(gandr_kernel_core::AdmittedDeclaration::rank)
    };
    let owner_by_rank: BTreeMap<SourceRank, ConstantIndex> = owner_at
        .iter()
        .filter_map(|(&position, &old)| rank_in_record(position).map(|rank| (rank, old)))
        .collect();
    let first_reader = |seed: ConstantIndex| {
        let rank = rank_in_record(seed)?;
        owner_by_rank
            .range((
                core::ops::Bound::Excluded(rank),
                core::ops::Bound::Unbounded,
            ))
            .next()
            .map(|(_, &old)| old)
    };
    let mut environment = record.environment.handed_on();
    let live = |environment: &Environment, position: ConstantIndex| {
        environment.entries().get(usize::from(position)).is_some()
    };
    // The edited declarations: each the match leaves, each that unfolds an
    // edited one, and each whose entry the kernel's reach of the edited
    // entries and the moved seeds holds, until none is added.
    let mut edited: BTreeSet<ConstantIndex> = record
        .readmitted
        .iter()
        .map(|entry| entry.constant)
        .filter(|constant| !kept_from.contains_key(constant))
        .collect();
    let mut retiring: BTreeSet<ConstantIndex> = BTreeSet::new();
    let mut pending: Vec<ConstantIndex> = edited.iter().copied().collect();
    let reach: BTreeSet<ConstantIndex> = loop {
        while let Some(at) = pending.pop() {
            if let Some(&position) = position_at.get(&at) {
                retiring.insert(position);
            }
            for &reader in unfolders.get(&at).map_or(&[][..], Vec::as_slice) {
                if edited.insert(reader) {
                    pending.push(reader);
                }
            }
        }
        let reach: BTreeSet<ConstantIndex> = environment
            .reach(retiring.iter().copied())
            .iter()
            .copied()
            .collect();
        for position in &reach {
            if let Some(&owner) = owner_at.get(position)
                && edited.insert(owner)
            {
                pending.push(owner);
            }
        }
        // A seed whose first reader is edited moves: it retires with each
        // entry that reads it, and the walk seeds it again where it is read
        // first.
        let mut moved = false;
        for &seed in &seeds {
            if live(&environment, seed)
                && !reach.contains(&seed)
                && first_reader(seed).is_none_or(|old| edited.contains(&old))
                && retiring.insert(seed)
            {
                moved = true;
            }
        }
        // Each pass adds an edited declaration or a retired seed, or ends.
        if pending.is_empty() && !moved {
            break reach;
        }
    };
    let retired: Vec<ConstantIndex> = reach.iter().copied().collect();
    if environment.retire(&retired).is_err() {
        return Maybe::Absent(keeping::Absent::Unranked);
    }
    // Each kept declaration's seeds take the ranks from its place's on, in
    // the order they were seeded, which is their order of rank in the record,
    // and its own entry the rank after them.
    let mut seeded: Vec<(SourceRank, ConstantIndex)> = seeds
        .iter()
        .filter(|&&seed| live(&environment, seed))
        .filter_map(|&seed| rank_in_record(seed).map(|rank| (rank, seed)))
        .collect();
    seeded.sort_unstable();
    let mut below: BTreeMap<ConstantIndex, Vec<ConstantIndex>> = BTreeMap::new();
    for (_, seed) in seeded {
        if let Some(old) = first_reader(seed) {
            below.entry(old).or_default().push(seed);
        }
    }
    let entry_of: BTreeMap<ConstantIndex, &Readmitted> = record
        .readmitted
        .iter()
        .map(|entry| (entry.constant, entry))
        .collect();
    let mut kept = Vec::with_capacity(judged.len());
    let mut ranks = Vec::new();
    for (place, declaration) in judged.iter().enumerate() {
        let held = matched
            .binary_search_by_key(&declaration.constant(), |&(new, _)| new)
            .ok()
            .and_then(|at| matched.get(at))
            .and_then(|&(_, old)| entry_of.get(&old).copied());
        let Some(entry) = held.filter(|entry| !edited.contains(&entry.constant))
        else {
            kept.push(None);
            continue;
        };
        let base = place.saturating_mul(STRIDE);
        let mut offset = 0_usize;
        for &seed in below.get(&entry.constant).map_or(&[][..], Vec::as_slice) {
            ranks.push((seed, SourceRank::from(base.saturating_add(offset))));
            offset = offset.saturating_add(1);
        }
        if let Maybe::Present(position) = position_of(&entry.outcome) {
            ranks.push((position, SourceRank::from(base.saturating_add(offset))));
        }
        kept.push(Some(entry));
    }
    if environment.rerank(&ranks).is_err() {
        return Maybe::Absent(keeping::Absent::Unranked);
    }
    let mut positions = record.positions.clone();
    positions.admitted = BTreeMap::new();
    positions.definitions = CodeDefinitions::new();
    positions
        .native
        .retain(|_, position| !reach.contains(position));
    positions
        .assumed
        .retain(|_, position| !reach.contains(position));
    positions
        .models
        .retain(|model| !reach.contains(&model.position));
    Maybe::Present(Kept {
        environment,
        positions,
        held: kept,
        renames: kept_from
            .into_iter()
            .filter(|&(old, _)| !edited.contains(&old))
            .collect(),
    })
}
