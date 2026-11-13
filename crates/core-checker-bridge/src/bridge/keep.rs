//! A readmission that keeps each entry an edit leaves. The leading run that
//! the edit leaves stands as the record holds it, as the run of a resumed
//! readmission stands: the readmission reads, retires and ranks nothing in
//! it. Past the run, the declarations of the edited source are matched in
//! order to the declarations of the record by their content keys. The
//! readmission retires the reach of each declaration that the match leaves
//! out. Each other entry takes the rank of its place in the edited source,
//! and the walk keeps it in place at its own key.
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
//! A seal stays whole or the readmission keeps nothing. The kernel keys a
//! sealed module when its seal closes, so a kept atom and each kept member
//! stand by their own keys. A readmission whose edit touches a seal
//! readmits whole. Each extent is then the one a whole readmission draws.
//!
//! The witnesses of a formation are seeds of their first reader, and each
//! keeps by its own key. Each takes the name of its formation's content, so
//! it can move. No reader names a witness by its kernel position, so a
//! witness that retires edits each reader of its formation, and the first of
//! them that crosses again forms it under the same name. A formation that
//! reads a constant by its kernel position keeps no witness past the run,
//! until #7261 names that constant by its admission key. A walk that places a
//! kept formation below a later reader readmits whole.
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
use gandr_kernel_core::Environment;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::SourceRank;
use quenchant_shape::shape::Maybe;

use super::CodeDefinitions;
use super::Crossed;
use super::DeclarationKey;
use super::LeadingCount;
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
            /// A formation past the run reads a datatype, an atom or an
            /// axiom by its kernel position. A walk that keeps numbers these
            /// otherwise than a whole readmission, so the formation's name
            /// differs.
            Positional,
            /// A seal of the report does not stay whole. The match keeps no
            /// record entry for one of its abstract types, or the reach
            /// holds a position of a record seal. An atom or a member that
            /// crosses again draws another extent than a whole readmission
            /// draws.
            Sealed,
            /// The kernel refused to retire the reach or to rewrite the
            /// ranks.
            Unranked,
            /// The record does not resume the leading run that the edit
            /// leaves.
            Unresumed,
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
pub(super) enum Agreement
{
    /// The kinds agree: the outcome may be kept for the verdict.
    Agrees,
    /// The kinds differ: the declaration crosses again.
    Differs,
}

/// What a readmission keeps of a record: the leading run that the edit
/// leaves, shared with the record as a resumed readmission shares it; the
/// environment with the reach of the edit retired and each other entry past
/// the run at the rank of its place in the edited source; the positions with
/// each retired seed taken out; and the record's entry that each place past
/// the run keeps.
#[derive(Debug)]
pub(super) struct Kept<'record>
{
    /// The record's environment, the reach retired and the entries past the
    /// run reranked.
    pub environment: Environment,
    /// The record's positions, with the module positions and the core bodies
    /// of the run alone, and no retired seed.
    pub positions: Positions,
    /// The entries of the leading run, one for each of its places.
    pub leading: Vec<Readmitted>,
    /// The record's entry each place of the edited source keeps, by place;
    /// none for a place of the run or a place the walk crosses.
    pub held: Vec<Option<&'record Readmitted>>,
    /// The module position in the edited source of each record declaration
    /// the readmission keeps past the run, by its module position in the
    /// record.
    pub renames: BTreeMap<ConstantIndex, ConstantIndex>,
    /// The kernel positions that a closed seal of the record holds: each
    /// atom and its scope. A keep refused there crosses at another extent
    /// than a whole readmission draws, so the walk readmits whole.
    pub sealed: BTreeSet<ConstantIndex>,
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
pub(super) fn define(
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
pub(super) fn agrees(
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

/// How many leading places of `report` the edit leaves as `record` holds
/// them. Each declaration of the run carries the key of the record's entry
/// at its index, at its module position, under a verdict of the kind the
/// entry crossed under. A mutual block is kept whole or crossed whole, so the
/// run ends where a unit of the record's environment ends.
///
/// # Specification
/// trivial.
fn leading_run(
    record: &Crossed,
    report: &ModuleReport,
    keys: &[DeclarationKey],
) -> LeadingCount
{
    let mut run = record
        .keys
        .iter()
        .zip(&record.readmitted)
        .zip(keys.iter().zip(report.judged()))
        .take_while(|&((held, entry), (key, declaration))| {
            matches!((*held, *key), (Maybe::Present(held), Maybe::Present(key)) if held == key)
                && entry.constant == declaration.constant()
                && agrees(
                    report,
                    (
                        declaration.constant(),
                        &entry.outcome,
                        declaration.verdict(),
                    ),
                ) == Agreement::Agrees
        })
        .count();
    if let Some(entry) = run
        .checked_sub(1)
        .and_then(|last| record.readmitted.get(last))
        && let Maybe::Present(position) = position_of(&entry.outcome)
        && let Some(unit) = record
            .environment
            .entries()
            .live(position)
            .map(gandr_kernel_core::AdmittedDeclaration::unit)
        && usize::from(unit.end) > usize::from(position).saturating_add(1)
    {
        run = run.saturating_sub(
            usize::from(position)
                .saturating_sub(usize::from(unit.first))
                .saturating_add(1),
        );
    }
    LeadingCount(run)
}

/// What a readmission of `report`, whose declarations carry `keys`, keeps
/// of `record`: [`Kept`], or why it keeps nothing.
///
/// # Specification
/// - requires: `keys` holds the content key of each declaration of `report`, in
///   order, as the record's keys hold those of its own.
/// - ensures: when present, the leading run that the edit leaves, resumed from
///   the record as [`Crossed::resume`] resumes it, and the record's environment
///   handed on ([`Environment::handed_on`]) with the reach of the edit retired:
///   the entries of each record declaration past the run that the in-order
///   match leaves, of each declaration whose certificates unfold an edited one,
///   of each seed whose first reader is edited, of each reader of a formation
///   whose witness retires, and of each entry that reads one of them. The first
///   reader of a seed is the record declaration whose entry ranks least past
///   the seed. The run keeps its ranks. Each kept place `p` past the run holds
///   the record's entry it keeps, and that entry's kernel entry and the seeds
///   below it, in their order of rank in the record, take the ranks from `p ×
///   STRIDE` on. The positions hold the module positions and the core bodies of
///   the run alone, no retired seed and no formation whose witness retires;
///   each reader of a kept formation stands at its module position in `report`.
///   Nothing past the run is read, retired or ranked when the run holds every
///   declaration of the record and of `report`. The record is unchanged.
/// - fails: never; absent as [`keeping::Absent::Unkeyed`] without keys, as
///   [`keeping::Absent::Positional`] when the name of a formation past the run
///   reads a kernel position, as [`keeping::Absent::Sealed`] when a seal of
///   `report` does not stay whole, as [`keeping::Absent::Unresumed`] when the
///   record does not resume the run, and as [`keeping::Absent::Unranked`] when
///   the kernel refuses the retirement or the rank rewrite.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a readmission that shares the leading run, retires the
///   reach of an edit and keeps the rest in place answers as a whole
///   readmission of the edited source.
/// - witness: `bridge::tests::a_kept_readmission_answers_as_a_whole_one_6846`
/// - witness: `bridge::tests::a_seed_whose_first_reader_leaves_retires_6846`
/// - witness: `bridge::tests::a_crossing_that_reads_a_kept_seed_first_takes_it_below_itself_7196`
/// - witness: `bridge::tests::a_readmission_keeps_a_sealed_module_whose_seal_stays_whole_7200`
/// - witness: `bridge::tests::a_readmission_keeps_the_witnesses_of_a_formation_its_edit_leaves_7200`
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
    // The leading run that the edit leaves stands as the record holds it, as
    // the run of a resumed readmission stands.
    let run = leading_run(record, report, keys);
    let Some((mut environment, mut positions, leading)) = record.resume(report, run)
    else {
        return Maybe::Absent(keeping::Absent::Unresumed);
    };
    let LeadingCount(run) = run;
    let rank_in_record = |position: ConstantIndex| {
        record
            .environment
            .entries()
            .get(usize::from(position))
            .map(gandr_kernel_core::AdmittedDeclaration::rank)
    };
    // The run keeps its ranks, so a rank rewrite starts past the last of them.
    let floor = record
        .readmitted
        .get(.. run)
        .unwrap_or_default()
        .iter()
        .rev()
        .find_map(|entry| match position_of(&entry.outcome) {
            Maybe::Present(position) => rank_in_record(position),
            Maybe::Absent(_) => None,
        })
        .map_or_else(
            || SourceRank::from(0_usize),
            |top| SourceRank::from(usize::from(top).saturating_add(1)),
        );
    // The name of a formation past the run that reads a kernel position
    // differs in a walk that keeps.
    if record.positions.formations.values().any(|formation| {
        matches!(formation.reads, super::NameReads::Position)
            && formation
                .witnesses
                .iter()
                .any(|&witness| rank_in_record(witness).is_some_and(|rank| rank >= floor))
    }) {
        return Maybe::Absent(keeping::Absent::Positional);
    }
    let past = record.readmitted.get(run ..).unwrap_or_default();
    // Each declaration of the edited source past the run takes the first
    // record declaration past the run with its key that no earlier one took,
    // when the kinds of their verdicts agree; the longest run of those in the
    // order of both sources is kept.
    let mut by_key: BTreeMap<ContentDigest, VecDeque<&Readmitted>> = BTreeMap::new();
    for (key, entry) in record.keys.get(run ..).unwrap_or_default().iter().zip(past) {
        if let Maybe::Present(digest) = *key {
            by_key.entry(digest).or_default().push_back(entry);
        }
    }
    let mut pairs = Vec::new();
    for (key, declaration) in keys
        .get(run ..)
        .unwrap_or_default()
        .iter()
        .zip(judged.get(run ..).unwrap_or_default())
    {
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
    // The record declaration past the run at each kernel position, by its
    // module position, and the record declarations whose certificates unfold
    // each one: a decode or an instance of a definition crosses as its body,
    // so its reader's entry holds that body, and no kernel reference records
    // the definition. A declaration of the run unfolds no declaration past it.
    let mut owner_at = BTreeMap::new();
    let mut position_at = BTreeMap::new();
    let mut unfolders: BTreeMap<ConstantIndex, Vec<ConstantIndex>> = BTreeMap::new();
    for entry in past {
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
    // stands. A seed below the floor is read first in the run. The
    // witnesses of a formation stand below their first reader too. No reader
    // names a witness by its kernel position, so a witness that retires
    // edits each reader of its formation. The first of them that crosses
    // again forms it where a whole readmission forms it, under its name.
    let readers_of: BTreeMap<ConstantIndex, &BTreeSet<ConstantIndex>> = record
        .positions
        .formations
        .values()
        .flat_map(|formation| {
            formation
                .witnesses
                .iter()
                .map(move |&witness| (witness, &formation.readers))
        })
        .collect();
    let seeds: BTreeSet<ConstantIndex> = record
        .positions
        .native
        .values()
        .chain(record.positions.assumed.values())
        .copied()
        .chain(record.positions.models.iter().map(|model| model.position))
        .chain(readers_of.keys().copied())
        .filter(|&seed| rank_in_record(seed).is_some_and(|rank| rank >= floor))
        .collect();
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
    let live = |environment: &Environment, position: ConstantIndex| {
        environment.entries().get(usize::from(position)).is_some()
    };
    // The edited declarations: each the match leaves, each that unfolds an
    // edited one, and each whose entry the kernel's reach of the edited
    // entries and the moved seeds holds, until none is added.
    let mut edited: BTreeSet<ConstantIndex> = past
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
        // Each reader of a formation whose witness retires is edited.
        for (witness, readers) in &readers_of {
            if reach.contains(witness) || retiring.contains(witness) {
                for &reader in *readers {
                    if edited.insert(reader) {
                        pending.push(reader);
                    }
                }
            }
        }
        // Each pass adds an edited declaration or a retired seed, or ends.
        if pending.is_empty() && !moved {
            break reach;
        }
    };
    // A seal of the edited source stays whole, or the readmission keeps
    // nothing: an atom or a member that crosses again draws another extent
    // than a whole readmission draws. A scope as a set of positions is the
    // general form, which this slice does not build.
    let sealed: BTreeSet<ConstantIndex> = if report.abstract_types().is_empty() {
        BTreeSet::new()
    }
    else {
        record
            .environment
            .in_rank_order()
            .filter_map(|atom| {
                match record
                    .environment
                    .entries()
                    .get(usize::from(atom))
                    .map(gandr_kernel_core::AdmittedDeclaration::content)
                {
                    Some(&gandr_kernel_term::DeclarationContent::AbstractType {
                        scope: gandr_kernel_term::SealScope::Closed(extent),
                        ..
                    }) => Some((atom, extent)),
                    Some(_) | None => None,
                }
            })
            .flat_map(|(atom, extent)| {
                (usize::from(atom) ..= usize::from(atom).saturating_add(usize::from(extent)))
                    .map(ConstantIndex::from)
            })
            .collect()
    };
    if !report.abstract_types().is_empty() {
        // The run holds each of its declarations at its own position.
        let held: BTreeSet<ConstantIndex> = judged
            .iter()
            .take(run)
            .map(gandr_core_checker_base::Judged::constant)
            .chain(
                matched
                    .iter()
                    .filter(|&&(_, old)| !edited.contains(&old))
                    .map(|&(new, _)| new),
            )
            .collect();
        if report
            .abstract_types()
            .keys()
            .any(|constant| !held.contains(constant))
            || reach.iter().any(|position| sealed.contains(position))
        {
            return Maybe::Absent(keeping::Absent::Sealed);
        }
    }
    // Each kept declaration's seeds take the ranks from its place's on, in
    // the order they were seeded, which is their order of rank in the record,
    // and its own entry the rank after them.
    let entry_of: BTreeMap<ConstantIndex, &Readmitted> =
        past.iter().map(|entry| (entry.constant, entry)).collect();
    let mut kept: Vec<Option<&Readmitted>> = Vec::with_capacity(judged.len());
    kept.extend(core::iter::repeat_n(None, run));
    let mut ranks = Vec::new();
    // A run that holds every declaration of both leaves nothing to retire or
    // to rank.
    if run < judged.len() || !past.is_empty() {
        let retired: Vec<ConstantIndex> = reach.iter().copied().collect();
        if environment.retire(&retired).is_err() {
            return Maybe::Absent(keeping::Absent::Unranked);
        }
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
        for (place, declaration) in judged.iter().enumerate().skip(run) {
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
        if environment.rerank((floor, &ranks)).is_err() {
            return Maybe::Absent(keeping::Absent::Unranked);
        }
    }
    // The walk files each module position past the run again.
    if let Some(entry) = past.first() {
        let _past = positions.admitted.split_off(&entry.constant);
    }
    // A formation whose witness retires forms again at the first of its
    // readers that crosses. Each kept reader takes its module position in
    // the edited source.
    let renames: BTreeMap<ConstantIndex, ConstantIndex> = kept_from
        .into_iter()
        .filter(|&(old, _)| !edited.contains(&old))
        .collect();
    let first_past = past.first().map(|entry| entry.constant);
    positions.formations.retain(|_, formation| {
        !formation
            .witnesses
            .iter()
            .any(|witness| reach.contains(witness))
    });
    for formation in positions.formations.values_mut() {
        formation.readers = formation
            .readers
            .iter()
            .filter_map(|&old| {
                if first_past.is_none_or(|first| old < first) {
                    Some(old)
                }
                else {
                    renames.get(&old).copied()
                }
            })
            .collect();
    }
    if !reach.is_empty() {
        positions
            .native
            .retain(|_, position| !reach.contains(position));
        positions
            .assumed
            .retain(|_, position| !reach.contains(position));
        positions
            .models
            .retain(|model| !reach.contains(&model.position));
    }
    Maybe::Present(Kept {
        environment,
        positions,
        leading,
        held: kept,
        renames,
        sealed,
    })
}
