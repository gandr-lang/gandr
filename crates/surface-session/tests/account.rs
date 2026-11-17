//! The account: each declaration's row holds the checker's verdict at its
//! judgement and the kernel tier once its admission ends, and a judgement
//! keeps the row of each declaration whose content it did not change.

use gandr_core_incremental::ContentKey;
use gandr_core_incremental::MemoryCheckpointStore;
use gandr_kernel_term::ConstantIndex;
use gandr_storage_records::InMemoryBlockStore;
use gandr_surface_dispatcher::KernelTier;
use gandr_surface_dispatcher::SourceRoot;
use gandr_surface_session::AccountRow;
use gandr_surface_session::CheckerVerdict;
use gandr_surface_session::KernelState;
use gandr_surface_session::Session;
use gandr_surface_session::compiled;
use gandr_surface_session::unrowed;
use gandr_surface_syntax::SourceText;
use quenchant_shape::shape::Maybe;

use crate::common::session;

/// A session over memory stores.
type Memory = Session<MemoryCheckpointStore, InMemoryBlockStore>;

/// Each row of `session`'s account: its position, its key and its row.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the account's rows, in its order.
/// - panics: none.
/// - executable: none — the result is the account's own listing, and the
///   session's predicates check the table it lists.
///
/// # Adequacy
/// - hypothesis: L3 — as the account's rows.
/// - witness: `tests::account::a_comment_edit_keeps_every_row_and_an_edit_moves_one`
fn rows(session: &Memory) -> Vec<(ConstantIndex, ContentKey, AccountRow)>
{
    session.account().rows().collect()
}

/// Each row of `session`'s account: its position, the checker's verdict and
/// the kernel's state.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the account's rows, in its order, without their keys.
/// - panics: none.
/// - executable: none — as [`rows`].
///
/// # Adequacy
/// - hypothesis: L3 — as the account's rows.
/// - witness: `tests::account::each_row_holds_the_verdict_and_then_the_kernel_tier`
fn verdicts(session: &Memory) -> Vec<(ConstantIndex, CheckerVerdict, KernelState)>
{
    session
        .account()
        .rows()
        .map(|(constant, _, row)| (constant, row.verdict(), row.kernel()))
        .collect()
}

/// Judge `text` in `session` and leave its admission pending.
///
/// # Specification
/// - requires: `text` parses.
/// - ensures: `session` judged `text`.
/// - panics: when the judgement fails.
/// - executable: none — the function returns nothing a predicate could read.
///
/// # Adequacy
/// - hypothesis: L3 — the session judges a revision of its own text.
/// - witness: `tests::account::each_row_holds_the_verdict_and_then_the_kernel_tier`
fn judge(
    session: &mut Memory,
    text: SourceText<'_>,
)
{
    let _judged = session
        .judge_reading(text, |_| ())
        .expect("the revision is judged");
}

/// Run the admission the latest judgement of `session` left.
///
/// # Specification
/// - requires: `session` judged a revision whose admission is pending.
/// - ensures: the admission settled.
/// - panics: when the kernel disagrees or no admission is pending.
/// - executable: none — the function returns nothing a predicate could read.
///
/// # Adequacy
/// - hypothesis: L3 — the session admits the revision it judged last.
/// - witness: `tests::account::each_row_holds_the_verdict_and_then_the_kernel_tier`
fn admit(session: &mut Memory)
{
    let Ok(Maybe::Present(_admitted)) = session.admit()
    else {
        panic!("the kernel agrees and the admission settles");
    };
}

/// A module with a nominal type, a checked definition, a declaration owed its
/// body, a refused one and a reader of the refused one: the judgement writes
/// each verdict at pending, and the admission writes each tier, the reader's
/// withheld behind the declaration it reads. No row has a compile tier, and a
/// position past the last declaration has no row.
#[test]
fn each_row_holds_the_verdict_and_then_the_kernel_tier()
{
    let mut session = session(SourceRoot::Strict);
    judge(
        &mut session,
        SourceText::from(include_str!(
            "account/fixtures/each-row-holds-the-verdict-and-then-the-kernel-tier.gandr"
        )),
    );
    assert_eq!(
        verdicts(&session),
        [
            (CheckerVerdict::Data, KernelState::Pending),
            (CheckerVerdict::Checked, KernelState::Pending),
            (CheckerVerdict::Owed, KernelState::Pending),
            (CheckerVerdict::Refused, KernelState::Pending),
            (CheckerVerdict::Synthesised, KernelState::Pending),
        ]
        .into_iter()
        .enumerate()
        .map(|(at, (verdict, kernel))| (ConstantIndex::from(at), verdict, kernel))
        .collect::<Vec<_>>(),
        "the judgement writes each verdict, and the kernel has reported none"
    );
    admit(&mut session);
    assert_eq!(
        verdicts(&session),
        [
            (CheckerVerdict::Data, KernelTier::Replayed),
            (CheckerVerdict::Checked, KernelTier::Replayed),
            (CheckerVerdict::Owed, KernelTier::Assumed),
            (CheckerVerdict::Refused, KernelTier::Unoffered),
            (CheckerVerdict::Synthesised, KernelTier::Withheld {
                behind: ConstantIndex::from(3_usize),
            }),
        ]
        .into_iter()
        .enumerate()
        .map(|(at, (verdict, tier))| (ConstantIndex::from(at), verdict, KernelState::Settled(tier)))
        .collect::<Vec<_>>(),
        "the admission writes each tier at its own declaration"
    );
    assert!(
        session
            .account()
            .rows()
            .all(|(_, _, row)| row.compile() == Maybe::Absent(compiled::Absent::Uncompiled)),
        "the hub compiles nothing"
    );
    assert_eq!(
        session.account().row_at(ConstantIndex::from(5_usize)),
        Maybe::Absent(unrowed::Absent::Unkeyed),
        "no declaration stands past the last"
    );
}

/// A comment keeps every key and every tier before its admission ends. An
/// edit to one declaration moves its row alone to pending, and its admission
/// settles it again. A declaration inserted above the others moves each
/// position, and each row follows its content to its new position with its
/// tier. A withheld tier goes back to pending at a judgement that keeps its
/// key, since it names its support by position.
#[test]
fn a_comment_edit_keeps_every_row_and_an_edit_moves_one()
{
    let mut session = session(SourceRoot::Strict);
    judge(
        &mut session,
        SourceText::from(include_str!(
            "account/fixtures/a-comment-edit-keeps-every-row-first.gandr"
        )),
    );
    admit(&mut session);
    let settled = rows(&session);
    assert_eq!(
        settled
            .iter()
            .map(|&(at, _, row)| (at, row.kernel()))
            .collect::<Vec<_>>(),
        [0_usize, 1_usize, 2_usize].map(|at| (
            ConstantIndex::from(at),
            KernelState::Settled(KernelTier::Replayed)
        )),
        "each declaration replays"
    );
    judge(
        &mut session,
        SourceText::from(include_str!(
            "account/fixtures/a-comment-edit-keeps-every-row-noted.gandr"
        )),
    );
    assert_eq!(
        rows(&session),
        settled,
        "a comment keeps every key and every tier before its admission ends"
    );
    judge(
        &mut session,
        SourceText::from(include_str!(
            "account/fixtures/a-comment-edit-keeps-every-row-edited.gandr"
        )),
    );
    assert_eq!(
        rows(&session)
            .iter()
            .zip(&settled)
            .map(|(&(at, key, row), &(_, before, _))| (at, key == before, row.kernel()))
            .collect::<Vec<_>>(),
        [
            (ConstantIndex::from(0_usize), false, KernelState::Pending),
            (
                ConstantIndex::from(1_usize),
                true,
                KernelState::Settled(KernelTier::Replayed)
            ),
            (
                ConstantIndex::from(2_usize),
                true,
                KernelState::Settled(KernelTier::Replayed)
            ),
        ],
        "the edited declaration alone takes a new key at pending"
    );
    admit(&mut session);
    assert!(
        rows(&session)
            .iter()
            .all(|&(_, _, row)| row.kernel() == KernelState::Settled(KernelTier::Replayed)),
        "the admission settles the edited declaration again"
    );
    let before = rows(&session);
    judge(
        &mut session,
        SourceText::from(include_str!(
            "account/fixtures/a-comment-edit-keeps-every-row-inserted.gandr"
        )),
    );
    assert_eq!(
        rows(&session).get(1_usize ..).map(<[_]>::to_vec),
        Some(
            before
                .iter()
                .map(|&(at, key, row)| (
                    ConstantIndex::from(usize::from(at).saturating_add(1_usize)),
                    key,
                    row
                ))
                .collect()
        ),
        "each row follows its content one position down, with its tier"
    );
    assert_eq!(
        session
            .account()
            .row_at(ConstantIndex::from(0_usize))
            .map(|(_, row)| row.kernel()),
        Maybe::Present(KernelState::Pending),
        "the inserted declaration waits on its admission"
    );
    judge(
        &mut session,
        SourceText::from(include_str!(
            "account/fixtures/a-comment-edit-keeps-every-row-withheld.gandr"
        )),
    );
    admit(&mut session);
    judge(
        &mut session,
        SourceText::from(include_str!(
            "account/fixtures/a-comment-edit-keeps-every-row-withheld-noted.gandr"
        )),
    );
    assert_eq!(
        verdicts(&session),
        [
            (
                ConstantIndex::from(0_usize),
                CheckerVerdict::Refused,
                KernelState::Settled(KernelTier::Unoffered)
            ),
            (
                ConstantIndex::from(1_usize),
                CheckerVerdict::Synthesised,
                KernelState::Pending
            ),
        ],
        "a withheld tier names its support by position, so a judgement does not keep it"
    );
}
