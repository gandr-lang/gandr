//! Goals against checkpoints: the declarations a submission reports as goals
//! are exactly the items whose checkpoint marks the body a hole.

use gandr_core_incremental::HoleMark;
use gandr_core_incremental::ItemKey;
use gandr_surface_dispatcher::Composed;
use gandr_surface_dispatcher::Goals;
use gandr_surface_dispatcher::Shown;
use gandr_surface_dispatcher::SourceRoot;
use gandr_surface_dispatcher::Verb;
use gandr_surface_dispatcher::shown;

use crate::common::footprints;
use crate::common::session;
use crate::common::submit;

/// A recovering source: a declaration owed its body, one that checks, and
/// one the stray `~` leaves malformed.
const PARSER_RECOVERY: &str = include_str!("fixtures/parser-recovery.gandr");
/// An unfinished source: a thunk that checks, a declaration owed its body,
/// and a definition cut off at an open parenthesis.
const INCOMPLETE_INPUT: &str = include_str!("fixtures/incomplete-input.gandr");

#[test]
#[cfg_attr(
    dylint_lib = "quenchant_dylints",
    expect(
        linear_search_in_loop,
        reason = "bounded: one recovery fixture's few goals and checkpoints"
    )
)]
fn goal_flags_match_checkpoint_footprints_for_recovery_fixtures()
{
    // Two predicates over one revision, computed apart: the dispatcher's, a
    // declaration `check --goals` prints as a goal, and the incremental
    // checker's, an item whose checkpoint footprint marks its body a hole.
    for (name, source, expected) in [
        ("parser-recovery", PARSER_RECOVERY, [
            (ItemKey::from("owed"), HoleMark::Hole),
            (ItemKey::from("answer"), HoleMark::Filled),
        ]),
        ("incomplete-input", INCOMPLETE_INPUT, [
            (ItemKey::from("k"), HoleMark::Filled),
            (ItemKey::from("later"), HoleMark::Hole),
        ]),
    ] {
        let mut session = session(SourceRoot::Strict);
        let submission = submit(&mut session, source);
        let Composed::Settled { ref report, .. } = *submission.composed()
        else {
            panic!("{name} is read as a module");
        };
        let mut spelled = String::new();
        let goals: Vec<ItemKey> = report
            .declarations()
            .iter()
            .filter(|declaration| shown(declaration, Verb::Check(Goals::Reported)) == Shown::Goal)
            .map(|declaration| {
                spelled.clear();
                core::fmt::Write::write_fmt(&mut spelled, format_args!("{}", declaration.name()))
                    .expect("a name writes");
                ItemKey::from(spelled.as_str())
            })
            .collect();
        let checkpoints = footprints(&session);
        assert!(
            goals
                .iter()
                .all(|goal| checkpoints.iter().any(|checkpoint| checkpoint.0 == *goal)),
            "every goal of {name} is an item: {goals:?}"
        );
        let flags: Vec<(ItemKey, HoleMark)> = checkpoints
            .iter()
            .map(|checkpoint| {
                let key = &checkpoint.0;
                let flag = if goals.contains(key) {
                    HoleMark::Hole
                }
                else {
                    HoleMark::Filled
                };
                (key.clone(), flag)
            })
            .collect();
        assert_eq!(
            flags, checkpoints,
            "goal and checkpoint hole predicates diverged for {name}"
        );
        assert_eq!(checkpoints, expected, "{name} resumes the items pinned");
    }
}
