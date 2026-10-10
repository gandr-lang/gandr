//! Exact first-refusal and completion boundaries.

use gandr_core_session::Action;
use gandr_core_session::Completion;
use gandr_core_session::Move;
use gandr_core_session::MoveIndex;
use gandr_core_session::Node;
use gandr_core_session::NodeId;
use gandr_core_session::Payload;
use gandr_core_session::PayloadDigest;
use gandr_core_session::Refusal;
use gandr_core_session::ReplayError;
use gandr_core_session::replay;

use crate::common::REPORT;
use crate::common::YIELD;
use crate::common::payload;
use crate::common::session;

#[test]
fn refusals_preserve_the_accepted_prefix()
{
    let rows = [
        (
            Node::Send(YIELD, NodeId(2)),
            Move::Send(payload(YIELD)),
            Action::Send(YIELD),
            Move::Send(payload(REPORT)),
            Refusal::WrongPayloadIdentity,
        ),
        (
            Node::Receive(YIELD, NodeId(2)),
            Move::Receive(payload(YIELD)),
            Action::Receive(YIELD),
            Move::Receive(payload(REPORT)),
            Refusal::WrongPayloadIdentity,
        ),
        (
            Node::Select([("yes".into(), NodeId(2))].into()),
            Move::Select("yes".into()),
            Action::Select,
            Move::Select("no".into()),
            Refusal::WrongLabel,
        ),
        (
            Node::Offer([("yes".into(), NodeId(2))].into()),
            Move::Offer("yes".into()),
            Action::Offer,
            Move::Offer("no".into()),
            Refusal::WrongLabel,
        ),
    ];
    for (index, &(ref node, ref valid, expected, ref bad, reason)) in rows.iter().enumerate() {
        let protocol = session(alloc::vec![
            Node::Send(REPORT, NodeId(1)),
            node.clone(),
            Node::End
        ]);
        let prefix = Move::Send(payload(REPORT));
        assert_eq!(
            replay(&protocol, &[prefix.clone(), valid.clone(), Move::End]),
            Ok(Completion)
        );
        assert_eq!(
            replay(&protocol, &[prefix.clone(), bad.clone(), Move::End]),
            Err(ReplayError::Refused {
                at: MoveIndex(1),
                expected,
                observed: bad.clone(),
                reason,
            })
        );
        for (other, row) in rows.iter().enumerate() {
            let wrong = &row.1;
            if index != other {
                assert_eq!(
                    replay(&protocol, &[prefix.clone(), wrong.clone(), Move::End]),
                    Err(ReplayError::Refused {
                        at: MoveIndex(1),
                        expected,
                        observed: wrong.clone(),
                        reason: Refusal::WrongDirection,
                    })
                );
            }
        }
        assert_eq!(
            replay(&protocol, &[prefix, Move::End]),
            Err(ReplayError::Refused {
                at: MoveIndex(1),
                expected,
                observed: Move::End,
                reason: Refusal::WrongDirection,
            })
        );
    }
    for digest in [PayloadDigest([0; 32]), PayloadDigest([255; 32])] {
        let body = Payload {
            identity: YIELD,
            digest,
        };
        assert_eq!(
            replay(
                &session(alloc::vec![Node::Send(YIELD, NodeId(1)), Node::End]),
                &[Move::Send(body), Move::End]
            ),
            Ok(Completion)
        );
        assert_eq!(
            replay(
                &session(alloc::vec![Node::Receive(YIELD, NodeId(1)), Node::End]),
                &[Move::Receive(body), Move::End]
            ),
            Ok(Completion)
        );
    }
}

#[test]
fn end_and_incomplete_runs_are_distinct()
{
    let end = session(alloc::vec![Node::End]);
    assert_eq!(
        replay(&end, &[]),
        Err(ReplayError::IncompleteRun {
            at: MoveIndex(0),
            expected: Action::End
        })
    );
    assert_eq!(replay(&end, &[Move::End]), Ok(Completion));
    let send = session(alloc::vec![Node::Send(YIELD, NodeId(1)), Node::End]);
    assert_eq!(
        replay(&send, &[]),
        Err(ReplayError::IncompleteRun {
            at: MoveIndex(0),
            expected: Action::Send(YIELD)
        })
    );
    assert_eq!(
        replay(&send, &[Move::Send(payload(YIELD))]),
        Err(ReplayError::IncompleteRun {
            at: MoveIndex(1),
            expected: Action::End
        })
    );
    for observed in [
        Move::Send(payload(YIELD)),
        Move::Receive(payload(YIELD)),
        Move::Select("next".into()),
        Move::Offer("next".into()),
    ] {
        assert_eq!(
            replay(&end, core::slice::from_ref(&observed)),
            Err(ReplayError::Refused {
                at: MoveIndex(0),
                expected: Action::End,
                observed: observed.clone(),
                reason: Refusal::ResumeAfterEnd,
            })
        );
        assert_eq!(
            replay(&end, &[Move::End, observed.clone()]),
            Err(ReplayError::Refused {
                at: MoveIndex(1),
                expected: Action::End,
                observed,
                reason: Refusal::ResumeAfterEnd,
            })
        );
    }
    assert_eq!(
        replay(&end, &[Move::End, Move::End]),
        Err(ReplayError::Refused {
            at: MoveIndex(1),
            expected: Action::End,
            observed: Move::End,
            reason: Refusal::ResumeAfterEnd,
        })
    );
}
