//! Protocol-level acceptance and terminal-state refusals.

use gandr_core_session::Action;
use gandr_core_session::Completion;
use gandr_core_session::Decision;
use gandr_core_session::Move;
use gandr_core_session::MoveIndex;
use gandr_core_session::Refusal;
use gandr_core_session::ReplayError;
use gandr_core_session::duality;
use gandr_core_session::replay;

use crate::common::DISPATCH;
use crate::common::HANDOFF;
use crate::common::REPORT;
use crate::common::YIELD;
use crate::common::consumer;
use crate::common::generator;
use crate::common::operator;
use crate::common::payload;
use crate::common::seat;

#[test]
fn generator_duality_and_two_yields()
{
    assert_eq!(duality(&generator(), &consumer()), Ok(Decision::Related));
    assert_eq!(duality(&consumer(), &generator()), Ok(Decision::Related));
    assert_eq!(duality(&generator(), &generator()), Ok(Decision::Unrelated));
    assert_eq!(
        replay(&generator(), &[
            Move::Offer("next".into()),
            Move::Send(payload(YIELD)),
            Move::Offer("next".into()),
            Move::Send(payload(YIELD)),
            Move::Offer("stop".into()),
            Move::End,
        ]),
        Ok(Completion)
    );
    assert_eq!(
        replay(&consumer(), &[
            Move::Select("next".into()),
            Move::Receive(payload(YIELD)),
            Move::Select("next".into()),
            Move::Receive(payload(YIELD)),
            Move::Select("stop".into()),
            Move::End,
        ]),
        Ok(Completion)
    );
}

#[test]
fn generator_refuses_resume_after_end()
{
    let next = Move::Offer("next".into());
    assert_eq!(
        replay(&generator(), &[
            next.clone(),
            Move::Send(payload(YIELD)),
            next.clone(),
            Move::Send(payload(YIELD)),
            Move::Offer("stop".into()),
            Move::End,
            next.clone(),
        ]),
        Err(ReplayError::Refused {
            at: MoveIndex(6),
            expected: Action::End,
            observed: next,
            reason: Refusal::ResumeAfterEnd,
        })
    );
}

#[test]
fn seat_duality_report_and_handoff()
{
    assert_eq!(duality(&seat(), &operator()), Ok(Decision::Related));
    assert_eq!(duality(&operator(), &seat()), Ok(Decision::Related));
    assert_eq!(
        replay(&seat(), &[
            Move::Receive(payload(DISPATCH)),
            Move::Select("report".into()),
            Move::Send(payload(REPORT)),
            Move::Offer("next".into()),
            Move::Select("report".into()),
            Move::Send(payload(REPORT)),
            Move::Offer("retire".into()),
            Move::End,
        ]),
        Ok(Completion)
    );
    assert_eq!(
        replay(&operator(), &[
            Move::Send(payload(DISPATCH)),
            Move::Offer("report".into()),
            Move::Receive(payload(REPORT)),
            Move::Select("next".into()),
            Move::Offer("report".into()),
            Move::Receive(payload(REPORT)),
            Move::Select("retire".into()),
            Move::End,
        ]),
        Ok(Completion)
    );
    assert_eq!(
        replay(&seat(), &[
            Move::Receive(payload(DISPATCH)),
            Move::Select("handoff".into()),
            Move::Send(payload(HANDOFF)),
            Move::End,
        ]),
        Ok(Completion)
    );
    assert_eq!(
        replay(&operator(), &[
            Move::Send(payload(DISPATCH)),
            Move::Offer("handoff".into()),
            Move::Receive(payload(HANDOFF)),
            Move::End,
        ]),
        Ok(Completion)
    );
}

#[test]
fn seat_refuses_report_after_retire()
{
    let report = Move::Select("report".into());
    assert_eq!(
        replay(&seat(), &[
            Move::Receive(payload(DISPATCH)),
            report.clone(),
            Move::Send(payload(REPORT)),
            Move::Offer("retire".into()),
            Move::End,
            report.clone(),
        ]),
        Err(ReplayError::Refused {
            at: MoveIndex(5),
            expected: Action::End,
            observed: report,
            reason: Refusal::ResumeAfterEnd,
        })
    );
}
