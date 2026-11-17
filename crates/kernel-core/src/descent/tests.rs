//! The skeleton's laws, observed on a datum that records every call.

use alloc::vec::Vec;

use super::*;

/// A class, a gluing and a position of the recording datum.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct Mark(u8);

/// One call the skeleton made, and the refusal of the call that refused.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Call
{
    /// [`Descent::glue`] at a class.
    Glue(Mark),
    /// [`Descent::bind`] at a gluing.
    Bind(Mark),
    /// [`Descent::agree`] at a position.
    Agree(Mark),
}

/// A datum whose class glues to itself unless it is zero, and whose position
/// agrees when it does not exceed the gluing.
#[repr(transparent)]
#[derive(Debug, Default)]
struct Recording
{
    /// Every call, in the order the skeleton made it.
    calls: Vec<Call>,
}

impl Descent<Mark> for Recording
{
    type Bound<'glued> = &'glued Mark;
    type Gluing = Mark;
    type Position = Mark;
    type Refusal = Call;

    /// Record the call; refuse the zero class.
    ///
    /// # Specification
    /// trivial.
    fn glue(
        &mut self,
        class: Mark,
    ) -> Result<Mark, Call>
    {
        self.calls.push(Call::Glue(class));
        if class == Mark(0) {
            Err(Call::Glue(class))
        }
        else {
            Ok(class)
        }
    }

    /// Record the call; bind the gluing by reference.
    ///
    /// # Specification
    /// trivial.
    fn bind<'glued>(
        &mut self,
        gluing: &'glued Mark,
    ) -> Result<&'glued Mark, Call>
    {
        self.calls.push(Call::Bind(*gluing));
        Ok(gluing)
    }

    /// Record the call; refuse a position above the gluing.
    ///
    /// # Specification
    /// trivial.
    fn agree(
        &mut self,
        bound: &&Mark,
        position: Mark,
    ) -> Result<(), Call>
    {
        self.calls.push(Call::Agree(position));
        if position <= **bound {
            Ok(())
        }
        else {
            Err(Call::Agree(position))
        }
    }
}

#[test]
fn a_class_is_glued_once_and_its_positions_agreed_in_order()
{
    let mut datum = Recording::default();
    let positions = [Mark(1), Mark(3), Mark(5)];
    assert_eq!(replay(&mut datum, Mark(5), positions), Ok(Mark(5)));
    assert_eq!(datum.calls, [
        Call::Glue(Mark(5)),
        Call::Bind(Mark(5)),
        Call::Agree(Mark(1)),
        Call::Agree(Mark(3)),
        Call::Agree(Mark(5)),
    ]);
    let mut empty = Recording::default();
    assert_eq!(replay(&mut empty, Mark(2), []), Ok(Mark(2)));
    assert_eq!(empty.calls, [Call::Glue(Mark(2)), Call::Bind(Mark(2))]);
}

#[test]
fn the_first_refusal_ends_the_replay()
{
    let mut datum = Recording::default();
    let positions = [Mark(1), Mark(7), Mark(2), Mark(9)];
    assert_eq!(
        replay(&mut datum, Mark(5), positions),
        Err(Call::Agree(Mark(7)))
    );
    assert_eq!(datum.calls, [
        Call::Glue(Mark(5)),
        Call::Bind(Mark(5)),
        Call::Agree(Mark(1)),
        Call::Agree(Mark(7)),
    ]);
    let mut refused = Recording::default();
    assert_eq!(
        replay(&mut refused, Mark(0), [Mark(0)]),
        Err(Call::Glue(Mark(0)))
    );
    assert_eq!(refused.calls, [Call::Glue(Mark(0))]);
}
