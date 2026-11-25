use alloc::vec::Vec;

use anodized::spec;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::GlobalIndex;

use super::CompTermFace;
use super::Elimination;
use super::ForceRefusal;
use super::Glued;
use super::Neutral;
use super::NeutralHead;
use super::TermFace;
use super::Unfolding;
use crate::arena::DomainArena;

/// A neutral headed by a manifest definition whose body is not yet forced.
///
/// # Specification
/// - requires: nothing.
/// - ensures: a spineless neutral headed by a manifest definition whose
///   unfolding face is loaded but not forced, so it is the one input state from
///   which a force succeeds.
/// - provides: the entry state the three-state force fixture below is separated
///   from.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the fixture has no input and supplies the unforced
///   boundary of the three-state transition; successful forcing records the
///   requested face and a repeated force refuses without replacing it. A rigid
///   or already-forced fixture, a nonempty spine or loss of the head changes
///   those observations.
/// - witness: `domain::tests::forcing_adds_a_reading_and_keeps_the_neutral_form`
#[spec(ensures: |ret| ret.spine.is_empty()
        && matches!(ret.head, NeutralHead::Constant(_))
        && matches!(ret.unfolding, Unfolding::Unforced(_)))]
fn unforced() -> Neutral
{
    Neutral::new(
        NeutralHead::Constant(ConstantIndex::from(3_usize)),
        Vec::new(),
        Unfolding::Unforced(GlobalIndex::from(7_u32)),
    )
}

#[test]
fn forcing_adds_a_reading_and_keeps_the_neutral_form()
{
    let mut arena = DomainArena::new();
    let first = Glued::Value(arena.value_unit(TermFace::Reduced));
    let second = Glued::Value(arena.value_unit(TermFace::Reduced));
    let mut neutral = unforced();
    let head = neutral.head();

    assert_eq!(Ok(()), neutral.force_to(first));
    assert_eq!(
        Unfolding::Forced(first),
        neutral.unfolding(),
        "the unfolded form is recorded"
    );
    assert_eq!(
        head,
        neutral.head(),
        "beside the neutral form rather than instead of it"
    );
    assert!(
        neutral.spine().is_empty(),
        "and the spine is untouched by forcing"
    );
    assert_eq!(
        Err(ForceRefusal::AlreadyForced),
        neutral.force_to(second),
        "forcing twice is refused rather than silently discarding the first result"
    );
    assert_eq!(
        Unfolding::Forced(first),
        neutral.unfolding(),
        "and the refusal kept the first result"
    );
}

#[test]
fn a_rigid_neutral_has_nothing_to_force()
{
    let mut arena = DomainArena::new();
    let glued = Glued::Value(arena.value_unit(TermFace::Reduced));
    let mut neutral = Neutral::new(
        NeutralHead::Module(ConstantIndex::from(0_usize)),
        Vec::new(),
        Unfolding::Rigid,
    );
    assert_eq!(
        Err(ForceRefusal::Rigid),
        neutral.force_to(glued),
        "a module form is rigid: no arm replaces it by a representation"
    );
    assert_eq!(
        Unfolding::Rigid,
        neutral.unfolding(),
        "and the refusal left it rigid rather than half-forced"
    );
}

#[test]
fn forcing_preserves_nonempty_spines_on_every_outcome()
{
    let mut arena = DomainArena::new();
    let argument = arena.value_unit(TermFace::Reduced);
    let first = Glued::Value(argument);
    let second = Glued::Computation(arena.comp_return(argument, CompTermFace::Reduced));
    let head = NeutralHead::Constant(ConstantIndex::from(3_usize));
    let spine = Vec::from([Elimination::Force, Elimination::Apply(argument)]);
    for (initial, result, final_face) in [
        (Unfolding::Rigid, Err(ForceRefusal::Rigid), Unfolding::Rigid),
        (
            Unfolding::Unforced(GlobalIndex::from(7_u32)),
            Ok(()),
            Unfolding::Forced(second),
        ),
        (
            Unfolding::Forced(first),
            Err(ForceRefusal::AlreadyForced),
            Unfolding::Forced(first),
        ),
    ] {
        let mut neutral = Neutral::new(head, spine.clone(), initial);
        assert_eq!(result, neutral.force_to(second));
        assert_eq!(final_face, neutral.unfolding());
        assert_eq!(head, neutral.head());
        assert_eq!(spine.as_slice(), neutral.spine());
    }
}
