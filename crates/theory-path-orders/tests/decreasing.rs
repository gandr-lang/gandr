//! The decreasing shape of the labelled diagrams of Youssef's thesis, and the
//! replay of their evidence.

use gandr_theory_path_orders::decreasing::Break;
use gandr_theory_path_orders::decreasing::Decreasing;
use gandr_theory_path_orders::decreasing::Diagram;
use gandr_theory_path_orders::decreasing::LabelOrder;
use gandr_theory_path_orders::decreasing::Middle;
use gandr_theory_path_orders::decreasing::Parts;
use gandr_theory_path_orders::decreasing::Shape;
use gandr_theory_path_orders::decreasing::Side;
use gandr_theory_path_orders::decreasing::Steps;
use gandr_theory_path_orders::decreasing::check;
use gandr_theory_path_orders::decreasing::decide;

/// A label: a natural number.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Label(u8);

/// The natural numbers in their order.
#[derive(Clone, Copy, Debug)]
struct Naturals;

impl LabelOrder for Naturals
{
    type Label = Label;

    /// Whether `lower` is a smaller number than `upper`.
    ///
    /// # Specification
    /// trivial.
    fn below(
        &self,
        lower: &Label,
        upper: &Label,
    ) -> bool
    {
        lower.0 < upper.0
    }
}

/// The parts of a closing path: `below` steps, the facing step when `facing`,
/// and `rest` steps.
///
/// # Specification
/// trivial.
fn parts(
    below: usize,
    facing: bool,
    rest: usize,
) -> Parts
{
    Parts {
        below: Steps::from(below),
        middle: if facing {
            Middle::Facing
        }
        else {
            Middle::Empty
        },
        rest: Steps::from(rest),
    }
}

/// The diagram of the peak `(left, right)` closed by the two paths, and the
/// shape `decide` gives it, which `check` replays.
///
/// # Specification
/// - ensures: the verdict of `decide`.
/// - panics: when a shape that `decide` gives does not replay.
fn decided(
    (left, right): (Label, Label),
    left_path: &[Label],
    right_path: &[Label],
) -> Decreasing
{
    let diagram = Diagram {
        left: &left,
        right: &right,
        left_path,
        right_path,
    };
    let verdict = decide(&Naturals, diagram);
    if let Decreasing::Shaped(ref shape) = verdict {
        assert_eq!(
            check(&Naturals, diagram, shape),
            Ok(()),
            "the shape replays"
        );
    }
    verdict
}

/// Example 3.3.2: in `X`, `v : y → x` has the label 2, `u : x → y` the label
/// 1, and `v' : y → b` the label 0. `Y` adds `u' : x → a` with the label 1 and
/// `w : a → b` with the label 0. Example 3.4.18 closes each local peak.
#[test]
fn the_two_systems_of_the_first_example_are_decreasing()
{
    // The peak `(v', v)` at `y`, in `X` and in `Y`: `v'` is closed by no step,
    // and `v` by `u` then `v'`, each below 2.
    assert_eq!(
        decided((Label(0), Label(2)), &[], &[Label(1), Label(0)]),
        Decreasing::Shaped(Shape {
            left: parts(0, false, 0),
            right: parts(2, false, 0),
        })
    );
    // The peak `(u, u')` at `x`, in `Y`: `u` is closed by `v'`, and `u'` by
    // `w`, each below 1.
    assert_eq!(
        decided((Label(1), Label(1)), &[Label(0)], &[Label(0)]),
        Decreasing::Shaped(Shape {
            left: parts(1, false, 0),
            right: parts(1, false, 0),
        })
    );
}

/// Example 5.2.6: the positive braids on three strands with `α : sts ⇒ tst`
/// and `β : tst ⇒ sts`, each with the label 1. Each of the four critical peaks
/// closes by one step on each side, each step the facing step of its side.
#[test]
fn the_four_peaks_of_the_braids_with_one_label_are_decreasing()
{
    let one = Label(1);
    // `(αt, sβ)` on `stst`, closed by `βt` and `sα`; `(βs, tα)` on `tsts`,
    // closed by `αs` and `tβ`; `(αts, stβ)` on `ststs`, closed by `βts` and
    // `stα`; `(βst, tsα)` on `tstst`, closed by `αst` and `tsβ`.
    for peak in ["stst", "tsts", "ststs", "tstst"] {
        assert_eq!(
            decided((one, one), &[one], &[one]),
            Decreasing::Shaped(Shape {
                left: parts(0, true, 0),
                right: parts(0, true, 0),
            }),
            "the peak on {peak}"
        );
    }
}

/// Example 5.2.7: `α : a² ⇒ ab` with the label 2 and `β : ba ⇒ a²` with the
/// label 1, a system with the loop `a³ ⇒ aba ⇒ a³`.
#[test]
fn the_system_with_a_loop_is_decreasing_by_the_labels_2_and_1()
{
    let (alpha, beta) = (Label(2), Label(1));
    // `(αa, aα)` on `a³`: `αa` is closed by `aβ`, below 2, then `aα`, the
    // facing step; `aα` is closed by no step.
    assert_eq!(
        decided((alpha, alpha), &[beta, alpha], &[]),
        Decreasing::Shaped(Shape {
            left: parts(1, true, 0),
            right: parts(0, false, 0),
        })
    );
    // `(βa, bα)` on `ba²`: `βa` is closed by `aα`, the facing step; `bα` is
    // closed by `βb`, below 2.
    assert_eq!(
        decided((beta, alpha), &[alpha], &[beta]),
        Decreasing::Shaped(Shape {
            left: parts(0, true, 0),
            right: parts(1, false, 0),
        })
    );
}

/// The system of Example 5.2.7 under the swapped labels, `α` with 1 and `β`
/// with 2: the first closing step of the peak on `a³`, `aβ`, is below neither
/// label 1 of the peak and is not the facing step.
#[test]
fn the_labels_1_and_2_swapped_break_the_first_closing_step()
{
    let (alpha, beta) = (Label(1), Label(2));
    assert_eq!(
        decided((alpha, alpha), &[beta, alpha], &[]),
        Decreasing::Broken(Break {
            side: Side::Left,
            step: Steps::from(0_usize),
        })
    );
    // The peak on `ba²` keeps its shape: `aα` is below 2, and `βb` is the
    // facing step.
    assert_eq!(
        decided((beta, alpha), &[alpha], &[beta]),
        Decreasing::Shaped(Shape {
            left: parts(1, false, 0),
            right: parts(0, true, 0),
        })
    );
}

/// A shape that puts the facing step of a braid peak in the first part is
/// refused at that step, and a shape that names fewer steps than the path has
/// is refused at the first step that it does not name.
#[test]
fn a_forged_shape_is_refused_at_its_first_wrong_step()
{
    let one = Label(1);
    let diagram = Diagram {
        left: &one,
        right: &one,
        left_path: &[one],
        right_path: &[one],
    };
    let facing = parts(0, true, 0);
    assert_eq!(
        check(&Naturals, diagram, &Shape {
            left: facing,
            right: parts(1, false, 0),
        }),
        Err(Break {
            side: Side::Right,
            step: Steps::from(0_usize),
        })
    );
    assert_eq!(
        check(&Naturals, diagram, &Shape {
            left: parts(0, false, 0),
            right: facing,
        }),
        Err(Break {
            side: Side::Left,
            step: Steps::from(0_usize),
        })
    );
    let (alpha, beta) = (Label(2), Label(1));
    assert_eq!(
        check(
            &Naturals,
            Diagram {
                left: &alpha,
                right: &alpha,
                left_path: &[beta, alpha],
                right_path: &[],
            },
            &Shape {
                left: parts(1, false, 0),
                right: parts(0, false, 0),
            }
        ),
        Err(Break {
            side: Side::Left,
            step: Steps::from(1_usize),
        })
    );
}
