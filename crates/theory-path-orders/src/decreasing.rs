//! The decreasing shape of a labelled peak and the paths that close it.
//!
//! A caller labels each step by a well-founded order of its own
//! ([`LabelOrder`]). A peak is two steps from one source, `u` and `v`. Each is
//! closed by a path from its target. [`decide`] reads the two labels of the
//! peak and the labels of the two closing paths, and decides whether the
//! diagram has the decreasing shape. After `u`, the closing path is three
//! parts in sequence:
//!
//! 1. steps whose labels are below the label of `u`;
//! 2. at most one step whose label is the label of `v`;
//! 3. steps whose labels are below the label of `u` or below the label of `v`.
//!
//! The path after `v` has the mirror shape. When each local peak of a system
//! closes in this shape, the system is confluent, with no termination
//! necessary.
//!
//! The evidence ([`Shape`]) names the three parts of each path by their
//! lengths, and [`check`] replays it by the label of each step. A refusal
//! ([`Break`]) names the first step that breaks the shape. Each part is read in
//! one pass over its path: [`decide`] takes the longest first part, which
//! leaves each choice of the later parts open, so it searches nothing.
//!
//! # References
//!
//! - Vincent van Oostrom. "Confluence by Decreasing Diagrams." _Theoretical
//!   Computer Science_ 126(2), 1994, `doi:10.1016/0304-3975(92)00023-K` — the
//!   decreasing shape and the confluence theorem.
//! - Mariane Youssef. "Coherence of Algebraic Rewriting Systems by
//!   Decreasingness." Thesis, Université Claude Bernard Lyon 1, 2025,
//!   `doi:10.70675/ac84f832z1632z49d3za008zba5df4cfed2e` — the shape as five
//!   conditions (3.4.5), the systems of Example 3.3.2, and the rule labels of
//!   Examples 5.2.6 and 5.2.7.

use anodized::spec;

/// A well-founded order of the labels of the steps, given by the caller.
///
/// # Specification
/// - requires: the order is strict and well founded.
/// - ensures: whether one label is below another.
/// - panics: none.
/// - executable: none — a trait declaration; each implementation's witnesses
///   observe its order.
pub trait LabelOrder
{
    /// The labels.
    type Label: Eq;

    /// Whether `lower` is below `upper`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the strict order of the labels at the two.
    /// - panics: none.
    /// - executable: none — a trait method; implementations state theirs.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the labels 2 and 1 of two rules close each peak of
    ///   their system in the shape, and the two labels swapped do not.
    /// - witness: `tests::decreasing::the_system_with_a_loop_is_decreasing_by_the_labels_2_and_1`
    /// - witness: `tests::decreasing::the_labels_1_and_2_swapped_break_the_first_closing_step`
    fn below(
        &self,
        lower: &Self::Label,
        upper: &Self::Label,
    ) -> bool;
}

/// A labelled peak and the two paths that close it.
///
/// # Specification
/// trivial.
#[derive(Debug, Eq, PartialEq)]
pub struct Diagram<'labels, L>
{
    /// The label of the left step of the peak.
    pub left: &'labels L,
    /// The label of the right step of the peak.
    pub right: &'labels L,
    /// The labels of the path from the target of the left step, in order.
    pub left_path: &'labels [L],
    /// The labels of the path from the target of the right step, in order.
    pub right_path: &'labels [L],
}

impl<L> Clone for Diagram<'_, L>
{
    /// Copies the borrows.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn clone(&self) -> Self
    {
        *self
    }
}

impl<L> Copy for Diagram<'_, L>
{
}

/// A number of steps of a closing path: a count of steps, or the index of a
/// step from the start of its path.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Steps(usize);

impl From<usize> for Steps
{
    /// The number `steps`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(steps: usize) -> Self
    {
        Self(steps)
    }
}

impl From<Steps> for usize
{
    /// The number of steps.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(steps: Steps) -> Self
    {
        steps.0
    }
}

/// The second part of a closing path.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Middle
{
    /// No step.
    Empty,
    /// One step whose label is the label of the other step of the peak.
    Facing,
}

/// The three parts of one closing path.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct Parts
{
    /// The steps below the label of the step that the path closes.
    pub below: Steps,
    /// At most one step with the label of the other step of the peak.
    pub middle: Middle,
    /// The steps below one of the two labels of the peak.
    pub rest: Steps,
}

/// The evidence of a decreasing diagram: the parts of each closing path.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct Shape
{
    /// The parts of the path from the target of the left step.
    pub left: Parts,
    /// The parts of the path from the target of the right step.
    pub right: Parts,
}

/// One of the two closing paths.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Side
{
    /// The path from the target of the left step.
    Left,
    /// The path from the target of the right step.
    Right,
}

/// The first step that breaks the shape.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct Break
{
    /// The path that holds the step.
    pub side: Side,
    /// The index of the step in its path. It is the length of the path when the
    /// evidence names more steps than the path has.
    pub step: Steps,
}

/// What [`decide`] returns for a diagram.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Decreasing
{
    /// The diagram has the shape, with this evidence.
    Shaped(Shape),
    /// The diagram does not have the shape.
    Broken(Break),
}

/// Whether `diagram` has the decreasing shape under `order`, and the evidence
/// when it has.
///
/// # Specification
/// - requires: nothing.
/// - ensures: shaped exactly when each closing path is a first part below the
///   label of its own step, then at most one step with the label of the other
///   step, then a part below one of the two labels; the evidence is then a
///   shape that [`check`] replays.
/// - ensures: otherwise broken at the left path when it has no such parts, else
///   at the right path, at its first step past the longest first part and the
///   facing step that it can hold.
/// - panics: none.
/// - intension: one pass over each path, the first part taken longest.
///
/// # Adequacy
/// - hypothesis: L3 — the two systems of Example 3.3.2 of Youssef, the four
///   peaks of the positive braids with one label, and the system with a loop
///   under the labels 2 and 1 are each shaped with the parts the thesis draws,
///   and their evidence replays; the labels 1 and 2 swapped break the first
///   closing step. Taking a facing step before the first part, or two facing
///   steps, changes one of them.
/// - witness: `tests::decreasing::the_two_systems_of_the_first_example_are_decreasing`
/// - witness: `tests::decreasing::the_four_peaks_of_the_braids_with_one_label_are_decreasing`
/// - witness: `tests::decreasing::the_system_with_a_loop_is_decreasing_by_the_labels_2_and_1`
/// - witness: `tests::decreasing::the_labels_1_and_2_swapped_break_the_first_closing_step`
///
/// # Cost
/// - allocation: none
#[spec(ensures: |ret| match ret {
    Decreasing::Shaped(ref shape) => check(order, diagram, shape).is_ok(),
    Decreasing::Broken(_) => true,
})]
#[inline]
pub fn decide<O>(
    order: &O,
    diagram: Diagram<'_, O::Label>,
) -> Decreasing
where
    O: LabelOrder,
{
    let left = match parts(order, (diagram.left, diagram.right), diagram.left_path) {
        Ok(left) => left,
        Err(step) => {
            return Decreasing::Broken(Break {
                side: Side::Left,
                step,
            });
        },
    };
    match parts(order, (diagram.right, diagram.left), diagram.right_path) {
        Ok(right) => Decreasing::Shaped(Shape { left, right }),
        Err(step) => Decreasing::Broken(Break {
            side: Side::Right,
            step,
        }),
    }
}

/// Whether `shape` replays as the evidence that `diagram` is decreasing under
/// `order`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: holds exactly when the parts of each side sum to the length of
///   its path and each step holds in its part: below the label of its own step
///   in the first part, equal to the label of the other step in the second, and
///   below one of the two in the third.
/// - fails: at the left path, else the right, at the first step that does not
///   hold in its part, or at the length of the path when the parts are short of
///   it or name more steps than it has.
/// - panics: none.
/// - executable: none — the replay is the predicate; restating it would replay
///   again.
/// - intension: one pass over each path.
///
/// # Errors
/// As `- fails:`.
///
/// # Adequacy
/// - hypothesis: L3 — the evidence of each shaped witness replays; a first part
///   that holds a step at the label of its own step, and parts short of their
///   path, are refused at the step. Accepting a step by the part that
///   [`decide`] would give it, or reading only the steps the parts name,
///   changes one of them.
/// - witness: `tests::decreasing::the_four_peaks_of_the_braids_with_one_label_are_decreasing`
/// - witness: `tests::decreasing::a_forged_shape_is_refused_at_its_first_wrong_step`
///
/// # Cost
/// - allocation: none
#[inline]
pub fn check<O>(
    order: &O,
    diagram: Diagram<'_, O::Label>,
    shape: &Shape,
) -> Result<(), Break>
where
    O: LabelOrder,
{
    replay(
        order,
        (diagram.left, diagram.right),
        diagram.left_path,
        shape.left,
    )
    .map_err(|step| Break {
        side: Side::Left,
        step,
    })?;
    replay(
        order,
        (diagram.right, diagram.left),
        diagram.right_path,
        shape.right,
    )
    .map_err(|step| Break {
        side: Side::Right,
        step,
    })
}

/// The parts of `path`, the path that closes the step labelled `own` of a peak
/// whose other step is labelled `other`.
///
/// # Specification
/// - ensures: the longest first part below `own`, then the facing step when the
///   next label is `other`, then the rest when each of its labels is below
///   `own` or `other`; otherwise the index of the first step of the rest that
///   is below neither.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — as [`decide`].
/// - witness: `tests::decreasing::the_system_with_a_loop_is_decreasing_by_the_labels_2_and_1`
/// - witness: `tests::decreasing::the_labels_1_and_2_swapped_break_the_first_closing_step`
fn parts<O>(
    order: &O,
    (own, other): (&O::Label, &O::Label),
    path: &[O::Label],
) -> Result<Parts, Steps>
where
    O: LabelOrder,
{
    let below = path
        .iter()
        .take_while(|label| order.below(label, own))
        .count();
    let after = path.get(below ..).unwrap_or_default();
    let (middle, rest) = match after.split_first() {
        Some((label, rest)) if label == other => (Middle::Facing, rest),
        Some(_) | None => (Middle::Empty, after),
    };
    let start = below.saturating_add(usize::from(middle == Middle::Facing));
    if let Some(offset) = rest
        .iter()
        .position(|label| !order.below(label, own) && !order.below(label, other))
    {
        return Err(Steps(start.saturating_add(offset)));
    }
    Ok(Parts {
        below: Steps(below),
        middle,
        rest: Steps(rest.len()),
    })
}

/// Whether `parts` replays on `path`, the path that closes the step labelled
/// `own` of a peak whose other step is labelled `other`.
///
/// # Specification
/// - ensures: as [`check`] for one side: the index of the first step that does
///   not hold in its part, or the length of the path when the parts do not sum
///   to it, whichever comes first.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — as [`check`].
/// - witness: `tests::decreasing::a_forged_shape_is_refused_at_its_first_wrong_step`
fn replay<O>(
    order: &O,
    (own, other): (&O::Label, &O::Label),
    path: &[O::Label],
    parts: Parts,
) -> Result<(), Steps>
where
    O: LabelOrder,
{
    let below = parts.below.0;
    let rest = below.saturating_add(usize::from(parts.middle == Middle::Facing));
    let end = rest.saturating_add(parts.rest.0);
    for (index, label) in path.iter().enumerate() {
        let holds = if index < below {
            order.below(label, own)
        }
        else if index < rest {
            label == other
        }
        else if index < end {
            order.below(label, own) || order.below(label, other)
        }
        else {
            false
        };
        if !holds {
            return Err(Steps(index));
        }
    }
    if path.len() == end {
        Ok(())
    }
    else {
        Err(Steps(path.len()))
    }
}
