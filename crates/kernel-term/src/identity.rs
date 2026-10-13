//! Inline payloads of the persisted identity nodes: the guarded program of a
//! higher field, the replay dialogues of a higher evaluation, the steps of a
//! quantified evaluation and the endpoint dialogues of a reflexivity.
//!
//! All four are untrusted data. The reader checks their framing, never their
//! meaning: a guard's evidence is checked, a cycle's productivity decided and a
//! dialogue replayed by the kernel, which owns every verdict.

/// One decision trace of the portable alphabet the universe-path evidence
/// uses; unit anchors carry no arena identity.
pub type Dialogue = alloc::vec::Vec<gandr_kernel_conversion_trace::ConversionDecision<()>>;

/// A position in a higher-field program's layer list.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct LayerPosition(pub u32);

/// The number of guard layers a higher-field observation must expose,
/// starting at identity between the two given identities.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct HigherDepth(pub u32);

/// One instruction of a guarded higher-field program.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum HigherLayer
{
    /// Expose the next evidence value, then observe identity of that evidence
    /// with itself at the tail.
    Guard
    {
        /// The layer observing the next level.
        tail: LayerPosition,
    },
    /// Follow an edge without exposing a constructor.
    Redirect(LayerPosition),
}

/// The finite syntax of a guarded higher field.
///
/// # Specification
/// - provides: the depth the kernel replays to, the root layer and the layer
///   list. The node holding this program carries one evidence value per guard
///   layer, in layer order: the guard at the `k`-th guard position exposes the
///   `k`-th evidence child.
/// - panics: none.
/// - executable: none — framing data; the reader checks positions and the
///   kernel decides productivity and evidence.
///
/// # Adequacy
/// - hypothesis: L3 — the round trip retains the depth, the root, both layer
///   kinds and their targets; an out-of-range position is a named framing
///   refusal.
/// - witness: `decode::tests::identity_nodes_round_trip_and_refuse_their_malformed_sites`
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct HigherProgram
{
    /// Constructor layers the kernel replays; zero is refused at checking.
    pub depth: HigherDepth,
    /// The first layer observed.
    pub root: LayerPosition,
    /// The layers; every position names one of them.
    pub layers: alloc::vec::Vec<HigherLayer>,
}

impl HigherProgram
{
    /// Stream the canonical inline payload without allocating an image.
    ///
    /// # Specification
    /// - requires: nothing; the program is still untrusted.
    /// - ensures: the depth, the root, the layer count, then per layer its kind
    ///   word — [`crate::HIGHER_GUARD`] or [`crate::HIGHER_REDIRECT`] —
    ///   followed by its target position.
    /// - provides: identical payload content for the wire and memo encoders.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — framing is a law of subsequent iterator
    ///   consumption; checking the opaque iterator here would consume it.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the round trip retains depth, root, layer order, both
    ///   kinds and every target.
    /// - witness: `decode::tests::identity_nodes_round_trip_and_refuse_their_malformed_sites`
    #[inline]
    pub fn words(&self) -> impl Iterator<Item = crate::EvidenceWord> + '_
    {
        [
            crate::EvidenceWord(u64::from(self.depth.0)),
            crate::EvidenceWord(u64::from(self.root.0)),
            crate::EvidenceWord(u64::from(crate::wire::WireU64::from(
                crate::wire::WireUsize::from(self.layers.len()),
            ))),
        ]
        .into_iter()
        .chain(self.layers.iter().flat_map(|layer| {
            let (kind, target) = match *layer {
                | HigherLayer::Guard { tail } => (crate::HIGHER_GUARD, tail),
                | HigherLayer::Redirect(target) => (crate::HIGHER_REDIRECT, target),
            };
            [
                crate::EvidenceWord(u64::from(u8::from(kind))),
                crate::EvidenceWord(u64::from(target.0)),
            ]
        }))
    }
}

/// Stream a higher evaluation's canonical inline payload without allocating
/// an image.
///
/// # Specification
/// - requires: nothing; the dialogues are still untrusted.
/// - ensures: the component count, then per component its left and its right
///   dialogue, each as a decision count followed by the decision words of the
///   universe-path evidence alphabet.
/// - provides: identical payload content for the wire and memo encoders.
/// - fails: never.
/// - panics: none.
/// - executable: none — framing is a law of subsequent iterator consumption;
///   checking the opaque iterator here would consume it.
///
/// # Adequacy
/// - hypothesis: L3 — the round trip retains component boundaries, sides and
///   every decision.
/// - witness: `decode::tests::identity_nodes_round_trip_and_refuse_their_malformed_sites`
#[inline]
pub fn evaluation_words(
    dialogues: &[EvaluationDialogues]
) -> impl Iterator<Item = crate::EvidenceWord> + '_
{
    let count = |length: usize| {
        crate::EvidenceWord(u64::from(crate::wire::WireU64::from(
            crate::wire::WireUsize::from(length),
        )))
    };
    core::iter::once(count(dialogues.len())).chain(dialogues.iter().flat_map(move |component| {
        [&component.left, &component.right]
            .into_iter()
            .flat_map(move |dialogue| {
                core::iter::once(count(dialogue.len()))
                    .chain(dialogue.iter().copied().map(crate::term::decision_word))
            })
    }))
}

/// The two replay dialogues of one higher-evaluation component.
#[derive(Clone, Debug, Default, Eq, Hash, PartialEq)]
pub struct EvaluationDialogues
{
    /// Certifies that the left function returns the component's left value.
    pub left: Dialogue,
    /// Certifies that the right function returns the component's right value.
    pub right: Dialogue,
}

/// The three value children of one higher-evaluation component.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct EvaluationComponent
{
    /// The value the left function returns at the component's pattern.
    pub left: crate::ValueId,
    /// The value the right function returns at the component's pattern.
    pub right: crate::ValueId,
    /// An inhabitant of the output identity between the two.
    pub evidence: crate::ValueId,
}

/// One step of a quantified evaluation.
///
/// The steps run in the pre-order of the tree the kernel's coverage
/// generates: a return closes a branch, an application opens one branch per
/// covering pattern of the applied function's result relation.
///
/// # Specification
/// - provides: the step's kind and its two untrusted dialogues. A return owes
///   three value children — the two returned values and their output evidence —
///   and its dialogues certify that each side returns its value. An application
///   owes two, the closed normal form each side reaches, stuck at an
///   application of the function the premise at `fibre` relates; its dialogues
///   certify that each side converts to its normal form.
/// - panics: none.
/// - executable: none — framing data; the kernel regenerates the tree from its
///   coverage and replays every dialogue.
///
/// # Adequacy
/// - hypothesis: L3 — the round trip retains step kinds, fibres, sides and
///   every decision; a fibre word past the index range is a named framing
///   refusal.
/// - witness: `decode::tests::identity_nodes_round_trip_and_refuse_their_malformed_sites`
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum QuantifiedStep
{
    /// Both sides return; three value children follow.
    Return(EvaluationDialogues),
    /// Both sides apply the functions the premise at `fibre` relates; two
    /// value children follow.
    Apply
    {
        /// The premise's de Bruijn index in the step's telescope.
        fibre: crate::DeBruijnIndex,
        /// Certifies each side's claim against its stuck normal form.
        dialogues: EvaluationDialogues,
    },
}

impl QuantifiedStep
{
    /// The step's two dialogues.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn dialogues(&self) -> &EvaluationDialogues
    {
        match *self {
            | Self::Return(ref dialogues) | Self::Apply { ref dialogues, .. } => dialogues,
        }
    }
}

/// Stream a quantified evaluation's canonical inline payload without
/// allocating an image.
///
/// # Specification
/// - requires: nothing; the steps are still untrusted.
/// - ensures: the step count, then per step its step word — zero for a return,
///   one more than the fibre's index for an application — and its left and
///   right dialogue, each as a decision count followed by the decision words of
///   the universe-path evidence alphabet.
/// - provides: identical payload content for the wire and memo encoders.
/// - fails: never.
/// - panics: none.
/// - executable: none — framing is a law of subsequent iterator consumption;
///   checking the opaque iterator here would consume it.
///
/// # Adequacy
/// - hypothesis: L3 — the round trip retains step boundaries, kinds, fibres,
///   sides and every decision.
/// - witness: `decode::tests::identity_nodes_round_trip_and_refuse_their_malformed_sites`
#[inline]
pub fn quantified_words(steps: &[QuantifiedStep])
-> impl Iterator<Item = crate::EvidenceWord> + '_
{
    let count = |length: usize| {
        crate::EvidenceWord(u64::from(crate::wire::WireU64::from(
            crate::wire::WireUsize::from(length),
        )))
    };
    core::iter::once(count(steps.len())).chain(steps.iter().flat_map(move |step| {
        let kind = match *step {
            | QuantifiedStep::Return(_) => crate::EvidenceWord(0),
            | QuantifiedStep::Apply { fibre, .. } => {
                crate::EvidenceWord(u64::from(u32::from(fibre)).saturating_add(1))
            },
        };
        let dialogues = step.dialogues();
        core::iter::once(kind).chain([&dialogues.left, &dialogues.right].into_iter().flat_map(
            move |dialogue| {
                core::iter::once(count(dialogue.len()))
                    .chain(dialogue.iter().copied().map(crate::term::decision_word))
            },
        ))
    }))
}

/// The two replay dialogues of a reflexivity: its point against each endpoint
/// of the identity it is checked at.
///
/// # Specification
/// - provides: the conversion trace the checker kept between the point and the
///   left endpoint, then the right one; empty where the two are the same term.
/// - panics: none.
/// - executable: none — framing data; the kernel replays each dialogue and owns
///   the verdict.
///
/// # Adequacy
/// - hypothesis: L3 — the round trip retains both sides and every decision, and
///   a dialogue naming an unfolding the endpoint does not hold is refused by
///   the kernel's replay.
/// - witness: `decode::tests::identity_nodes_round_trip_and_refuse_their_malformed_sites`
#[derive(Clone, Debug, Default, Eq, Hash, PartialEq)]
pub struct EndpointDialogues
{
    /// Certifies that the point converts with the left endpoint.
    pub left: Dialogue,
    /// Certifies that the point converts with the right endpoint.
    pub right: Dialogue,
}

/// Stream a reflexivity's canonical inline payload without allocating an
/// image.
///
/// # Specification
/// - requires: nothing; the dialogues are still untrusted.
/// - ensures: the left dialogue, then the right, each as a decision count
///   followed by the decision words of the universe-path evidence alphabet.
/// - provides: identical payload content for the wire and memo encoders.
/// - fails: never.
/// - panics: none.
/// - executable: none — framing is a law of subsequent iterator consumption;
///   checking the opaque iterator here would consume it.
///
/// # Adequacy
/// - hypothesis: L3 — the round trip retains both sides, an empty dialogue
///   beside a non-empty one, and every decision.
/// - witness: `decode::tests::identity_nodes_round_trip_and_refuse_their_malformed_sites`
#[inline]
pub fn endpoint_words(
    dialogues: &EndpointDialogues
) -> impl Iterator<Item = crate::EvidenceWord> + '_
{
    [&dialogues.left, &dialogues.right]
        .into_iter()
        .flat_map(|dialogue| {
            core::iter::once(crate::EvidenceWord(u64::from(crate::wire::WireU64::from(
                crate::wire::WireUsize::from(dialogue.len()),
            ))))
            .chain(dialogue.iter().copied().map(crate::term::decision_word))
        })
}
