//! Holds at the kernel boundary. The kernel has no store, so a hold crosses
//! as its state-passing reduct: the reduct passes the held value along the
//! spine of the hold's block as a value, and the kernel types the reduct.
//!
//! An exclusive access answers its result beside the value its view leaves in
//! the place, and the rest of the block reads that value. A shared access
//! reads the held value. A consuming read answers it. The reduct keeps no
//! linear binder of a slot: the checker alone decides linear use, and the
//! reduct relies on its verdict that each view ends once on each path. The
//! end of a session that a fork opens is no slot: the reduct keeps its
//! binder, and each form that reads no slot keeps its form.
//!
//! The reduct covers the lexical case: each access stands on the spine of a
//! block that holds its slot, at the whole place, and each read of a slot
//! stands in a step's own values, under no binder. A block may end in a case,
//! and a step may bind a case or a block. The reduct reads each arm, or the
//! bound block, as a block beneath the same slots. A slot that the frame reads
//! after the form is fixed there: the form may read it and may not write it.
//! So no arm answers the value it leaves, and the case keeps its motive. Any
//! other form refuses the hold whole, as [`UnadmittedFormer::Memory`].
//!
//! The reduct reads one block at a time on an explicit stack of frames: a
//! nested hold, an access's body, a bound block and each arm of a case open
//! a frame, and its end gives its reduct to the frame below.
//!
//! # References
//!
//! - `vault:01a178aa-6917-7983-b5cd-86e2af86b3ec` — anchor: memory crosses by
//!   simulation, a pure translation that the kernel types, never an erasure.

use alloc::collections::BTreeMap;
use alloc::vec::Vec;

use anodized::spec;
use gandr_core_term::Binders;
use gandr_core_term::ComponentCount;
use gandr_core_term::ComputationId;
use gandr_core_term::CoreArena;
use gandr_core_term::SplitMotive;
use gandr_core_term::ValueId;
use gandr_core_term::ValueTypeId;
use gandr_core_term::Zone;
use gandr_core_term::memory::AccessMode;
use gandr_core_term::memory::MemoryForm;
use gandr_core_term::memory::Place;
use gandr_core_term::primitive::Arguments;
use gandr_core_term::session::SessionAction;
use gandr_kernel_term::Component;
use gandr_kernel_term::DeBruijnIndex;

use super::Computation;
use super::CoreNode;
use super::Erasure;
use super::Refusal;
use super::TermNode;
use super::UnadmittedFormer;
use super::Value;

/// A value of the reduct and the reduct's binders above where it was read.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Read
{
    /// The value.
    value: ValueId,
    /// The binders above it where it was read.
    depth: Binders,
}

/// What one linear binder of the block stands for in the reduct.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Slot
{
    /// A hold: the value it holds now. A frozen hold is one a nested block
    /// reads and does not write.
    Held
    {
        /// The held value now.
        now: Read,
        /// Whether the block under translation may not write it.
        frozen: bool,
    },
    /// A view an access lends of a hold's whole value.
    View
    {
        /// The value of the place now.
        now: Read,
        /// The unwind of an exclusive access and the depth the access stands
        /// at; none for a shared one.
        unwind: Option<Read>,
    },
    /// A linear binder the block opens that is no slot: the end of a
    /// session a fork opens. The reduct keeps the binder and each read of
    /// it, so such binders stand innermost, past every slot.
    Kept,
}

/// The place of a slot among a block's slots, counted from the outermost.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Position(usize);

/// Whether a node reads a slot of its block.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Reads
{
    /// It reads none: each linear binder it reads is one the reduct keeps.
    Nothing,
    /// It reads a slot, or a linear binder outside the hold.
    Linear,
}

/// What the reduct of a block answers at its end.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Ending
{
    /// The block answers its own result.
    Plain,
    /// The block is an exclusive access's body: it answers its result beside
    /// the value its view, the innermost slot, leaves in the place.
    Paired,
}

/// One step of a spine the reduct put in front of the rest, innermost last.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Wrap
{
    /// `y ← bound; rest`.
    Bind(ComputationId),
    /// `p ← bound; s ← p.1; y ← p.0; rest`: an exclusive access's body, which
    /// answers its result beside the value it leaves.
    Paired(ComputationId),
    /// A split of `arity` components of `scrutinee` around the rest.
    Split
    {
        /// The value split.
        scrutinee: ValueId,
        /// The components it binds.
        arity: ComponentCount,
    },
    /// `let d = fork (c : protocol) { child }; rest`: the rest runs under
    /// the parent's end, a binder the reduct keeps.
    Fork
    {
        /// The session type of the child's end.
        protocol: ValueTypeId,
        /// The child, which reads no slot.
        child: ComputationId,
    },
}

/// What a block's reduct becomes in the block that holds it.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Resume
{
    /// The block is the hold's own, and its reduct is the hold's.
    Root,
    /// The block is a nested hold's or a shared access's body: the step
    /// `y ← reduct; rest`.
    Bind
    {
        /// The rest of the spine past the step.
        rest: ComputationId,
    },
    /// The block is an exclusive access's body: the steps `p ← reduct; s ←
    /// p.1; y ← p.0; rest`, and the slot at `position` holds `s` past them.
    Paired
    {
        /// The rest of the spine past the access.
        rest: ComputationId,
        /// The hold the access writes.
        position: Position,
    },
    /// The block is an arm of a case, under `lambdas` binders of its fields
    /// and equations: its reduct, under as many lambdas, is the arm of the
    /// case the frame below reads.
    Arm
    {
        /// The binders the arm's body stands under.
        lambdas: ComponentCount,
    },
}

/// What the reduct of a case becomes in the frame that reads it.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Then
{
    /// The case ends the frame's spine.
    Tail,
    /// The case is the bound of the step `y ← case; rest`.
    Bound
    {
        /// The rest of the spine past the step.
        rest: ComputationId,
    },
}

/// A case whose arms the reduct reads one at a time.
#[derive(Clone, Debug, Eq, PartialEq)]
struct Pending
{
    /// The case as written, which a derivation of the match names.
    origin: ComputationId,
    /// The case the reduct reads: the form the judgement checked it in.
    at: ComputationId,
    /// The reduct of its scrutinee.
    scrutinee: ValueId,
    /// The reducts of the arms read so far, in tag order.
    arms: Vec<ComputationId>,
    /// The slots each arm reads.
    slots: Vec<Slot>,
    /// The reduct's binders above the case.
    depth: Binders,
    /// What the case's reduct becomes.
    then: Then,
}

/// A block under translation: the spine still to read and the steps read
/// so far.
#[derive(Clone, Debug, Eq, PartialEq)]
struct Frame
{
    /// The node of the spine to read next.
    current: ComputationId,
    /// The reduct's binders above `current`.
    depth: Binders,
    /// The steps read so far, innermost last.
    wraps: Vec<Wrap>,
    /// The linear binders the block reads, innermost last.
    slots: Vec<Slot>,
    /// What the block answers at its end.
    ending: Ending,
    /// What its reduct becomes in the block that holds it.
    resume: Resume,
    /// The case the frame waits for while the reduct reads its arms.
    pending: Option<Pending>,
}

/// What one node of a frame's spine asks of the reduct.
#[derive(Clone, Debug, Eq, PartialEq)]
enum Advance
{
    /// The frame read the node and stands at the next one.
    Stepped,
    /// The node opens a block, and the frame waits for its reduct.
    Entered(Frame),
    /// The spine ended, with the block's reduct.
    Ended(ComputationId),
}

/// One turn of the walk that reads the slots of a value.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Visit
{
    /// Read the value.
    Enter(ValueId),
    /// Build a tuple of the last `count` values read.
    Tuple(usize),
}

/// The state-passing reduct of one hold, minted into `arena`.
struct Reduct<'arena>
{
    /// The arena the hold's nodes resolve in and the reduct is minted into.
    arena: &'arena mut CoreArena,
    /// The hold's node, which a refusal names.
    at: ComputationId,
    /// The nodes the judgement checked in another form than written,
    /// ascending, each beside the node checked in its place.
    restated: &'arena [(TermNode, TermNode)],
    /// Each case the reduct rebuilds, beside its rebuilt node, so the
    /// derivation of the match crosses at the rebuilt case.
    rebuilt: &'arena mut BTreeMap<ComputationId, ComputationId>,
}

impl Erasure<'_, '_>
{
    /// The computation a hold is erased to, minted into the source arena: its
    /// state-passing reduct.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: for `hold x = v; t`, the block `t` read along its spine with
    ///   each read of `x` as the value `x` holds there, `v` first: a step whose
    ///   values read a slot runs with those reads replaced; an exclusive access
    ///   `access x as w { b } unwind { u }; K` runs as `p ← b′; s ← p.1; y ←
    ///   p.0; K′`, where `b′` is `b` read along its spine with `w` as the held
    ///   value, `resume w v′` making `v′` the value it leaves and answering the
    ///   unit, `abort w` running `u` and leaving the held value, its end
    ///   answering its result beside the value left, and `K′` reads `s` for
    ///   `x`; a shared access runs its body with the view and `x` as the held
    ///   value; a consuming read answers the held value; a split of no
    ///   components at the ambient motive is its body; a hold on the spine is
    ///   its own reduct, reading the outer holds and writing none; a case at
    ///   the spine's end, or bound by a step, is the case of its arms' reducts
    ///   at its motive, each arm read beneath the slots, each slot the frame
    ///   reads after the case fixed; a bound block is its own reduct beneath
    ///   the same fixed slots; a fork runs its parent as the rest of the spine
    ///   past the end it keeps. The result has no memory form, and its only
    ///   linear variables are the ends of its forks.
    /// - fails: [`Refusal::OutOfFragment`] naming [`UnadmittedFormer::Memory`]
    ///   at the hold for any other form: an access off a spine or at an index,
    ///   a read of a slot under a binder or in a form the reduct does not read,
    ///   a write of a frozen hold or a fixed slot, an unwind that reads a
    ///   linear binder, a fork's child that reads a slot, a hold or an access
    ///   past a fork's end, a linear variable of a binder outside the hold;
    ///   [`Refusal::DanglingNode`] for an absent node.
    /// - panics: none.
    ///
    /// # Errors
    /// As `- fails:`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a hold whose exclusive accesses resume and abort, a
    ///   hold read beside a shared view, and a hold whose view is read under a
    ///   thunk distinguish the state each step reads, the pair an access
    ///   answers and the refusal of a form the reduct does not read; a reduct
    ///   whose access leaves the wrong value is the kernel's rejection. A hold
    ///   read across a case at a spine's end, across a case a step binds, past
    ///   a fork's end and after a case distinguish each arm's reading; a write
    ///   the rest reads after a case is refused, and an arm forged to answer
    ///   the wrong value is the kernel's rejection.
    /// - witness: `bridge::tests::a_lexical_hold_crosses_as_its_state_passing_reduct_6609`
    /// - witness: `bridge::tests::a_hold_read_under_a_thunk_is_refused_by_name_6609`
    /// - witness: `bridge::tests::a_reduct_leaving_the_wrong_value_is_the_kernel_s_rejection_6609`
    /// - witness: `bridge::tests::a_hold_read_across_a_case_s_arms_crosses_as_its_reduct_6641`
    /// - witness: `bridge::tests::a_write_the_rest_reads_after_a_case_is_refused_by_name_6641`
    /// - witness: `bridge::tests::an_arm_answering_the_wrong_value_is_the_kernel_s_rejection_6641`
    #[spec(ensures: |ret| match ret {
        | Ok(reduct) => self.arena.computation(reduct).is_some(),
        | Err(Refusal::OutOfFragment { at: site, former: UnadmittedFormer::Memory }) =>
            site == CoreNode::Term(TermNode::Computation(at)),
        | Err(Refusal::DanglingNode { .. }) => true,
        | Err(_) => false,
    })]
    pub(super) fn hold_reduct(
        &mut self,
        at: ComputationId,
    ) -> Result<ComputationId, Refusal>
    {
        Reduct {
            arena: self.arena,
            at,
            restated: self.restated,
            rebuilt: &mut self.rebuilt,
        }
        .reduce()
    }
}

/// The slots `slots` as a nested block reads them: each hold frozen.
///
/// # Specification
/// trivial.
fn frozen(slots: &[Slot]) -> Vec<Slot>
{
    slots
        .iter()
        .map(|&slot| match slot {
            Slot::Held { now, .. } => Slot::Held { now, frozen: true },
            kept @ (Slot::View { .. } | Slot::Kept) => kept,
        })
        .collect()
}

/// `slot` held fixed: a hold frozen, a view shared, so a block may read it
/// and may not write it.
///
/// # Specification
/// trivial.
const fn pinned(slot: Slot) -> Slot
{
    match slot {
        Slot::Held { now, .. } => Slot::Held { now, frozen: true },
        Slot::View { now, .. } => Slot::View { now, unwind: None },
        Slot::Kept => Slot::Kept,
    }
}

/// `frame` past the step `y ← bound`, standing at `rest`.
///
/// # Specification
/// trivial.
fn stepped(
    frame: &mut Frame,
    bound: ComputationId,
    rest: ComputationId,
) -> Advance
{
    frame.wraps.push(Wrap::Bind(bound));
    frame.depth = frame.depth.deeper();
    frame.current = rest;
    Advance::Stepped
}

impl Reduct<'_>
{
    /// The refusal of the hold the reduct is of.
    ///
    /// # Specification
    /// trivial.
    const fn refused(&self) -> Refusal
    {
        Refusal::OutOfFragment {
            at: CoreNode::Term(TermNode::Computation(self.at)),
            former: UnadmittedFormer::Memory,
        }
    }

    /// The reduct of the hold, read one block at a time on a stack of frames.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: as [`Erasure::hold_reduct`].
    /// - fails: as [`Erasure::hold_reduct`].
    /// - panics: none.
    /// - executable: none — the clause names the reduct's reading of each
    ///   block, which the witnesses of [`Erasure::hold_reduct`] observe.
    ///
    /// # Errors
    /// As `- fails:`.
    ///
    /// # Termination
    /// - reason: the `loop` over the frames, and the `while` that resumes the
    ///   frames below a frame that ended.
    /// - measure: the nodes not yet read. Each turn reads one node of a spine,
    ///   opens a frame on a strict subterm, or ends frames; each frame that
    ///   ends leaves the stack. The arena is finite and acyclic.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Erasure::hold_reduct`].
    /// - witness: `bridge::tests::a_lexical_hold_crosses_as_its_state_passing_reduct_6609`
    /// - witness: `bridge::tests::a_hold_read_under_a_thunk_is_refused_by_name_6609`
    /// - witness: `bridge::tests::a_hold_read_across_a_case_s_arms_crosses_as_its_reduct_6641`
    fn reduce(&mut self) -> Result<ComputationId, Refusal>
    {
        let at = self.at;
        let mut frames = Vec::from([self.entered(at, &[], Binders::NONE, Resume::Root)?]);
        loop {
            let Some(frame) = frames.last_mut()
            else {
                return Err(self.refused());
            };
            let mut advance = self.advance(frame)?;
            // A block that ends resumes the frame below it, which may end in
            // turn: a case's last arm ends the frame whose spine it ends.
            while let Advance::Ended(reduct) = advance {
                let Some(ended) = frames.pop()
                else {
                    return Err(self.refused());
                };
                let Some(outer) = frames.last_mut()
                else {
                    return match ended.resume {
                        Resume::Root => Ok(reduct),
                        Resume::Bind { .. } | Resume::Paired { .. } | Resume::Arm { .. } => {
                            Err(self.refused())
                        },
                    };
                };
                advance = self.resumed(outer, ended.resume, reduct)?;
            }
            if let Advance::Entered(inner) = advance {
                frames.push(inner);
            }
        }
    }

    /// The frame of the hold `at`'s block beneath `slots` and `depth` of the
    /// reduct's binders: one slot more, holding the hold's value, and each
    /// outer hold frozen.
    ///
    /// # Specification
    /// - requires: `at` stands beneath the linear binders `slots` names,
    ///   innermost last, and `depth` binders of the reduct.
    /// - ensures: a frame at the hold's block that ends as `resume` asks.
    /// - fails: as [`Erasure::hold_reduct`] for the hold's value;
    ///   [`Refusal::DanglingNode`] when `at` is no hold.
    /// - panics: none.
    /// - executable: none — the clause names the frame's reading of the block,
    ///   which the witnesses of [`Erasure::hold_reduct`] observe.
    ///
    /// # Errors
    /// As `- fails:`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Erasure::hold_reduct`].
    /// - witness: `bridge::tests::a_lexical_hold_crosses_as_its_state_passing_reduct_6609`
    fn entered(
        &mut self,
        at: ComputationId,
        slots: &[Slot],
        depth: Binders,
        resume: Resume,
    ) -> Result<Frame, Refusal>
    {
        let Some(&Computation::Memory(MemoryForm::Hold { value, body, .. })) =
            self.arena.computation(at)
        else {
            return Err(Refusal::DanglingNode {
                node: CoreNode::Term(TermNode::Computation(at)),
            });
        };
        let held = self.value(value, slots, depth)?;
        // A kept binder stands past every slot, so no hold opens past one.
        if matches!(slots.last(), Some(&Slot::Kept)) {
            return Err(self.refused());
        }
        let mut inner = frozen(slots);
        inner.push(Slot::Held {
            now: Read { value: held, depth },
            frozen: false,
        });
        Ok(Frame {
            current: body,
            depth,
            wraps: Vec::new(),
            slots: inner,
            ending: Ending::Plain,
            resume,
            pending: None,
        })
    }

    /// `outer` past the block whose reduct is `reduct`, as `resume` asks.
    ///
    /// # Specification
    /// - requires: `outer` holds the block that ended.
    /// - ensures: for [`Resume::Bind`], `outer` past `y ← reduct`; for
    ///   [`Resume::Paired`], `outer` past `p ← reduct; s ← p.1; y ← p.0`, its
    ///   rest raised past `p` and `s`, and the written hold holding `s`; for
    ///   [`Resume::Arm`], `reduct` under its lambdas as the next arm of the
    ///   case `outer` waits for, and `outer` as [`Self::arms`] leaves it.
    /// - fails: [`Refusal::OutOfFragment`] naming [`UnadmittedFormer::Memory`]
    ///   at the hold for [`Resume::Root`], a position past the slots, or an arm
    ///   with no case to wait for; as [`Self::arms`] for an arm.
    /// - panics: none.
    /// - executable: none — the clause names the reduct's steps, which the
    ///   witnesses of [`Erasure::hold_reduct`] observe.
    ///
    /// # Errors
    /// As `- fails:`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Erasure::hold_reduct`].
    /// - witness: `bridge::tests::a_lexical_hold_crosses_as_its_state_passing_reduct_6609`
    /// - witness: `bridge::tests::a_reduct_leaving_the_wrong_value_is_the_kernel_s_rejection_6609`
    /// - witness: `bridge::tests::a_hold_read_across_a_case_s_arms_crosses_as_its_reduct_6641`
    fn resumed(
        &mut self,
        outer: &mut Frame,
        resume: Resume,
        reduct: ComputationId,
    ) -> Result<Advance, Refusal>
    {
        match resume {
            Resume::Root => Err(self.refused()),
            Resume::Bind { rest } => Ok(stepped(outer, reduct, rest)),
            Resume::Paired { rest, position } => {
                // The rest reads `s` for the hold: `p` and `s` stand outside
                // the rest's own binder `y`.
                let rest = gandr_core_term::shift_computation_under(
                    self.arena,
                    rest,
                    Binders::ONE,
                    Binders::from(2_u32),
                )
                .settle(self.arena);
                let left = self.variable(DeBruijnIndex::from(0_u32));
                let written = outer.depth.beyond(Binders::from(2_u32));
                let Some(slot) = outer.slots.get_mut(position.0)
                else {
                    return Err(self.refused());
                };
                *slot = Slot::Held {
                    now: Read {
                        value: left,
                        depth: written,
                    },
                    frozen: false,
                };
                outer.wraps.push(Wrap::Paired(reduct));
                outer.depth = outer.depth.beyond(Binders::from(3_u32));
                outer.current = rest;
                Ok(Advance::Stepped)
            },
            Resume::Arm { lambdas } => {
                let mut arm = reduct;
                for _ in 0 .. usize::from(lambdas) {
                    arm = self.arena.computation_lambda(arm);
                }
                let Some(mut pending) = outer.pending.take()
                else {
                    return Err(self.refused());
                };
                pending.arms.push(arm);
                self.arms(outer, pending)
            },
        }
    }

    /// `frame` past the node it stands at.
    ///
    /// # Specification
    /// - requires: `frame` stands beneath its slots and its depth.
    /// - ensures: a step read, a block opened, or the block's reduct at the
    ///   spine's end, as [`Erasure::hold_reduct`] reads the node; a case at the
    ///   spine's end that reads a slot opens its arms ([`Self::opened`]); a
    ///   fork whose parent reads a slot keeps its child and the parent's end
    ///   ([`Slot::Kept`]), and the frame reads the parent as its rest.
    /// - fails: as [`Erasure::hold_reduct`].
    /// - panics: none.
    /// - executable: none — the clause names the reduct's reading of one node,
    ///   which the witnesses of [`Erasure::hold_reduct`] observe.
    ///
    /// # Errors
    /// As `- fails:`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Erasure::hold_reduct`].
    /// - witness: `bridge::tests::a_lexical_hold_crosses_as_its_state_passing_reduct_6609`
    /// - witness: `bridge::tests::a_hold_read_under_a_thunk_is_refused_by_name_6609`
    /// - witness: `bridge::tests::a_hold_read_across_a_case_s_arms_crosses_as_its_reduct_6641`
    fn advance(
        &mut self,
        frame: &mut Frame,
    ) -> Result<Advance, Refusal>
    {
        let current = frame.current;
        match self.arena.computation(current) {
            Some(&Computation::Bind(bound, rest)) => self.step(frame, bound, rest),
            Some(&Computation::Split {
                scrutinee,
                arity,
                motive: SplitMotive::Ambient,
                body,
            }) => {
                if usize::from(arity) != 0 {
                    let scrutinee = self.value(scrutinee, &frame.slots, frame.depth)?;
                    frame.wraps.push(Wrap::Split { scrutinee, arity });
                    frame.depth = frame.depth.deeper_by(arity);
                }
                frame.current = body;
                Ok(Advance::Stepped)
            },
            Some(&Computation::Memory(_)) => {
                // An access, an end or a consuming read at the spine's end
                // runs as the step `y ← it; return y`.
                let returned = self.variable(DeBruijnIndex::from(0_u32));
                let returned = self.arena.computation_return(returned);
                self.step(frame, current, returned)
            },
            Some(&Computation::DataCase { .. })
                if self.reads(TermNode::Computation(current), &frame.slots)? == Reads::Linear =>
            {
                self.opened(frame, current, Then::Tail)
            },
            Some(&Computation::Session(SessionAction::Fork {
                protocol,
                child,
                parent,
            })) if self.reads(TermNode::Computation(current), &frame.slots)? == Reads::Linear => {
                // The parent's end is a binder the reduct keeps. The child runs
                // apart under its own end, so it may read no slot.
                frame.slots.push(Slot::Kept);
                if self.reads(TermNode::Computation(child), &frame.slots)? == Reads::Linear {
                    return Err(self.refused());
                }
                frame.wraps.push(Wrap::Fork { protocol, child });
                frame.current = parent;
                Ok(Advance::Stepped)
            },
            Some(_) => {
                let tail = self.computation(current, &frame.slots, frame.depth)?;
                Ok(Advance::Ended(self.ended(frame, tail)?))
            },
            None => Err(Refusal::DanglingNode {
                node: CoreNode::Term(TermNode::Computation(current)),
            }),
        }
    }

    /// `frame` past the step `y ← bound; rest`.
    ///
    /// # Specification
    /// - requires: `frame` stands at the step.
    /// - ensures: as [`Erasure::hold_reduct`] for one step: a memory form read
    ///   as the reduct reads it, a block it opens as a frame, a case that reads
    ///   a slot with its arms opened ([`Self::opened`]), a bound block that
    ///   reads a slot as a frame beneath [`Self::fixed`]'s slots, and any other
    ///   step with its reads of a slot replaced.
    /// - fails: as [`Erasure::hold_reduct`].
    /// - panics: none.
    /// - executable: none — the clause names the reduct's reading of the step,
    ///   which the witnesses of [`Erasure::hold_reduct`] observe.
    ///
    /// # Errors
    /// As `- fails:`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Erasure::hold_reduct`].
    /// - witness: `bridge::tests::a_lexical_hold_crosses_as_its_state_passing_reduct_6609`
    /// - witness: `bridge::tests::a_hold_read_across_a_case_s_arms_crosses_as_its_reduct_6641`
    fn step(
        &mut self,
        frame: &mut Frame,
        bound: ComputationId,
        rest: ComputationId,
    ) -> Result<Advance, Refusal>
    {
        let form = match self.arena.computation(bound) {
            Some(&Computation::Memory(ref form)) => form.clone(),
            Some(&Computation::DataCase { .. })
                if self.reads(TermNode::Computation(bound), &frame.slots)? == Reads::Linear =>
            {
                return self.opened(frame, bound, Then::Bound { rest });
            },
            Some(&Computation::Bind(..))
                if self.reads(TermNode::Computation(bound), &frame.slots)? == Reads::Linear =>
            {
                let slots = self.fixed(frame, Then::Bound { rest })?;
                return Ok(Advance::Entered(Frame {
                    current: bound,
                    depth: frame.depth,
                    wraps: Vec::new(),
                    slots,
                    ending: Ending::Plain,
                    resume: Resume::Bind { rest },
                    pending: None,
                }));
            },
            Some(_) => {
                let bound = self.computation(bound, &frame.slots, frame.depth)?;
                return Ok(stepped(frame, bound, rest));
            },
            None => {
                return Err(Refusal::DanglingNode {
                    node: CoreNode::Term(TermNode::Computation(bound)),
                });
            },
        };
        match form {
            MemoryForm::Hold { .. } => Ok(Advance::Entered(self.entered(
                bound,
                &frame.slots,
                frame.depth,
                Resume::Bind { rest },
            )?)),
            MemoryForm::Access {
                mode,
                held,
                place: Place::Whole,
                body,
            } => {
                let position = self.position(&frame.slots, held)?;
                let Some(&Slot::Held { now, frozen: fixed }) = frame.slots.get(position.0)
                else {
                    return Err(self.refused());
                };
                let (unwind, ending, resume) = match mode {
                    AccessMode::Shared => (None, Ending::Plain, Resume::Bind { rest }),
                    AccessMode::Exclusive { unwind } => {
                        if fixed {
                            return Err(self.refused());
                        }
                        let unwind = Read {
                            value: self.unwind(unwind)?,
                            depth: frame.depth,
                        };
                        (Some(unwind), Ending::Paired, Resume::Paired {
                            rest,
                            position,
                        })
                    },
                };
                if matches!(frame.slots.last(), Some(&Slot::Kept)) {
                    return Err(self.refused());
                }
                let mut slots = frozen(&frame.slots);
                slots.push(Slot::View { now, unwind });
                Ok(Advance::Entered(Frame {
                    current: body,
                    depth: frame.depth,
                    wraps: Vec::new(),
                    slots,
                    ending,
                    resume,
                    pending: None,
                }))
            },
            MemoryForm::Resume { view, value } => {
                let (position, unwind) = self.exclusive_view(&frame.slots, view)?;
                let written = Read {
                    value: self.value(value, &frame.slots, frame.depth)?,
                    depth: frame.depth,
                };
                let Some(slot) = frame.slots.get_mut(position.0)
                else {
                    return Err(self.refused());
                };
                *slot = Slot::View {
                    now: written,
                    unwind: Some(unwind),
                };
                let unit = self.arena.value_unit();
                let unit = self.arena.computation_return(unit);
                Ok(stepped(frame, unit, rest))
            },
            MemoryForm::Abort { view } => {
                let (_position, unwind) = self.exclusive_view(&frame.slots, view)?;
                // The unwind answers the unit, as the abort does.
                let thunk = self.at_depth(unwind, frame.depth)?;
                let unwind = self.arena.computation_force(thunk);
                Ok(stepped(frame, unwind, rest))
            },
            MemoryForm::Consume { held } => {
                let position = self.position(&frame.slots, held)?;
                let Some(&Slot::Held { now, frozen: false }) = frame.slots.get(position.0)
                else {
                    return Err(self.refused());
                };
                let value = self.at_depth(now, frame.depth)?;
                let value = self.arena.computation_return(value);
                Ok(stepped(frame, value, rest))
            },
            MemoryForm::Access { .. } => Err(self.refused()),
        }
    }

    /// `frame` at the case `origin`, read in the form the judgement checked
    /// it in, its scrutinee read and its arms opened one at a time beneath
    /// [`Self::fixed`]'s slots.
    ///
    /// # Specification
    /// - requires: `frame` stands at `origin`, a case at the spine's end for
    ///   [`Then::Tail`] or the bound of the step `then` names.
    /// - ensures: as [`Self::arms`] for the case with no arm read.
    /// - fails: [`Refusal::OutOfFragment`] naming [`UnadmittedFormer::Memory`]
    ///   at the hold when the form the judgement checked is no case; as
    ///   [`Erasure::hold_reduct`] for the scrutinee; as [`Self::fixed`] and
    ///   [`Self::arms`].
    /// - panics: none.
    /// - executable: none — the clause names the reduct's reading of a case,
    ///   which the witnesses of [`Erasure::hold_reduct`] observe.
    ///
    /// # Errors
    /// As `- fails:`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a case at a spine's end and a case a step binds, each
    ///   with an arm that reads the slot, cross as their reducts, and a
    ///   derivation of the match crosses at the rebuilt case.
    /// - witness: `bridge::tests::a_hold_read_across_a_case_s_arms_crosses_as_its_reduct_6641`
    /// - witness: `bridge::tests::a_held_match_s_derivation_crosses_at_its_rebuilt_case_6641`
    fn opened(
        &mut self,
        frame: &mut Frame,
        origin: ComputationId,
        then: Then,
    ) -> Result<Advance, Refusal>
    {
        let at = self.refined(origin);
        let Some(&Computation::DataCase {
            scrutinee,
            ref branches,
            ..
        }) = self.arena.computation(at)
        else {
            return Err(self.refused());
        };
        let arms = Vec::with_capacity(branches.len());
        let scrutinee = self.value(scrutinee, &frame.slots, frame.depth)?;
        let slots = self.fixed(frame, then)?;
        self.arms(frame, Pending {
            origin,
            at,
            scrutinee,
            arms,
            slots,
            depth: frame.depth,
            then,
        })
    }

    /// The node the judgement checked in `at`'s place: its restated form, or
    /// `at` itself.
    ///
    /// # Specification
    /// trivial.
    fn refined(
        &self,
        at: ComputationId,
    ) -> ComputationId
    {
        self.restated
            .binary_search_by_key(&TermNode::Computation(at), |&(node, _)| node)
            .ok()
            .and_then(|place| self.restated.get(place))
            .and_then(|&(_, refined)| match refined {
                TermNode::Computation(refined) => Some(refined),
                TermNode::Value(_) => None,
            })
            .unwrap_or(at)
    }

    /// `frame` past the arms of `pending` still to read: the next arm that
    /// reads a slot opened as a frame, each arm that reads none kept as it
    /// stands, and the case rebuilt once every arm is read.
    ///
    /// # Specification
    /// - requires: `frame` reads `pending`'s case, and `pending` holds the
    ///   reducts of its leading arms.
    /// - ensures: the frame of the next arm that reads a slot, beneath
    ///   `pending`'s slots and its field and equation binders, with `frame`
    ///   waiting for it; once every arm is read, the case of the reducts at the
    ///   same motive, as the frame's tail ([`Self::ended`]) or as the bound of
    ///   its step.
    /// - fails: [`Refusal::OutOfFragment`] naming [`UnadmittedFormer::Memory`]
    ///   at the hold when an arm that reads a slot is no lambda over its
    ///   binders; [`Refusal::DanglingNode`] when the case is gone; as
    ///   [`Self::ended`].
    /// - panics: none.
    /// - executable: none — the clause names the reduct's reading of the arms,
    ///   which the witnesses of [`Erasure::hold_reduct`] observe.
    ///
    /// # Errors
    /// As `- fails:`.
    ///
    /// # Termination
    /// - reason: the `loop` over the arms, and the `for` over an arm's binders.
    /// - measure: the arms not yet read, and the binders not yet crossed; each
    ///   turn reads one arm or one binder.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an arm under a field binder, an arm under none, and
    ///   an arm that reads no slot cross in tag order.
    /// - witness: `bridge::tests::a_hold_read_across_a_case_s_arms_crosses_as_its_reduct_6641`
    fn arms(
        &mut self,
        frame: &mut Frame,
        mut pending: Pending,
    ) -> Result<Advance, Refusal>
    {
        let dangling = Refusal::DanglingNode {
            node: CoreNode::Term(TermNode::Computation(pending.at)),
        };
        let (branch, lambdas) = loop {
            let Some(&Computation::DataCase {
                ref branches,
                ref arities,
                equations,
                ..
            }) = self.arena.computation(pending.at)
            else {
                return Err(dangling);
            };
            let index = pending.arms.len();
            let Some(&branch) = branches.get(index)
            else {
                break (None, 0);
            };
            // A constructor's arm binds its fields, then its equations; a
            // loop arm after the constructors' binds none.
            let lambdas = arities.get(index).map_or(0, |&fields| {
                usize::from(fields).saturating_add(usize::from(equations))
            });
            if self.reads(TermNode::Computation(branch), &pending.slots)? == Reads::Linear {
                break (Some(self.refined(branch)), lambdas);
            }
            pending.arms.push(branch);
        };
        let Some(branch) = branch
        else {
            let Some(&Computation::DataCase {
                motive,
                ref arities,
                equations,
                ..
            }) = self.arena.computation(pending.at)
            else {
                return Err(dangling);
            };
            let arities = arities.clone();
            let built = self.arena.computation_data_case_with_equations(
                pending.scrutinee,
                motive,
                (pending.arms, arities),
                equations,
            );
            // A derivation of the match names the case as written, and it
            // crosses at the case rebuilt in its place.
            self.rebuilt.insert(pending.origin, built);
            return match pending.then {
                Then::Tail => Ok(Advance::Ended(self.ended(frame, built)?)),
                Then::Bound { rest } => Ok(stepped(frame, built, rest)),
            };
        };
        let mut body = branch;
        for _ in 0 .. lambdas {
            let Some(&Computation::Lambda(inner)) = self.arena.computation(body)
            else {
                return Err(self.refused());
            };
            body = inner;
        }
        let lambdas = ComponentCount::from(lambdas);
        let arm = Frame {
            current: body,
            depth: pending.depth.deeper_by(lambdas),
            wraps: Vec::new(),
            slots: pending.slots.clone(),
            ending: Ending::Plain,
            resume: Resume::Arm { lambdas },
            pending: None,
        };
        frame.pending = Some(pending);
        Ok(Advance::Entered(arm))
    }

    /// The slots a case's arms or a bound block read beneath `frame`: each
    /// slot the frame reads after the form held fixed, so the form may read
    /// it and may not write it.
    ///
    /// # Specification
    /// - requires: `frame` stands at the form `then` names.
    /// - ensures: `frame`'s slots, each hold the rest of the step reads frozen
    ///   and each view it reads shared; for a frame that answers the value its
    ///   view leaves ([`Ending::Paired`]), that view shared too. Every other
    ///   slot keeps its mode: the frame never reads its value past the form.
    /// - fails: [`Refusal::OutOfFragment`] naming [`UnadmittedFormer::Memory`]
    ///   at the hold when the rest reads a linear binder outside the hold;
    ///   [`Refusal::DanglingNode`] for an absent rest.
    /// - panics: none.
    ///
    /// # Errors
    /// As `- fails:`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a hold the rest reads after a case is fixed in its
    ///   arms, and a hold a bound block consumes and the rest never reads is
    ///   not.
    /// - witness: `bridge::tests::a_hold_read_across_a_case_s_arms_crosses_as_its_reduct_6641`
    /// - witness: `bridge::tests::a_write_the_rest_reads_after_a_case_is_refused_by_name_6641`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |slots| slots.len() == frame.slots.len()))]
    fn fixed(
        &self,
        frame: &Frame,
        then: Then,
    ) -> Result<Vec<Slot>, Refusal>
    {
        let mut slots = frame.slots.clone();
        if let Then::Bound { rest } = then {
            let Some(support) = self.arena.computation_support(rest)
            else {
                return Err(Refusal::DanglingNode {
                    node: CoreNode::Term(TermNode::Computation(rest)),
                });
            };
            for index in support.indices(Zone::Linear) {
                let position = self.position(&frame.slots, index)?;
                if let Some(slot) = slots.get_mut(position.0) {
                    *slot = pinned(*slot);
                }
            }
        }
        if matches!(frame.ending, Ending::Paired)
            && let Some(view) = slots.last_mut()
        {
            *view = pinned(*view);
        }
        Ok(slots)
    }

    /// The reduct of `frame`'s block, whose spine ends at `tail`.
    ///
    /// # Specification
    /// - requires: `tail` stands beneath the frame's steps.
    /// - ensures: the frame's steps around `tail`; for [`Ending::Paired`],
    ///   `tail` answers its result beside the value the view leaves.
    /// - fails: [`Refusal::OutOfFragment`] naming [`UnadmittedFormer::Memory`]
    ///   at the hold for a paired frame whose innermost slot is no view.
    /// - panics: none.
    /// - executable: none — the clause names the reduct's steps, which the
    ///   witnesses of [`Erasure::hold_reduct`] observe.
    ///
    /// # Errors
    /// As `- fails:`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Erasure::hold_reduct`].
    /// - witness: `bridge::tests::a_lexical_hold_crosses_as_its_state_passing_reduct_6609`
    /// - witness: `bridge::tests::a_reduct_leaving_the_wrong_value_is_the_kernel_s_rejection_6609`
    fn ended(
        &mut self,
        frame: &Frame,
        tail: ComputationId,
    ) -> Result<ComputationId, Refusal>
    {
        let mut built = match frame.ending {
            Ending::Plain => tail,
            Ending::Paired => {
                let Some(&Slot::View { now, .. }) = frame.slots.last()
                else {
                    return Err(self.refused());
                };
                let result = self.variable(DeBruijnIndex::from(0_u32));
                let left = self.at_depth(now, frame.depth.deeper())?;
                let pair = self.arena.value_tuple(&[result, left]);
                let answered = self.arena.computation_return(pair);
                self.arena.computation_bind(tail, answered)
            },
        };
        for &wrap in frame.wraps.iter().rev() {
            built = match wrap {
                Wrap::Bind(bound) => self.arena.computation_bind(bound, built),
                Wrap::Paired(bound) => {
                    let pair = self.variable(DeBruijnIndex::from(1_u32));
                    let result = self
                        .arena
                        .computation_tuple_projection(pair, Component::from(0_usize));
                    let inner = self.arena.computation_bind(result, built);
                    let pair = self.variable(DeBruijnIndex::from(0_u32));
                    let left = self
                        .arena
                        .computation_tuple_projection(pair, Component::from(1_usize));
                    let inner = self.arena.computation_bind(left, inner);
                    self.arena.computation_bind(bound, inner)
                },
                Wrap::Split { scrutinee, arity } => {
                    self.arena.computation_split(scrutinee, arity, built)
                },
                Wrap::Fork { protocol, child } => {
                    self.arena.computation_session(SessionAction::Fork {
                        protocol,
                        child,
                        parent: built,
                    })
                },
            };
        }
        Ok(built)
    }

    /// The unwind `unwind` of an exclusive access, as a thunk the abort
    /// forces: it may read no slot.
    ///
    /// # Specification
    /// - ensures: a thunk of `unwind`.
    /// - fails: [`Refusal::OutOfFragment`] naming [`UnadmittedFormer::Memory`]
    ///   at the hold when `unwind` reads a linear binder.
    /// - panics: none.
    ///
    /// # Errors
    /// As `- fails:`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an access that aborts runs its unwind, and an unwind
    ///   that reads the view refuses the hold.
    /// - witness: `bridge::tests::a_lexical_hold_crosses_as_its_state_passing_reduct_6609`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |&thunk| self.arena.value(thunk).is_some()))]
    fn unwind(
        &mut self,
        unwind: ComputationId,
    ) -> Result<ValueId, Refusal>
    {
        // The abort forces the unwind past the view's binder, so it may read
        // no linear binder at all, kept or not.
        match self.reads(TermNode::Computation(unwind), &[])? {
            Reads::Nothing => Ok(self.arena.value_thunk(unwind)),
            Reads::Linear => Err(self.refused()),
        }
    }

    /// The exclusive view `view` among `slots`: its position and its unwind.
    ///
    /// # Specification
    /// - ensures: the position of the innermost slot, an exclusive view.
    /// - fails: [`Refusal::OutOfFragment`] naming [`UnadmittedFormer::Memory`]
    ///   at the hold when `view` names no exclusive view or not the innermost
    ///   slot.
    /// - panics: none.
    ///
    /// # Errors
    /// As `- fails:`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an access that resumes and one that aborts read their
    ///   view as the innermost slot.
    /// - witness: `bridge::tests::a_lexical_hold_crosses_as_its_state_passing_reduct_6609`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |&(position, _)| position.0.checked_add(1) == Some(slots.len())))]
    fn exclusive_view(
        &self,
        slots: &[Slot],
        view: DeBruijnIndex,
    ) -> Result<(Position, Read), Refusal>
    {
        let position = self.position(slots, view)?;
        let Some(&Slot::View {
            unwind: Some(unwind),
            ..
        }) = slots.get(position.0)
        else {
            return Err(self.refused());
        };
        if position.0.checked_add(1) != Some(slots.len()) {
            return Err(self.refused());
        }
        Ok((position, unwind))
    }

    /// The slot the linear binder `index` counts to among `slots`.
    ///
    /// # Specification
    /// - ensures: the position of the slot, counted from the outermost.
    /// - fails: [`Refusal::OutOfFragment`] naming [`UnadmittedFormer::Memory`]
    ///   at the hold for an index past `slots`.
    /// - panics: none.
    ///
    /// # Errors
    /// As `- fails:`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a hold read beside a shared view reads the outer slot
    ///   past the inner one.
    /// - witness: `bridge::tests::a_lexical_hold_crosses_as_its_state_passing_reduct_6609`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |&position| position.0 < slots.len()))]
    fn position(
        &self,
        slots: &[Slot],
        index: DeBruijnIndex,
    ) -> Result<Position, Refusal>
    {
        let index = usize::try_from(u32::from(index)).map_err(|_wide| self.refused())?;
        slots
            .len()
            .checked_sub(1)
            .and_then(|last| last.checked_sub(index))
            .map(Position)
            .ok_or_else(|| self.refused())
    }

    /// The intuitionistic variable `index`.
    ///
    /// # Specification
    /// trivial.
    fn variable(
        &mut self,
        index: DeBruijnIndex,
    ) -> ValueId
    {
        self.arena.value_variable(Zone::Intuitionistic, index)
    }

    /// `read` raised to `depth` of the reduct's binders.
    ///
    /// # Specification
    /// - ensures: the value raised past the binders between its read and
    ///   `depth`.
    /// - fails: [`Refusal::OutOfFragment`] naming [`UnadmittedFormer::Memory`]
    ///   at the hold when `depth` stands above the read.
    /// - panics: none.
    ///
    /// # Errors
    /// As `- fails:`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a hold read after an access reads the value the
    ///   access leaves, raised past the binders between.
    /// - witness: `bridge::tests::a_lexical_hold_crosses_as_its_state_passing_reduct_6609`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |&value| self.arena.value(value).is_some()))]
    fn at_depth(
        &mut self,
        read: Read,
        depth: Binders,
    ) -> Result<ValueId, Refusal>
    {
        let crossed = u32::from(depth)
            .checked_sub(u32::from(read.depth))
            .ok_or_else(|| self.refused())?;
        if crossed == 0 {
            return Ok(read.value);
        }
        Ok(
            gandr_core_term::shift_value(self.arena, read.value, Binders::from(crossed))
                .settle(self.arena),
        )
    }

    /// Whether `node` reads a slot of `slots`, or a linear binder outside the
    /// hold.
    ///
    /// # Specification
    /// - requires: the binders [`Slot::Kept`] names stand innermost among
    ///   `slots`.
    /// - ensures: whether the node's support names a linear index past the kept
    ///   binders; a read of a kept binder alone is no read.
    /// - fails: [`Refusal::DanglingNode`] for an absent node.
    /// - panics: none.
    ///
    /// # Errors
    /// As `- fails:`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a step that reads no slot keeps its form, a session
    ///   action on a kept end keeps its form, and an unwind that reads a slot
    ///   refuses the hold.
    /// - witness: `bridge::tests::a_lexical_hold_crosses_as_its_state_passing_reduct_6609`
    /// - witness: `bridge::tests::a_hold_read_across_a_case_s_arms_crosses_as_its_reduct_6641`
    #[spec(ensures: |ret| ret.is_err() == match node {
        | TermNode::Value(at) => self.arena.value(at).is_none(),
        | TermNode::Computation(at) => self.arena.computation(at).is_none(),
    })]
    fn reads(
        &self,
        node: TermNode,
        slots: &[Slot],
    ) -> Result<Reads, Refusal>
    {
        let support = match node {
            TermNode::Value(at) => self.arena.value_support(at),
            TermNode::Computation(at) => self.arena.computation_support(at),
        };
        let Some(support) = support
        else {
            return Err(Refusal::DanglingNode {
                node: CoreNode::Term(node),
            });
        };
        let kept = slots
            .iter()
            .rev()
            .take_while(|&&slot| matches!(slot, Slot::Kept))
            .count();
        let read = support
            .indices(Zone::Linear)
            .any(|index| usize::try_from(u32::from(index)).map_or(true, |index| index >= kept));
        Ok(if read { Reads::Linear } else { Reads::Nothing })
    }

    /// The value `at` with each read of a slot replaced by the value the slot
    /// holds at `depth`, walked with an explicit stack.
    ///
    /// # Specification
    /// - ensures: `at` itself when it reads no linear binder; a read of a slot
    ///   and a tuple rebuilt from their components'.
    /// - fails: [`Refusal::OutOfFragment`] naming [`UnadmittedFormer::Memory`]
    ///   at the hold for a read under any other form or past the slots.
    /// - panics: none.
    ///
    /// # Errors
    /// As `- fails:`.
    ///
    /// # Termination
    /// - reason: the `while` over the visits.
    /// - measure: the subterms not yet entered; a tuple enters each of its
    ///   components once, and the arena is finite and acyclic.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a hold read in a tuple beside a shared view reads
    ///   both slots.
    /// - witness: `bridge::tests::a_lexical_hold_crosses_as_its_state_passing_reduct_6609`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |&value| self.arena.value(value).is_some()))]
    fn value(
        &mut self,
        at: ValueId,
        slots: &[Slot],
        depth: Binders,
    ) -> Result<ValueId, Refusal>
    {
        let mut visits = Vec::from([Visit::Enter(at)]);
        let mut read: Vec<ValueId> = Vec::new();
        while let Some(visit) = visits.pop() {
            match visit {
                Visit::Enter(at) => {
                    if self.reads(TermNode::Value(at), slots)? == Reads::Nothing {
                        read.push(at);
                        continue;
                    }
                    let index = match self.arena.value(at) {
                        Some(&Value::Variable {
                            zone: Zone::Linear,
                            index,
                        }) => index,
                        Some(&Value::Tuple(ref components)) => {
                            visits.push(Visit::Tuple(components.len()));
                            visits.extend(
                                components
                                    .iter()
                                    .rev()
                                    .map(|&component| Visit::Enter(component)),
                            );
                            continue;
                        },
                        Some(_) | None => return Err(self.refused()),
                    };
                    let position = self.position(slots, index)?;
                    let Some(&(Slot::Held { now, .. } | Slot::View { now, .. })) =
                        slots.get(position.0)
                    else {
                        return Err(self.refused());
                    };
                    read.push(self.at_depth(now, depth)?);
                },
                Visit::Tuple(count) => {
                    let start = read
                        .len()
                        .checked_sub(count)
                        .ok_or_else(|| self.refused())?;
                    let components = read.split_off(start);
                    read.push(self.arena.value_tuple(&components));
                },
            }
        }
        match (read.pop(), read.is_empty()) {
            (Some(value), true) => Ok(value),
            (Some(_) | None, _) => Err(self.refused()),
        }
    }

    /// The step `at` of a spine with each read of a slot replaced by the
    /// value the slot holds at `depth`: the applications around its head
    /// unwound, the head read, and the applications rebuilt.
    ///
    /// # Specification
    /// - ensures: `at` itself when it reads no linear binder; a return, an
    ///   application, a force and a native operation rebuilt from their
    ///   children's.
    /// - fails: [`Refusal::OutOfFragment`] naming [`UnadmittedFormer::Memory`]
    ///   at the hold for a read under any other form, a memory form off the
    ///   spine among them.
    /// - panics: none.
    ///
    /// # Errors
    /// As `- fails:`.
    ///
    /// # Termination
    /// - reason: the `while` over the applications.
    /// - measure: the application's function, a strict subterm; the arena is
    ///   finite and acyclic.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a native operation over the held value, and a step
    ///   that reads no slot, distinguish a rebuilt step from a kept one.
    /// - witness: `bridge::tests::a_lexical_hold_crosses_as_its_state_passing_reduct_6609`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |&computation| self.arena.computation(computation).is_some()))]
    fn computation(
        &mut self,
        at: ComputationId,
        slots: &[Slot],
        depth: Binders,
    ) -> Result<ComputationId, Refusal>
    {
        let mut arguments = Vec::new();
        let mut head = at;
        while self.reads(TermNode::Computation(head), slots)? == Reads::Linear {
            let Some(&Computation::Application(function, argument)) = self.arena.computation(head)
            else {
                break;
            };
            arguments.push(argument);
            head = function;
        }
        let mut built = match self.reads(TermNode::Computation(head), slots)? {
            Reads::Nothing => head,
            Reads::Linear => match self.arena.computation(head).cloned() {
                Some(Computation::Return(value)) => {
                    let value = self.value(value, slots, depth)?;
                    self.arena.computation_return(value)
                },
                Some(Computation::Force(value)) => {
                    let value = self.value(value, slots, depth)?;
                    self.arena.computation_force(value)
                },
                Some(Computation::Primitive {
                    primitive,
                    arguments: operands,
                }) => {
                    let operands = match operands {
                        Arguments::Unary(operand) => {
                            Arguments::Unary(self.value(operand, slots, depth)?)
                        },
                        Arguments::Binary([first, second]) => Arguments::Binary([
                            self.value(first, slots, depth)?,
                            self.value(second, slots, depth)?,
                        ]),
                    };
                    self.arena.computation_primitive(primitive, operands)
                },
                Some(_) | None => return Err(self.refused()),
            },
        };
        for &argument in arguments.iter().rev() {
            let argument = self.value(argument, slots, depth)?;
            built = self.arena.computation_application(built, argument);
        }
        Ok(built)
    }
}
