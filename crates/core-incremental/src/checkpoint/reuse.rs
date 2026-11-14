//! The standing decisions of a session's last pass, which a revision's
//! judgement takes in place of its own.
//!
//! A keystroke changes one declaration, and its judgement decides every
//! declaration again. [`Reuse`] gives the judgement the decision of each
//! declaration whose checkpoint stands: the run admits the declaration as the
//! pass adopts it, and decides only the declarations whose checkpoints fall.

use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use alloc::sync::Arc;
use alloc::vec::Vec;

use gandr_core_checker::CheckRefusal;
use gandr_core_checker::Checked;
use gandr_core_checker::CheckingContext;
use gandr_core_checker::ConversionCount;
use gandr_core_checker::Declaration;
use gandr_core_checker::DeclarationContent;
use gandr_core_checker::Entered;
use gandr_core_checker::Synthesised;
use gandr_core_checker::Taken;
use gandr_core_checker::Taking;
use gandr_core_checker::Verdict;
use gandr_core_checker::elaborated;
use gandr_core_checker::kept;
use gandr_core_checker::taken;
use gandr_core_checker::waits;
use gandr_core_term::ValueId;
use quenchant_shape::shape::Maybe;

use super::AdoptionInput;
use super::Answer;
use super::Candidate;
use super::ContentKey;
use super::ItemCheckpoint;
use super::Leading;
use super::Leads;
use super::Resume;
use super::ResumeCensus;
use super::Supplied;
use super::adopt;
use super::answer_in;
use super::close_value_changes;
use super::content_key_of;
use super::recall;
use super::seat_of;
use super::started_after;
use crate::boundary::ItemCount;
use crate::boundary::ItemOrdinal;
use crate::content::Encoded;
use crate::content::TypeMemo;
use crate::content::encode_item;
use crate::footprint::Footprint;
use crate::footprint::footprint_of;
use crate::region::Item;
use crate::region::Layout;
use crate::region::Program;
use crate::region::Reference;
use crate::report::reported;
use crate::typing::Typing;

/// The checkpoints of a session's last pass, offered to the judgement of the
/// next revision: each declaration whose checkpoint stands is taken from it.
///
/// The judgement asks for the declarations in order. Before each one, the
/// taker reads from the context the answer of each declaration that the run
/// decided since the last one it took, so the stand test reads what the
/// declaration would read now.
///
/// # Specification
/// - executable: none — a taker whose decisions only the run's report attests.
///
/// # Adequacy
/// - hypothesis: L3 — a revision that changes one declaration takes every other
///   one and reports as its whole judgement.
/// - witness: `tests::incremental::a_judgement_takes_each_standing_item_from_the_last_pass_6620`
pub struct Reuse<'base>
{
    /// The last pass's checkpoints of the items after the leading ones.
    base: &'base [ItemCheckpoint],
    /// Each base checkpoint's index, by its content key.
    recalled: BTreeMap<ContentKey, usize>,
    /// The revision's items.
    layout: &'base Layout,
    /// The revision's items after the leading ones, encoded.
    encoded: Vec<Encoded>,
    /// Each encoded item's content key.
    keys: Vec<Maybe<ContentKey, recall::Absent>>,
    /// Each encoded item's footprint.
    footprints: Vec<Footprint>,
    /// The references whose values the revision changed, closed over their
    /// readers.
    value_changed: BTreeSet<Reference>,
    /// The answers of the items before the next one the judgement asks for.
    supplied: Supplied<'base>,
    /// The type contents read so far.
    types: TypeMemo,
    /// How many declarations the judgement took.
    taken: ItemCount,
}

/// What a taken decision is, read off its checkpoint before the context
/// changes: no step after the adoption can fail.
#[derive(Clone, Copy, Debug)]
enum Kind
{
    /// A nominal declaration that formed.
    Data,
    /// A body checked against its written signature.
    Checked(ConversionCount, ValueId),
    /// An unsigned body that synthesised its type.
    Synthesised(ConversionCount, ValueId),
}

impl<'base> Reuse<'base>
{
    /// The taker of the checkpoints that `resume` holds for the revision
    /// `program`, laid after `leading` when the revision has one.
    ///
    /// The base is the one the pass resumes from: every checkpoint without
    /// leading items, the checkpoints after them when the resume started after
    /// that very state, and none otherwise.
    ///
    /// # Specification
    /// trivial.
    pub(crate) fn of(
        resume: Option<&'base Resume>,
        program: &'base Program,
        leading: Option<&'base Arc<Leading>>,
    ) -> Self
    {
        let (base, answers): (&[ItemCheckpoint], &[Answer]) = match (resume, leading) {
            (Some(resume), None) => (&resume.checkpoints.items, &[]),
            (Some(resume), Some(leading)) if leading.leads(program) == Leads::Departs => {
                (&resume.checkpoints.items, &[])
            },
            (Some(resume), Some(leading))
                if started_after(&resume.after, &resume.checkpoints, leading) == Leads::Leads =>
            {
                (
                    resume
                        .checkpoints
                        .items
                        .get(leading.checkpoints.len() ..)
                        .unwrap_or_default(),
                    &leading.answers,
                )
            },
            (Some(_) | None, Some(leading)) if leading.leads(program) == Leads::Leads => {
                (&[], &leading.answers)
            },
            (Some(_) | None, Some(_)) | (None, None) => (&[], &[]),
        };
        let encoded: Vec<Encoded> = (answers.len() .. program.items().len())
            .map(|index| encode_item(program.arena(), program.layout(), ItemOrdinal::from(index)))
            .collect();
        let keys = encoded
            .iter()
            .map(|item| content_key_of(&item.content))
            .collect();
        let footprints: Vec<Footprint> = encoded
            .iter()
            .map(|item| footprint_of(&item.content))
            .collect();
        let value_changed =
            close_value_changes(base, &encoded, &footprints, &mut ResumeCensus::default());
        let recalled = base
            .iter()
            .enumerate()
            .filter_map(|(index, checkpoint)| match checkpoint.key() {
                Maybe::Present(key) => Some((key, index)),
                Maybe::Absent(_) => None,
            })
            .collect();
        Self {
            base,
            recalled,
            layout: program.layout(),
            encoded,
            keys,
            footprints,
            value_changed,
            supplied: Supplied {
                leading: answers,
                own: Vec::with_capacity(program.items().len()),
            },
            types: TypeMemo::default(),
            taken: ItemCount::default(),
        }
    }

    /// How many declarations the judgement took.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn taken(&self) -> ItemCount
    {
        self.taken
    }

    /// Read from `context` the answer of each item before the item at
    /// `ordinal` among the encoded ones that the run decided.
    ///
    /// # Specification
    /// trivial.
    fn catch_up(
        &mut self,
        context: &CheckingContext<'_>,
        ordinal: ItemOrdinal,
    )
    {
        let index = usize::from(ordinal).saturating_sub(self.supplied.leading.len());
        while self.supplied.own.len() < index {
            let next = self.supplied.next();
            let Some(declaration) = self
                .layout
                .items
                .get(usize::from(next))
                .map(Item::declaration)
            else {
                return;
            };
            self.supplied
                .own
                .push(answer_in(context, declaration, self.layout, &self.types));
        }
    }
}

impl Taking for Reuse<'_>
{
    /// The decision of `declaration` when its last checkpoint stands, entered
    /// into `context` as the pass adopts it.
    ///
    /// A checkpoint is taken when its item is entered as written, keeps no
    /// report and no failure, and is typed as data, checked or synthesised.
    /// Every other declaration is decided.
    ///
    /// # Specification
    /// - requires: the run has judged each declaration before `declaration`.
    /// - ensures: on a decision, `context` holds `declaration` as the pass's
    ///   adoption leaves it, and the verdict is the one the checkpoint's typing
    ///   names over the written body and the type the context now holds; on an
    ///   absence, `context` is unchanged but for a type that a synthesised item
    ///   mints.
    /// - panics: none.
    /// - executable: none — the decision's agreement with a judgement is the
    ///   witness's claim.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Reuse`].
    /// - witness: `tests::incremental::a_judgement_takes_each_standing_item_from_the_last_pass_6620`
    #[inline]
    fn take(
        &mut self,
        context: &mut CheckingContext<'_>,
        declaration: &Declaration,
    ) -> Maybe<Taken, taken::Absent>
    {
        let unheld = Maybe::Absent(taken::Absent::Unheld);
        let Some(ordinal) = self.layout.ordinal(declaration.constant())
        else {
            return unheld;
        };
        let Some(index) = usize::from(ordinal).checked_sub(self.supplied.leading.len())
        else {
            return unheld;
        };
        self.catch_up(context, ordinal);
        if self.supplied.own.len() != index {
            return unheld;
        }
        let (Some(item), Some(footprint), Some(&Maybe::Present(key))) = (
            self.encoded.get(index),
            self.footprints.get(index),
            self.keys.get(index),
        )
        else {
            return unheld;
        };
        let Some(checkpoint) = self
            .recalled
            .get(&key)
            .and_then(|&at| self.base.get(at))
            .filter(|checkpoint| *checkpoint.content() == item.content)
        else {
            return unheld;
        };
        if checkpoint.entered() != Entered::AsWritten
            || !matches!(
                checkpoint.report(),
                Maybe::Absent(reported::Absent::Unreported)
            )
            || matches!(checkpoint.failure(), Maybe::Present(_))
        {
            return unheld;
        }
        let kind = match (checkpoint.typing(), declaration.content()) {
            (&Typing::Data, _) => Kind::Data,
            (
                &Typing::Checked { conversions },
                &DeclarationContent::Value {
                    signature: Maybe::Present(_),
                    body: Maybe::Present(body),
                },
            ) => Kind::Checked(conversions, body),
            (
                &Typing::Synthesised { conversions, .. },
                &DeclarationContent::Value {
                    signature: Maybe::Absent(_),
                    body: Maybe::Present(body),
                },
            ) => Kind::Synthesised(conversions, body),
            _ => return unheld,
        };
        let seat = seat_of(
            checkpoint,
            item,
            context.arena_mut(),
            self.layout,
            &mut ResumeCensus::default(),
        );
        let candidate = Candidate { checkpoint, seat };
        let adopted = adopt(context, &AdoptionInput {
            candidate: &candidate,
            item,
            footprint,
            declaration,
            layout: self.layout,
            supplied: &self.supplied,
            ordinal,
            value_changed: &self.value_changed,
        });
        let Maybe::Present((_support, _typing, answer)) = adopted
        else {
            return unheld;
        };
        self.supplied.own.push(answer);
        self.taken = ItemCount::from(usize::from(self.taken).saturating_add(1));
        let verdict = match (kind, context.signature(declaration.constant())) {
            (Kind::Data, _) => Verdict::Data,
            (Kind::Checked(conversions, body), Maybe::Present(declared)) => Verdict::Checked {
                declared,
                body,
                evidence: Checked::new(conversions),
            },
            (Kind::Synthesised(conversions, body), Maybe::Present(declared)) => {
                Verdict::Synthesised {
                    body,
                    synthesised: Synthesised::new(declared, conversions),
                }
            },
            // The adoption seats the signature of a checked or synthesised
            // item; a table without it is a broken invariant, refused by name.
            (Kind::Checked(..) | Kind::Synthesised(..), Maybe::Absent(_)) => {
                Verdict::Refused(CheckRefusal::MachineInvariant)
            },
        };
        Maybe::Present(Taken::new(
            verdict,
            (
                Maybe::Absent(kept::Absent::Accepted),
                Maybe::Absent(elaborated::Absent::Unnested),
                Maybe::Absent(waits::Absent::Unsuspended),
            ),
        ))
    }
}
