//! Declaration checking: the judgement applied to one declaration, and to a
//! module of them in admission order.
//!
//! # The signature decides the direction
//!
//! A declaration with a declared type checks its body against it; one without
//! synthesises its body's type. The declared type is the contract: it enters
//! the signature table whether or not the body met it, so one wrong body does
//! not turn every later reference into an unknown constant. A body with no
//! signature supplies a type only when it synthesised one.
//!
//! # A declaration hole read in both directions
//!
//! A declaration with no body is a hole at the declaration's grain. In
//! checking position it absorbs the type handed in and owes it: the
//! declaration's verdict is [`Verdict::Owed`] and its [`ObligationEntry`]
//! enters the run's ledger. In synthesis position it has nothing to absorb and
//! is refused as a checking-only form: given the unknown type, it would enter
//! the signature table as a type every reader is consistent with. A hole
//! written as a body is a term hole, read by the judgement without contents;
//! it synthesises the unknown type and owes nothing to the ledger. The run
//! continues past a refusal because every declaration is judged on its own.
//!
//! An owed declaration's verdict carries its [`ObligationEntry`], so a caller
//! judging one declaration needs no ledger. A declaration with neither half is
//! refused rather than owed, or one missing signature would travel silently
//! through the module.
//!
//! # Every declaration gets a verdict
//!
//! [`check_module`] judges every declaration, in the order given, and a
//! refused one does not stop the run: the report is total over the module.
//!
//! A declaration reports its first refusal. Every error of a term in one pass
//! is the total elaboration's, at the term's grain; the module report keeps the
//! strict verdicts.
//!
//! # An accepted body is a definition
//!
//! A declaration whose body was accepted defines its constant: a later decode
//! of a code naming it unfolds to that body. A refused or owed declaration
//! leaves its constant rigid. The report carries the lifts the run's value
//! bridges recorded beside the verdicts, and the components of each function
//! extensionality the run decided, so the kernel bridge writes each one where
//! it stands.
//!
//! The definition is elaborated: when the declared type is a value universe
//! above the body's own level, the definition is the body lifted to the
//! declared universe, so `El(T, l)` unfolds to a code at the level it is
//! decoded at, and weak-head reading never has to insert a lift itself. The
//! kernel admits the same lifted body, so the two sides unfold one constant to
//! one term. [`CheckingContext::adopt`] admits an earlier verdict's body the
//! same way, so an incremental run unfolds what a batch run would. An adopted
//! body becomes a definition only with a supplied formed signature; an untyped
//! adopted body stays unavailable to synthesis and rigid to unfolding. The
//! definition table accepts strictly increasing positions: a repeated or lower
//! position leaves every held body intact rather than replacing or erasing it.
//!
//! The alternatives were defining the constant as the body as written, which
//! makes a decode at the declared level unfold to a code at a smaller one and
//! forces a lift into every unfolding, and unfolding only within the
//! declaration that made the definition, which makes a type alias unusable from
//! the next declaration. The choice reverses with transparency control: an
//! opaque definition then stays rigid by request, and the support log grows a
//! read per unfolding.
//!
//! # A refused body keeps the rules it was refused inside
//!
//! [`check_module`] keeps the [`Failure`] of each body the judgement refused:
//! the rules pending when the refusal came, each on the node it stands on and
//! the type that node was checked against, and the hypotheses the run had
//! opened. They are the refusal's nested reasons, read from the run that
//! refused rather than from a second one. A refused data signature keeps the
//! failure of the step that refused: its hypotheses are the parameters, then
//! the indices or the fields the signature had opened there, and then any
//! binder the step's own run opened. A value's declared type that did not form
//! keeps the failure forming it, under the binders the formation had opened
//! (#4043). A declaration refused before its body was run otherwise — out of
//! order, a hole in synthesis position — keeps none: no rule of the judgement
//! was pending.
//! [`check_declaration`] runs the same judgement and hands back the verdict
//! alone. Witness:
//! `module::tests::a_refused_body_keeps_the_rules_it_was_refused_inside`.
//!
//! # A typed module keeps the type of every term each body judged
//!
//! [`type_module`] judges a module as [`check_module`] does and, for each
//! declaration whose body was judged, runs the typed run over the body at the
//! same point of the run — before the declaration's own type enters the table
//! — so the types it keeps are the ones the judgement met. A face answering a
//! position inside a declaration reads them; no other entry pays for them.
//! Witness: `module::tests::a_typed_module_keeps_each_judged_body_s_term_types`.
//!
//! # A body holding a nested computation is judged twice
//!
//! A body holding a computation written where a value is read is judged, then
//! elaborated as the judgement decided each one, then judged again: the
//! verdict is the second run's and carries the elaborated body, and the report
//! keeps what the elaboration did under the declaration's position. The
//! decisions, the alternatives and the reversal are in `nested`.
//!
//! # A mutual block is admitted on a schedule
//!
//! A data declaration whose fields name a later declaration is admitted in a
//! block with it: [`crate::occurrence::reach`] measures the block from the
//! fields, the run of data declarations at its head are its families and the
//! declarations after them its definitions. The block is admitted on one
//! schedule, the kernel's: the families' formations come into scope, each
//! definition's declared type forms and is foreseen, each family's
//! constructors form naming the definitions at those types, and then each
//! definition's body is judged with every family admitted. Nothing here is a
//! new judgement: each step is the one a lone declaration takes, taken in the
//! block's order. A universe and its decoder are the instance —
//! `data U where { | PiC : (a : U, b : +U (el(a) -> -F U)) --> U }` names `el`,
//! whose declared type names `U` — and inside the decoder's own fixpoint its
//! constant in the family's fields reads as its self binder, as
//! [`crate::recursion::stage_branch`] states. Witness:
//! `tests::recursive_data::a_mutual_block_is_admitted_in_both_checkers`.
//!
//! The block is one admission, so one refused family refuses it whole: every
//! family the run accepted takes the first family's refusal, as the kernel's
//! one admission refuses them all. The block's families share one stage, so
//! a recursion over the sum of them — a rose tree's node and its forest,
//! measured together — descends through either, as
//! [`crate::recursion::families`] states. Witnesses:
//! `tests::recursive_data::a_mutual_block_is_refused_whole_in_both_checkers`,
//! `tests::recursive_data::a_mutual_recursion_descends_through_its_block_s_families_in_both_checkers`.
//!
//! # References
//!
//! - `vault:01a178aa-b5ea-75c1-8677-c85c447790b4` — anchor: the ∃! rule of the
//!   implicit layer. With no candidate, the refusal names the slot. With two or
//!   more, it names every candidate. So a declared type that meets an undecided
//!   slot is refused as the slot's resolution refuses it.

use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use alloc::vec::Vec;

use anodized::spec;
use gandr_core_term::Solutions;
use gandr_core_term::ValueId;
use gandr_core_term::ValueTypeId;
use gandr_core_term::world::World;
use gandr_kernel_term::ConstantIndex;
use quenchant_shape::shape::Maybe;

use crate::answer::Direction;
use crate::context::CheckingContext;
use crate::declaration::AbstractType;
use crate::declaration::Declaration;
use crate::declaration::OriginToken;
use crate::declaration::body;
use crate::declaration::signature;
use crate::elaboration::Collecting;
use crate::elaboration::Deferred;
use crate::elaboration::Residue;
use crate::elaboration::Signing;
use crate::elaboration::Suspension;
use crate::failure::Failure;
use crate::failure::Pursuit;
use crate::failure::Stage;
use crate::failure::judged;
use crate::formation::FormedValueType;
use crate::formation::form_value_type;
use crate::formation::form_value_type_with_failure;
use crate::judgement::Typings;
use crate::judgement::check_value_with_failure;
use crate::judgement::synthesise_value_with_failure;
use crate::judgement::type_value;
use crate::ledger::Absence;
use crate::ledger::ObligationEntry;
use crate::ledger::ObligationLedger;
use crate::nested::NestedElaboration;
use crate::record::Kept;
use crate::refusal::CheckRefusal;
use crate::refusal::CheckingForm;
use crate::refusal::CoreNode;
use crate::refusal::TermNode;
use crate::refusal::TypeNode;
use crate::report::Judged;
use crate::report::ModuleReport;
use crate::report::Verdict;
use crate::retire::Demand;
use crate::retire::Polled;
use crate::retire::Retirement;
use crate::retire::Unretired;
use crate::support::Entered;
use crate::support::Supported;
use crate::support::elaborated;
use crate::support::kept;
use crate::support::waits;
use crate::worlds::Entry;
use crate::worlds::Spending;

quenchant_shape::reason_enum! {
    /// Why no mutual block is open in a module run.
    mod open {
        /// The reason no block is open.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The declarations judged are each admitted alone.
            Lone,
        }
    }
}

/// Whether a declaration is a member of the mutual block a [`Schedule`] holds
/// open.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Membership
{
    /// No block is open: the declaration is admitted alone.
    Alone,
    /// The declaration is a member of the open block. It reads its siblings
    /// before they stand, as no judgement of one declaration alone does.
    Member,
}

/// The admission schedule of a module's mutual blocks: the block it holds
/// open, and each block it opened.
///
/// Every judgement of a module in admission order steps one schedule before
/// each declaration: [`ModuleRun`], [`rejudge`], [`type_module`] and an
/// incremental pass over a module's items. So each of them opens a block where
/// the others do, and refuses it whole where they do.
///
/// # Specification
/// - executable: none — a data type; the witnesses compare a block's verdicts
///   in both checkers.
///
/// # Adequacy
/// - hypothesis: L3 — a universe and its decoder admitted as one block, a
///   declaration after the block admitted alone, and a block refused whole.
/// - witness: `tests::recursive_data::a_mutual_block_is_admitted_in_both_checkers`
/// - witness: `tests::recursive_data::a_mutual_block_is_refused_whole_in_both_checkers`
#[derive(Clone, Debug)]
pub struct Schedule
{
    /// The end of the mutual block the schedule holds open, or why none is.
    open: Maybe<ConstantIndex, open::Absent>,
    /// Each mutual block opened, by its first position and its end.
    blocks: Vec<(ConstantIndex, ConstantIndex)>,
}

impl Schedule
{
    /// A schedule that holds no block open and has opened none.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn new() -> Self
    {
        Self {
            open: Maybe::Absent(open::Absent::Lone),
            blocks: Vec::new(),
        }
    }

    /// Open the mutual block the first of `run`, the declarations from it on,
    /// leads, when it leads one, and close the block the schedule holds open
    /// once `run` passes the block's end.
    ///
    /// # Specification
    /// - requires: every earlier step was over the same declarations, in order,
    ///   in `context`; `run` is a suffix of them, in order.
    /// - ensures: a block whose end the first of `run` reaches is closed; then,
    ///   with none open, a data declaration whose fields name a later position
    ///   opens its block: the families its run of data declarations holds in
    ///   scope, each later definition's declared type formed and foreseen — one
    ///   that does not form is left to its own admission to refuse — and the
    ///   block kept among the blocks opened. The answer is
    ///   [`Membership::Member`] exactly when a block is open after the step.
    /// - provides: the first two steps of a mutual block's admission schedule;
    ///   the rest is each member's own admission, in order.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a universe and its decoder admitted as one block, and
    ///   a declaration after the block admitted alone.
    /// - witness: `tests::recursive_data::a_mutual_block_is_admitted_in_both_checkers`
    #[spec(
        captures: leader = run.clone().next().map(Declaration::constant),
        ensures: |ret| match self.open {
            Maybe::Present(end) => ret == Membership::Member
                && leader.is_some_and(|leader| leader < end),
            Maybe::Absent(_) => ret == Membership::Alone,
        },
    )]
    #[inline]
    pub fn step<'run, Run>(
        &mut self,
        context: &mut CheckingContext<'_>,
        run: Run,
    ) -> Membership
    where
        Run: Iterator<Item = &'run Declaration> + Clone,
    {
        let Some(leader) = run.clone().next()
        else {
            return self.membership();
        };
        if let Maybe::Present(end) = self.open
            && leader.constant() >= end
        {
            context.close_mutual();
            self.open = Maybe::Absent(open::Absent::Lone);
        }
        if let Maybe::Present(_) = self.open {
            // A definition of the block is judged as a lone one is: the
            // definitions foreseen for the families' fields are forgotten from
            // its own position on, so its body names none not yet admitted.
            if let crate::DeclarationContent::Value { .. } = *leader.content() {
                context.unforesee(leader.constant());
            }
            return Membership::Member;
        }
        let crate::DeclarationContent::Data(ref signature) = *leader.content()
        else {
            return Membership::Alone;
        };
        let first = leader.constant();
        let mut end = crate::occurrence::reach(context.arena(), first, signature);
        if usize::from(end) <= usize::from(first).saturating_add(1) {
            return Membership::Alone;
        }
        let mut families = Vec::new();
        let mut definitions = Vec::new();
        let mut past_families = ConstantIndex::from(usize::from(first).saturating_add(1));
        let mut phase = Members::Families;
        let mut members = 0_usize;
        for member in run.clone() {
            if member.constant() >= end {
                break;
            }
            // The block is its members' run, with no position missing: data
            // declarations at its head, definitions after them.
            if usize::from(member.constant()) != usize::from(first).saturating_add(members) {
                return Membership::Alone;
            }
            members = members.saturating_add(1);
            match (member.content(), phase) {
                (&crate::DeclarationContent::Data(ref family), Members::Families) => {
                    end = end.max(crate::occurrence::reach(
                        context.arena(),
                        member.constant(),
                        family,
                    ));
                    past_families =
                        ConstantIndex::from(usize::from(member.constant()).saturating_add(1));
                    families.push((member.constant(), alloc::sync::Arc::clone(family)));
                },
                (&crate::DeclarationContent::Value { body, .. }, _) => {
                    phase = Members::Definitions;
                    if let Maybe::Present(body) = body {
                        definitions.push((member.constant(), body));
                    }
                },
                (
                    &crate::DeclarationContent::Data(_)
                    | &crate::DeclarationContent::Codata(_)
                    | &crate::DeclarationContent::Abstract(_)
                    | &crate::DeclarationContent::World(_),
                    _,
                ) => {
                    return Membership::Alone;
                },
            }
        }
        if usize::from(first).saturating_add(members) != usize::from(end) {
            return Membership::Alone;
        }
        context.open_mutual(
            crate::occurrence::Block::new(first, past_families, end),
            families,
            definitions,
        );
        // Every definition's declared type forms before any is foreseen: a
        // declared type names the block's families, never its definitions.
        let mut foreseen = Vec::new();
        for member in run {
            if member.constant() >= end {
                break;
            }
            if let crate::DeclarationContent::Value {
                signature: Maybe::Present(declared),
                ..
            } = *member.content()
                && member.constant() >= past_families
                && let Ok(formed) = form_value_type(context, declared)
            {
                foreseen.push((member.constant(), formed));
            }
        }
        for (constant, formed) in foreseen {
            context.foresee(constant, formed);
        }
        self.open = Maybe::Present(end);
        self.blocks.push((first, end));
        Membership::Member
    }

    /// Close the block the schedule holds open, if it holds one.
    ///
    /// # Specification
    /// - requires: `context` is the context the schedule's steps were in.
    /// - ensures: no block is open.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`step`](Self::step), a module that ends inside a
    ///   block.
    /// - witness: `tests::recursive_data::a_mutual_block_is_admitted_in_both_checkers`
    #[spec(ensures: matches!(self.open, Maybe::Absent(_)))]
    #[inline]
    pub fn close(
        &mut self,
        context: &mut CheckingContext<'_>,
    )
    {
        if let Maybe::Present(_) = self.open {
            context.close_mutual();
            self.open = Maybe::Absent(open::Absent::Lone);
        }
    }

    /// Refuse each block the schedule opened whole over `entries`: once one of
    /// its members is refused, `refuse` refuses every member of it the run
    /// accepted with the first refusal, as the kernel refuses the block's one
    /// admission.
    ///
    /// # Specification
    /// - requires: `read` gives each entry's position and verdict.
    /// - ensures: inside a block holding a refused member, family or
    ///   definition, `refuse` is called once for every entry whose verdict is
    ///   [`Verdict::Data`], [`Verdict::Checked`] or [`Verdict::Synthesised`],
    ///   with the refusal of the block's first refused member and that member's
    ///   position; for no other entry.
    /// - provides: one verdict for a block, as the kernel's admission gives
    ///   one.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the clause compares every verdict before and after,
    ///   a walk of the module's verdicts no clause makes; the witness reads
    ///   them back.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a family whose own fields are positive, in a block
    ///   with a family consuming it, is refused as the block is; a universe
    ///   whose decoder is refused is refused with it.
    /// - witness: `tests::recursive_data::a_mutual_block_is_refused_whole_in_both_checkers`
    /// - witness: `tests::recursive_data::a_mutual_block_is_admitted_in_both_checkers`
    #[inline]
    pub fn refuse_whole<Entry, Read, Refuse>(
        &self,
        entries: &mut [Entry],
        read: Read,
        mut refuse: Refuse,
    ) where
        Read: Fn(&Entry) -> (ConstantIndex, Verdict),
        Refuse: FnMut(&mut Entry, CheckRefusal, ConstantIndex),
    {
        for &(first, end) in &self.blocks {
            let within = |constant: ConstantIndex| first <= constant && constant < end;
            let refused = entries.iter().find_map(|entry| match read(entry) {
                (constant, Verdict::Refused(refusal)) if within(constant) => {
                    Some((refusal, constant))
                },
                (
                    _,
                    Verdict::Refused(_)
                    | Verdict::Data
                    | Verdict::Checked { .. }
                    | Verdict::Synthesised { .. }
                    | Verdict::Owed(_)
                    | Verdict::Suspended(_),
                ) => None,
            });
            let Some((refusal, culprit)) = refused
            else {
                continue;
            };
            for entry in entries.iter_mut() {
                let (constant, verdict) = read(entry);
                if within(constant)
                    && matches!(
                        verdict,
                        Verdict::Data | Verdict::Checked { .. } | Verdict::Synthesised { .. }
                    )
                {
                    refuse(entry, refusal, culprit);
                }
            }
        }
    }

    /// Whether a block is open.
    ///
    /// # Specification
    /// trivial.
    const fn membership(&self) -> Membership
    {
        match self.open {
            Maybe::Present(_) => Membership::Member,
            Maybe::Absent(_) => Membership::Alone,
        }
    }
}

impl Default for Schedule
{
    /// [`Schedule::new`].
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn default() -> Self
    {
        Self::new()
    }
}

/// Which run of a mutual block a walk over its members is in.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Members
{
    /// The data declarations at its head: its families.
    Families,
    /// The declarations past them: its definitions.
    Definitions,
}

quenchant_shape::reason_enum! {
    /// Why a declaration's judgement keeps no term types.
    mod typed {
        /// The reason no term types are kept.
        #[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
        pub enum Absent {
            /// The run was not asked to keep them.
            Unasked,
            /// The declaration has no body that was run.
            Unrun,
        }
    }
}

quenchant_shape::reason_enum! {
    /// Why a declaration's judgement carries no filled declared type.
    mod filled {
        /// The reason no filled type is carried.
        #[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
        pub enum Absent {
            /// No body was judged, or the declared type held no hole the
            /// body's calls nominated for an omitted implicit.
            Unfilled,
        }
    }
}

/// Whether a declaration's judgement also keeps the type of every term its
/// body judges.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
enum Run
{
    /// The judgement alone.
    Judged,
    /// The judgement, and a typed run of its body at the same point.
    Typed,
}

/// Judge one declaration in `context`.
///
/// # Specification
/// - requires: nothing — an out-of-order position, an unformed signature and an
///   ill-typed body are admissible input and refused.
/// - ensures: the declaration is admitted at its position, then: a signature
///   and a body give [`Verdict::Checked`] when the body checks against the
///   formed signature; a signature and a hole give [`Verdict::Owed`] with the
///   hole's absence; a signature and a model's omitted law
///   ([`crate::body::Absent::Discharged`]) give [`Verdict::Checked`] over the
///   `here` [`crate::discharge::here`] mints when it checks, and
///   [`CheckRefusal::UndischargedLaw`] at the declared type otherwise; a body
///   alone gives [`Verdict::Synthesised`] when it synthesises; neither is
///   refused. An accepted verdict carries the body it judged — the
///   declaration's own; or, when its calls omit implicits, the body with each
///   one's hole filled by the solution the judgement bound it to; or the
///   elaboration of either when it held a computation written where a value is
///   read; each minted after the declaration's — and defines the constant as
///   that body. A call's omitted implicit no conversion determines is refused
///   as [`CheckRefusal::ImplicitUnsolved`]. The judgement reads a signature
///   through the holes its formation bound before it judges the body. A
///   signature without a body that leaves a hole unbound is refused as
///   [`CheckRefusal::ImplicitUnsolved`] at that hole. A value declaration whose
///   judgement, accepted otherwise, left a bare flex–rigid equation on a hole
///   the context holds owed, or read the type of a declaration it holds
///   suspended, is [`Verdict::Suspended`] at the type it supplies instead,
///   defines nothing, and is held suspended; a refusal wins over any residual.
///   An owed hole is held owed. A formed signature enters the signature table
///   after the body is judged, whatever the body's verdict, filled as the
///   verdict's when the body was judged again with its omitted implicits
///   filled; a signature holding a record update forms with each built as its
///   record (#2159), so it enters the table as built; a synthesised type enters
///   it after synthesis; a refused body alone enters nothing. A definition
///   quantified over stages checks at a stage minted per binder and enters the
///   table at its plain type, its stage signature kept beside it. An abstract
///   type's retention is checked where the context retains it, by
///   `CheckingContext::seal_abstract`.
/// - provides: the one obligation a declaration can owe, carried in its
///   verdict, so a caller judging a single declaration needs no ledger.
/// - fails: never; a refusal is the verdict [`Verdict::Refused`].
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the decision surfaces are the admission, the four
///   combinations of present and absent halves, and when a type enters the
///   table; separated by one declaration of each combination, an admission out
///   of order, a self-reference, and a reference after a refused signed body
///   and after a refused unsigned one.
/// - witness: `module::tests::each_combination_of_halves_gets_its_verdict`
/// - witness: `module::tests::an_admission_out_of_order_is_refused`
/// - witness: `module::tests::a_declaration_cannot_read_its_own_type`
/// - witness: `module::tests::a_refused_signed_body_still_supplies_its_type`
/// - witness: `module::tests::a_body_that_synthesised_nothing_supplies_no_type`
/// - witness: `module::tests::a_later_declaration_reads_an_earlier_type`
/// - witness: `gandr-core-checker::tests::elaboration::owed_conversion_suspends`
/// - witness: `module::tests::a_decoded_hole_in_a_signature_is_solved_where_it_forms_5026`
/// - witness: `gandr-core-checker::tests::elaboration::dependent_resumption_closes_its_prerequisites`
#[spec(
    captures: depth = context.depth(gandr_core_term::Zone::Intuitionistic),
    ensures: |ret| context.depth(gandr_core_term::Zone::Intuitionistic) == depth && match ret {
        | Verdict::Data => match *declaration.content() {
            | crate::DeclarationContent::Data(ref signature) => context.data_signatures().get(&declaration.constant()) == Some(signature),
            | crate::DeclarationContent::Codata(ref signature) => context.codata_signatures().get(&declaration.constant()) == Some(signature),
            | crate::DeclarationContent::Abstract(_) | crate::DeclarationContent::World(_) => true,
            | crate::DeclarationContent::Value { .. } => false,
        },
        | Verdict::Checked { declared, body, .. } => (matches!(declaration.content(), crate::DeclarationContent::Value { signature: Maybe::Present(_), body: Maybe::Present(value) } if *value <= body)
                || matches!(declaration.content(), crate::DeclarationContent::Value { signature: Maybe::Present(_), body: Maybe::Absent(crate::body::Absent::Discharged) }))
            && (context.signature(declaration.constant()) == Maybe::Present(declared) || !declaration.stages().is_empty()),
        | Verdict::Synthesised { synthesised, body } => matches!(declaration.content(), crate::DeclarationContent::Value { signature: Maybe::Absent(_), body: Maybe::Present(value) } if *value <= body)
            && context.signature(declaration.constant()) == Maybe::Present(synthesised.produced()),
        | Verdict::Owed(entry) => matches!(declaration.content(), crate::DeclarationContent::Value { signature: Maybe::Present(_), body: Maybe::Absent(_) })
            && entry.absence().constant() == declaration.constant()
            && entry.absence().origin() == declaration.origin()
            && (context.signature(declaration.constant()) == Maybe::Present(entry.absence().declared()) || !declaration.stages().is_empty()),
        | Verdict::Suspended(supplied) => matches!(declaration.content(), crate::DeclarationContent::Value { .. })
            && (context.signature(declaration.constant()) == Maybe::Present(supplied) || !declaration.stages().is_empty())
            && matches!(context.definitions().body(declaration.constant()), Maybe::Absent(_)),
        | Verdict::Refused(_) => true,
    },
)]
#[inline]
#[must_use]
pub fn check_declaration(
    context: &mut CheckingContext<'_>,
    declaration: &Declaration,
) -> Verdict
{
    decide(context, declaration, Run::Judged).verdict
}

/// What judging one declaration answers.
#[derive(Clone, Debug)]
struct Decision
{
    /// The verdict.
    verdict: Verdict,
    /// The failure of the run that refused the body, when one did.
    failure: Maybe<Failure, kept::Absent>,
    /// The type of every term the body judged, when asked.
    typings: Maybe<Typings, typed::Absent>,
    /// What elaborating the body did, when it held a computation written
    /// where a value is read and the first run accepted it.
    elaboration: Maybe<NestedElaboration, elaborated::Absent>,
    /// The declared type the table took, filled with the solutions of the
    /// implicits the body's calls omit, when the fill changed it.
    filled: Maybe<ValueTypeId, filled::Absent>,
    /// What the judgement left undecided, when its verdict is
    /// [`Verdict::Suspended`]; empty otherwise.
    residue: Residue,
}

/// Judge one declaration in `context`, keeping a refused body's failure, what
/// elaborating its body did and, when `run` asks, the type of every term its
/// body judges.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the verdict [`check_declaration`] gives, with the same effect on
///   `context`; beside it, when a run of the body, a step of a data signature
///   or a step forming a value's declared type refused, the failure of that run
///   or step under the binders it stood under, whose refusal is the verdict's,
///   save that a law the module omits keeps a bare failure at its declared type
///   refused [`CheckRefusal::UndischargedLaw`]; when the body's calls omit
///   implicits, the verdict of the run over the body and the declared type both
///   filled with their solutions ([`implicits`]), and the declared type so
///   filled beside the verdict when the fill changed it; when the first run
///   accepted a body holding a computation written where a value is read, a
///   value the bridge carried by a reduct, or a record update, what elaborating
///   it did, the verdict then being the second run's over the elaborated body
///   at the declared type so filled; and, when `run` is [`Run::Typed`] and the
///   body was run, what [`type_value`] keeps for the body as written, each type
///   read with the solutions of the holes its calls nominated, read before the
///   declaration's own type entered the table. An accepted value keeps, under
///   its position, the path endpoint pairs the run its verdict is from related,
///   and nothing an earlier declaration or another run related. A suspended
///   verdict carries the residue its verdict's run left; every other verdict an
///   empty one.
/// - fails: never; a refusal is the verdict [`Verdict::Refused`].
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a module with a body refused inside a thunk, a signature
///   refused before its body, and an accepted body separate the kept, the unrun
///   and the accepted answers; a nested run accepted, one refused by the second
///   run and one with nowhere to run separate the elaborated answers.
/// - witness: `module::tests::a_refused_body_keeps_the_rules_it_was_refused_inside`
/// - witness: `module::tests::a_typed_module_keeps_each_judged_body_s_term_types`
/// - witness: `tests::module::a_nested_run_elaborates_into_a_bind_before_its_region`
/// - witness: `module::tests::a_run_in_a_definition_s_own_value_is_unenclosed_only_when_effectful_4812`
/// - witness: `module::tests::an_ascription_keeps_the_endpoints_it_related`
/// - witness: `module::tests::a_typed_module_keys_what_each_run_formed`
/// - witness: `module::tests::a_refused_first_run_leaves_its_nesting_unaccepted`
/// - witness: `module::tests::an_omitted_implicit_is_typed_at_its_solution_1216`
/// - witness: `gandr-core-checker-bridge::bridge::tests::an_omitted_implicit_is_supplied_before_the_kernel_1216`
/// - witness: `gandr-core-checker::tests::elaboration::owed_conversion_suspends`
#[spec(ensures: |ret| (run == Run::Typed || matches!(ret.typings, Maybe::Absent(typed::Absent::Unasked)))
    && (matches!(ret.verdict, Verdict::Suspended(_)) == (ret.residue.pending() == Deferred::Yes))
    && match (&ret.verdict, &ret.failure) {
    | (&Verdict::Refused(refusal), &Maybe::Present(ref failure)) => failure.refusal() == refusal,
    | (&Verdict::Refused(_), &Maybe::Absent(kept::Absent::Unrun))
    | (&(Verdict::Data | Verdict::Checked { .. } | Verdict::Synthesised { .. } | Verdict::Owed(_) | Verdict::Suspended(_)), &Maybe::Absent(kept::Absent::Accepted)) => true,
        | _ => false,
    })]
#[cfg_attr(feature = "hotpath", hotpath::measure)]
fn decide(
    context: &mut CheckingContext<'_>,
    declaration: &Declaration,
    run: Run,
) -> Decision
{
    let untyped = match run {
        Run::Judged => typed::Absent::Unasked,
        Run::Typed => typed::Absent::Unrun,
    };
    let unrun = |refusal| Decision {
        verdict: Verdict::Refused(refusal),
        failure: Maybe::Absent(kept::Absent::Unrun),
        typings: Maybe::Absent(untyped),
        elaboration: Maybe::Absent(elaborated::Absent::Unnested),
        filled: Maybe::Absent(filled::Absent::Unfilled),
        residue: Residue::default(),
    };
    let constant = declaration.constant();
    #[cfg(feature = "unfolding-probe")]
    context.unfolding_subject(constant);
    // A value declaration's judgement may wait on an owed hole; a nominal
    // declaration forms rigidly.
    let collecting = match *declaration.content() {
        crate::DeclarationContent::Value { .. } => Collecting::On,
        crate::DeclarationContent::Data(_)
        | crate::DeclarationContent::Codata(_)
        | crate::DeclarationContent::Abstract(_)
        | crate::DeclarationContent::World(_) => Collecting::Off,
    };
    context.deferrals_mut().open(collecting);
    // The pairs a declaration's conversions relate, the nodes its solved
    // variables refine, and the stages its recursion typing mints, are its
    // own: whatever an earlier declaration's typing pass left is dropped.
    let _earlier = context.take_relating();
    let _earlier_restated = context.take_restating();
    context.forget_stages();
    if let Err(refusal) = context.admit(constant) {
        return unrun(refusal);
    }
    // The role is claimed before the content is judged. A declaration that
    // the judgement refuses later keeps its role.
    if let Maybe::Present(role) = declaration.builtin()
        && let Err(refusal) = context.claim_builtin(constant, role, declaration.content())
    {
        return unrun(refusal);
    }
    context.keep_laws(constant, declaration.laws().to_vec());
    context.keep_operation_rules(constant, declaration.operation_rules().clone());
    context.keep_covers(constant, declaration.covers().to_vec());
    let outer = (run == Run::Typed).then(|| context.start_typings());
    let finish = |context: &mut CheckingContext<'_>, outer: Option<Option<Kept>>| {
        outer.map(|outer| context.finish_typings(outer))
    };
    let kept = |signed: Option<Kept>| match signed {
        Some(signed) if !(signed.typings.is_empty() && signed.formed.is_empty()) => {
            Maybe::Present(Typings::after(signed, Typings::default()))
        },
        Some(_) | None => Maybe::Absent(untyped),
    };
    let formed = |verdict: Result<(), CheckRefusal>, typings| match verdict {
        Ok(()) => Decision {
            verdict: Verdict::Data,
            failure: Maybe::Absent(kept::Absent::Accepted),
            typings,
            elaboration: Maybe::Absent(elaborated::Absent::Unnested),
            filled: Maybe::Absent(filled::Absent::Unfilled),
            residue: Residue::default(),
        },
        Err(refusal) => Decision {
            typings,
            ..unrun(refusal)
        },
    };
    let (signature, body) = match *(declaration.content()) {
        crate::DeclarationContent::Data(ref signature) => {
            let verdict = crate::former::form_signature_with_failure(context, constant, signature);
            if verdict.is_ok() {
                context.record_data(constant, alloc::sync::Arc::clone(signature));
            }
            let signed = finish(context, outer);
            return match verdict {
                Ok(()) => formed(Ok(()), kept(signed)),
                // The signature's refusal keeps the binders it stood under.
                Err(failure) => {
                    let refusal = failure.refusal();
                    Decision {
                        failure: Maybe::Present(failure),
                        ..formed(Err(refusal), kept(signed))
                    }
                },
            };
        },
        crate::DeclarationContent::Codata(ref signature) => {
            let verdict = crate::codata::form_signature(context, constant, signature);
            if verdict.is_ok() {
                context.record_codata(constant, alloc::sync::Arc::clone(signature));
            }
            let signed = finish(context, outer);
            return formed(verdict, kept(signed));
        },
        crate::DeclarationContent::Abstract(declared) => {
            let verdict = crate::former::form_abstract(context, declared)
                .and_then(|level| {
                    crate::former::form_interface(context, declared, &level).map(|()| level)
                })
                .and_then(|level| founded(context, constant, declared).map(|()| level))
                .and_then(|level| context.seal_abstract(constant, declared, level))
                .map(|_atom| ());
            let signed = finish(context, outer);
            return formed(verdict, kept(signed));
        },
        crate::DeclarationContent::World(ref requirement) => {
            context.worlds_mut().declare(constant, requirement);
            let signed = finish(context, outer);
            return formed(Ok(()), kept(signed));
        },
        crate::DeclarationContent::Value {
            ref signature,
            ref body,
        } => (*signature, *body),
    };
    // A declaration with neither half is refused by the hole rule before its
    // entry matters.
    let resolved = match (body, signature) {
        (Maybe::Present(body), _) => context
            .worlds()
            .resolve(constant, declaration.entry())
            .map_err(|defect| (CoreNode::Term(TermNode::Value(body)), defect)),
        (Maybe::Absent(_), Maybe::Present(declared)) => context
            .worlds()
            .resolve(constant, declaration.entry())
            .map_err(|defect| {
                (
                    CoreNode::Type(crate::refusal::TypeNode::Value(declared)),
                    defect,
                )
            }),
        (Maybe::Absent(_), Maybe::Absent(_)) => Ok(Entry::default()),
    };
    let entry = match resolved {
        Ok(entry) => entry,
        Err((at, defect)) => {
            let signed = finish(context, outer);
            return Decision {
                typings: kept(signed),
                ..unrun(CheckRefusal::Located { at, defect })
            };
        },
    };
    let home = entry.home();
    let _host = context.binders().relocate(home);
    // A definition quantified over stages forms its signature with each binder
    // at the stage it mints, the stage the binder's ordinal names; the plain
    // type it enters the table at, and the marks its stages leave, are read
    // first, so a stage the kernel could not place refuses the signature.
    let mut quantified = None;
    let direction = match signature {
        Maybe::Present(declared) => {
            // A step that runs no machine pursues the declared type.
            let bare = move |refusal| {
                Failure::bare(
                    refusal,
                    Pursuit::new(
                        CoreNode::Type(TypeNode::Value(declared)),
                        Maybe::Absent(judged::Absent::Formed),
                        Stage::Starting,
                    ),
                )
            };
            context.deferrals_mut().signing = Signing::Signature;
            crate::quantified::bounded(declaration.stages(), declared)
                .map_err(bare)
                .and_then(|()| {
                    if !declaration.stages().is_empty() {
                        let (erased, marks) = crate::quantified::split(
                            context.arena_mut(),
                            declared,
                            declaration.stages(),
                        )
                        .map_err(bare)?;
                        quantified = Some((form_built(context, erased)?, marks));
                    }
                    crate::quantified::mint(context.stages_mut(), declaration.stages());
                    form_built(context, declared)
                })
                .and_then(|formed| {
                    crate::session::unrestricted(context, formed.id())
                        .map(|()| formed)
                        .map_err(bare)
                })
                .map(Direction::Check)
        },
        Maybe::Absent(signature::Absent::Unsigned) => Ok(Direction::Synthesise),
    };
    context.deferrals_mut().signing = Signing::Body;
    let mut signed = finish(context, outer);
    // The holes the signature's formation nominated and bound are read through
    // their solutions, so the body is judged against the type they fix. A
    // model slot the signature decides binds first, so a decode in the type
    // runs the call that omits it (#6158). A hole still unbound, an undecided
    // slot's among them, waits for the body.
    let formed = direction.and_then(|written| {
        context
            .resolve_models(declaration.models(), Signing::Signature)
            .map_err(|(at, refusal)| call_failure(refusal, at))?;
        let (filled, signing) = match context.deferrals().solutions(context.arena()) {
            Ok(solutions) if !solutions.is_empty() => {
                (formed_filled(context, written, &solutions)?, solutions)
            },
            Ok(_) | Err(_) => (written, Solutions::new()),
        };
        Ok((written, filled, signing))
    });
    // The solutions the signature bound fill the table where the body binds
    // none, as when the body is refused.
    let (written, direction, signing) = match formed {
        Ok(directions) => directions,
        // The signature's refusal keeps the binders it stood under, and
        // names what the solver bound while it formed.
        Err(failure) => {
            let failure = solved_failure(context, failure);
            let _home = context.binders().relocate(World::Host);
            let refusal = failure.refusal();
            return Decision {
                failure: Maybe::Present(failure),
                typings: kept(signed),
                ..unrun(refusal)
            };
        },
    };
    let mut spending = Spending::Unspent;
    let mut typings = Maybe::Absent(untyped);
    let mut elaboration = Maybe::Absent(elaborated::Absent::Unnested);
    let mut relating = Vec::new();
    let mut restating = Vec::new();
    let residue: Residue;
    let mut following = Maybe::Absent(crate::recursion::Unstaged::Plain);
    // The type the table takes: the declared one, filled with the solutions
    // of the implicits the body's calls omit, as the verdict carries it.
    let mut entered = direction;
    // A model's omitted law is answered by the first source of a filler that
    // checks, `here` at its left side ([`crate::discharge`]), and its body is
    // judged as a written one.
    let discharging = match (body, direction) {
        (Maybe::Absent(body::Absent::Discharged), Direction::Check(declared)) => Some(declared),
        (Maybe::Present(_) | Maybe::Absent(_), Direction::Check(_) | Direction::Synthesise) => None,
    };
    let body = match discharging.map(|declared| crate::discharge::here(context, declared)) {
        Some(Ok(minted)) => Maybe::Present(minted),
        Some(Err(refusal)) => {
            let _home = context.binders().relocate(World::Host);
            return Decision {
                typings: kept(signed),
                ..unrun(refusal)
            };
        },
        None => body,
    };
    let (verdict, failure) = match body {
        Maybe::Present(body) => {
            let _stale = context.take_nesting();
            let _stale_updates = context.take_updates();
            context.open_rows();
            context.own_body(body);
            context.supply(declaration.supplies());
            context.worlds_mut().enter(entry);
            // A scope over a theory owes the theory's laws, read through its
            // clauses where it was lowered, so on the body as lowered.
            let first = judge(context, body, direction).and_then(|verdict| {
                crate::handler::lawful(context, declaration.handler_laws()).map(|()| verdict)
            });
            let (solved, filled, first, solutions) = implicits(
                context,
                body,
                (direction, declaration.stages(), declaration.models()),
                first,
            );
            entered = filled;
            let decisions = context.take_nesting();
            let crossings = context.take_crossings();
            let updates = context.take_updates();
            // A value the bridge carried by a reduct runs the reduct at it, a
            // run the nested elaboration binds before its region; a decimal at
            // `f64` stands as its float, which no run carries, so the body is
            // elaborated where any crossing stands a value.
            let stood = crossings
                .values()
                .any(|crossing| matches!(crossing.by, Maybe::Absent(())));
            let (solved, crossed, decisions) = if first.is_ok() && !crossings.is_empty() {
                crate::nested::cross(context.arena_mut(), solved, &crossings, &decisions)
            }
            else {
                (solved, Vec::new(), decisions)
            };
            let judged = match first {
                Ok(_) if !decisions.is_empty() || !updates.is_empty() || stood => {
                    match crate::nested::elaborate(context.arena_mut(), solved, &decisions) {
                        Ok((elaborated, done)) => {
                            // An update stands as its record once every run
                            // its base or its fields hold is bound.
                            let (elaborated, done) =
                                done.updated(context.arena_mut(), elaborated, &updates, &crossed);
                            elaboration = Maybe::Present(done.after_crossing(crossings, crossed));
                            // The verdict is the second run's, and so are the
                            // pairs it relates, the nodes it refines, the rows
                            // it records and what it leaves undecided.
                            let _first = context.take_relating();
                            let _first_restated = context.take_restating();
                            context.forget_rows();
                            context.forget_stages();
                            crate::quantified::mint(context.stages_mut(), declaration.stages());
                            context.deferrals_mut().open(Collecting::On);
                            context.own_body(elaborated);
                            let second = judge(context, elaborated, filled);
                            let _second = context.take_crossings();
                            second
                        },
                        Err(unenclosed) => Err(unenclosed_failure(unenclosed.run())),
                    }
                },
                Ok(_) | Err(_) => {
                    if !decisions.is_empty() || !updates.is_empty() {
                        elaboration = Maybe::Absent(elaborated::Absent::Unaccepted);
                    }
                    first
                },
            };
            // An omitted law no source fills is refused naming the law,
            // whichever rule refused its `here`.
            let judged = match (judged, discharging) {
                (Err(_), Some(declared)) => Err(Failure::bare(
                    CheckRefusal::UndischargedLaw { at: declared.id() },
                    Pursuit::new(
                        CoreNode::Type(TypeNode::Value(declared.id())),
                        Maybe::Absent(judged::Absent::Formed),
                        Stage::Starting,
                    ),
                )),
                (judged, _) => judged,
            };
            // A refusal names what the solver bound before it.
            let judged = judged.map_err(|failure| solved_failure(context, failure));
            relating = context.take_relating();
            restating = context.take_restating();
            residue = context.deferrals_mut().take();
            following = follows(
                context,
                &judged,
                (residue.pending(), direction),
                declaration.stages(),
            );
            if let Some(signed) = signed.take() {
                // The typed run reads the table again, and those reads are no
                // part of the judgement's support.
                let held = context.hold_support();
                context.own_body(body);
                let typed = type_value(context, body, direction);
                // The bridge's crossings in the run are those of the body as
                // written, which a face reads at the values it shows.
                let crossed = context.take_crossings();
                // The run types the body as written, its omitted implicits
                // standing as holes; each type is read with their solutions.
                // A hole the body leaves unbound reads the signature's solution.
                let mut read = signing;
                read.extend(solutions.iter().map(|(&hole, &solved)| (hole, solved)));
                typings = Maybe::Present(
                    Typings::after(signed, typed.crossed(crossed))
                        .retyped(|ty, depth| solved_type(context.arena_mut(), (ty, depth), &read)),
                );
                let _typed = context.take_nesting();
                let _updated = context.take_updates();
                context.restore_support(held);
            }
            spending = context.worlds_mut().leave();
            match judged {
                Ok(verdict) => (verdict, Maybe::Absent(kept::Absent::Accepted)),
                Err(failure) => (Verdict::Refused(failure.refusal()), Maybe::Present(failure)),
            }
        },
        // A discharged body is minted above, so one reaching here is unsigned,
        // and the hole's rule refuses it as a hole's.
        Maybe::Absent(absent) => {
            // No body poses a further comparison, so the holes the signature's
            // formation nominated are solved by now or never: an unbound one
            // is refused, and the table takes the type filled.
            let solved = match context.deferrals().solutions(context.arena()) {
                Ok(solutions) => formed_filled(context, direction, &solutions)
                    .inspect(|&filled| entered = filled),
                Err((at, reason)) => Err(unsolved_failure(at, reason)),
            };
            let owed = solved
                .map_err(|failure| failure.refusal())
                .and_then(|entered| hole(entered, constant, declaration.origin()));
            let owed = owed.and_then(|absence| {
                crate::capability::held(context, constant, absence.declared())?;
                if absent == body::Absent::Hosted {
                    hosted(context, absence.declared())?;
                }
                Ok(absence)
            });
            residue = context.deferrals_mut().take();
            match owed {
                Ok(absence) => (
                    Verdict::Owed(ObligationEntry::from(absence)),
                    Maybe::Absent(kept::Absent::Accepted),
                ),
                Err(refusal @ CheckRefusal::ImplicitUnsolved { at, .. }) => (
                    Verdict::Refused(refusal),
                    Maybe::Present(call_failure(refusal, at)),
                ),
                Err(refusal) => (
                    Verdict::Refused(refusal),
                    Maybe::Absent(kept::Absent::Unrun),
                ),
            }
        },
    };
    if signed.is_some() {
        typings = kept(signed);
    }
    // A refusal wins over every residual; an accepted verdict that left one,
    // or read a waiting declaration, waits itself.
    let verdict = match (residue.pending(), verdict) {
        (Deferred::Yes, Verdict::Checked { declared, .. }) => Verdict::Suspended(declared),
        (Deferred::Yes, Verdict::Synthesised { synthesised, .. }) => {
            Verdict::Suspended(synthesised.produced())
        },
        (Deferred::Yes, Verdict::Owed(entry)) => Verdict::Suspended(entry.absence().declared()),
        (
            Deferred::Yes | Deferred::No,
            settled @ (Verdict::Data | Verdict::Refused(_) | Verdict::Suspended(_)),
        )
        | (
            Deferred::No,
            settled @ (Verdict::Checked { .. } | Verdict::Synthesised { .. } | Verdict::Owed(_)),
        ) => settled,
    };
    // The holders of `E` and `F` answer their canonical bodies, compared
    // before the table takes the definition. A refused holder keeps no role.
    let (verdict, failure) = match (declaration.builtin(), verdict) {
        (
            Maybe::Present(
                role @ (gandr_kernel_term::Builtin::IrArgs | gandr_kernel_term::Builtin::IrDecode),
            ),
            Verdict::Checked { body, .. } | Verdict::Synthesised { body, .. },
        ) => match crate::canonical::answers(context, role, (constant, body)) {
            Ok(()) => (verdict, failure),
            Err(departure) => {
                context.release_builtin(role, constant);
                (
                    Verdict::Refused(CheckRefusal::BuiltinNotCanonical { role, departure }),
                    Maybe::Absent(kept::Absent::Unrun),
                )
            },
        },
        (
            Maybe::Present(_) | Maybe::Absent(_),
            Verdict::Data
            | Verdict::Checked { .. }
            | Verdict::Synthesised { .. }
            | Verdict::Owed(_)
            | Verdict::Suspended(_)
            | Verdict::Refused(_),
        ) => (verdict, failure),
    };
    let filled = match (written, entered) {
        (Direction::Check(written), Direction::Check(entered)) if written != entered => {
            Maybe::Present(entered.id())
        },
        (Direction::Check(_) | Direction::Synthesise, _) => Maybe::Absent(filled::Absent::Unfilled),
    };
    // A definition quantified over stages enters the table at its plain type:
    // each call instantiates the stages its signature marks.
    let direction = match (entered, quantified) {
        (Direction::Check(_), Some((plain, marks))) => {
            context.keep_stage_signature(
                constant,
                gandr_kernel_term::StageSignature::new(declaration.stages().to_vec(), marks),
            );
            Direction::Check(plain)
        },
        (direction @ (Direction::Check(_) | Direction::Synthesise), _) => direction,
    };
    match (direction, verdict) {
        (Direction::Check(declared), Verdict::Checked { body, .. }) => {
            // Native declarations return before the value judgment.
            context.record(constant, declared);
            context.define(constant, declared, body);
            context.keep_relations(constant, relating);
            context.keep_restatements(constant, restating);
            if let Maybe::Present(position) = following {
                context.record_following(constant, position);
            }
        },
        (Direction::Check(declared), Verdict::Owed(_)) => {
            context.record(constant, declared);
            context.deferrals_mut().owed.insert(constant);
        },
        (Direction::Check(declared), Verdict::Suspended(_)) => {
            context.record(constant, declared);
            context.deferrals_mut().suspended.insert(constant);
        },
        (
            Direction::Check(declared),
            Verdict::Data | Verdict::Synthesised { .. } | Verdict::Refused(_),
        ) => context.record(constant, declared),
        (Direction::Synthesise, Verdict::Synthesised { synthesised, body }) => {
            context.record(constant, synthesised.produced());
            context.define(constant, synthesised.produced(), body);
            context.keep_relations(constant, relating);
            context.keep_restatements(constant, restating);
        },
        (Direction::Synthesise, Verdict::Suspended(supplied)) => {
            context.record(constant, supplied);
            context.deferrals_mut().suspended.insert(constant);
        },
        (
            Direction::Synthesise,
            Verdict::Data | Verdict::Checked { .. } | Verdict::Owed(_) | Verdict::Refused(_),
        ) => {},
    }
    context.worlds_mut().settle(constant, home, spending);
    let _home = context.binders().relocate(World::Host);
    Decision {
        verdict,
        failure,
        typings,
        elaboration,
        filled,
        residue: match verdict {
            Verdict::Suspended(_) => residue,
            Verdict::Data
            | Verdict::Checked { .. }
            | Verdict::Synthesised { .. }
            | Verdict::Owed(_)
            | Verdict::Refused(_) => Residue::default(),
        },
    }
}

/// Form the signature `declared`, then each record update its formation
/// checked built as the record it stands for, and that formed in turn.
///
/// A type's updates are checked where it forms, but conversion reads no update:
/// a signature holding one would compare it unelaborated against the record it
/// stands for (#2159). The build is the one a body's updates take
/// ([`gandr_core_term::build_type_updates`]).
///
/// # Specification
/// - requires: nothing.
/// - ensures: the formed `declared` when its formation checked no record
///   update; otherwise the formation of `declared` with every update it checked
///   standing as the record of its overlay's fields beside its base's kept
///   ones. No update the formation recorded stays recorded.
/// - fails: the failure forming `declared`, or forming the built type, under
///   the binders the formation had opened where it refused.
/// - panics: none.
/// - executable: none — the build is a walk of the type, which a predicate
///   would repeat.
///
/// # Adequacy
/// - hypothesis: L3 — two updates at distinct labels commuting, and an update
///   writing a field's own value, each read in a path type's endpoints, convert
///   to the record they build only once the signature is built.
/// - witness: `tests::module::a_record_update_in_a_signature_reads_its_record_2159`
fn form_built(
    context: &mut CheckingContext<'_>,
    declared: gandr_core_term::ValueTypeId,
) -> Result<FormedValueType, Failure>
{
    let _earlier = context.take_updates();
    let formed = form_value_type_with_failure(context, declared)?;
    let updates = context.take_updates();
    if updates.is_empty() {
        return Ok(formed);
    }
    let mut carried = Vec::new();
    let built = gandr_core_term::build_type_updates(
        context.arena_mut(),
        formed.id(),
        &updates,
        &mut carried,
    );
    form_value_type_with_failure(context, built)
}

/// Judge an accepted structural definition once more with its own fixpoint's
/// result read at the stage of the parameter it recurses on: the position of
/// that parameter when the body checks there, so a call reads the result at
/// its argument's stage.
///
/// Nothing the second judgement relates, owes, decides or mints is kept.
///
/// # Specification
/// - requires: `judged` is the verdict of the definition under way's body, with
///   nothing left pending when `pending` says so.
/// - ensures: for a checked body thunking a structural fixpoint, settled with
///   nothing pending, whose type returns the type it recurses on, the
///   parameter's position when the body checks with that result at the
///   parameter's stage; [`crate::recursion::Unstaged::Plain`] otherwise. The
///   second judgement mints the stage binders `bounds` states first, as the
///   first did. The context reads results as declared again on return.
/// - fails: never; a second judgement's refusal is
///   [`crate::recursion::Unstaged::Plain`].
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a subtraction recursing on its first argument follows it,
///   and an addition returning its accumulator does not.
/// - witness: `tests::recursion::a_result_follows_the_parameter_it_recurses_on`
#[spec(ensures: context.result_stage() == crate::recursion::ResultStage::Declared)]
fn follows(
    context: &mut CheckingContext<'_>,
    judged: &Result<Verdict, Failure>,
    (pending, direction): (Deferred, Direction<FormedValueType>),
    bounds: &[gandr_kernel_term::StageBound],
) -> Maybe<gandr_kernel_term::StagedPosition, crate::recursion::Unstaged>
{
    let plain = Maybe::Absent(crate::recursion::Unstaged::Plain);
    let (Deferred::No, &Ok(Verdict::Checked { body, .. }), Direction::Check(declared)) =
        (pending, judged, direction)
    else {
        return plain;
    };
    let Some(&gandr_core_term::Value::Thunk(root)) = context.arena().value(body)
    else {
        return plain;
    };
    let Some(&gandr_core_term::Computation::Fixpoint { evidence, .. }) =
        context.arena().computation(root)
    else {
        return plain;
    };
    let Some(recursed) = evidence.descent()
    else {
        return plain;
    };
    // Only a fixpoint whose type returns the type it recurses on is judged
    // again: no other can follow its parameter.
    let Ok(head) = context.whnf_value_type(declared.id())
    else {
        return plain;
    };
    let Some(&gandr_core_term::ValueType::Thunk(classifier)) = context.arena().value_type(head)
    else {
        return plain;
    };
    if !matches!(
        crate::recursion::returns_recursed_on(context, classifier, recursed),
        Ok(Maybe::Present(_))
    ) {
        return plain;
    }
    context.forget_stages();
    crate::quantified::mint(context.stages_mut(), bounds);
    context.deferrals_mut().open(Collecting::On);
    context.own_body(body);
    context.read_result(crate::recursion::ResultStage::Asked(root));
    let staged = judge(context, body, direction);
    let read = context.result_stage();
    context.read_result(crate::recursion::ResultStage::Declared);
    let _nesting = context.take_nesting();
    let _updates = context.take_updates();
    let _relating = context.take_relating();
    let _restating = context.take_restating();
    let _residue = context.deferrals_mut().take();
    match (staged, read) {
        (Ok(_), crate::recursion::ResultStage::Staged(position)) => Maybe::Present(position),
        (
            Ok(_) | Err(_),
            crate::recursion::ResultStage::Declared
            | crate::recursion::ResultStage::Asked(_)
            | crate::recursion::ResultStage::Staged(_),
        ) => plain,
    }
}

/// Refuse the abstract type `declared` at `atom` when its signature marks it
/// mobile and its representation does not cross: the promise a client relies
/// on is checked where the representation is visible.
///
/// # Specification
/// - requires: `declared` is formed.
/// - ensures: nothing changes.
/// - fails: [`crate::worlds::LocatedDefect::MarkUnfounded`] at the
///   representation naming the former that does not cross; the crossing
///   decision's own refusal.
/// - panics: none.
///
/// # Errors
/// As above.
///
/// # Adequacy
/// - hypothesis: L3 — a mobile mark over a string checks, one over a thunk is
///   refused at sealing.
/// - witness: `worlds::tests::a_mobility_mark_over_an_immobile_representation_is_refused_at_sealing`
#[spec(ensures: |ret| declared.mobility() == crate::worlds::Mobility::Mobile || ret.is_ok())]
fn founded(
    context: &mut CheckingContext<'_>,
    atom: ConstantIndex,
    declared: AbstractType,
) -> Result<(), CheckRefusal>
{
    if declared.mobility() == crate::worlds::Mobility::Immobile {
        return Ok(());
    }
    let representation = declared.representation();
    match crate::worlds::crosses(context, representation)? {
        crate::worlds::Crossing::Crosses => Ok(()),
        crate::worlds::Crossing::Stays { former, predicate } => Err(CheckRefusal::Located {
            at: CoreNode::Type(crate::refusal::TypeNode::Value(representation)),
            defect: crate::worlds::LocatedDefect::MarkUnfounded {
                atom,
                former,
                predicate,
            },
        }),
    }
}

/// Judge `body` in `direction`: the verdict an accepted body gets, or the
/// failure of the run that refused it.
///
/// # Specification
/// - requires: nothing.
/// - ensures: [`Verdict::Checked`] over `body` when it checks against a
///   declared type, [`Verdict::Synthesised`] over `body` when it synthesises
///   one; the run's failure otherwise.
/// - fails: the failure of the run that refused `body`.
/// - panics: none.
///
/// # Errors
/// The run's [`Failure`].
///
/// # Adequacy
/// - hypothesis: L3 — as [`decide`].
/// - witness: `module::tests::each_combination_of_halves_gets_its_verdict`
#[spec(ensures: |ret| match ret {
    | Ok(Verdict::Checked { body: judged, .. } | Verdict::Synthesised { body: judged, .. }) => judged == body,
    | Ok(_) => false,
    | Err(_) => true,
})]
fn judge(
    context: &mut CheckingContext<'_>,
    body: ValueId,
    direction: Direction<FormedValueType>,
) -> Result<Verdict, Failure>
{
    match direction {
        Direction::Synthesise => synthesise_value_with_failure(context, body)
            .map(|synthesised| Verdict::Synthesised { body, synthesised }),
        Direction::Check(declared) => {
            check_value_with_failure(context, body, declared).map(|evidence| Verdict::Checked {
                declared,
                body,
                evidence,
            })
        },
    }
}

/// Judge `body` again with each hole its calls nominated for an omitted
/// implicit filled by the solution the run `first` bound it to, each model
/// slot of `models` the run met first resolved to its one candidate, against
/// the declared type filled alike.
///
/// # Specification
/// - requires: `first` is the run over `body` in `direction` that left the
///   collector as it stands; `models` are the slots the declaration's calls
///   omit.
/// - ensures: `body`, `direction`, `first` and no solution when the run met no
///   nominated hole, or refused with no type it compares holding a hole of a
///   slot of `models`; the resolution's refusal,
///   [`CheckRefusal::ModelUnanswered`], [`CheckRefusal::ModelAmbiguous`] or
///   [`CheckRefusal::Undecided`], at the first hole of the first slot it
///   refuses, when the run checked or when it refused at a compared type
///   holding such a hole; with `body`, `direction` and no solution in the
///   second case; the refusal of the run that refused otherwise; the run's
///   failure as [`CheckRefusal::ImplicitUnsolved`] at the first hole the solver
///   left unbound; otherwise the filled body, minted after `body`, the
///   direction with its declared type filled and formed again
///   ([`formed_filled`]), a fresh run of the one against the other, the pairs,
///   stages and residue `first` left dropped as the nesting elaboration's
///   second run drops them, and the solutions both were filled with. A filled
///   type that does not form gives the failure forming it in place of the fresh
///   run.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a call whose argument determines its implicit, one whose
///   two arguments disagree on it and one whose arguments determine none
///   separate the filled run, the refuted run and the unsolved refusal; a call
///   omitting a model slot one module answers runs as that module supplied. A
///   declared type that decodes through a slot two modules answer, or none, is
///   refused as the slot's resolution refuses it.
/// - witness: `gandr-core-checker-bridge::bridge::tests::an_omitted_implicit_is_supplied_before_the_kernel_1216`
/// - witness: `gandr-core-checker-bridge::bridge::tests::an_omitted_implicit_is_refused_unforced_or_apart_1216`
/// - witness: `elaboration::tests::a_model_slot_resolves_to_the_candidate_its_sort_admits_739`
/// - witness: `gandr-core-checker-bridge::bridge::tests::a_stated_type_s_undecided_slot_is_refused_by_its_resolution_6195`
#[spec(
    captures: refused = first.is_err(),
    ensures: |ret| ret.0 >= body && (!refused || (ret.0 == body && ret.3.is_empty())),
)]
fn implicits(
    context: &mut CheckingContext<'_>,
    body: ValueId,
    (direction, stages, models): (
        Direction<FormedValueType>,
        &[gandr_kernel_term::StageBound],
        &[gandr_core_term::model::ModelSlot],
    ),
    first: Result<Verdict, Failure>,
) -> (
    ValueId,
    Direction<FormedValueType>,
    Result<Verdict, Failure>,
    Solutions,
)
{
    if let &Err(ref failure) = &first {
        // A refusal that compares a type holding a hole of an omitted model
        // slot met the slot unresolved: the declared type decodes through it,
        // and the signature left it to the body. The slots resolve now, so the
        // refusal names the modules that answer, or the slot no module
        // answers. Any other refusal stands.
        let compared = failure.refusal().compared();
        let meets = !models.is_empty()
            && [compared.expected, compared.found, compared.unfolded]
                .into_iter()
                .any(|side| {
                    let holes = match side {
                        Maybe::Present(TypeNode::Value(ty)) => {
                            gandr_core_term::value_type_holes(context.arena_mut(), ty)
                        },
                        Maybe::Present(TypeNode::Computation(ty)) => {
                            gandr_core_term::comp_type_holes(context.arena_mut(), ty)
                        },
                        Maybe::Absent(_) => BTreeSet::new(),
                    };
                    models
                        .iter()
                        .any(|slot| slot.holes.iter().any(|hole| holes.contains(hole)))
                });
        if meets && let Err((at, refusal)) = context.resolve_models(models, Signing::Body) {
            return (
                body,
                direction,
                Err(call_failure(refusal, at)),
                Solutions::new(),
            );
        }
        return (body, direction, first, Solutions::new());
    }
    if let Err((at, refusal)) = context.resolve_models(models, Signing::Body) {
        return (
            body,
            direction,
            Err(call_failure(refusal, at)),
            Solutions::new(),
        );
    }
    let solutions = match context.deferrals().solutions(context.arena()) {
        Ok(solutions) if solutions.is_empty() => return (body, direction, first, solutions),
        Ok(solutions) => solutions,
        Err((at, reason)) => {
            return (
                body,
                direction,
                Err(unsolved_failure(at, reason)),
                Solutions::new(),
            );
        },
    };
    let filled = fill(context.arena_mut(), body, &solutions);
    let _first = context.take_relating();
    let _first_restated = context.take_restating();
    let _stale = context.take_nesting();
    let _stale_updates = context.take_updates();
    let _crossed = context.take_crossings();
    context.forget_stages();
    crate::quantified::mint(context.stages_mut(), stages);
    let direction = match formed_filled(context, direction, &solutions) {
        Ok(direction) => direction,
        Err(failure) => return (filled, direction, Err(failure), solutions),
    };
    context.deferrals_mut().open(Collecting::On);
    context.own_body(filled);
    let judged = judge(context, filled, direction);
    (filled, direction, judged, solutions)
}

/// `direction` with the type it checks against read with every solution in
/// `solutions`, as [`fill`] reads a body, and formed again where the fill
/// changes it.
///
/// The fill mints each node it changes, and a formation records the dialogues
/// of each reflexivity it checks by node. So the filled type forms again, and
/// each reflexivity its endpoints hold carries its dialogues at the node that
/// crosses to the kernel (#5521).
///
/// # Specification
/// - requires: as [`fill`]; the declared type stands under no binder.
/// - ensures: [`Direction::Check`] of the declared type with each hole
///   `solutions` names filled and formed as [`form_built`] forms it, or of the
///   declared type itself when it holds none; [`Direction::Synthesise`]
///   unchanged.
/// - fails: the failure forming the filled type, under the binders the
///   formation had opened where it refused.
/// - panics: none.
///
/// # Errors
/// As `fails`.
///
/// # Adequacy
/// - hypothesis: L3 — a path type whose endpoints call a definition over an
///   omitted model is met by a point calling it alike once the models are
///   resolved, and a path returned at a path type over calls of their own
///   converts; judging the filled body against the type as written leaves the
///   endpoints on their unfilled holes, and both are refused. A reflexivity in
///   the type's endpoints over a call whose implicit the signature binds
///   crosses with the dialogues of the filled type, and the kernel admits it.
/// - witness: `gandr-core-checker-bridge::bridge::tests::an_endpoint_over_an_omitted_model_waits_for_its_resolution_2391`
/// - witness: `gandr-core-checker-bridge::bridge::tests::a_path_type_over_an_omitted_model_converts_once_resolved_2391`
/// - witness: `gandr-core-checker-bridge::bridge::tests::a_filled_signature_s_reflexivity_crosses_with_its_dialogues_5521`
#[spec(ensures: |ret| ret.as_ref().is_err_and(|_| matches!(direction, Direction::Check(_)))
    || ret.as_ref().is_ok_and(|filled| matches!(filled, Direction::Synthesise) == matches!(direction, Direction::Synthesise)))]
fn formed_filled(
    context: &mut CheckingContext<'_>,
    direction: Direction<FormedValueType>,
    solutions: &Solutions,
) -> Result<Direction<FormedValueType>, Failure>
{
    let Direction::Check(declared) = direction
    else {
        return Ok(direction);
    };
    match solved_type(
        context.arena_mut(),
        (
            TypeNode::Value(declared.id()),
            gandr_core_term::BinderDepth::default(),
        ),
        solutions,
    ) {
        TypeNode::Value(filled) if filled != declared.id() => {
            form_built(context, filled).map(Direction::Check)
        },
        TypeNode::Value(_) | TypeNode::Computation(_) => Ok(direction),
    }
}

/// `body` with each hole `solutions` names filled by its solution, read
/// through every solution another one mentions.
///
/// # Specification
/// - requires: no solution mentions its own hole, through others or directly:
///   the solver's occurs check.
/// - ensures: `body` with every hole `solutions` names replaced, each solution
///   raised past the binders between its scope and where the hole stands,
///   minted after `body`, or `body` itself when it holds none.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a solution mentioning a hole solved after it is read
///   through, raised past the binders between the two.
/// - witness: `module::tests::a_solution_naming_a_later_hole_is_read_through_1216`
/// - witness: `gandr-core-checker-bridge::bridge::tests::an_omitted_implicit_is_supplied_before_the_kernel_1216`
#[spec(ensures: |ret| ret >= body)]
fn fill(
    arena: &mut gandr_core_term::CoreArena,
    body: ValueId,
    solutions: &Solutions,
) -> ValueId
{
    gandr_core_term::fill_value_holes(arena, (body, gandr_core_term::Binders::NONE), solutions)
}

/// `ty`, a type a typed run recorded under `depth` intuitionistic binders,
/// read with every solution in `solutions`, as [`fill`] reads a body.
///
/// # Specification
/// - requires: as [`fill`].
/// - ensures: `ty` in its own family, each hole `solutions` names that stands
///   inside its solution's scope replaced, raised past the binders between;
///   `ty` itself when it holds none, or when `depth` is past the count a binder
///   index can name.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the type of a call's head instantiated at the hole reads
///   at the solved implicit.
/// - witness: `module::tests::a_solution_naming_a_later_hole_is_read_through_1216`
#[spec(ensures: |ret| core::mem::discriminant(&ret) == core::mem::discriminant(&ty))]
fn solved_type(
    arena: &mut gandr_core_term::CoreArena,
    (ty, depth): (TypeNode, gandr_core_term::BinderDepth),
    solutions: &Solutions,
) -> TypeNode
{
    let Ok(under) = u32::try_from(usize::from(depth)).map(gandr_core_term::Binders::from)
    else {
        return ty;
    };
    match ty {
        TypeNode::Value(id) => TypeNode::Value(gandr_core_term::fill_value_type_holes(
            arena,
            (id, under),
            solutions,
        )),
        TypeNode::Computation(id) => TypeNode::Computation(gandr_core_term::fill_comp_type_holes(
            arena,
            (id, under),
            solutions,
        )),
    }
}

/// `failure` with each type its refusal compares read through every solution
/// the solver holds now. A hole the solver left unbound stays a hole.
///
/// # Specification
/// - requires: `context`'s deferrals are those of the run that refused.
/// - ensures: `failure` whose [`Failure::solved`] reads each type its refusal
///   compares through [`crate::elaboration::Deferrals::bound`], as
///   [`solved_type`] reads it under the binders the failure stood under, where
///   a solution changes one; the refusal itself unchanged.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a mismatch at a call whose argument bound its implicit
///   reads the found type at the solution.
/// - witness: `module::tests::a_refusal_names_the_implicit_its_call_solved_5033`
#[spec(
    captures: refusal = failure.refusal(),
    ensures: |ret| ret.refusal() == refusal,
)]
fn solved_failure(
    context: &mut CheckingContext<'_>,
    failure: Failure,
) -> Failure
{
    let bound = context.deferrals().bound(context.arena());
    if bound.is_empty() {
        return failure;
    }
    let depth = gandr_core_term::BinderDepth::from(failure.hypotheses().len());
    let compared = failure.refusal().compared();
    let mut read = |side| match side {
        Maybe::Present(written) => {
            Maybe::Present(solved_type(context.arena_mut(), (written, depth), &bound))
        },
        absent @ Maybe::Absent(_) => absent,
    };
    let solved = crate::refusal::Compared {
        expected: read(compared.expected),
        found: read(compared.found),
        unfolded: read(compared.unfolded),
    };
    if solved == compared {
        failure
    }
    else {
        failure.solved_as(solved)
    }
}

/// The failure of a body whose call omits an implicit the solver left
/// unbound at `at`, the hole the call nominated, for `reason`.
///
/// # Specification
/// trivial.
fn unsolved_failure(
    at: ValueId,
    reason: crate::Unsolved,
) -> Failure
{
    call_failure(CheckRefusal::ImplicitUnsolved { at, reason }, at)
}

/// The failure `refusal` of a body's call, pursued at the hole `at` the call
/// nominated.
///
/// # Specification
/// trivial.
fn call_failure(
    refusal: CheckRefusal,
    at: ValueId,
) -> Failure
{
    Failure::bare(
        refusal,
        Pursuit::new(
            CoreNode::Term(TermNode::Value(at)),
            Maybe::Absent(judged::Absent::Synthesised),
            Stage::Starting,
        ),
    )
}

/// The failure of a body whose elaboration found the effectful `run` with no
/// computation around it: no rule of the judgement is pending, and the
/// refusal names the run.
///
/// # Specification
/// trivial.
fn unenclosed_failure(run: ValueId) -> Failure
{
    Failure::bare(
        CheckRefusal::UnenclosedRun { at: run },
        Pursuit::new(
            CoreNode::Term(TermNode::Value(run)),
            Maybe::Absent(judged::Absent::Synthesised),
            Stage::Starting,
        ),
    )
}

/// Judge one declaration in `context`, and report the signature answers the
/// judgement consulted and the form the table holds the declaration in.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the verdict [`check_declaration`] gives, with the same effect on
///   `context`; beside it, every answer the judgement read from the signature
///   table, once per position, ascending by position, and no answer read before
///   this call; and [`Entered::Elaborated`] exactly when the verdict defines a
///   body and the table departs from the written declaration, as [`entered`]
///   states; and the failure of a refused run, as [`ModuleReport::failures`]
///   keeps it. An answer at an earlier position is the table's answer after the
///   call. An answer at a later position is the one the open mutual block
///   foresaw when the judgement read it, which the table can drop after the
///   call; outside a block, a later position answers untyped.
/// - provides: the support an incremental caller compares pointwise before it
///   reuses the verdict: equal answers mean an equal judgement, because the
///   signature table is the only input outside the declaration the judgement
///   reads. A caller that seats the written form in place of the judgement
///   reuses only an [`Entered::AsWritten`] verdict.
/// - fails: never; a refusal is the verdict [`Verdict::Refused`].
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the surfaces are the log's span and its canonical form,
///   separated by an unsupported judgement before a supported one, a supported
///   one reading positions out of order and one twice, a read of an unadmitted
///   position, and a refusal that stops the run before a later read; a
///   declaration whose omitted implicit is filled separates the two entered
///   forms.
/// - witness: `module::tests::the_support_holds_each_consulted_answer_once_in_position_order`
/// - witness: `module::tests::a_refusal_cuts_the_support_where_the_run_stopped`
/// - witness: `gandr-core-checker-bridge::bridge::tests::a_declaration_whose_implicit_is_filled_enters_elaborated_6549`
#[spec(ensures: |ret| {
    let entries = ret.support().consulted();
    entries.iter().zip(entries.iter().skip(1)).all(|(left, right)| left.constant() < right.constant())
        && entries.iter().all(|entry| match entry.constant().cmp(&declaration.constant()) {
            core::cmp::Ordering::Less => entry.answer() == context.signature(entry.constant()),
            core::cmp::Ordering::Equal => entry.answer() == Maybe::Absent(crate::context::signature_table::Absent::Untyped),
            core::cmp::Ordering::Greater => true,
        })
})]
#[inline]
#[must_use]
pub fn check_declaration_supported(
    context: &mut CheckingContext<'_>,
    declaration: &Declaration,
) -> Supported
{
    context.start_support();
    let decision = decide(context, declaration, Run::Judged);
    let entered = entered(context, declaration, decision.verdict);
    let residue = match decision.verdict {
        Verdict::Suspended(_) => Maybe::Present(decision.residue),
        Verdict::Data
        | Verdict::Checked { .. }
        | Verdict::Synthesised { .. }
        | Verdict::Owed(_)
        | Verdict::Refused(_) => Maybe::Absent(waits::Absent::Unsuspended),
    };
    Supported::new(
        (decision.verdict, context.finish_support(), entered),
        decision.failure,
        (decision.elaboration, residue),
    )
}

/// The form the table holds `declaration` in after its judgement gave
/// `verdict`.
///
/// # Specification
/// - requires: `verdict` is the judgement of `declaration` that `context` has
///   just entered.
/// - ensures: [`Entered::AsWritten`] for a verdict that defines no body;
///   otherwise [`Entered::Elaborated`] exactly when the verdict's body is not
///   the written body, the table's type is not the written signature, or the
///   table keeps a stage signature or a following position for the declaration.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — as [`check_declaration_supported`].
/// - witness: `gandr-core-checker-bridge::bridge::tests::a_declaration_whose_implicit_is_filled_enters_elaborated_6549`
#[spec(ensures: |ret| ret == Entered::AsWritten
    || matches!(verdict, Verdict::Checked { .. } | Verdict::Synthesised { .. }))]
fn entered(
    context: &CheckingContext<'_>,
    declaration: &Declaration,
    verdict: Verdict,
) -> Entered
{
    let constant = declaration.constant();
    let (
        &crate::DeclarationContent::Value { signature, body },
        Verdict::Checked { body: judged, .. } | Verdict::Synthesised { body: judged, .. },
    ) = (declaration.content(), verdict)
    else {
        return Entered::AsWritten;
    };
    let signed = match signature {
        Maybe::Present(written) => {
            matches!(context.signature(constant), Maybe::Present(formed) if formed.id() == written)
        },
        Maybe::Absent(_) => true,
    };
    let plain = matches!(context.following(constant), Maybe::Absent(_))
        && !context.stage_signatures().contains_key(&constant);
    if body == Maybe::Present(judged) && signed && plain {
        Entered::AsWritten
    }
    else {
        Entered::Elaborated
    }
}

/// Judge every declaration of a module, in the order given.
///
/// # Specification
/// - requires: nothing.
/// - ensures: one [`Judged`] per declaration, in the order given, each carrying
///   the verdict [`check_declaration`] gives at that point of the run; the
///   ledger holds exactly the owed verdicts' entries, in order; each suspended
///   verdict keeps its [`Suspension`] under its position, built over the holes
///   owed and the suspensions kept when it was judged, and no other verdict has
///   one; the lifts are every lift the context's value bridges recorded by the
///   run's end, the function extensionalities every one it decided, the
///   endpoint relations every pair an accepted declaration's conversions
///   related, and the definitions every body the context defines a constant as;
///   each body run and refused, and each declared type that did not form, keeps
///   its failure under its position, and no other declaration has one; each
///   body the first run accepted holding a computation written where a value is
///   read keeps its elaboration under its position.
/// - provides: total marking — a refused declaration does not stop the run.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the surfaces are the run's totality and the ledger's
///   feed, separated by a module mixing every verdict, with a refusal before
///   later declarations, asserted entry by entry, and the ledger asserted to
///   hold the owed entries and no refused one; a hole a later declaration
///   decodes separates a suspension from the refusal ordinary checking gave.
/// - witness: `module::tests::a_refusal_does_not_stop_the_run`
/// - witness: `module::tests::every_owed_hole_enters_the_ledger_in_order`
/// - witness: `module::tests::a_refusal_never_enters_the_ledger`
/// - witness: `module::tests::a_refused_body_keeps_the_rules_it_was_refused_inside`
/// - witness: `gandr-core-checker::tests::elaboration::owed_conversion_suspends`
#[cfg_attr(
    dylint_lib = "quenchant_dylints",
    expect(
        spec_clause_traversal,
        reason = "parity: the body judges every declaration and copies the context's lifts and definitions into the report; the check compares each copy once; #104 owns the cost of the clause"
    )
)]
#[spec(ensures: |ret| ret.judged().len() == declarations.len()
    && ret.judged().iter().zip(declarations).all(|(judged, declaration)|
        judged.constant() == declaration.constant() && judged.origin() == declaration.origin())
    && ret.ledger().entries().iter().copied().eq(ret.judged().iter().filter_map(|judged| match judged.verdict() {
        | Verdict::Owed(entry) => Some(entry),
        | Verdict::Data | Verdict::Checked { .. } | Verdict::Synthesised { .. } | Verdict::Suspended(_) | Verdict::Refused(_) => None,
    }))
    && ret.suspensions().keys().copied().eq(ret.judged().iter().filter(|judged| matches!(judged.verdict(), Verdict::Suspended(_))).map(Judged::constant))
    && ret.lifts() == context.lifts()
    && ret.funexts() == context.funexts()
    && ret.coercions() == context.coercions()
    && ret.equivalences() == context.equivalences()
    && ret.flows() == context.flows()
    && ret.directed() == context.directed()
    && ret.motives() == context.motives()
    && ret.payloads() == context.payloads()
    && ret.handled() == context.handled()
    && ret.rows() == context.rows()
    && ret.reflexivities() == context.reflexivities()
    && ret.relations() == context.relations()
    && ret.restatements() == context.restatements()
    && ret.natives() == context.natives()
    && ret.definitions().iter().map(|(&constant, &body)| (constant, body))
        .eq(context.definitions().definitions())
    && ret.failures().iter().all(|(constant, failure)|
        ret.judged().iter().any(|judged| judged.constant() == *constant
            && judged.verdict() == Verdict::Refused(failure.refusal()))))]
#[inline]
#[must_use]
pub fn check_module(
    context: &mut CheckingContext<'_>,
    declarations: &[Declaration],
) -> ModuleReport
{
    run(context, declarations, |_, _, _| {})
}

/// Judge `declarations` in order, as [`check_module`] states, handing each
/// declaration's verdict to `settle` the moment it is judged, before the next
/// declaration is.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the report [`check_module`] states; `settle` is called once per
///   declaration, in order, with the context as the judgement left it and the
///   verdict judged then, before a mutual block's refusal is spread over it.
/// - provides: the seat a term-producing run reads each verdict's recorded
///   transports from before the next judgement restarts them.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — as [`check_module`]; a term-producing run emitting a lift
///   recorded by one declaration and none by the next separates a settlement
///   called per declaration from one called once.
/// - witness: `module::tests::a_refusal_does_not_stop_the_run`
/// - witness: `gandr-core-checker::tests::elaboration::shared_code_occurrences_keep_distinct_transports`
#[spec(ensures: |ret| ret.judged().len() == declarations.len())]
#[inline]
pub fn run<Settle>(
    context: &mut CheckingContext<'_>,
    declarations: &[Declaration],
    settle: Settle,
) -> ModuleReport
where
    Settle: FnMut(&mut CheckingContext<'_>, &Declaration, Verdict),
{
    let mut run = ModuleRun::new();
    run.judge(context, declarations, settle);
    run.finish(context)
}

quenchant_shape::reason_enum! {
    /// Why a run decides a declaration in place of taking its decision.
    pub mod taken {
        /// The reason a run takes no decision of a declaration.
        #[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
        pub enum Absent {
            /// The caller holds no standing decision of the declaration.
            Unheld,
        }
    }
}

/// A decision that a run takes from its caller in place of its own.
///
/// It holds the verdict of a declaration that the caller entered into the
/// context, and the failure, the elaboration and the suspension that its
/// judgement kept.
///
/// # Specification
/// - executable: none — a data type; the witness takes each accepted
///   declaration of a module from the report of a whole run.
///
/// # Adequacy
/// - hypothesis: L3 — as [`ModuleRun::judge_taking`].
/// - witness: `module::tests::a_run_that_takes_each_accepted_declaration_reports_as_the_whole_run_6620`
#[derive(Clone, Debug)]
pub struct Taken
{
    /// The verdict.
    verdict: Verdict,
    /// The failure of the run that refused the body, when the judgement kept
    /// one.
    failure: Maybe<Failure, kept::Absent>,
    /// What elaborating the body did, when the judgement kept it.
    elaboration: Maybe<NestedElaboration, elaborated::Absent>,
    /// What the declaration waits on, when its verdict is suspended.
    suspension: Maybe<Suspension, waits::Absent>,
}

impl Taken
{
    /// The decision `verdict`, beside the `failure`, the `elaboration` and the
    /// `suspension` that its judgement kept.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn new(
        verdict: Verdict,
        (failure, elaboration, suspension): (
            Maybe<Failure, kept::Absent>,
            Maybe<NestedElaboration, elaborated::Absent>,
            Maybe<Suspension, waits::Absent>,
        ),
    ) -> Self
    {
        Self {
            verdict,
            failure,
            elaboration,
            suspension,
        }
    }
}

/// What a run asks of each declaration that it judges alone, before it decides
/// the declaration.
pub trait Taking
{
    /// The decision of `declaration` that the caller holds, which this call
    /// enters into `context`; or why the run decides the declaration.
    ///
    /// # Specification
    /// - requires: the run has judged each declaration before `declaration`.
    /// - ensures: on a decision, `context` holds `declaration` as the judgement
    ///   that gave the decision left it: admitted at its position, with its
    ///   type, its definition, its home and its stages; on an absence,
    ///   `context` is unchanged.
    /// - panics: none.
    /// - executable: none — a trait method whose implementors are untrusted;
    ///   the run's report is the check.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a run that takes each accepted declaration from the
    ///   report of a whole run reports as that run.
    /// - witness: `module::tests::a_run_that_takes_each_accepted_declaration_reports_as_the_whole_run_6620`
    fn take(
        &mut self,
        context: &mut CheckingContext<'_>,
        declaration: &Declaration,
    ) -> Maybe<Taken, taken::Absent>;
}

/// The caller that holds no decision, so the run decides each declaration.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct Deciding;

impl Taking for Deciding
{
    /// No decision: the run decides `_declaration`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn take(
        &mut self,
        _context: &mut CheckingContext<'_>,
        _declaration: &Declaration,
    ) -> Maybe<Taken, taken::Absent>
    {
        Maybe::Absent(taken::Absent::Unheld)
    }
}

/// A module run part way: the verdicts of the declarations judged so far and
/// the schedule's state after the last of them, so that judging the rest
/// later continues the run.
///
/// A run judged in stretches reports what one run over every stretch reports.
/// Together with a [`crate::context::Checkpoint`] taken where a stretch ends,
/// it lets a module's leading declarations be judged once and every revision
/// of the declarations after them be judged on a copy.
///
/// # Specification
/// - executable: none — a data type; the witness compares a run judged in two
///   stretches, resumed between them, with one run.
///
/// # Adequacy
/// - hypothesis: L3 — a module whose mutual block ends where the first stretch
///   ends reports what one run reports.
/// - witness: `tests::recursive_data::a_run_resumed_from_a_checkpoint_judges_as_one_run_776`
#[derive(Clone, Debug)]
pub struct ModuleRun
{
    /// One entry per declaration judged, in order.
    judged: Vec<Judged>,
    /// The holes owed, in the order met.
    ledger: ObligationLedger,
    /// The failure of each body refused, and each declared type that did not
    /// form, by position.
    failures: BTreeMap<ConstantIndex, Failure>,
    /// What elaborating each body with a nested computation did, by position.
    nested_elaborations: BTreeMap<ConstantIndex, NestedElaboration>,
    /// What each suspended declaration waits on, by position.
    suspensions: BTreeMap<ConstantIndex, Suspension>,
    /// The schedule of the module's mutual blocks.
    schedule: Schedule,
    /// What the run keeps of each declaration's typed run, once asked to.
    typed: Option<TypedModule>,
    /// The verdict and the support of each declaration decided outside a
    /// mutual block, by position, once asked to.
    supported: Option<BTreeMap<ConstantIndex, Supported>>,
}

impl ModuleRun
{
    /// A run that has judged nothing.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn new() -> Self
    {
        Self {
            judged: Vec::new(),
            ledger: ObligationLedger::new(),
            failures: BTreeMap::new(),
            nested_elaborations: BTreeMap::new(),
            suspensions: BTreeMap::new(),
            schedule: Schedule::new(),
            typed: None,
            supported: None,
        }
    }

    /// Judge `declarations` in order after the ones judged so far, handing
    /// each verdict to `settle` the moment it is judged, as [`run`] does.
    ///
    /// # Specification
    /// - requires: `context` is the context the declarations judged so far were
    ///   judged in, or one resumed from a checkpoint taken after the last of
    ///   them; `declarations` follow them in the module, and hold every member
    ///   of each mutual block they begin: the schedule opens a block only when
    ///   it sees all of its members.
    /// - ensures: one more verdict per declaration, in order; `settle` is
    ///   called once per declaration, as [`run`] states.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`ModuleRun`].
    /// - witness: `tests::recursive_data::a_run_resumed_from_a_checkpoint_judges_as_one_run_776`
    /// - witness: `module::tests::a_refusal_does_not_stop_the_run`
    #[spec(
        captures: before = self.judged.len(),
        ensures: self.judged.len() == before.saturating_add(declarations.len()),
    )]
    #[inline]
    pub fn judge<Settle>(
        &mut self,
        context: &mut CheckingContext<'_>,
        declarations: &[Declaration],
        settle: Settle,
    ) where
        Settle: FnMut(&mut CheckingContext<'_>, &Declaration, Verdict),
    {
        self.judge_retiring(context, declarations, settle, &Unretired)
            .whole();
    }

    /// Judge `declarations` as [`judge`](Self::judge) does, polling
    /// `retirement` before each of them.
    ///
    /// # Specification
    /// - requires: as [`judge`](Self::judge).
    /// - ensures: [`Polled::Whole`] when every poll answered wanted, the run
    ///   then as [`judge`](Self::judge) leaves it; otherwise
    ///   [`Polled::Retired`] with what the first poll to answer retired named,
    ///   the declarations before that poll judged and none from it on.
    ///   `retirement` is polled once before each declaration judged, and once
    ///   more when it retires the run.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a run polled to retirement before its second
    ///   declaration judges the first alone, and the run nobody retires judges
    ///   as [`judge`](Self::judge) does.
    /// - witness: `module::tests::a_retired_run_judges_nothing_after_its_poll_1663`
    #[spec(
        captures: before = self.judged.len(),
        ensures: |ret| if matches!(ret, Polled::Whole(())) {
            self.judged.len() == before.saturating_add(declarations.len())
        } else {
            self.judged.len() < before.saturating_add(declarations.len())
        },
    )]
    #[inline]
    pub fn judge_retiring<Settle, Poll>(
        &mut self,
        context: &mut CheckingContext<'_>,
        declarations: &[Declaration],
        settle: Settle,
        retirement: &Poll,
    ) -> Polled<(), Poll::Retired, ()>
    where
        Settle: FnMut(&mut CheckingContext<'_>, &Declaration, Verdict),
        Poll: Retirement,
    {
        self.judge_taking(context, declarations, settle, (retirement, &mut Deciding))
    }

    /// Judge `declarations` as [`judge_retiring`](Self::judge_retiring) does,
    /// but take from `taking` the decision of each declaration that the run
    /// judges alone and that `taking` holds. The run decides each other
    /// declaration.
    ///
    /// # Specification
    /// - requires: as [`judge`](Self::judge); each decision that `taking` gives
    ///   is the decision that a judgement of the declaration gives at this
    ///   point of the run.
    /// - ensures: as [`judge_retiring`](Self::judge_retiring). A taken
    ///   declaration keeps its laws, its operation's rules and its matches in
    ///   `context`, as its judgement keeps them. The run keeps its failure, its
    ///   elaboration and its suspension as `taking` gives them, and keeps no
    ///   support of it. A run that keeps typings takes nothing, and nor does a
    ///   member of a mutual block.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a run that takes each accepted declaration of a
    ///   module from the report of a whole run, and decides the owed and the
    ///   refused ones, reports the verdicts, the definitions, the failures and
    ///   the ledger of the whole run.
    /// - witness: `module::tests::a_run_that_takes_each_accepted_declaration_reports_as_the_whole_run_6620`
    #[spec(
        captures: before = self.judged.len(),
        ensures: |ret| if matches!(ret, Polled::Whole(())) {
            self.judged.len() == before.saturating_add(declarations.len())
        } else {
            self.judged.len() < before.saturating_add(declarations.len())
        },
    )]
    #[inline]
    pub fn judge_taking<Settle, Poll, Take>(
        &mut self,
        context: &mut CheckingContext<'_>,
        declarations: &[Declaration],
        mut settle: Settle,
        (retirement, taking): (&Poll, &mut Take),
    ) -> Polled<(), Poll::Retired, ()>
    where
        Settle: FnMut(&mut CheckingContext<'_>, &Declaration, Verdict),
        Poll: Retirement,
        Take: Taking + ?Sized,
    {
        for (index, declaration) in declarations.iter().enumerate() {
            if let Demand::Retired(retired) = retirement.demand() {
                return Polled::Retired(retired, ());
            }
            let membership = self.schedule.step(
                context,
                declarations.get(index ..).unwrap_or_default().iter(),
            );
            let kind = match self.typed {
                Some(_) => Run::Typed,
                None => Run::Judged,
            };
            let taken = if membership == Membership::Alone && self.typed.is_none() {
                taking.take(context, declaration)
            }
            else {
                Maybe::Absent(taken::Absent::Unheld)
            };
            let (decision, suspension) = match taken {
                Maybe::Present(taken) => {
                    let constant = declaration.constant();
                    context.keep_laws(constant, declaration.laws().to_vec());
                    context.keep_operation_rules(constant, declaration.operation_rules().clone());
                    context.keep_covers(constant, declaration.covers().to_vec());
                    (
                        Decision {
                            verdict: taken.verdict,
                            failure: taken.failure,
                            typings: Maybe::Absent(typed::Absent::Unasked),
                            elaboration: taken.elaboration,
                            filled: Maybe::Absent(filled::Absent::Unfilled),
                            residue: Residue::default(),
                        },
                        taken.suspension,
                    )
                },
                Maybe::Absent(_) => {
                    let decision = match self.supported {
                        // A member of an open block reads its siblings before
                        // they stand, as no judgement of one declaration alone
                        // does.
                        Some(ref mut supported) if membership == Membership::Alone => {
                            #[cfg(feature = "instrument")]
                            let before = context.tally();
                            context.start_support();
                            let decision = decide(context, declaration, kind);
                            let support = context.finish_support();
                            let entered = entered(context, declaration, decision.verdict);
                            let kept = Supported::new(
                                (decision.verdict, support, entered),
                                Maybe::Absent(kept::Absent::Reported),
                                (
                                    Maybe::Absent(elaborated::Absent::Reported),
                                    Maybe::Absent(waits::Absent::Reported),
                                ),
                            );
                            // The counts layer charges these consults to the
                            // item a pass takes the verdict for.
                            #[cfg(feature = "instrument")]
                            let kept = kept.consulting(context.tally().since(before));
                            let _replaced = supported.insert(declaration.constant(), kept);
                            decision
                        },
                        Some(_) | None => decide(context, declaration, kind),
                    };
                    (decision, Maybe::Absent(waits::Absent::Unsuspended))
                },
            };
            if let Some(ref mut typed) = self.typed {
                if let Verdict::Refused(refusal) = decision.verdict {
                    let _replaced = typed.refused.insert(declaration.constant(), refusal);
                }
                if let Maybe::Present(typings) = decision.typings {
                    let _replaced = typed.typings.insert(declaration.constant(), typings);
                }
                if let Maybe::Present(filled) = decision.filled {
                    let _replaced = typed.filled.insert(declaration.constant(), filled);
                }
            }
            if let Maybe::Present(failure) = decision.failure {
                self.failures.insert(declaration.constant(), failure);
            }
            if let Maybe::Present(elaboration) = decision.elaboration {
                self.nested_elaborations
                    .insert(declaration.constant(), elaboration);
            }
            match decision.verdict {
                Verdict::Owed(entry) => self.ledger.record(entry),
                Verdict::Suspended(declared) => {
                    let suspension = match suspension {
                        Maybe::Present(taken) => taken,
                        Maybe::Absent(_) => Suspension::new(
                            declared,
                            decision.residue,
                            &context.deferrals().owed,
                            &self.suspensions,
                        ),
                    };
                    self.suspensions.insert(declaration.constant(), suspension);
                },
                Verdict::Data
                | Verdict::Checked { .. }
                | Verdict::Synthesised { .. }
                | Verdict::Refused(_) => {},
            }
            settle(context, declaration, decision.verdict);
            self.judged.push(Judged::new(
                declaration.constant(),
                declaration.origin(),
                decision.verdict,
            ));
        }
        Polled::Whole(())
    }

    /// Keep, from here on, what [`type_module`] keeps of each declaration
    /// judged: the types its typed run formed and judged, the declared type
    /// its judgement filled, and its refusal. Each declaration is then decided
    /// as [`type_module`] decides it, which judges it as [`check_module`] does
    /// and then types its body as written.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn keep_typings(&mut self)
    {
        self.typed = Some(TypedModule::default());
    }

    /// What the run kept of the declarations judged since
    /// [`keep_typings`](Self::keep_typings), or nothing if it was never asked;
    /// the run keeps nothing more after.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn take_typings(&mut self) -> Option<TypedModule>
    {
        self.typed.take()
    }

    /// Keep, from here on, the verdict and the support of each declaration
    /// decided outside a mutual block: the support that
    /// [`check_declaration_supported`] records of the same declaration in the
    /// same context. The report then holds them ([`ModuleReport::supported`]).
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn keep_supports(&mut self)
    {
        self.supported = Some(BTreeMap::new());
    }

    /// The report of every declaration judged: the mutual block left open
    /// closed, a block's refusal spread over its members, and the context's
    /// tables read.
    ///
    /// # Specification
    /// - requires: `context` is the context the last declaration was judged in.
    /// - ensures: the report [`check_module`] states of the declarations
    ///   judged, in order.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`ModuleRun`].
    /// - witness: `tests::recursive_data::a_run_resumed_from_a_checkpoint_judges_as_one_run_776`
    #[spec(
        captures: before = self.judged.len(),
        ensures: |ret| ret.judged().len() == before,
    )]
    #[must_use]
    #[inline]
    pub fn finish(
        self,
        context: &mut CheckingContext<'_>,
    ) -> ModuleReport
    {
        let Self {
            mut judged,
            ledger,
            mut failures,
            nested_elaborations,
            suspensions,
            mut schedule,
            typed: _,
            supported,
        } = self;
        schedule.close(context);
        schedule.refuse_whole(
            &mut judged,
            |entry| (entry.constant(), entry.verdict()),
            |entry, refusal, culprit| {
                *entry = Judged::new(entry.constant(), entry.origin(), Verdict::Refused(refusal));
                if let Some(failure) = failures.get(&culprit).cloned() {
                    failures.insert(entry.constant(), failure);
                }
            },
        );
        ModuleReport::read(
            context,
            (judged, ledger),
            failures,
            nested_elaborations,
            suspensions,
            supported.unwrap_or_default(),
        )
    }
}

impl Default for ModuleRun
{
    /// [`ModuleRun::new`].
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn default() -> Self
    {
        Self::new()
    }
}

/// Judge the declaration at `target` of `declarations` once more, after
/// admitting every declaration before it as an earlier run answered it.
///
/// Each value declaration enters through `adopt`, never judged again, and each
/// nominal declaration is formed again.
///
/// # Specification
/// - requires: `declarations` is the module an earlier run judged, with at most
///   the declaration at `target` changed; `adopt` admits a value declaration
///   from that run's answer.
/// - ensures: every declaration before `target` is admitted in order, mutual
///   blocks scheduled as [`check_module`] schedules them; the answer is the
///   verdict [`check_declaration`] then gives the declaration at `target`, with
///   the residue it left when it is suspended.
/// - fails: the refusal `adopt` gives; [`CheckRefusal::MachineInvariant`] when
///   no declaration is at `target`.
/// - panics: none.
///
/// # Errors
/// As above.
///
/// # Adequacy
/// - hypothesis: L2/L3 — a resumption agreeing with a batch run of the filled
///   module, and judgement counts unchanged on the adopted prefix, separate
///   adoption from judging again.
/// - witness: `gandr-core-checker::tests::elaboration::incremental_equals_from_scratch`
/// - witness: `gandr-core-checker::tests::elaboration::checked_success_is_stable_without_rejudgement`
#[spec(ensures: |ret| ret.as_ref().is_err() || ret.as_ref().is_ok_and(|&(verdict, ref residue)|
    matches!(verdict, Verdict::Suspended(_)) == (residue.pending() == Deferred::Yes)))]
#[inline]
pub fn rejudge<Adopt>(
    context: &mut CheckingContext<'_>,
    declarations: &[Declaration],
    target: ConstantIndex,
    mut adopt: Adopt,
) -> Result<(Verdict, Residue), CheckRefusal>
where
    Adopt: FnMut(&mut CheckingContext<'_>, &Declaration) -> Result<(), CheckRefusal>,
{
    let position = declarations
        .iter()
        .position(|declaration| declaration.constant() == target)
        .ok_or(CheckRefusal::MachineInvariant)?;
    let mut schedule = Schedule::new();
    for (index, declaration) in declarations.iter().enumerate().take(position) {
        let _membership = schedule.step(
            context,
            declarations.get(index ..).unwrap_or_default().iter(),
        );
        match *declaration.content() {
            crate::DeclarationContent::Value { .. } => adopt(context, declaration)?,
            crate::DeclarationContent::Data(_)
            | crate::DeclarationContent::Codata(_)
            | crate::DeclarationContent::Abstract(_)
            | crate::DeclarationContent::World(_) => {
                let _formed = decide(context, declaration, Run::Judged);
            },
        }
    }
    let judged = declarations
        .get(position)
        .ok_or(CheckRefusal::MachineInvariant)?;
    let _membership = schedule.step(
        context,
        declarations.get(position ..).unwrap_or_default().iter(),
    );
    let decision = decide(context, judged, Run::Judged);
    Ok((decision.verdict, decision.residue))
}

/// What [`type_module`] keeps of a module's typed run: the types each
/// declaration's run formed and judged, the declared type each judgement
/// filled, and the refusal of each declaration the run refused.
#[derive(Clone, Debug, Default)]
pub struct TypedModule
{
    /// What each declaration's run formed or judged, by its constant.
    typings: BTreeMap<ConstantIndex, Typings>,
    /// The declared type each judgement filled with the solutions of the
    /// implicits its body's calls omit, as the table took it, by its
    /// constant.
    filled: BTreeMap<ConstantIndex, ValueTypeId>,
    /// The refusal of each declaration the run refused, by its constant.
    refused: BTreeMap<ConstantIndex, CheckRefusal>,
}

impl TypedModule
{
    /// What each declaration's run formed or judged, by its constant.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn typings(&self) -> &BTreeMap<ConstantIndex, Typings>
    {
        &self.typings
    }

    /// The declared type each judgement filled with the solutions of the
    /// implicits its body's calls omit, as the table took it, by its
    /// constant.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn filled(&self) -> &BTreeMap<ConstantIndex, ValueTypeId>
    {
        &self.filled
    }

    /// The refusal of each declaration the run refused, by its constant.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn refused(&self) -> &BTreeMap<ConstantIndex, CheckRefusal>
    {
        &self.refused
    }
}

/// Judge `declarations` in order, as [`check_module`] does, keeping the type
/// of every term each judged body judges and the refusal of every
/// declaration refused.
///
/// # Specification
/// - requires: nothing.
/// - ensures: `context` is left as [`check_module`] leaves it, every
///   declaration judged in order; each declaration whose run formed a type or
///   judged a term, refused or not, is keyed in the typings by its constant
///   with what [`type_value`] keeps for it, read before its own type entered
///   the table: a judged body, a hole's formed signature, a data declaration's
///   formed kind and the components a refused signature formed before its
///   refusal; a declaration whose run formed nothing is not keyed. Each
///   declaration whose judgement filled its declared type with the solutions of
///   the implicits its body's calls omit is keyed in the filled types by its
///   constant with the type the table took, and no other is. Each declaration
///   the run refused is keyed in the refusals by its constant with the refusal
///   its verdict carries, and no other is.
/// - provides: the type of every term a module's bodies judge, and the refusal
///   of every declaration refused, for a face answering a position inside a
///   declaration.
/// - fails: never; a refusal is kept as the typed run's mark and its
///   declaration's refusal.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a module of an accepted body, a refused body and a hole
///   keys all three, the hole by its signature alone, and separates the
///   accepted body's own type from its parts'; data declarations and a
///   signature refused at its second component keep what they formed, and a
///   signature refused before forming anything is not keyed; the refused body's
///   refusal, and no other declaration's, is kept.
/// - witness: `module::tests::a_typed_module_keeps_each_judged_body_s_term_types`
/// - witness: `module::tests::a_typed_module_keys_what_each_run_formed`
#[spec(ensures: |ref ret| ret.typings.keys().chain(ret.filled.keys()).chain(ret.refused.keys()).all(|constant|
    declarations.iter().any(|declaration| declaration.constant() == *constant)))]
#[inline]
#[must_use]
pub fn type_module(
    context: &mut CheckingContext<'_>,
    declarations: &[Declaration],
) -> TypedModule
{
    let mut typed = TypedModule::default();
    let mut schedule = Schedule::new();
    for (index, declaration) in declarations.iter().enumerate() {
        let _membership = schedule.step(
            context,
            declarations.get(index ..).unwrap_or_default().iter(),
        );
        let decision = decide(context, declaration, Run::Typed);
        if let Verdict::Refused(refusal) = decision.verdict {
            let _replaced = typed.refused.insert(declaration.constant(), refusal);
        }
        if let Maybe::Present(typings) = decision.typings {
            let _replaced = typed.typings.insert(declaration.constant(), typings);
        }
        if let Maybe::Present(filled) = decision.filled {
            let _replaced = typed.filled.insert(declaration.constant(), filled);
        }
    }
    schedule.close(context);
    typed
}

/// The hole rule, in both directions.
///
/// # Specification
/// - requires: nothing.
/// - ensures: in checking position the hole absorbs the expected type and owes
///   it as the absence of the declaration at `constant`.
/// - fails: [`CheckRefusal::NotSynthesisable`] naming the hole in synthesis
///   position.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — holes under a formed signature and without a signature
///   expose either the exact owed type, position and origin or the named
///   synthesis refusal; unformed signatures are rejected before this rule.
/// - witness: `module::tests::each_combination_of_halves_gets_its_verdict`
/// - witness: `module::tests::every_owed_hole_enters_the_ledger_in_order`
#[spec(ensures: |ret| match direction {
    | Direction::Check(expected) => ret.is_ok_and(|absence| absence.constant() == constant
        && absence.declared() == expected && absence.origin() == origin),
    | Direction::Synthesise => ret == Err(CheckRefusal::NotSynthesisable { form: CheckingForm::Hole(constant) }),
})]
fn hole(
    direction: Direction<FormedValueType>,
    constant: ConstantIndex,
    origin: OriginToken,
) -> Result<Absence, CheckRefusal>
{
    match direction {
        Direction::Check(expected) => Ok(Absence::new(constant, expected, origin)),
        Direction::Synthesise => Err(CheckRefusal::NotSynthesisable {
            form: CheckingForm::Hole(constant),
        }),
    }
}

/// Whether the host asserts `declared`: some law of its law table, stated
/// over its primitive, converts with it.
///
/// # Specification
/// - requires: `declared` is formed.
/// - ensures: `Ok` exactly when, for some row of
///   [`gandr_core_term::primitive::PRELUDE`] and some law
///   [`gandr_core_term::primitive::Primitive::laws`] lists for it, the
///   statement [`gandr_core_term::primitive::Primitive::law_statement`] mints
///   forms and converts with `declared`; a statement that does not form or
///   convert is another row's to match.
/// - fails: [`CheckRefusal::UnassertedLaw`] at `declared` when none does.
/// - panics: none.
/// - executable: none — the search is the predicate.
///
/// # Errors
/// As `- fails:`.
///
/// # Adequacy
/// - hypothesis: L3 — a law at the integers stated through a model's own
///   component is admitted, reflexivity at the floats and a statement over an
///   ordering are refused.
/// - witness: `module::tests::a_hosted_law_is_admitted_only_where_the_host_asserts_it_2302`
fn hosted(
    context: &mut CheckingContext<'_>,
    declared: FormedValueType,
) -> Result<(), CheckRefusal>
{
    for primitive in gandr_core_term::primitive::PRELUDE.iter().copied() {
        let Some((_, laws)) = primitive.laws()
        else {
            continue;
        };
        for &law in laws {
            let Some(statement) = primitive.law_statement(law, context.arena_mut())
            else {
                continue;
            };
            let Ok(statement) = crate::formation::form_value_type(context, statement)
            else {
                continue;
            };
            if matches!(
                crate::conversion::equivalent(context, declared.id(), statement.id()),
                Ok(crate::conversion::Agreement::Convertible)
            ) {
                return Ok(());
            }
        }
    }
    Err(CheckRefusal::UnassertedLaw { at: declared.id() })
}

#[cfg(test)]
mod tests;
