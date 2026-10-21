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
//! refused rather than from a second one. A declaration refused before its body
//! was run — out of order, a signature that did not form, a data signature, a
//! hole in synthesis position — keeps none: no rule of the judgement was
//! pending. [`check_declaration`] runs the same judgement and hands back the
//! verdict alone. Witness:
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
//! `data U { PiC : (a : U, b : +U (el(a) -> -F U)) --> U }` names `el`, whose
//! declared type names `U` — and inside the decoder's own fixpoint its
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

use alloc::collections::BTreeMap;
use alloc::vec::Vec;

use anodized::spec;
use gandr_core_term::ValueId;
use gandr_core_term::world::World;
use gandr_kernel_term::ConstantIndex;
use quenchant_shape::shape::Maybe;

use crate::code::EndpointRelation;
use crate::code::Lift;
use crate::code::Reflexivity;
use crate::context::CheckingContext;
use crate::declaration::AbstractType;
use crate::declaration::Declaration;
use crate::declaration::OriginToken;
use crate::declaration::body;
use crate::declaration::signature;
use crate::elaboration::Collecting;
use crate::elaboration::Deferred;
use crate::elaboration::Residue;
use crate::elaboration::Suspension;
use crate::equiv::Equivalence;
use crate::failure::Failure;
use crate::failure::Pursuit;
use crate::failure::Stage;
use crate::failure::judged;
use crate::formation::FormedValueType;
use crate::formation::form_value_type;
use crate::funext::Funext;
use crate::judgement::Checked;
use crate::judgement::Direction;
use crate::judgement::Kept;
use crate::judgement::Synthesised;
use crate::judgement::Typings;
use crate::judgement::check_value_with_failure;
use crate::judgement::synthesise_value_with_failure;
use crate::judgement::type_value;
use crate::ledger::Absence;
use crate::ledger::ObligationEntry;
use crate::ledger::ObligationLedger;
use crate::nested::NestedElaboration;
use crate::refusal::CheckRefusal;
use crate::refusal::CheckingForm;
use crate::refusal::CoreNode;
use crate::refusal::TermNode;
use crate::seal::SealTable;
use crate::support::Supported;
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

/// Open the mutual block the first of `run`, the declarations from it on,
/// leads, when it leads one, and close the block a run left open once it passes
/// the block's end.
///
/// # Specification
/// - requires: `open` is what the previous call left, over the same
///   declarations; `run` is a suffix of them, in order.
/// - ensures: a block whose end the first of `run` reaches is closed; then,
///   with none open, a data declaration whose fields name a later position
///   opens its block: the families its run of data declarations holds in scope,
///   each later definition's declared type formed and foreseen — one that does
///   not form is left to its own admission to refuse — and the block's end
///   returned in `open`.
/// - provides: the first two steps of a mutual block's admission schedule; the
///   rest is each member's own admission, in order.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a universe and its decoder admitted as one block, and a
///   declaration after the block admitted alone.
/// - witness: `tests::recursive_data::a_mutual_block_is_admitted_in_both_checkers`
#[spec(ensures: match *open {
    Maybe::Present(end) => run.first().is_some_and(|leader| leader.constant() < end),
    Maybe::Absent(_) => true,
})]
fn schedule(
    context: &mut CheckingContext<'_>,
    run: &[Declaration],
    open: &mut Maybe<ConstantIndex, open::Absent>,
)
{
    let Some(leader) = run.first()
    else {
        return;
    };
    if let Maybe::Present(end) = *open
        && leader.constant() >= end
    {
        context.close_mutual();
        *open = Maybe::Absent(open::Absent::Lone);
    }
    if let Maybe::Present(_) = *open {
        // A definition of the block is judged as a lone one is: the
        // definitions foreseen for the families' fields are forgotten from
        // its own position on, so its body names none not yet admitted.
        if let crate::DeclarationContent::Value { .. } = *leader.content() {
            context.unforesee(leader.constant());
        }
        return;
    }
    let crate::DeclarationContent::Data(ref signature) = *leader.content()
    else {
        return;
    };
    let first = leader.constant();
    let mut end = crate::occurrence::reach(context.arena(), first, signature);
    if usize::from(end) <= usize::from(first).saturating_add(1) {
        return;
    }
    let mut families = Vec::new();
    let mut definitions = Vec::new();
    let mut past_families = ConstantIndex::from(usize::from(first).saturating_add(1));
    let mut phase = Members::Families;
    let mut members = 0_usize;
    for member in run {
        if member.constant() >= end {
            break;
        }
        // The block is its members' run, with no position missing: data
        // declarations at its head, definitions after them.
        if usize::from(member.constant()) != usize::from(first).saturating_add(members) {
            return;
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
                | &crate::DeclarationContent::World,
                _,
            ) => {
                return;
            },
        }
    }
    if usize::from(first).saturating_add(members) != usize::from(end) {
        return;
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
    *open = Maybe::Present(end);
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

/// Refuse each mutual block of `blocks` whole: once one of its members is
/// refused, every member of it the run accepted is refused with the first
/// refusal, as the kernel refuses the block's one admission.
///
/// # Specification
/// - requires: `judged` holds one entry per declaration of the module, in
///   order, and `blocks` the run's blocks as first and end positions.
/// - ensures: inside a block holding a refused member, family or definition,
///   every member judged [`Verdict::Data`], [`Verdict::Checked`] or
///   [`Verdict::Synthesised`] is judged [`Verdict::Refused`] with the refusal
///   of the block's first refused member, under a copy of its failure when it
///   kept one; every other entry unchanged.
/// - provides: one verdict for a block, as the kernel's admission gives one.
/// - fails: never.
/// - panics: none.
/// - executable: none — the clause compares every verdict before and after, a
///   walk of the module's verdicts no clause makes; the witness reads them
///   back.
///
/// # Adequacy
/// - hypothesis: L3 — a family whose own fields are positive, in a block with a
///   family consuming it, is refused as the block is; a universe whose decoder
///   is refused is refused with it.
/// - witness: `tests::recursive_data::a_mutual_block_is_refused_whole_in_both_checkers`
/// - witness: `tests::recursive_data::a_mutual_block_is_admitted_in_both_checkers`
fn refuse_whole(
    blocks: &[(ConstantIndex, ConstantIndex)],
    judged: &mut [Judged],
    failures: &mut BTreeMap<ConstantIndex, Failure>,
)
{
    for &(first, end) in blocks {
        let within = |constant: ConstantIndex| first <= constant && constant < end;
        let refused = judged.iter().find_map(|entry| match entry.verdict {
            Verdict::Refused(refusal) if within(entry.constant) => {
                Some((refusal, failures.get(&entry.constant).cloned()))
            },
            Verdict::Refused(_)
            | Verdict::Data
            | Verdict::Checked { .. }
            | Verdict::Synthesised { .. }
            | Verdict::Owed(_)
            | Verdict::Suspended(_) => None,
        });
        let Some((refusal, failure)) = refused
        else {
            continue;
        };
        for entry in judged.iter_mut() {
            if within(entry.constant)
                && matches!(
                    entry.verdict,
                    Verdict::Data | Verdict::Checked { .. } | Verdict::Synthesised { .. }
                )
            {
                entry.verdict = Verdict::Refused(refusal);
                if let Some(ref failure) = failure {
                    failures.insert(entry.constant, failure.clone());
                }
            }
        }
    }
}

/// The judgement's answer for one declaration.
///
/// An accepted verdict carries the body it judged, so a consumer re-deriving
/// the declaration — the kernel bridge — reads everything it needs here.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Verdict
{
    /// A nominal declaration that formed: a native data declaration's complete
    /// signature, or a sealed abstract type's kind and representation, its
    /// atom minted.
    Data,
    /// The body checked against the declared type.
    Checked
    {
        /// The declared type.
        declared: FormedValueType,
        /// The body checked.
        body: ValueId,
        /// The check's evidence.
        evidence: Checked,
    },
    /// The unsigned body synthesised its type.
    Synthesised
    {
        /// The body synthesised.
        body: ValueId,
        /// The synthesis's evidence.
        synthesised: Synthesised<FormedValueType>,
    },
    /// The body is a hole under a declared type, owed.
    Owed(ObligationEntry),
    /// The declaration waits on owed holes: its judgement left a bare
    /// flex–rigid equation on an owed code constant, or read the type of a
    /// declaration that waits. Nothing is defined for it; it supplies the type
    /// it carries, and the report keeps its [`Suspension`] under its position.
    Suspended(FormedValueType),
    /// The declaration was refused.
    Refused(CheckRefusal),
}

/// One declaration's verdict, beside the position and origin it was offered
/// with.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct Judged
{
    /// The declaration's admission position.
    constant: ConstantIndex,
    /// The declaration's origin, echoed back.
    origin: OriginToken,
    /// The verdict.
    verdict: Verdict,
}

impl Judged
{
    /// The declaration's admission position.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn constant(&self) -> ConstantIndex
    {
        self.constant
    }

    /// The declaration's origin.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn origin(&self) -> OriginToken
    {
        self.origin
    }

    /// The verdict.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn verdict(&self) -> Verdict
    {
        self.verdict
    }
}

/// A module's verdicts, in the order given, and the obligations they owe.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct ModuleReport
{
    /// One entry per declaration, in the order given.
    judged: Vec<Judged>,
    /// The holes owed, in the order met.
    ledger: ObligationLedger,
    /// The codes the run checked at a universe above their own, by node.
    lifts: BTreeMap<ValueId, Lift>,
    /// The function extensionalities the run decided, by node.
    funexts: BTreeMap<ValueId, Funext>,
    /// The universe equivalences the run decided, by node.
    equivalences: BTreeMap<ValueId, Equivalence>,
    /// The session statements the run decided, by node.
    flows: BTreeMap<ValueId, crate::flow::Statement>,
    /// The forward and function flows the run decided, by node.
    directed: BTreeMap<ValueId, crate::forward::Directed>,
    /// The reflexivities the run checked, by node.
    reflexivities: BTreeMap<ValueId, Reflexivity>,
    /// The path endpoint pairs each accepted declaration's type conversions
    /// related, by position, with each derivation.
    relations: BTreeMap<ConstantIndex, Vec<EndpointRelation>>,
    /// The laws each lawful declaration's folds rest on, by position, in its
    /// folded type's rule order.
    laws: BTreeMap<ConstantIndex, Vec<ConstantIndex>>,
    /// The rules of the operation each ruled declaration lowered from, by
    /// position.
    operation_rules: BTreeMap<ConstantIndex, gandr_kernel_term::OperationRules>,
    /// The stage signature of each definition quantified over stages, by
    /// position.
    stage_signatures: BTreeMap<ConstantIndex, gandr_kernel_term::StageSignature>,
    /// The native path each univalence statement the run decided derives, and
    /// each path product it judged elaborates to, by node.
    natives: BTreeMap<ValueId, ValueId>,
    /// The body each accepted declaration defines its constant as, elaborated
    /// to the universe it was declared at, by position.
    definitions: BTreeMap<ConstantIndex, ValueId>,
    /// Native signatures retained for kernel readmission.
    data_signatures: BTreeMap<ConstantIndex, alloc::sync::Arc<gandr_core_term::DataSignature>>,
    /// Codata signatures retained for kernel readmission.
    codata_signatures: BTreeMap<ConstantIndex, alloc::sync::Arc<gandr_core_term::CodataSignature>>,
    /// The sealed abstract types that formed, by position, for kernel
    /// readmission.
    abstract_types: BTreeMap<ConstantIndex, AbstractType>,
    /// The failure of each body the judgement refused, by position.
    failures: BTreeMap<ConstantIndex, Failure>,
    /// What elaborating each body that held a computation written where a
    /// value is read did, by position.
    nested_elaborations: BTreeMap<ConstantIndex, NestedElaboration>,
    /// The sealing sites the run minted atoms for, in minting order.
    seal_table: SealTable,
    /// The world declarations admitted, by position.
    worlds: alloc::collections::BTreeSet<ConstantIndex>,
    /// What each suspended declaration waits on, by position.
    suspensions: BTreeMap<ConstantIndex, Suspension>,
}

impl ModuleReport
{
    /// The successfully formed nominal signatures.
    ///
    /// # Specification
    /// trivial.
    #[must_use]
    #[inline]
    pub const fn data_signatures(
        &self
    ) -> &BTreeMap<ConstantIndex, alloc::sync::Arc<gandr_core_term::DataSignature>>
    {
        &self.data_signatures
    }

    /// The successfully formed codata signatures.
    ///
    /// # Specification
    /// trivial.
    #[must_use]
    #[inline]
    pub const fn codata_signatures(
        &self
    ) -> &BTreeMap<ConstantIndex, alloc::sync::Arc<gandr_core_term::CodataSignature>>
    {
        &self.codata_signatures
    }

    /// The sealed abstract types that formed, by position.
    ///
    /// # Specification
    /// trivial.
    #[must_use]
    #[inline]
    pub const fn abstract_types(&self) -> &BTreeMap<ConstantIndex, AbstractType>
    {
        &self.abstract_types
    }

    /// The world declarations admitted, by position: positions no kernel
    /// term carries.
    ///
    /// # Specification
    /// trivial.
    #[must_use]
    #[inline]
    pub const fn worlds(&self) -> &alloc::collections::BTreeSet<ConstantIndex>
    {
        &self.worlds
    }

    /// The sealing sites the run minted atoms for, in minting order: the
    /// record a re-elaboration verifies with [`SealTable::verify_reminting`].
    ///
    /// # Specification
    /// trivial.
    #[must_use]
    #[inline]
    pub const fn seal_table(&self) -> &SealTable
    {
        &self.seal_table
    }

    /// One entry per declaration, in the order given.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn judged(&self) -> &[Judged]
    {
        &self.judged
    }

    /// The holes owed, in the order met.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn ledger(&self) -> &ObligationLedger
    {
        &self.ledger
    }

    /// The codes the run checked at a universe above their own, by node.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn lifts(&self) -> &BTreeMap<ValueId, Lift>
    {
        &self.lifts
    }

    /// The function extensionalities the run decided, by node, with the
    /// evaluations each component replays.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn funexts(&self) -> &BTreeMap<ValueId, Funext>
    {
        &self.funexts
    }

    /// The universe equivalences the run decided, by node, with the evidence
    /// each round trip replays.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn equivalences(&self) -> &BTreeMap<ValueId, Equivalence>
    {
        &self.equivalences
    }

    /// The session statements the run decided, by node, with the engine's
    /// pairs the kernel replays.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn flows(&self) -> &BTreeMap<ValueId, crate::flow::Statement>
    {
        &self.flows
    }

    /// The forward and function flows the run decided, by node, with the
    /// images and dialogues the kernel replays.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn directed(&self) -> &BTreeMap<ValueId, crate::forward::Directed>
    {
        &self.directed
    }

    /// The reflexivities the run checked, by node, with the dialogues relating
    /// each point to its endpoints.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn reflexivities(&self) -> &BTreeMap<ValueId, Reflexivity>
    {
        &self.reflexivities
    }

    /// The path endpoint pairs each accepted declaration's type conversions
    /// related, by position, with the derivation relating each pair: what the
    /// declaration crosses to the kernel carrying.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn relations(&self) -> &BTreeMap<ConstantIndex, Vec<EndpointRelation>>
    {
        &self.relations
    }

    /// The laws each lawful declaration's folds rest on, by position, in its
    /// folded type's rule order: what the declaration crosses to the kernel
    /// carrying.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn laws(&self) -> &BTreeMap<ConstantIndex, Vec<ConstantIndex>>
    {
        &self.laws
    }

    /// The rules of the operation each ruled declaration lowered from, by
    /// position: what the declaration crosses to the kernel carrying.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn operation_rules(
        &self
    ) -> &BTreeMap<ConstantIndex, gandr_kernel_term::OperationRules>
    {
        &self.operation_rules
    }

    /// The stage signature of each definition quantified over stages, by
    /// position: what the definition crosses to the kernel carrying beside
    /// its plain declared type.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn stage_signatures(
        &self
    ) -> &BTreeMap<ConstantIndex, gandr_kernel_term::StageSignature>
    {
        &self.stage_signatures
    }

    /// The native path each univalence statement the run decided derives, and
    /// each path product it judged elaborates to, by node: what the statement
    /// or the product crosses to the kernel as.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn natives(&self) -> &BTreeMap<ValueId, ValueId>
    {
        &self.natives
    }

    /// The body each accepted declaration defines its constant as: its body,
    /// lifted to the universe it was declared at when the body is a code of a
    /// smaller one.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn definitions(&self) -> &BTreeMap<ConstantIndex, ValueId>
    {
        &self.definitions
    }

    /// The failure of each body the judgement refused, by position; a
    /// declaration refused before its body was run, or accepted, has no entry.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn failures(&self) -> &BTreeMap<ConstantIndex, Failure>
    {
        &self.failures
    }

    /// What elaborating each body that held a computation written where a
    /// value is read did, by position: the decisions, the rebuilt nodes beside
    /// the nodes they were built from, and each minted bind beside its run.
    /// A body the first run refused, or that held none, has no entry.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn nested_elaborations(&self) -> &BTreeMap<ConstantIndex, NestedElaboration>
    {
        &self.nested_elaborations
    }

    /// What each suspended declaration waits on, by position: one entry per
    /// [`Verdict::Suspended`] verdict, and none for any other.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn suspensions(&self) -> &BTreeMap<ConstantIndex, Suspension>
    {
        &self.suspensions
    }
}

quenchant_shape::reason_enum! {
    /// Why a declaration's judgement keeps no failure.
    mod kept {
        /// The reason no failure is kept.
        #[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
        pub enum Absent {
            /// The declaration was not refused.
            Accepted,
            /// The declaration was refused before its body was run.
            Unrun,
        }
    }
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
    /// Why a declaration's judgement carries no elaboration.
    mod elaborated {
        /// The reason no elaboration is carried.
        #[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
        pub enum Absent {
            /// The body held no computation written where a value is read, or
            /// there was no body.
            Unnested,
            /// The first run refused the body, so nothing was elaborated.
            Unaccepted,
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
///   hole's absence; a body alone gives [`Verdict::Synthesised`] when it
///   synthesises; neither is refused. An accepted verdict carries the body it
///   judged — the declaration's own, or its elaboration when the body held a
///   computation written where a value is read, minted after it — and defines
///   the constant as that body. A value declaration whose judgement, accepted
///   otherwise, left a bare flex–rigid equation on a hole the context holds
///   owed, or read the type of a declaration it holds suspended, is
///   [`Verdict::Suspended`] at the type it supplies instead, defines nothing,
///   and is held suspended; a refusal wins over any residual. An owed hole is
///   held owed. A formed signature enters the signature table after the body is
///   judged, whatever the body's verdict; a synthesised type enters it after
///   synthesis; a refused body alone enters nothing. A definition quantified
///   over stages checks at a stage minted per binder and enters the table at
///   its plain type, its stage signature kept beside it. An abstract type's
///   retention is checked where the context retains it, by
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
/// - witness: `elaboration::tests::owed_conversion_suspends`
/// - witness: `elaboration::tests::dependent_resumption_closes_its_prerequisites`
#[spec(
    captures: depth = context.depth(gandr_core_term::Zone::Intuitionistic),
    ensures: |ret| context.depth(gandr_core_term::Zone::Intuitionistic) == depth && match ret {
        | Verdict::Data => match *declaration.content() {
            | crate::DeclarationContent::Data(ref signature) => context.data_signatures().get(&declaration.constant()) == Some(signature),
            | crate::DeclarationContent::Codata(ref signature) => context.codata_signatures().get(&declaration.constant()) == Some(signature),
            | crate::DeclarationContent::Abstract(_) | crate::DeclarationContent::World => true,
            | crate::DeclarationContent::Value { .. } => false,
        },
        | Verdict::Checked { declared, body, .. } => matches!(declaration.content(), crate::DeclarationContent::Value { signature: Maybe::Present(ty), body: Maybe::Present(value) } if *ty == declared.id() && *value <= body)
            && (context.signature(declaration.constant()) == Maybe::Present(declared) || !declaration.stages().is_empty()),
        | Verdict::Synthesised { synthesised, body } => matches!(declaration.content(), crate::DeclarationContent::Value { signature: Maybe::Absent(_), body: Maybe::Present(value) } if *value <= body)
            && context.signature(declaration.constant()) == Maybe::Present(synthesised.produced()),
        | Verdict::Owed(entry) => matches!(declaration.content(), crate::DeclarationContent::Value { signature: Maybe::Present(ty), body: Maybe::Absent(_) } if *ty == entry.absence().declared().id())
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
///   `context`; beside it, when a run of the body refused, the failure of that
///   run, whose refusal is the verdict's; when the first run accepted a body
///   holding a computation written where a value is read, what elaborating it
///   did, the verdict then being the second run's over the elaborated body;
///   and, when `run` is [`Run::Typed`] and the body was run, what
///   [`type_value`] keeps for the body as written, read before the
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
/// - witness: `module::tests::a_nested_run_elaborates_into_a_bind_before_its_region`
/// - witness: `module::tests::a_run_in_a_definition_s_own_value_is_unenclosed`
/// - witness: `module::tests::an_ascription_keeps_the_endpoints_it_related`
/// - witness: `module::tests::a_typed_module_keys_what_each_run_formed`
/// - witness: `module::tests::a_refused_first_run_leaves_its_nesting_unaccepted`
/// - witness: `elaboration::tests::owed_conversion_suspends`
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
        residue: Residue::default(),
    };
    let constant = declaration.constant();
    // A value declaration's judgement may wait on an owed hole; a nominal
    // declaration forms rigidly.
    let collecting = match *declaration.content() {
        crate::DeclarationContent::Value { .. } => Collecting::On,
        crate::DeclarationContent::Data(_)
        | crate::DeclarationContent::Codata(_)
        | crate::DeclarationContent::Abstract(_)
        | crate::DeclarationContent::World => Collecting::Off,
    };
    context.deferrals_mut().open(collecting);
    // The pairs a declaration's conversions relate, and the stages its
    // recursion typing mints, are its own: whatever an earlier declaration's
    // typing pass left is dropped.
    let _earlier = context.take_relating();
    context.forget_stages();
    if let Err(refusal) = context.admit(constant) {
        return unrun(refusal);
    }
    context.keep_laws(constant, declaration.laws().to_vec());
    context.keep_operation_rules(constant, declaration.operation_rules().clone());
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
            residue: Residue::default(),
        },
        Err(refusal) => Decision {
            typings,
            ..unrun(refusal)
        },
    };
    let (signature, body) = match *(declaration.content()) {
        crate::DeclarationContent::Data(ref signature) => {
            let verdict = crate::former::form_signature(context, constant, signature);
            if verdict.is_ok() {
                context.record_data(constant, alloc::sync::Arc::clone(signature));
            }
            let signed = finish(context, outer);
            return formed(verdict, kept(signed));
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
                .and_then(|level| founded(context, constant, declared).map(|()| level))
                .and_then(|level| context.seal_abstract(constant, declared, level))
                .map(|_atom| ());
            let signed = finish(context, outer);
            return formed(verdict, kept(signed));
        },
        crate::DeclarationContent::World => {
            context.worlds_mut().declare(constant);
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
        Maybe::Present(declared) => crate::quantified::bounded(declaration.stages(), declared)
            .and_then(|()| {
                if !declaration.stages().is_empty() {
                    let (erased, marks) = crate::quantified::split(
                        context.arena_mut(),
                        declared,
                        declaration.stages(),
                    )?;
                    quantified = Some((form_value_type(context, erased)?, marks));
                }
                crate::quantified::mint(context.stages_mut(), declaration.stages());
                form_value_type(context, declared)
            })
            .and_then(|formed| crate::session::unrestricted(context, formed.id()).map(|()| formed))
            .map(Direction::Check),
        Maybe::Absent(signature::Absent::Unsigned) => Ok(Direction::Synthesise),
    };
    let mut signed = finish(context, outer);
    let direction = match direction {
        Ok(direction) => direction,
        Err(refusal) => {
            let _home = context.binders().relocate(World::Host);
            return Decision {
                typings: kept(signed),
                ..unrun(refusal)
            };
        },
    };
    let mut spending = Spending::Unspent;
    let mut typings = Maybe::Absent(untyped);
    let mut elaboration = Maybe::Absent(elaborated::Absent::Unnested);
    let mut relating = Vec::new();
    let residue: Residue;
    let mut following = Maybe::Absent(crate::recursion::Unstaged::Plain);
    let (verdict, failure) = match body {
        Maybe::Present(body) => {
            let _stale = context.take_nesting();
            context.own_body(body);
            context.supply(declaration.supplies());
            context.worlds_mut().enter(entry);
            let first = judge(context, body, direction);
            let decisions = context.take_nesting();
            let judged = match first {
                Ok(_) if !decisions.is_empty() => {
                    match crate::nested::elaborate(context.arena_mut(), body, &decisions) {
                        Ok((elaborated, done)) => {
                            elaboration = Maybe::Present(done);
                            // The verdict is the second run's, and so are the
                            // pairs it relates and what it leaves undecided.
                            let _first = context.take_relating();
                            context.forget_stages();
                            crate::quantified::mint(context.stages_mut(), declaration.stages());
                            context.deferrals_mut().open(Collecting::On);
                            context.own_body(elaborated);
                            judge(context, elaborated, direction)
                        },
                        Err(unenclosed) => Err(unenclosed_failure(unenclosed.run())),
                    }
                },
                Ok(_) | Err(_) => {
                    if !decisions.is_empty() {
                        elaboration = Maybe::Absent(elaborated::Absent::Unaccepted);
                    }
                    first
                },
            };
            relating = context.take_relating();
            residue = context.deferrals_mut().take();
            following = follows(
                context,
                &judged,
                (residue.pending(), direction),
                declaration.stages(),
            );
            if let Some(signed) = signed.take() {
                context.own_body(body);
                typings =
                    Maybe::Present(Typings::after(signed, type_value(context, body, direction)));
                let _typed = context.take_nesting();
            }
            spending = context.worlds_mut().leave();
            match judged {
                Ok(verdict) => (verdict, Maybe::Absent(kept::Absent::Accepted)),
                Err(failure) => (Verdict::Refused(failure.refusal()), Maybe::Present(failure)),
            }
        },
        Maybe::Absent(body::Absent::Hole) => {
            let owed = hole(direction, constant, declaration.origin()).and_then(|absence| {
                crate::capability::held(context, constant, absence.declared())?;
                Ok(absence)
            });
            residue = context.deferrals_mut().take();
            match owed {
                Ok(absence) => (
                    Verdict::Owed(ObligationEntry::from(absence)),
                    Maybe::Absent(kept::Absent::Accepted),
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
    // A definition quantified over stages enters the table at its plain type:
    // each call instantiates the stages its signature marks.
    let direction = match (direction, quantified) {
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
/// - witness: `recursion::tests::a_result_follows_the_parameter_it_recurses_on`
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
    let recursed = match context.arena().computation(root) {
        Some(&gandr_core_term::Computation::Fixpoint {
            evidence: gandr_kernel_term::FixpointEvidence::StructuralDescent,
            ..
        }) => gandr_kernel_term::StagedPosition::default(),
        Some(&gandr_core_term::Computation::Fixpoint {
            evidence: gandr_kernel_term::FixpointEvidence::Staged { position },
            ..
        }) => position,
        Some(_) | None => return plain,
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
    let _relating = context.take_relating();
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

/// The failure of a body whose elaboration found `run` with no computation
/// around it: no rule of the judgement is pending, and the refusal names the
/// run.
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
/// judgement consulted.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the verdict [`check_declaration`] gives, with the same effect on
///   `context`; beside it, every answer the judgement read from the signature
///   table, once per position, ascending by position, and no answer read before
///   this call.
/// - provides: the support an incremental caller compares pointwise before it
///   reuses the verdict: equal answers mean an equal judgement, because the
///   signature table is the only input outside the declaration the judgement
///   reads.
/// - fails: never; a refusal is the verdict [`Verdict::Refused`].
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the surfaces are the log's span and its canonical form,
///   separated by an unsupported judgement before a supported one, a supported
///   one reading positions out of order and one twice, a read of an unadmitted
///   position, and a refusal that stops the run before a later read.
/// - witness: `module::tests::the_support_holds_each_consulted_answer_once_in_position_order`
/// - witness: `module::tests::a_refusal_cuts_the_support_where_the_run_stopped`
#[spec(ensures: |ret| {
    let entries = ret.support().consulted();
    entries.iter().zip(entries.iter().skip(1)).all(|(left, right)| left.constant() < right.constant())
        && entries.iter().all(|entry| entry.answer() == if entry.constant() == declaration.constant() {
            Maybe::Absent(crate::context::signature_table::Absent::Untyped)
        } else {
            context.signature(entry.constant())
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
    let verdict = check_declaration(context, declaration);
    Supported::new(verdict, context.finish_support())
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
///   each body run and refused keeps its failure under its position, and no
///   other declaration has one; each body the first run accepted holding a
///   computation written where a value is read keeps its elaboration under its
///   position.
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
/// - witness: `elaboration::tests::owed_conversion_suspends`
#[cfg_attr(
    dylint_lib = "quenchant_dylints",
    expect(
        spec_clause_traversal,
        reason = "parity: the body judges every declaration and copies the context's lifts and definitions into the report; the check compares each copy once"
    )
)]
#[spec(ensures: |ret| ret.judged.len() == declarations.len()
    && ret.judged.iter().zip(declarations).all(|(judged, declaration)|
        judged.constant == declaration.constant() && judged.origin == declaration.origin())
    && ret.ledger.entries().iter().copied().eq(ret.judged.iter().filter_map(|judged| match judged.verdict {
        | Verdict::Owed(entry) => Some(entry),
        | Verdict::Data | Verdict::Checked { .. } | Verdict::Synthesised { .. } | Verdict::Suspended(_) | Verdict::Refused(_) => None,
    }))
    && ret.suspensions.keys().copied().eq(ret.judged.iter().filter(|judged| matches!(judged.verdict, Verdict::Suspended(_))).map(|judged| judged.constant))
    && &ret.lifts == context.lifts()
    && &ret.funexts == context.funexts()
    && &ret.equivalences == context.equivalences()
    && &ret.flows == context.flows()
    && &ret.directed == context.directed()
    && &ret.reflexivities == context.reflexivities()
    && &ret.relations == context.relations()
    && &ret.natives == context.natives()
    && ret.definitions.iter().map(|(&constant, &body)| (constant, body))
        .eq(context.definitions().definitions())
    && ret.failures.iter().all(|(constant, failure)|
        ret.judged.iter().any(|judged| judged.constant == *constant
            && judged.verdict == Verdict::Refused(failure.refusal()))))]
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
/// - witness: `elaboration::tests::shared_code_occurrences_keep_distinct_transports`
#[spec(ensures: |ret| ret.judged.len() == declarations.len())]
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
    /// The failure of each body refused, by position.
    failures: BTreeMap<ConstantIndex, Failure>,
    /// What elaborating each body with a nested computation did, by position.
    nested_elaborations: BTreeMap<ConstantIndex, NestedElaboration>,
    /// What each suspended declaration waits on, by position.
    suspensions: BTreeMap<ConstantIndex, Suspension>,
    /// The end of the mutual block the schedule holds open, or why none is.
    open: Maybe<ConstantIndex, open::Absent>,
    /// Each mutual block opened, by its first position and its end.
    blocks: Vec<(ConstantIndex, ConstantIndex)>,
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
            open: Maybe::Absent(open::Absent::Lone),
            blocks: Vec::new(),
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
        mut settle: Settle,
    ) where
        Settle: FnMut(&mut CheckingContext<'_>, &Declaration, Verdict),
    {
        for (index, declaration) in declarations.iter().enumerate() {
            let was = self.open;
            schedule(
                context,
                declarations.get(index ..).unwrap_or_default(),
                &mut self.open,
            );
            if let Maybe::Present(end) = self.open
                && was != self.open
            {
                self.blocks.push((declaration.constant(), end));
            }
            let decision = decide(context, declaration, Run::Judged);
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
                    let suspension = Suspension::new(
                        declared,
                        decision.residue,
                        &context.deferrals().owed,
                        &self.suspensions,
                    );
                    self.suspensions.insert(declaration.constant(), suspension);
                },
                Verdict::Data
                | Verdict::Checked { .. }
                | Verdict::Synthesised { .. }
                | Verdict::Refused(_) => {},
            }
            settle(context, declaration, decision.verdict);
            self.judged.push(Judged {
                constant: declaration.constant(),
                origin: declaration.origin(),
                verdict: decision.verdict,
            });
        }
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
        ensures: |ret| ret.judged.len() == before,
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
            open,
            blocks,
        } = self;
        if let Maybe::Present(_) = open {
            context.close_mutual();
        }
        refuse_whole(&blocks, &mut judged, &mut failures);
        ModuleReport {
            judged,
            ledger,
            lifts: context.lifts().clone(),
            funexts: context.funexts().clone(),
            equivalences: context.equivalences().clone(),
            flows: context.flows().clone(),
            directed: context.directed().clone(),
            reflexivities: context.reflexivities().clone(),
            relations: context.relations().clone(),
            laws: context.laws().clone(),
            operation_rules: context.operation_rules().clone(),
            stage_signatures: context.stage_signatures().clone(),
            natives: context.natives().clone(),
            definitions: context.definitions().definitions().collect(),
            data_signatures: context.data_signatures().clone(),
            codata_signatures: context.codata_signatures().clone(),
            abstract_types: context.abstract_types().collect(),
            seal_table: context.seal_table().clone(),
            failures,
            nested_elaborations,
            worlds: context.worlds().declared().clone(),
            suspensions,
        }
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
/// admitting every declaration before it as an earlier run answered it: each
/// value declaration through `adopt`, never judged again, and each nominal
/// declaration formed again.
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
/// - witness: `elaboration::tests::incremental_equals_from_scratch`
/// - witness: `elaboration::tests::checked_success_is_stable_without_rejudgement`
#[spec(ensures: |ret| ret.as_ref().is_err() || ret.as_ref().is_ok_and(|&(verdict, ref residue)|
    matches!(verdict, Verdict::Suspended(_)) == (residue.pending() == Deferred::Yes)))]
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
    let mut open = Maybe::Absent(open::Absent::Lone);
    for (index, declaration) in declarations.iter().enumerate().take(position) {
        schedule(
            context,
            declarations.get(index ..).unwrap_or_default(),
            &mut open,
        );
        match *declaration.content() {
            crate::DeclarationContent::Value { .. } => adopt(context, declaration)?,
            crate::DeclarationContent::Data(_)
            | crate::DeclarationContent::Codata(_)
            | crate::DeclarationContent::Abstract(_)
            | crate::DeclarationContent::World => {
                let _formed = decide(context, declaration, Run::Judged);
            },
        }
    }
    let judged = declarations
        .get(position)
        .ok_or(CheckRefusal::MachineInvariant)?;
    schedule(
        context,
        declarations.get(position ..).unwrap_or_default(),
        &mut open,
    );
    let decision = decide(context, judged, Run::Judged);
    Ok((decision.verdict, decision.residue))
}

/// Add to `report` what a later judgement in `context` decided: the node-keyed
/// tables its rules filled and the position-keyed relations and laws.
///
/// # Specification
/// - requires: `context` judged declarations of `report`'s module, over the
///   same arena.
/// - ensures: every table named holds its earlier entries and `context`'s,
///   `context`'s winning where both hold a key; the verdicts, ledger, lifts and
///   definitions are unchanged.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L1 — a fill using a rule the batch run never decided is
///   readmitted only when its decision reaches the bridge.
/// - witness: `elaboration::tests::incremental_equals_from_scratch`
#[spec(ensures: context.funexts().keys().all(|at| report.funexts.contains_key(at))
    && context.relations().keys().all(|at| report.relations.contains_key(at)))]
pub fn absorb(
    report: &mut ModuleReport,
    context: &CheckingContext<'_>,
)
{
    report.funexts.extend(
        context
            .funexts()
            .iter()
            .map(|(&at, funext)| (at, funext.clone())),
    );
    report.equivalences.extend(
        context
            .equivalences()
            .iter()
            .map(|(&at, equivalence)| (at, equivalence.clone())),
    );
    report
        .flows
        .extend(context.flows().iter().map(|(&at, flow)| (at, flow.clone())));
    report.directed.extend(
        context
            .directed()
            .iter()
            .map(|(&at, directed)| (at, directed.clone())),
    );
    report.reflexivities.extend(
        context
            .reflexivities()
            .iter()
            .map(|(&at, reflexivity)| (at, reflexivity.clone())),
    );
    report.relations.extend(
        context
            .relations()
            .iter()
            .map(|(&at, relations)| (at, relations.clone())),
    );
    report
        .laws
        .extend(context.laws().iter().map(|(&at, laws)| (at, laws.clone())));
    report.operation_rules.extend(
        context
            .operation_rules()
            .iter()
            .map(|(&at, rules)| (at, rules.clone())),
    );
    report.stage_signatures.extend(
        context
            .stage_signatures()
            .iter()
            .map(|(&at, signature)| (at, signature.clone())),
    );
    report
        .natives
        .extend(context.natives().iter().map(|(&at, &native)| (at, native)));
}

/// The report a term-producing run's `entries` stand for, over the batch
/// report `base`.
///
/// The checker's report with each verdict the entry's, every lift an output
/// wrote explicit, and no conditional body.
///
/// # Specification
/// - requires: `entries` come from one elaboration session over the bridge
///   arena, in `base`'s order, and `base` is that session's batch report.
/// - ensures: one [`Judged`] per entry, carrying its verdict — an accepted one
///   over the emitted body; accepted bodies define their constants as emitted,
///   owed entries form the ledger, suspended entries keep their suspensions and
///   define nothing, and the lift side table holds only the lifts an output
///   left beneath a former it reads as a leaf. Every other table is `base`'s.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L1 — kernel readmission checks emitted terms without trusting
///   residual premises or an implicit-lift side table.
/// - witness: `elaboration::tests::every_fixture_the_checker_accepts_is_readmitted`
/// - witness: `elaboration::tests::outputs_materialize_nested_lifts`
#[spec(ensures: |ret| ret.judged.len() == entries.len()
    && ret.suspensions.len() == entries.iter().filter(|entry| matches!(entry.outcome(), crate::elaboration::Outcome::Suspended(_))).count())]
#[must_use]
#[inline]
pub fn elaborated_report(
    base: &ModuleReport,
    entries: &[crate::elaboration::Entry],
) -> ModuleReport
{
    let mut report = base.clone();
    report.judged = Vec::with_capacity(entries.len());
    report.ledger = ObligationLedger::new();
    report.lifts = BTreeMap::new();
    report.suspensions = BTreeMap::new();
    for entry in entries {
        let verdict = entry.verdict();
        match verdict {
            Verdict::Owed(owed) => report.ledger.record(owed),
            Verdict::Checked { body, .. } | Verdict::Synthesised { body, .. } => {
                report.definitions.insert(entry.constant(), body);
                report
                    .lifts
                    .extend(entry.lifts().iter().map(|(&at, lift)| (at, lift.clone())));
            },
            Verdict::Suspended(_) => {
                report.definitions.remove(&entry.constant());
                if let crate::elaboration::Outcome::Suspended(ref suspension) = *entry.outcome() {
                    report
                        .suspensions
                        .insert(entry.constant(), suspension.clone());
                }
            },
            Verdict::Data | Verdict::Refused(_) => {},
        }
        report.judged.push(Judged {
            constant: entry.constant(),
            origin: entry.origin(),
            verdict,
        });
    }
    report
}

/// What [`type_module`] keeps of a module's typed run: the types each
/// declaration's run formed and judged, and the refusal of each declaration
/// the run refused.
#[derive(Clone, Debug, Default)]
pub struct TypedModule
{
    /// What each declaration's run formed or judged, by its constant.
    typings: BTreeMap<ConstantIndex, Typings>,
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
///   declaration the run refused is keyed in the refusals by its constant with
///   the refusal its verdict carries, and no other is.
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
#[spec(ensures: |ref ret| ret.typings.keys().chain(ret.refused.keys()).all(|constant|
    declarations.iter().any(|declaration| declaration.constant() == *constant)))]
#[inline]
#[must_use]
pub fn type_module(
    context: &mut CheckingContext<'_>,
    declarations: &[Declaration],
) -> TypedModule
{
    let mut typed = TypedModule::default();
    let mut open = Maybe::Absent(open::Absent::Lone);
    for (index, declaration) in declarations.iter().enumerate() {
        schedule(
            context,
            declarations.get(index ..).unwrap_or_default(),
            &mut open,
        );
        let decision = decide(context, declaration, Run::Typed);
        if let Verdict::Refused(refusal) = decision.verdict {
            let _replaced = typed.refused.insert(declaration.constant(), refusal);
        }
        if let Maybe::Present(typings) = decision.typings {
            let _replaced = typed.typings.insert(declaration.constant(), typings);
        }
    }
    if let Maybe::Present(_) = open {
        context.close_mutual();
    }
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

#[cfg(test)]
mod tests;
