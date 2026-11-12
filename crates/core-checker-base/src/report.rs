//! A module's report: one verdict per declaration, the obligations they owe,
//! and the tables the run decided, which the kernel bridge readmits.
//!
//! The module run makes the report, and the bridge reads it. So the report
//! lives below both: [`ModuleReport::read`] takes the context's tables when a
//! run finishes, [`absorb`] adds what a later judgement decided, and
//! [`elaborated_report`] gives the report a term-producing run stands for.

use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use alloc::vec::Vec;

use anodized::spec;
use gandr_core_term::CompType;
use gandr_core_term::CompTypeId;
use gandr_core_term::ComputationId;
use gandr_core_term::CoreArena;
use gandr_core_term::Value;
use gandr_core_term::ValueId;
use gandr_core_term::ValueType;
use gandr_core_term::ValueTypeId;
use gandr_core_term::world::WorldType;
use gandr_kernel_term::ConstantIndex;
use quenchant_shape::shape::Maybe;

use crate::code::EndpointRelation;
use crate::code::Lift;
use crate::code::Reflexivity;
use crate::context::CheckingContext;
use crate::declaration::AbstractType;
use crate::declaration::OriginToken;
use crate::elaboration::Suspension;
use crate::equiv::Equivalence;
use crate::failure::Failure;
use crate::formation::FormedValueType;
use crate::funext::Funext;
use crate::judge::Checked;
use crate::judge::Synthesised;
use crate::ledger::ObligationEntry;
use crate::ledger::ObligationLedger;
use crate::nested::NestedElaboration;
use crate::refusal::CheckRefusal;
use crate::refusal::TermNode;
use crate::seal::SealTable;
use crate::support::Supported;
use crate::worlds::Mobility;

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
    /// The verdict `verdict` of the declaration at `constant`, offered with
    /// `origin`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn new(
        constant: ConstantIndex,
        origin: OriginToken,
        verdict: Verdict,
    ) -> Self
    {
        Self {
            constant,
            origin,
            verdict,
        }
    }

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
    /// The values the run coerced in to a patched type, by node, each with the
    /// fixed fields it compared.
    coercions: BTreeMap<ValueId, crate::conversion::Coercion>,
    /// The universe equivalences the run decided, by node.
    equivalences: BTreeMap<ValueId, Equivalence>,
    /// The session statements the run decided, by node.
    flows: BTreeMap<ValueId, crate::flow::Statement>,
    /// The forward and function flows the run decided, by node.
    directed: BTreeMap<ValueId, crate::forward::Directed>,
    /// The family each transport or ride above level zero formed its motive
    /// as, by node.
    motives: BTreeMap<ComputationId, ValueTypeId>,
    /// The payload type each send and each receive the run checked moves, by
    /// node.
    payloads: BTreeMap<ComputationId, ValueTypeId>,
    /// The types each handler and capability scope the run checked was judged
    /// at, by node.
    handled: BTreeMap<ComputationId, crate::handler::Handled>,
    /// The computations the run checked or synthesised at a returner over a
    /// row of operations, and the levels of those returners.
    rows: crate::program::Rows,
    /// The reflexivities the run checked, by node.
    reflexivities: BTreeMap<ValueId, Reflexivity>,
    /// The path endpoint pairs each accepted declaration's type conversions
    /// related, by position, with each derivation.
    relations: BTreeMap<ConstantIndex, Vec<EndpointRelation>>,
    /// The nodes each accepted declaration checked in another form than
    /// written, by position, each beside the node the kernel reads in its
    /// place.
    restatements: BTreeMap<ConstantIndex, Vec<(TermNode, TermNode)>>,
    /// The laws each lawful declaration's folds rest on, by position, in its
    /// folded type's rule order.
    laws: BTreeMap<ConstantIndex, Vec<ConstantIndex>>,
    /// The rules of the operation each ruled declaration lowered from, by
    /// position.
    operation_rules: BTreeMap<ConstantIndex, gandr_kernel_term::OperationRules>,
    /// The built-in role each holder holds, by position: what the holder
    /// crosses to the kernel carrying.
    builtins: BTreeMap<ConstantIndex, gandr_kernel_term::Builtin>,
    /// The matches of each declaration's body with their derivations, by
    /// position.
    covers: BTreeMap<ConstantIndex, Vec<(ComputationId, gandr_kernel_term::cover::Cover)>>,
    /// The stage signature of each definition quantified over stages, by
    /// position.
    stage_signatures: BTreeMap<ConstantIndex, gandr_kernel_term::StageSignature>,
    /// The native path each univalence statement the run decided derives, each
    /// path product it judged elaborates to, and the value each fill's
    /// induction returns, by node.
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
    /// The failure of each body, each data signature and each value's declared
    /// type the judgement refused, by position.
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
    /// The policy the run's closed pairs the tier met crossed under, which
    /// the kernel readmitting the report admits them under.
    admitting: gandr_kernel_core::AdmissionPolicy,
    /// The verdict and the support of each declaration the run decided
    /// outside a mutual block, by position, when the run kept them.
    supported: BTreeMap<ConstantIndex, Supported>,
}

impl ModuleReport
{
    /// The report of the verdicts `judged` and the `ledger` they owe, beside
    /// what the run kept and every table `context` holds after the run.
    ///
    /// # Specification
    /// - requires: `context` is the context the run judged in.
    /// - ensures: the verdicts, the ledger, the failures, the nested
    ///   elaborations, the suspensions and the supports as given; every other
    ///   table is the context's.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the report of a module run, which every module
    ///   witness reads.
    /// - witness: `tests::recursive_data::a_run_resumed_from_a_checkpoint_judges_as_one_run_776`
    #[spec(
        captures: count = judged.len(),
        ensures: |ret| ret.judged.len() == count,
    )]
    #[must_use]
    #[inline]
    pub fn read(
        context: &CheckingContext<'_>,
        (judged, ledger): (Vec<Judged>, ObligationLedger),
        failures: BTreeMap<ConstantIndex, Failure>,
        nested_elaborations: BTreeMap<ConstantIndex, NestedElaboration>,
        suspensions: BTreeMap<ConstantIndex, Suspension>,
        supported: BTreeMap<ConstantIndex, Supported>,
    ) -> Self
    {
        Self {
            supported,
            judged,
            ledger,
            lifts: context.lifts().clone(),
            funexts: context.funexts().clone(),
            coercions: context.coercions().clone(),
            equivalences: context.equivalences().clone(),
            flows: context.flows().clone(),
            directed: context.directed().clone(),
            motives: context.motives().clone(),
            payloads: context.payloads().clone(),
            handled: context.handled().clone(),
            rows: context.rows().clone(),
            reflexivities: context.reflexivities().clone(),
            relations: context.relations().clone(),
            restatements: context.restatements().clone(),
            laws: context.laws().clone(),
            operation_rules: context.operation_rules().clone(),
            covers: context.covers().clone(),
            builtins: context
                .builtins()
                .iter()
                .map(|(&role, &holder)| (holder, role))
                .collect(),
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
            admitting: context.admitting(),
        }
    }

    /// The policy the run's closed pairs the tier met crossed under.
    ///
    /// # Specification
    /// trivial.
    #[must_use]
    #[inline]
    pub const fn admitting(&self) -> gandr_kernel_core::AdmissionPolicy
    {
        self.admitting
    }

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

    /// The entries, open to a test that tampers one before a readmission.
    ///
    /// # Specification
    /// trivial.
    #[cfg(test)]
    pub fn judged_mut(&mut self) -> &mut [Judged]
    {
        &mut self.judged
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

    /// The values the run coerced in to a patched type, by node, each with the
    /// fixed fields it compared.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn coercions(&self) -> &BTreeMap<ValueId, crate::conversion::Coercion>
    {
        &self.coercions
    }

    /// The coercions, open to a test that tampers one before a readmission.
    ///
    /// # Specification
    /// trivial.
    #[cfg(test)]
    pub fn coercions_mut(&mut self) -> &mut BTreeMap<ValueId, crate::conversion::Coercion>
    {
        &mut self.coercions
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

    /// The family each transport or ride above level zero formed its motive
    /// as, by node.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a ride and a transport above level zero report the
    ///   family at the carrier's level, by a batch run and by a fill, and a run
    ///   with none reports an empty table, so an emptied or padded table shows.
    /// - witness: `flow::tests::a_motive_above_level_zero_reads_its_binder_at_the_carriers_level_1837`
    /// - witness: `elaboration::tests::a_filled_ride_above_level_zero_readmits_at_its_recorded_motive_1837`
    #[inline]
    #[must_use]
    pub const fn motives(&self) -> &BTreeMap<ComputationId, ValueTypeId>
    {
        &self.motives
    }

    /// The payload type each send and each receive the run checked moves, by
    /// node: the type a send's value was checked at, and the type a receive
    /// opened its slot at — a value's payload type, or the session or buffer
    /// at the payload's weak head.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a received value crosses as an assumption of the
    ///   recorded type and a sent one ascribed it, so an emptied table leaves
    ///   the receive uncrossed and a sent injection unchecked by the kernel.
    /// - witness: `judgement::session::tests::a_received_value_crosses_as_an_assumption_1319`
    #[inline]
    #[must_use]
    pub const fn payloads(&self) -> &BTreeMap<ComputationId, ValueTypeId>
    {
        &self.payloads
    }

    /// The types each handler and capability scope the run checked was judged
    /// at, by node: its subject's result and its answer, in the handler's own
    /// context.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a handler crosses as the fold of its free model at
    ///   the recorded types, so an emptied table leaves it refused.
    /// - witness: `bridge::tests::a_deep_handler_crosses_as_the_fold_of_its_free_model_1624`
    #[inline]
    #[must_use]
    pub const fn handled(&self) -> &BTreeMap<ComputationId, crate::handler::Handled>
    {
        &self.handled
    }

    /// The computations the run checked or synthesised at a returner over a
    /// row of operations, and the levels of those returners.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a declaration at a row crosses as a program of the
    ///   row's model at the recorded types, so an emptied record leaves it
    ///   refused.
    /// - witness: `bridge::tests::two_declarations_at_one_row_read_one_model_6642`
    #[inline]
    #[must_use]
    pub const fn rows(&self) -> &crate::program::Rows
    {
        &self.rows
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

    /// The nodes each accepted declaration checked in another form than
    /// written, by position, each beside the node the declaration crosses to
    /// the kernel in its place, ascending by the restated node: an arm or a
    /// case refined by a solved variable, and a constructor restated at its
    /// stated application.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn restatements(&self) -> &BTreeMap<ConstantIndex, Vec<(TermNode, TermNode)>>
    {
        &self.restatements
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

    /// The built-in role each holder holds, by position: what the holder
    /// crosses to the kernel carrying, for the kernel to validate.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn builtins(&self) -> &BTreeMap<ConstantIndex, gandr_kernel_term::Builtin>
    {
        &self.builtins
    }

    /// The matches of each declaration's body with their derivations, by
    /// position.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn covers(
        &self
    ) -> &BTreeMap<ConstantIndex, Vec<(ComputationId, gandr_kernel_term::cover::Cover)>>
    {
        &self.covers
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

    /// The native path each univalence statement the run decided derives, each
    /// path product it judged elaborates to, and the value each fill's
    /// induction returns, by node: what the statement, the product or the fill
    /// crosses to the kernel as.
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

    /// The failure of each body, each data signature and each value's declared
    /// type the judgement refused, by position; a declaration refused otherwise
    /// before its body was run, or accepted, has no entry.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn failures(&self) -> &BTreeMap<ConstantIndex, Failure>
    {
        &self.failures
    }

    /// Report the declaration at `constant` as refused with `refusal`, under
    /// `failure` when the judgement kept one: what a judgement that takes a
    /// refused declaration from its checkpoint reports for it.
    ///
    /// # Specification
    /// - requires: `failure`, when present, refused with `refusal`.
    /// - ensures: the judged declaration at `constant`, when the report holds
    ///   one, has the verdict [`Verdict::Refused`] of `refusal`; the failures
    ///   hold `failure` at `constant`, or nothing when it is absent; nothing
    ///   else changes.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — a refused and an accepted declaration, each given a
    ///   taken refusal with and without a failure, separate the verdict and the
    ///   failure that the report keeps.
    /// - witness: `module::tests::a_refusal_taken_from_a_checkpoint_replaces_the_verdict_and_the_failure`
    #[spec(
        requires: failure.as_ref().is_none_or(|kept| kept.refusal() == refusal),
        captures: kept = failure.clone(),
        ensures: self.failures.get(&constant) == kept.as_ref(),
    )]
    #[inline]
    pub fn refuse(
        &mut self,
        constant: ConstantIndex,
        refusal: CheckRefusal,
        failure: Option<Failure>,
    )
    {
        if let Some(judged) = self
            .judged
            .iter_mut()
            .find(|judged| judged.constant == constant)
        {
            judged.verdict = Verdict::Refused(refusal);
        }
        match failure {
            Some(failure) => {
                let _replaced = self.failures.insert(constant, failure);
            },
            None => {
                let _removed = self.failures.remove(&constant);
            },
        }
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

    /// The verdict and the support of each declaration the run decided outside
    /// a mutual block, by position: empty unless the run was asked
    /// (`ModuleRun::keep_supports`). Each verdict is the one the
    /// declaration's own decision gave, before a block's refusal spreads.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn supported(&self) -> &BTreeMap<ConstantIndex, Supported>
    {
        &self.supported
    }

    /// The first sealed atom with no `mobile` mark that a value of `ty` may
    /// hold, or that a function of it may take or answer: what keeps the
    /// value's representation inside its seal, where no printed answer
    /// reaches.
    ///
    /// # Specification
    /// - requires: `ty` is formed in `arena`, the arena the run judged in.
    /// - ensures: an atom met under `ty` that no signature marks `mobile`, an
    ///   atom this run formed no abstract type at among them; the walk reads
    ///   products, sums, records, lists, the carrier of a path or a flow, the
    ///   value a handle or a region holds, both sides of a thunk's function
    ///   types and of a stack, a returner's result, each field of a datatype
    ///   and each observation of a codata type once per declaration, and a code
    ///   through its quote or the body its constant is defined as;
    ///   [`unmarked::Absent::Unheld`] when it meets none.
    /// - fails: never; a dangling node holds nothing.
    /// - panics: none.
    /// - intension: an explicit worklist that reads each value type,
    ///   computation type and code once, so a shared node costs one read
    ///   however many paths reach it; each datatype, codata type and defined
    ///   constant is entered once.
    ///
    /// # Termination
    /// - reason: the `while let` loop over an explicit worklist, not recursion.
    /// - measure: the nodes not yet read: each node is read once, and a
    ///   declaration's fields, observations or definition are pushed once.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an unmarked atom standing alone, in a pair, in a list
    ///   and in a function's answer is met, and so is an atom no abstract type
    ///   formed at; a marked atom and a type naming no atom hold none. An atom
    ///   beside a pair thirty levels deep, whose two fields are one node at
    ///   each level, is met in one read of each level. An atom in a datatype's
    ///   field or a codata observation is not generated.
    /// - witness: `module::tests::an_unmarked_atom_is_met_wherever_a_type_holds_it_3375`
    /// - witness: `module::tests::an_unmarked_atom_beside_a_shared_pair_thirty_deep_is_met_5796`
    #[spec(ensures: |ret| match ret {
        Maybe::Present(atom) => self.abstract_types.get(&atom).is_none_or(|declared| declared.mobility() == Mobility::Immobile),
        Maybe::Absent(_) => true,
    })]
    #[inline]
    pub fn unmarked_atom(
        &self,
        arena: &CoreArena,
        ty: ValueTypeId,
    ) -> Maybe<ConstantIndex, unmarked::Absent>
    {
        /// A node still to read.
        #[derive(Clone, Copy, Eq, Ord, PartialEq, PartialOrd)]
        enum Node
        {
            /// A value type.
            Value(ValueTypeId),
            /// A computation type.
            Computation(CompTypeId),
            /// A code a type decodes.
            Code(ValueId),
        }
        let mut pending = Vec::from([Node::Value(ty)]);
        let mut entered: BTreeSet<ConstantIndex> = BTreeSet::new();
        let mut read: BTreeSet<Node> = BTreeSet::new();
        while let Some(node) = pending.pop() {
            if !read.insert(node) {
                continue;
            }
            match node {
                Node::Value(id) => match arena.value_type(id) {
                    Some(&ValueType::Abstract(atom)) => {
                        if self
                            .abstract_types
                            .get(&atom)
                            .is_none_or(|declared| declared.mobility() == Mobility::Immobile)
                        {
                            return Maybe::Present(atom);
                        }
                    },
                    Some(&ValueType::Data {
                        declaration,
                        ref arguments,
                    }) => {
                        pending.extend(arguments.iter().copied().map(Node::Code));
                        if entered.insert(declaration)
                            && let Some(signature) = self.data_signatures.get(&declaration)
                        {
                            pending.extend(
                                signature
                                    .constructors()
                                    .iter()
                                    .flatten()
                                    .copied()
                                    .map(Node::Value),
                            );
                        }
                    },
                    Some(&ValueType::Record(ref fields)) => {
                        pending.extend(fields.values().copied().map(Node::Value));
                    },
                    Some(&ValueType::Patched {
                        base,
                        ref fixed,
                        ref meets,
                    }) => {
                        pending.push(Node::Value(base));
                        pending.extend(fixed.values().copied().map(Node::Code));
                        pending.extend(meets.iter().map(|met| Node::Code(met.1)));
                    },
                    Some(&(ValueType::Product(ref parts) | ValueType::Sum(ref parts))) => {
                        pending.extend(parts.iter().copied().map(Node::Value));
                    },
                    Some(
                        &(ValueType::Path { carrier: inner, .. }
                        | ValueType::Bridge { carrier: inner, .. }
                        | ValueType::Flow { carrier: inner, .. }
                        | ValueType::List(inner)
                        | ValueType::Lift { inner, .. }
                        | ValueType::Staged { base: inner, .. }
                        | ValueType::Kept { value: inner, .. }
                        | ValueType::World(WorldType::At { inner, .. })),
                    ) => pending.push(Node::Value(inner)),
                    Some(&ValueType::Sigma { first, second }) => {
                        pending.extend([Node::Value(first), Node::Value(second)]);
                    },
                    Some(&ValueType::Thunk(computation)) => {
                        pending.push(Node::Computation(computation));
                    },
                    Some(&ValueType::Stack { input, output }) => {
                        pending.extend([Node::Computation(input), Node::Computation(output)]);
                    },
                    Some(&ValueType::Element { code, .. }) => pending.push(Node::Code(code)),
                    Some(
                        &(ValueType::PathUniverse(..)
                        | ValueType::Run(_)
                        | ValueType::Prefix(_)
                        | ValueType::Dialogue(_)
                        | ValueType::Web
                        | ValueType::Base(_)
                        | ValueType::Universe { .. }
                        | ValueType::Row
                        | ValueType::RowTail(_)
                        | ValueType::StaticPi { .. }
                        | ValueType::Unknown
                        | ValueType::Session(_)
                        | ValueType::Capability { .. }
                        | ValueType::Buffer
                        | ValueType::Qubit
                        | ValueType::World(WorldType::Capability(_))),
                    )
                    | None => {},
                },
                Node::Computation(id) => match arena.comp_type(id) {
                    Some(&CompType::Returner { result, .. }) => pending.push(Node::Value(result)),
                    Some(&CompType::Returns { ref results, .. }) => {
                        pending.extend(results.iter().copied().map(Node::Value));
                    },
                    Some(
                        &(CompType::Arrow { domain, codomain }
                        | CompType::Pi { domain, codomain }
                        | CompType::LinearArrow {
                            domain, codomain, ..
                        }),
                    ) => {
                        pending.extend([Node::Value(domain), Node::Computation(codomain)]);
                    },
                    Some(&CompType::Element { code, .. }) => pending.push(Node::Code(code)),
                    Some(&CompType::With(ref components)) => {
                        pending.extend(components.iter().copied().map(Node::Computation));
                    },
                    Some(&CompType::Codata {
                        declaration,
                        ref arguments,
                    }) => {
                        pending.extend(arguments.iter().copied().map(Node::Code));
                        if entered.insert(declaration)
                            && let Some(signature) = self.codata_signatures.get(&declaration)
                        {
                            pending.extend(
                                signature
                                    .observations()
                                    .iter()
                                    .copied()
                                    .map(Node::Computation),
                            );
                        }
                    },
                    Some(&CompType::Unknown) | None => {},
                },
                Node::Code(id) => match arena.value(id) {
                    Some(&Value::Quote(quoted)) => pending.push(Node::Value(quoted)),
                    Some(&Value::QuoteComputation(quoted)) => {
                        pending.push(Node::Computation(quoted));
                    },
                    Some(&Value::Constant(constant)) => {
                        if entered.insert(constant)
                            && let Some(&body) = self.definitions.get(&constant)
                        {
                            pending.push(Node::Code(body));
                        }
                    },
                    Some(_) | None => {},
                },
            }
        }
        Maybe::Absent(unmarked::Absent::Unheld)
    }
}

quenchant_shape::reason_enum! {
    /// Why a type holds no sealed atom without a mark.
    pub mod unmarked {
        /// The reason none is held.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// Every atom the type reaches is marked `mobile`, or it reaches
            /// none.
            Unheld,
        }
    }
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
/// - witness: `elaboration::tests::a_filled_ride_above_level_zero_readmits_at_its_recorded_motive_1837`
#[spec(ensures: context.funexts().keys().all(|at| report.funexts.contains_key(at))
    && context.coercions().keys().all(|at| report.coercions.contains_key(at))
    && context.relations().keys().all(|at| report.relations.contains_key(at))
    && context.restatements().keys().all(|at| report.restatements.contains_key(at))
    && context.motives().keys().all(|at| report.motives.contains_key(at))
    && context.payloads().keys().all(|at| report.payloads.contains_key(at))
    && context.handled().keys().all(|at| report.handled.contains_key(at)))]
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
    report.coercions.extend(
        context
            .coercions()
            .iter()
            .map(|(&at, fixed)| (at, fixed.clone())),
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
    report
        .motives
        .extend(context.motives().iter().map(|(&at, &family)| (at, family)));
    report
        .payloads
        .extend(context.payloads().iter().map(|(&at, &moved)| (at, moved)));
    report.handled.extend(
        context
            .handled()
            .iter()
            .map(|(&at, handled)| (at, handled.clone())),
    );
    report.rows.absorb(context.rows());
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
    report.restatements.extend(
        context
            .restatements()
            .iter()
            .map(|(&at, restated)| (at, restated.clone())),
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
    report.covers.extend(
        context
            .covers()
            .iter()
            .map(|(&at, covers)| (at, covers.clone())),
    );
    report.builtins.extend(
        context
            .builtins()
            .iter()
            .map(|(&role, &holder)| (holder, role)),
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
