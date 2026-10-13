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

use alloc::collections::BTreeMap;
use alloc::vec::Vec;

use anodized::spec;
use gandr_core_term::ValueId;
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
    /// The reflexivities the run checked, by node.
    reflexivities: BTreeMap<ValueId, Reflexivity>,
    /// The path endpoint pairs each accepted declaration's type conversions
    /// related, by position, with each derivation.
    relations: BTreeMap<ConstantIndex, Vec<EndpointRelation>>,
    /// The path each univalence statement the run decided derives, by node.
    universals: BTreeMap<ValueId, ValueId>,
    /// The body each accepted declaration defines its constant as, elaborated
    /// to the universe it was declared at, by position.
    definitions: BTreeMap<ConstantIndex, ValueId>,
    /// Native signatures retained for kernel readmission.
    data_signatures: BTreeMap<ConstantIndex, alloc::sync::Arc<gandr_core_term::DataSignature>>,
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

    /// The path each univalence statement the run decided derives, by node:
    /// what the statement crosses to the kernel as.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn universals(&self) -> &BTreeMap<ValueId, ValueId>
    {
        &self.universals
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
///   the constant as that body. A formed signature enters the signature table
///   after the body is judged, whatever the body's verdict; a synthesised type
///   enters it after synthesis; a refused body alone enters nothing. An
///   abstract type's retention is checked where the context retains it, by
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
#[spec(
    captures: depth = context.depth(gandr_core_term::Zone::Intuitionistic),
    ensures: |ret| context.depth(gandr_core_term::Zone::Intuitionistic) == depth && match ret {
        | Verdict::Data => match *declaration.content() {
            | crate::DeclarationContent::Data(ref signature) => context.data_signatures().get(&declaration.constant()) == Some(signature),
            | crate::DeclarationContent::Abstract(_) => true,
            | crate::DeclarationContent::Value { .. } => false,
        },
        | Verdict::Checked { declared, body, .. } => matches!(declaration.content(), crate::DeclarationContent::Value { signature: Maybe::Present(ty), body: Maybe::Present(value) } if *ty == declared.id() && *value <= body)
            && context.signature(declaration.constant()) == Maybe::Present(declared),
        | Verdict::Synthesised { synthesised, body } => matches!(declaration.content(), crate::DeclarationContent::Value { signature: Maybe::Absent(_), body: Maybe::Present(value) } if *value <= body)
            && context.signature(declaration.constant()) == Maybe::Present(synthesised.produced()),
        | Verdict::Owed(entry) => matches!(declaration.content(), crate::DeclarationContent::Value { signature: Maybe::Present(ty), body: Maybe::Absent(_) } if *ty == entry.absence().declared().id())
            && entry.absence().constant() == declaration.constant()
            && entry.absence().origin() == declaration.origin()
            && context.signature(declaration.constant()) == Maybe::Present(entry.absence().declared()),
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
///   and nothing an earlier declaration or another run related.
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
#[spec(ensures: |ret| (run == Run::Typed || matches!(ret.typings, Maybe::Absent(typed::Absent::Unasked)))
    && match (&ret.verdict, &ret.failure) {
    | (&Verdict::Refused(refusal), &Maybe::Present(ref failure)) => failure.refusal() == refusal,
    | (&Verdict::Refused(_), &Maybe::Absent(kept::Absent::Unrun))
    | (&(Verdict::Data | Verdict::Checked { .. } | Verdict::Synthesised { .. } | Verdict::Owed(_)), &Maybe::Absent(kept::Absent::Accepted)) => true,
        | _ => false,
    })]
fn decide(
    context: &mut CheckingContext<'_>,
    declaration: &Declaration,
    run: Run,
) -> Decision
{
    let untyped = match run {
        | Run::Judged => typed::Absent::Unasked,
        | Run::Typed => typed::Absent::Unrun,
    };
    let unrun = |refusal| Decision {
        verdict: Verdict::Refused(refusal),
        failure: Maybe::Absent(kept::Absent::Unrun),
        typings: Maybe::Absent(untyped),
        elaboration: Maybe::Absent(elaborated::Absent::Unnested),
    };
    let constant = declaration.constant();
    // The pairs a declaration's conversions relate are its own: whatever an
    // earlier declaration's typing pass left is dropped.
    let _earlier = context.take_relating();
    if let Err(refusal) = context.admit(constant) {
        return unrun(refusal);
    }
    let (signature, body) = match *(declaration.content()) {
        | crate::DeclarationContent::Data(ref signature) => {
            return match crate::former::form_signature(context, constant, signature) {
                | Ok(()) => {
                    context.record_data(constant, alloc::sync::Arc::clone(signature));
                    Decision {
                        verdict: Verdict::Data,
                        failure: Maybe::Absent(kept::Absent::Accepted),
                        typings: Maybe::Absent(untyped),
                        elaboration: Maybe::Absent(elaborated::Absent::Unnested),
                    }
                },
                | Err(refusal) => unrun(refusal),
            };
        },
        | crate::DeclarationContent::Abstract(declared) => {
            let sealed = crate::former::form_abstract(context, declared)
                .and_then(|level| context.seal_abstract(constant, declared, level));
            return match sealed {
                | Ok(_atom) => Decision {
                    verdict: Verdict::Data,
                    failure: Maybe::Absent(kept::Absent::Accepted),
                    typings: Maybe::Absent(untyped),
                    elaboration: Maybe::Absent(elaborated::Absent::Unnested),
                },
                | Err(refusal) => unrun(refusal),
            };
        },
        | crate::DeclarationContent::Value {
            ref signature,
            ref body,
        } => (*signature, *body),
    };
    let direction = match signature {
        | Maybe::Present(declared) => match form_value_type(context, declared)
            .and_then(|formed| crate::session::unrestricted(context, formed.id()).map(|()| formed))
        {
            | Ok(formed) => Direction::Check(formed),
            | Err(refusal) => return unrun(refusal),
        },
        | Maybe::Absent(signature::Absent::Unsigned) => Direction::Synthesise,
    };
    let mut typings = Maybe::Absent(untyped);
    let mut elaboration = Maybe::Absent(elaborated::Absent::Unnested);
    let mut relating = Vec::new();
    let (verdict, failure) = match body {
        | Maybe::Present(body) => {
            let _stale = context.take_nesting();
            let first = judge(context, body, direction);
            let decisions = context.take_nesting();
            let judged = match first {
                | Ok(_) if !decisions.is_empty() => {
                    match crate::nested::elaborate(context.arena_mut(), body, &decisions) {
                        | Ok((elaborated, done)) => {
                            elaboration = Maybe::Present(done);
                            // The verdict is the second run's, and so are the
                            // pairs it relates.
                            let _first = context.take_relating();
                            judge(context, elaborated, direction)
                        },
                        | Err(unenclosed) => Err(unenclosed_failure(unenclosed.run())),
                    }
                },
                | Ok(_) | Err(_) => {
                    if !decisions.is_empty() {
                        elaboration = Maybe::Absent(elaborated::Absent::Unaccepted);
                    }
                    first
                },
            };
            relating = context.take_relating();
            if run == Run::Typed {
                typings = Maybe::Present(type_value(context, body, direction));
                let _typed = context.take_nesting();
            }
            match judged {
                | Ok(verdict) => (verdict, Maybe::Absent(kept::Absent::Accepted)),
                | Err(failure) => (Verdict::Refused(failure.refusal()), Maybe::Present(failure)),
            }
        },
        | Maybe::Absent(body::Absent::Hole) => {
            let owed = hole(direction, constant, declaration.origin()).and_then(|absence| {
                crate::capability::held(context, constant, absence.declared())?;
                Ok(absence)
            });
            match owed {
                | Ok(absence) => (
                    Verdict::Owed(ObligationEntry::from(absence)),
                    Maybe::Absent(kept::Absent::Accepted),
                ),
                | Err(refusal) => (
                    Verdict::Refused(refusal),
                    Maybe::Absent(kept::Absent::Unrun),
                ),
            }
        },
    };
    match (direction, verdict) {
        | (Direction::Check(declared), Verdict::Checked { body, .. }) => {
            // Native declarations return before the value judgment.
            context.record(constant, declared);
            context.define(constant, declared, body);
            context.keep_relations(constant, relating);
        },
        | (
            Direction::Check(declared),
            Verdict::Data | Verdict::Synthesised { .. } | Verdict::Owed(_) | Verdict::Refused(_),
        ) => context.record(constant, declared),
        | (Direction::Synthesise, Verdict::Synthesised { synthesised, body }) => {
            context.record(constant, synthesised.produced());
            context.define(constant, synthesised.produced(), body);
            context.keep_relations(constant, relating);
        },
        | (
            Direction::Synthesise,
            Verdict::Data | Verdict::Checked { .. } | Verdict::Owed(_) | Verdict::Refused(_),
        ) => {},
    }
    Decision {
        verdict,
        failure,
        typings,
        elaboration,
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
        | Direction::Synthesise => synthesise_value_with_failure(context, body)
            .map(|synthesised| Verdict::Synthesised { body, synthesised }),
        | Direction::Check(declared) => {
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
///   ledger holds exactly the owed verdicts' entries, in order; the lifts are
///   every lift the context's value bridges recorded by the run's end, the
///   function extensionalities every one it decided, the endpoint relations
///   every pair an accepted declaration's conversions related, and the
///   definitions every body the context defines a constant as; each body run
///   and refused keeps its failure under its position, and no other declaration
///   has one; each body the first run accepted holding a computation written
///   where a value is read keeps its elaboration under its position.
/// - provides: total marking — a refused declaration does not stop the run.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the surfaces are the run's totality and the ledger's
///   feed, separated by a module mixing every verdict, with a refusal before
///   later declarations, asserted entry by entry, and the ledger asserted to
///   hold the owed entries and no refused one.
/// - witness: `module::tests::a_refusal_does_not_stop_the_run`
/// - witness: `module::tests::every_owed_hole_enters_the_ledger_in_order`
/// - witness: `module::tests::a_refusal_never_enters_the_ledger`
/// - witness: `module::tests::a_refused_body_keeps_the_rules_it_was_refused_inside`
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
        | Verdict::Data | Verdict::Checked { .. } | Verdict::Synthesised { .. } | Verdict::Refused(_) => None,
    }))
    && &ret.lifts == context.lifts()
    && &ret.funexts == context.funexts()
    && &ret.equivalences == context.equivalences()
    && &ret.flows == context.flows()
    && &ret.reflexivities == context.reflexivities()
    && &ret.relations == context.relations()
    && &ret.universals == context.universals()
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
    let mut judged = Vec::with_capacity(declarations.len());
    let mut ledger = ObligationLedger::new();
    let mut failures = BTreeMap::new();
    let mut nested_elaborations = BTreeMap::new();
    for declaration in declarations {
        let decision = decide(context, declaration, Run::Judged);
        if let Maybe::Present(failure) = decision.failure {
            failures.insert(declaration.constant(), failure);
        }
        if let Maybe::Present(elaboration) = decision.elaboration {
            nested_elaborations.insert(declaration.constant(), elaboration);
        }
        if let Verdict::Owed(entry) = decision.verdict {
            ledger.record(entry);
        }
        judged.push(Judged {
            constant: declaration.constant(),
            origin: declaration.origin(),
            verdict: decision.verdict,
        });
    }
    ModuleReport {
        judged,
        ledger,
        lifts: context.lifts().clone(),
        funexts: context.funexts().clone(),
        equivalences: context.equivalences().clone(),
        flows: context.flows().clone(),
        reflexivities: context.reflexivities().clone(),
        relations: context.relations().clone(),
        universals: context.universals().clone(),
        definitions: context.definitions().definitions().collect(),
        data_signatures: context.data_signatures().clone(),
        abstract_types: context.abstract_types().collect(),
        seal_table: context.seal_table().clone(),
        failures,
        nested_elaborations,
    }
}

/// Judge `declarations` in order, as [`check_module`] does, keeping the type
/// of every term each judged body judges.
///
/// # Specification
/// - requires: nothing.
/// - ensures: `context` is left as [`check_module`] leaves it, every
///   declaration judged in order; each declaration whose body was judged is
///   keyed by its constant with what [`type_value`] keeps for its body, read
///   before its own type entered the table; a declaration refused before its
///   body, a data declaration and a hole are not keyed.
/// - provides: the type of every term a module's bodies judge, for a face
///   answering a position inside a declaration.
/// - fails: never; a refusal is kept as the typed run's mark.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a module of an accepted body, a refused body and a hole
///   separates the keyed bodies from the unkeyed hole and the accepted body's
///   own type from its parts'.
/// - witness: `module::tests::a_typed_module_keeps_each_judged_body_s_term_types`
#[spec(ensures: |ret| ret.keys().all(|constant|
    declarations.iter().any(|declaration| declaration.constant() == *constant)))]
#[inline]
#[must_use]
pub fn type_module(
    context: &mut CheckingContext<'_>,
    declarations: &[Declaration],
) -> BTreeMap<ConstantIndex, Typings>
{
    let mut typed = BTreeMap::new();
    for declaration in declarations {
        if let Maybe::Present(typings) = decide(context, declaration, Run::Typed).typings {
            typed.insert(declaration.constant(), typings);
        }
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
        | Direction::Check(expected) => Ok(Absence::new(constant, expected, origin)),
        | Direction::Synthesise => Err(CheckRefusal::NotSynthesisable {
            form: CheckingForm::Hole(constant),
        }),
    }
}

#[cfg(test)]
mod tests
{
    use alloc::vec::Vec;

    use anodized::spec;
    use gandr_core_term::CoreArena;
    use gandr_core_term::FailureClass;
    use gandr_core_term::Sort;
    use gandr_core_term::ValueId;
    use gandr_core_term::ValueTypeId;
    use gandr_core_term::effect::Purity;
    use gandr_kernel_strata::Level;
    use gandr_kernel_term::BaseType;
    use gandr_kernel_term::ConstantIndex;
    use gandr_kernel_term::DeBruijnIndex;
    use gandr_kernel_term::GroundSort;
    use gandr_kernel_term::SealExtent;
    use quenchant_shape::shape::Maybe;

    use super::Verdict;
    use super::check_declaration;
    use super::check_module;
    use super::type_module;
    use crate::context::Atom;
    use crate::context::CheckBudget;
    use crate::context::CheckingContext;
    use crate::conversion::ConversionCount;
    use crate::declaration::AbstractType;
    use crate::declaration::Declaration;
    use crate::declaration::OriginToken;
    use crate::declaration::body;
    use crate::declaration::signature;
    use crate::failure::FrameRole;
    use crate::failure::Pursuit;
    use crate::failure::Stage;
    use crate::failure::judged;
    use crate::fixture::integer_literal;
    use crate::fixture::text_literal;
    use crate::nested::Nesting;
    use crate::refusal::CheckRefusal;
    use crate::refusal::CheckingForm;
    use crate::refusal::CoreNode;
    use crate::refusal::Mismatch;
    use crate::refusal::TermNode;
    use crate::refusal::TypeNode;
    use crate::refusal::UnadmittedFormer;
    use crate::seal::ComponentOrdinal;
    use crate::seal::SealSite;
    use crate::seal::SealingSite;

    /// An admission position in a fixture module.
    #[repr(transparent)]
    #[derive(Clone, Copy, Debug)]
    struct At(usize);

    /// The declaration at `position`, its origin `position + 100`.
    ///
    /// # Specification
    /// - requires: adding the origin offset one hundred does not overflow.
    /// - ensures: the fixture position and the distinct origin are retained
    ///   alongside the supplied signature and body.
    /// - panics: the position lies outside the offset domain.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a module with all four declaration shapes observes
    ///   verdicts and displaced origins, separating a lost half or confusion
    ///   between admission position and diagnostic origin.
    /// - witness: `module::tests::each_combination_of_halves_gets_its_verdict`
    /// - witness: `module::tests::every_owed_hole_enters_the_ledger_in_order`
    #[spec(
        requires: position.0.checked_add(100).is_some(),
        ensures: |ret| usize::from(ret.constant()) == position.0
            && Some(usize::from(ret.origin())) == position.0.checked_add(100)
            && matches!(ret.content(),&crate::DeclarationContent::Value {signature,body} if signature == declared && body == defined),
    )]
    fn declaration(
        position: At,
        declared: Maybe<ValueTypeId, signature::Absent>,
        defined: Maybe<ValueId, body::Absent>,
    ) -> Declaration
    {
        Declaration::new(
            ConstantIndex::from(position.0),
            declared,
            defined,
            OriginToken::from(position.0.checked_add(100).unwrap()),
        )
    }

    /// No declared type.
    const UNSIGNED: Maybe<ValueTypeId, signature::Absent> =
        Maybe::Absent(signature::Absent::Unsigned);

    /// No body.
    const HOLE: Maybe<ValueId, body::Absent> = Maybe::Absent(body::Absent::Hole);

    #[test]
    fn each_combination_of_halves_gets_its_verdict()
    {
        let mut arena = CoreArena::new();
        let integer = arena.value_type_base(BaseType::Integer);
        let zero = arena.value_literal(integer_literal());
        let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        let Verdict::Checked {
            declared,
            body,
            evidence,
        } = check_declaration(
            &mut context,
            &declaration(At(0), Maybe::Present(integer), Maybe::Present(zero)),
        )
        else {
            panic!("a signature and a body check");
        };
        assert_eq!(
            (declared.id(), body),
            (integer, zero),
            "the verdict carries the declared type and the body it checked"
        );
        assert_eq!(
            evidence.conversions(),
            ConversionCount::from(1_usize),
            "the literal crossed the value bridge once"
        );
        let Verdict::Owed(entry) = check_declaration(
            &mut context,
            &declaration(At(1), Maybe::Present(integer), HOLE),
        )
        else {
            panic!("a signature over a hole is owed");
        };
        assert_eq!(
            (
                entry.absence().constant(),
                entry.absence().declared().id(),
                entry.absence().origin()
            ),
            (
                ConstantIndex::from(1_usize),
                integer,
                OriginToken::from(101_usize)
            ),
            "the hole in checking position absorbs the declared type and owes it"
        );
        let Verdict::Synthesised { body, synthesised } = check_declaration(
            &mut context,
            &declaration(At(2), UNSIGNED, Maybe::Present(zero)),
        )
        else {
            panic!("a body alone synthesises");
        };
        assert_eq!(
            (body, synthesised.produced()),
            (zero, context.atom(Atom::Integer)),
            "the unsigned literal synthesises its atom, and the verdict carries the body"
        );
        assert_eq!(
            check_declaration(&mut context, &declaration(At(3), UNSIGNED, HOLE)),
            Verdict::Refused(CheckRefusal::NotSynthesisable {
                form: CheckingForm::Hole(ConstantIndex::from(3_usize)),
            }),
            "a hole in synthesis position has nothing to absorb and is refused"
        );
    }

    #[test]
    fn an_admission_out_of_order_is_refused()
    {
        let mut arena = CoreArena::new();
        let zero = arena.value_literal(integer_literal());
        let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        assert!(
            matches!(
                check_declaration(
                    &mut context,
                    &declaration(At(1), UNSIGNED, Maybe::Present(zero))
                ),
                Verdict::Synthesised { .. }
            ),
            "the first admission may take any position"
        );
        for repeated in [1_usize, 0_usize] {
            let verdict = check_declaration(
                &mut context,
                &declaration(At(repeated), UNSIGNED, Maybe::Present(zero)),
            );
            assert_eq!(
                verdict,
                Verdict::Refused(CheckRefusal::AdmissionOrder {
                    constant: ConstantIndex::from(repeated),
                    admitted: ConstantIndex::from(1_usize),
                }),
                "a position not above every admitted one is refused with both positions"
            );
            let Verdict::Refused(refusal) = verdict
            else {
                panic!("refused above");
            };
            assert_eq!(
                refusal.classify(),
                FailureClass::EngineFault,
                "an admission out of order is the producer's fault"
            );
        }
    }

    #[test]
    fn a_declaration_cannot_read_its_own_type()
    {
        let mut arena = CoreArena::new();
        let integer = arena.value_type_base(BaseType::Integer);
        let itself = arena.value_constant(ConstantIndex::from(0_usize));
        let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        let verdict = check_declaration(
            &mut context,
            &declaration(At(0), Maybe::Present(integer), Maybe::Present(itself)),
        );
        assert_eq!(
            verdict,
            Verdict::Refused(CheckRefusal::UnknownConstant {
                at: itself,
                constant: ConstantIndex::from(0_usize),
            }),
            "a body sees only the declarations strictly before it, so self-reference finds no type"
        );
        let Verdict::Refused(refusal) = verdict
        else {
            panic!("refused above");
        };
        assert_eq!(
            refusal.classify(),
            FailureClass::MalformedSource,
            "an unknown constant is the author's"
        );
    }

    #[test]
    fn a_refused_signed_body_still_supplies_its_type()
    {
        let mut arena = CoreArena::new();
        let integer = arena.value_type_base(BaseType::Integer);
        let text = arena.value_literal(text_literal());
        let earlier = arena.value_constant(ConstantIndex::from(0_usize));
        let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        assert!(
            matches!(
                check_declaration(
                    &mut context,
                    &declaration(At(0), Maybe::Present(integer), Maybe::Present(text))
                ),
                Verdict::Refused(CheckRefusal::TypeMismatch(Mismatch::Value { .. }))
            ),
            "the text does not have the declared integer type"
        );
        let Verdict::Synthesised { synthesised, .. } = check_declaration(
            &mut context,
            &declaration(At(1), UNSIGNED, Maybe::Present(earlier)),
        )
        else {
            panic!("the reference synthesises");
        };
        assert_eq!(
            synthesised.produced().id(),
            integer,
            "the declared type is the contract a later reference reads, whatever the body did"
        );
    }

    #[test]
    fn a_body_that_synthesised_nothing_supplies_no_type()
    {
        let mut arena = CoreArena::new();
        let zero = arena.value_literal(integer_literal());
        let returned = arena.computation_return(zero);
        let thunk = arena.value_thunk(returned);
        let earlier = arena.value_constant(ConstantIndex::from(0_usize));
        let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        assert_eq!(
            check_declaration(
                &mut context,
                &declaration(At(0), UNSIGNED, Maybe::Present(thunk))
            ),
            Verdict::Refused(CheckRefusal::NotSynthesisable {
                form: CheckingForm::Thunk(thunk),
            }),
            "an unsigned thunk does not synthesise"
        );
        assert_eq!(
            context.signature(ConstantIndex::from(0_usize)),
            Maybe::Absent(crate::context::signature_table::Absent::Untyped),
            "the refused body supplied no type"
        );
        assert_eq!(
            check_declaration(
                &mut context,
                &declaration(At(1), UNSIGNED, Maybe::Present(earlier))
            ),
            Verdict::Refused(CheckRefusal::UnknownConstant {
                at: earlier,
                constant: ConstantIndex::from(0_usize),
            }),
            "a reference to it finds no type"
        );
    }

    #[test]
    fn a_later_declaration_reads_an_earlier_type()
    {
        let mut arena = CoreArena::new();
        let integer = arena.value_type_base(BaseType::Integer);
        let returns_integer = arena.comp_type_returner(integer);
        let thunk_type = arena.value_type_thunk(returns_integer);
        let zero = arena.value_literal(integer_literal());
        let returned = arena.computation_return(zero);
        let thunk = arena.value_thunk(returned);
        let suspended = arena.value_constant(ConstantIndex::from(0_usize));
        let owed = arena.value_constant(ConstantIndex::from(1_usize));
        let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        let module = [
            declaration(At(0), Maybe::Present(thunk_type), Maybe::Present(thunk)),
            declaration(At(1), Maybe::Present(integer), HOLE),
            declaration(At(2), UNSIGNED, Maybe::Present(suspended)),
            declaration(At(3), Maybe::Present(integer), Maybe::Present(owed)),
        ];
        let report = check_module(&mut context, &module);
        let verdicts: Vec<_> = report.judged().iter().map(super::Judged::verdict).collect();
        assert!(
            matches!(verdicts[2], Verdict::Synthesised { synthesised, .. } if synthesised.produced().id() == thunk_type),
            "a reference synthesises the exact type its declaration supplied"
        );
        assert!(
            matches!(verdicts[3], Verdict::Checked { .. }),
            "an owed declaration supplies its declared type to later references"
        );
        assert_eq!(
            context
                .signature(ConstantIndex::from(1_usize))
                .map(crate::formation::FormedValueType::id),
            Maybe::Present(integer),
            "the table holds the owed declaration's type"
        );
    }

    #[test]
    fn an_ascription_keeps_the_endpoints_it_related()
    {
        // def k : U (Integer -> F Integer) = thunk { \x. return x } ;
        // def j : U (Integer -> F Integer) = k ;
        // def given : Path(U (…), thunk { force j }, k) = here(k) ;
        // def law : Path(U (…), k, k) = given ;
        // def again : Path(U (…), thunk { force j }, k) = given ;
        // `law`'s ascription relates `thunk { force j }` to `k`, unfolding `j`
        // under the thunk; `again`'s endpoints are the same syntax.
        let mut arena = CoreArena::new();
        let integer = arena.value_type_base(BaseType::Integer);
        let returns = arena.comp_type_returner(integer);
        let arrow = arena.comp_type_arrow(integer, returns);
        let function = arena.value_type_thunk(arrow);
        let bound = arena.value_variable(
            gandr_core_term::Zone::Intuitionistic,
            DeBruijnIndex::from(0_u32),
        );
        let returned = arena.computation_return(bound);
        let lambda = arena.computation_lambda(returned);
        let identity = arena.value_thunk(lambda);
        let [k, j, given] = [0_usize, 1, 2].map(|at| arena.value_constant(ConstantIndex::from(at)));
        let forced = arena.computation_force(j);
        let delayed = arena.value_thunk(forced);
        let stated = arena.value_type_path(function, delayed, k);
        let diagonal = arena.value_type_path(function, k, k);
        let here = arena.value_here(k);
        let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        let module = [
            declaration(At(0), Maybe::Present(function), Maybe::Present(identity)),
            declaration(At(1), Maybe::Present(function), Maybe::Present(k)),
            declaration(At(2), Maybe::Present(stated), Maybe::Present(here)),
            declaration(At(3), Maybe::Present(diagonal), Maybe::Present(given)),
            declaration(At(4), Maybe::Present(stated), Maybe::Present(given)),
        ];
        let report = check_module(&mut context, &module);
        assert!(
            report
                .judged()
                .iter()
                .all(|judged| matches!(judged.verdict(), Verdict::Checked { .. })),
            "every declaration checks: {:?}",
            report.judged()
        );
        assert_eq!(
            report.relations().keys().copied().collect::<Vec<_>>(),
            [ConstantIndex::from(3_usize)],
            "only the ascription whose endpoints differ keeps a pair"
        );
        let relations = report
            .relations()
            .get(&ConstantIndex::from(3_usize))
            .expect("the law's pairs");
        let [ref relation] = *relations.as_slice()
        else {
            panic!("one pair of endpoints differs: {relations:?}");
        };
        assert_eq!(
            (relation.left(), relation.right()),
            (delayed, k),
            "the pair is the synthesised endpoint against the declared one"
        );
        assert!(
            relation.decisions().iter().any(|decision| matches!(
                decision,
                gandr_kernel_conversion_trace::ConversionDecision::Unfold { .. }
            )),
            "the derivation names the unfoldings the kernel replays"
        );
    }

    #[test]
    fn a_refusal_does_not_stop_the_run()
    {
        let mut arena = CoreArena::new();
        let integer = arena.value_type_base(BaseType::Integer);
        let zero = arena.value_literal(integer_literal());
        let text = arena.value_literal(text_literal());
        let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        let module = [
            declaration(At(0), Maybe::Present(integer), Maybe::Present(text)),
            declaration(At(1), Maybe::Present(integer), Maybe::Present(zero)),
            declaration(At(2), Maybe::Present(integer), HOLE),
            declaration(At(3), UNSIGNED, HOLE),
            declaration(At(4), UNSIGNED, Maybe::Present(zero)),
        ];
        let report = check_module(&mut context, &module);
        let judged = report.judged();
        for (entry, offered) in judged.iter().zip(&module) {
            assert_eq!(
                (entry.constant(), entry.origin()),
                (offered.constant(), offered.origin()),
                "each verdict echoes its declaration's position and origin, in order"
            );
        }
        let [
            ref mismatched,
            ref checked,
            ref owed,
            ref unsigned_hole,
            ref synthesised,
        ] = *judged
        else {
            panic!("every declaration gets a verdict");
        };
        assert!(
            matches!(
                mismatched.verdict(),
                Verdict::Refused(CheckRefusal::TypeMismatch(_))
            ),
            "the first declaration is refused"
        );
        assert!(
            matches!(checked.verdict(), Verdict::Checked { .. }),
            "the next is judged on its own"
        );
        assert!(
            matches!(owed.verdict(), Verdict::Owed(_)),
            "the signed hole is owed"
        );
        assert!(
            matches!(
                unsigned_hole.verdict(),
                Verdict::Refused(CheckRefusal::NotSynthesisable { .. })
            ),
            "the unsigned hole is refused"
        );
        assert!(
            matches!(synthesised.verdict(), Verdict::Synthesised { .. }),
            "and the run goes on past it"
        );
    }

    #[test]
    fn every_owed_hole_enters_the_ledger_in_order()
    {
        let mut arena = CoreArena::new();
        let integer = arena.value_type_base(BaseType::Integer);
        let string = arena.value_type_base(BaseType::String);
        let zero = arena.value_literal(integer_literal());
        let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        let module = [
            declaration(At(0), Maybe::Present(integer), Maybe::Present(zero)),
            declaration(At(1), Maybe::Present(string), HOLE),
            declaration(At(2), UNSIGNED, Maybe::Present(zero)),
            declaration(At(3), Maybe::Present(integer), HOLE),
        ];
        let report = check_module(&mut context, &module);
        let owed: Vec<_> = report
            .ledger()
            .entries()
            .iter()
            .map(|entry| {
                let absence = entry.absence();
                (
                    absence.constant(),
                    absence.declared().id(),
                    absence.origin(),
                )
            })
            .collect();
        assert_eq!(
            owed,
            [
                (
                    ConstantIndex::from(1_usize),
                    string,
                    OriginToken::from(101_usize)
                ),
                (
                    ConstantIndex::from(3_usize),
                    integer,
                    OriginToken::from(103_usize)
                ),
            ],
            "the ledger holds each owed hole, in module order"
        );
        assert_eq!(
            usize::from(report.ledger().count()),
            2_usize,
            "the count is the holes owed"
        );
    }

    #[test]
    fn a_refusal_never_enters_the_ledger()
    {
        let mut arena = CoreArena::new();
        let integer = arena.value_type_base(BaseType::Integer);
        let unformed = arena.value_type_base(BaseType::Numeric);
        let text = arena.value_literal(text_literal());
        let unknown = arena.value_constant(ConstantIndex::from(9_usize));
        let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        let module = [
            declaration(At(0), Maybe::Present(integer), Maybe::Present(text)),
            declaration(At(1), UNSIGNED, HOLE),
            declaration(At(2), UNSIGNED, Maybe::Present(unknown)),
            declaration(At(3), Maybe::Present(unformed), HOLE),
            declaration(At(3), Maybe::Present(integer), HOLE),
        ];
        let report = check_module(&mut context, &module);
        assert!(
            report
                .judged()
                .iter()
                .all(|entry| matches!(entry.verdict(), Verdict::Refused(_))),
            "every declaration of this module is refused"
        );
        assert_eq!(
            report.judged()[3].verdict(),
            Verdict::Refused(CheckRefusal::OutOfFragment {
                at: CoreNode::Type(TypeNode::Value(unformed)),
                former: UnadmittedFormer::NumericAtom,
            }),
            "a signed hole under an unformed signature is refused, not owed"
        );
        assert_eq!(
            usize::from(report.ledger().count()),
            0_usize,
            "a refusal of any class leaves the ledger empty"
        );
    }

    #[test]
    fn a_refused_body_keeps_the_rules_it_was_refused_inside()
    {
        let mut arena = CoreArena::new();
        let integer = arena.value_type_base(BaseType::Integer);
        let unformed = arena.value_type_base(BaseType::Numeric);
        let itself = arena.value_constant(ConstantIndex::from(0_usize));
        let text = arena.value_literal(text_literal());
        let zero = arena.value_literal(integer_literal());
        let forced = arena.computation_force(zero);
        let thunk = arena.value_thunk(forced);
        let pair = arena.value_tuple(&[zero, thunk]);
        let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        let module = [
            declaration(At(0), Maybe::Present(integer), Maybe::Present(itself)),
            declaration(At(1), UNSIGNED, Maybe::Present(text)),
            declaration(At(2), Maybe::Present(unformed), Maybe::Present(text)),
            declaration(At(3), UNSIGNED, Maybe::Present(pair)),
        ];
        let report = check_module(&mut context, &module);
        assert_eq!(
            report.failures().keys().copied().collect::<Vec<_>>(),
            [ConstantIndex::from(0_usize), ConstantIndex::from(3_usize)],
            "the two refused bodies keep their failures; the accepted body and \
             the body under an unformed signature, never run, keep none"
        );
        let reference = &report.failures()[&ConstantIndex::from(0_usize)];
        assert_eq!(
            reference.refusal(),
            CheckRefusal::UnknownConstant {
                at: itself,
                constant: ConstantIndex::from(0_usize),
            },
            "the self-reference is refused before its type enters the table"
        );
        let [ref bridge] = *reference.obligations()
        else {
            panic!("one rule waits on the self-reference: {reference:?}");
        };
        assert_eq!(
            (bridge.role(), bridge.at()),
            (
                FrameRole::ValueBridge,
                CoreNode::Term(TermNode::Value(itself))
            ),
            "the check of the body waits on its synthesis, to cross the bridge"
        );
        assert!(
            matches!(bridge.expected(), Maybe::Present(TypeNode::Value(_))),
            "the body was checked against its declared type"
        );
        let synthesis = &report.failures()[&ConstantIndex::from(3_usize)];
        assert_eq!(
            synthesis
                .obligations()
                .iter()
                .map(|obligation| (obligation.role(), obligation.at()))
                .collect::<Vec<_>>(),
            [
                (
                    FrameRole::NativeTuple,
                    CoreNode::Term(TermNode::Value(pair))
                ),
                (
                    FrameRole::NativeCollect,
                    CoreNode::Term(TermNode::Value(pair))
                ),
            ],
            "the pair waits on its second component's type, outermost first"
        );
        assert_eq!(
            synthesis.pursuit(),
            Pursuit::new(
                CoreNode::Term(TermNode::Value(thunk)),
                Maybe::Absent(judged::Absent::Synthesised),
                Stage::Starting,
            ),
            "the thunk, which cannot synthesise, is the goal the refusal met"
        );
    }

    #[test]
    fn a_typed_module_keeps_each_judged_body_s_term_types()
    {
        let mut arena = CoreArena::new();
        let integer = arena.value_type_base(BaseType::Integer);
        let product = arena.value_type_product(&[integer, integer]);
        let zero = arena.value_literal(integer_literal());
        let text = arena.value_literal(text_literal());
        let pair = arena.value_tuple(&[zero, text]);
        let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        let module = [
            declaration(At(0), UNSIGNED, Maybe::Present(zero)),
            declaration(At(1), Maybe::Present(product), Maybe::Present(pair)),
            declaration(At(2), Maybe::Present(integer), HOLE),
        ];
        let typed = type_module(&mut context, &module);
        assert_eq!(
            typed.keys().copied().collect::<Vec<_>>(),
            [ConstantIndex::from(0_usize), ConstantIndex::from(1_usize)],
            "both judged bodies are typed; the hole is not"
        );
        let accepted = typed[&ConstantIndex::from(0_usize)].typings();
        assert_eq!(
            accepted
                .iter()
                .map(|typing| typing.term)
                .collect::<Vec<_>>(),
            [TermNode::Value(zero)],
            "the literal body is its only term"
        );
        let refused = &typed[&ConstantIndex::from(1_usize)];
        assert!(
            refused
                .typings()
                .iter()
                .any(|typing| typing.term == TermNode::Value(text)),
            "the refused component is typed where it was recovered"
        );
        assert_eq!(
            refused.typings().last().map(|typing| typing.term),
            Some(TermNode::Value(pair)),
            "the refused body itself finishes last"
        );
        assert_eq!(
            refused.marks().len(),
            1_usize,
            "the text component is the one mark"
        );
    }

    /// `U (Integer -> F Integer)`, and the identity function of that type.
    ///
    /// # Specification
    /// trivial.
    fn integer_function(arena: &mut CoreArena) -> (ValueTypeId, ValueId)
    {
        let integer = arena.value_type_base(BaseType::Integer);
        let returns = arena.comp_type_returner(integer);
        let arrow = arena.comp_type_arrow(integer, returns);
        let function = arena.value_type_thunk(arrow);
        let argument = arena.value_variable(
            gandr_core_term::Zone::Intuitionistic,
            DeBruijnIndex::from(0_u32),
        );
        let returned = arena.computation_return(argument);
        let lambda = arena.computation_lambda(returned);
        (function, arena.value_thunk(lambda))
    }

    /// A call of the constant `callee`, forced, at `argument`.
    ///
    /// # Specification
    /// trivial.
    fn call(
        arena: &mut CoreArena,
        callee: ConstantIndex,
        argument: ValueId,
    ) -> gandr_core_term::ComputationId
    {
        let callee = arena.value_constant(callee);
        let forced = arena.computation_force(callee);
        arena.computation_application(forced, argument)
    }

    #[test]
    fn a_nested_run_elaborates_into_a_bind_before_its_region()
    {
        let mut arena = CoreArena::new();
        let (function, identity) = integer_function(&mut arena);
        let [inner_x, expected_x, expected_inner_r, expected_r] = [(); 4].map(|()| {
            arena.value_variable(
                gandr_core_term::Zone::Intuitionistic,
                DeBruijnIndex::from(0_u32),
            )
        });
        let inner = call(&mut arena, ConstantIndex::from(0_usize), inner_x);
        let inner = arena.value_nested(inner);
        let outer = call(&mut arena, ConstantIndex::from(0_usize), inner);
        let outer = arena.value_nested(outer);
        let returned = arena.computation_return(outer);
        let lambda = arena.computation_lambda(returned);
        let twice = arena.value_thunk(lambda);
        let expected = {
            let first = call(&mut arena, ConstantIndex::from(0_usize), expected_x);
            let second = call(&mut arena, ConstantIndex::from(0_usize), expected_inner_r);
            let ran = arena.computation_bind(first, second);
            let returned = arena.computation_return(expected_r);
            let bound = arena.computation_bind(ran, returned);
            let lambda = arena.computation_lambda(bound);
            arena.value_thunk(lambda)
        };
        let report = {
            let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
            check_module(&mut context, &[
                declaration(At(0), Maybe::Present(function), Maybe::Present(identity)),
                declaration(At(1), Maybe::Present(function), Maybe::Present(twice)),
            ])
        };
        let Verdict::Checked { body, .. } = report.judged()[1].verdict()
        else {
            panic!("the nested calls check: {:?}", report.judged()[1].verdict());
        };
        assert_ne!(body, twice, "the verdict carries the elaborated body");
        assert_eq!(
            gandr_core_term::equal_certificate_syntax(&arena, body, expected),
            gandr_core_term::CertificateEquality::Equal,
            "the inner call runs inside the outer one's computation, and the outer before the return"
        );
        assert_eq!(
            report.definitions().get(&ConstantIndex::from(1_usize)),
            Some(&body),
            "the constant is defined as the elaborated body"
        );
        let elaboration = &report.nested_elaborations()[&ConstantIndex::from(1_usize)];
        assert_eq!(
            elaboration
                .decisions()
                .iter()
                .map(|(&at, &decided)| (at, decided))
                .collect::<Vec<_>>(),
            [
                (inner, Nesting::Ran(Purity::Pure)),
                (outer, Nesting::Ran(Purity::Pure))
            ],
            "both nested calls run, and neither performs an effect"
        );
        assert_eq!(
            elaboration
                .binds()
                .iter()
                .map(|&(run, _)| run)
                .collect::<Vec<_>>(),
            [inner, outer],
            "each run is reported beside the bind minted for it, the inner first"
        );
        assert!(
            !report
                .nested_elaborations()
                .contains_key(&ConstantIndex::from(0_usize)),
            "a body holding no nested computation is not elaborated"
        );
        let readmission = crate::bridge::readmit(&mut arena, &report);
        assert!(
            readmission.readmitted().iter().all(|readmitted| matches!(
                readmitted.outcome(),
                crate::bridge::Outcome::Defined { .. }
            )),
            "the kernel re-derives the elaborated body: {readmission:?}"
        );
    }

    #[test]
    fn a_nested_call_runs_with_the_effects_its_returner_performs()
    {
        use gandr_core_term::effect::EffectOp;
        use gandr_core_term::effect::EffectRow;
        use gandr_core_term::effect::EffectSig;
        use gandr_core_term::effect::OperationName;
        let mut arena = CoreArena::new();
        let (function, identity) = integer_function(&mut arena);
        let integer = arena.value_type_base(BaseType::Integer);
        let interface = EffectSig::new("Ask".into(), [EffectOp {
            name: OperationName::from("ask"),
            payload: integer,
            reply: integer,
        }])
        .expect("one operation");
        let asks =
            arena.comp_type_returner_with_effects(integer, EffectRow::singleton(interface.clone()));
        let asking_arrow = arena.comp_type_arrow(integer, asks);
        let asking_type = arena.value_type_thunk(asking_arrow);
        let [asked_x, effectful_x, pure_x] = [(); 3].map(|()| {
            arena.value_variable(
                gandr_core_term::Zone::Intuitionistic,
                DeBruijnIndex::from(0_u32),
            )
        });
        let asking = {
            let performed =
                arena.computation_perform(interface, OperationName::from("ask"), asked_x);
            let lambda = arena.computation_lambda(performed);
            arena.value_thunk(lambda)
        };
        let returned_of = |arena: &mut CoreArena, callee: ConstantIndex, argument: ValueId| {
            let called = call(arena, callee, argument);
            let nested = arena.value_nested(called);
            let returned = arena.computation_return(nested);
            let lambda = arena.computation_lambda(returned);
            (nested, arena.value_thunk(lambda))
        };
        let (effectful, asks_twice) =
            returned_of(&mut arena, ConstantIndex::from(1_usize), effectful_x);
        let (pure, identity_twice) = returned_of(&mut arena, ConstantIndex::from(0_usize), pure_x);
        let report = {
            let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
            check_module(&mut context, &[
                declaration(At(0), Maybe::Present(function), Maybe::Present(identity)),
                declaration(At(1), Maybe::Present(asking_type), Maybe::Present(asking)),
                declaration(
                    At(2),
                    Maybe::Present(asking_type),
                    Maybe::Present(asks_twice),
                ),
                declaration(
                    At(3),
                    Maybe::Present(function),
                    Maybe::Present(identity_twice),
                ),
            ])
        };
        let decided = |constant: usize, at: ValueId| {
            report
                .nested_elaborations()
                .get(&ConstantIndex::from(constant))
                .and_then(|elaboration| elaboration.decisions().get(&at).copied())
        };
        assert_eq!(
            decided(2, effectful),
            Some(Nesting::Ran(Purity::Effectful)),
            "a call whose returner performs `Ask` runs effectfully: {:?}",
            report.judged()[2].verdict()
        );
        assert_eq!(
            decided(3, pure),
            Some(Nesting::Ran(Purity::Pure)),
            "a call whose returner performs nothing runs purely"
        );
    }

    #[test]
    fn a_nested_computation_is_decided_by_its_expected_type()
    {
        let mut arena = CoreArena::new();
        let integer = arena.value_type_base(BaseType::Integer);
        let returns = arena.comp_type_returner(integer);
        let suspended_type = arena.value_type_thunk(returns);
        let parameter = arena.comp_type_arrow(suspended_type, returns);
        let consumer_type = arena.value_type_thunk(parameter);
        let consumer = {
            let argument = arena.value_variable(
                gandr_core_term::Zone::Intuitionistic,
                DeBruijnIndex::from(0_u32),
            );
            let forced = arena.computation_force(argument);
            let lambda = arena.computation_lambda(forced);
            arena.value_thunk(lambda)
        };
        let zero = arena.value_literal(integer_literal());
        let produce = arena.computation_return(zero);
        let suspended = arena.value_nested(produce);
        let consumed = call(&mut arena, ConstantIndex::from(0_usize), suspended);
        let use_site = arena.value_thunk(consumed);
        let unsigned_zero = arena.value_literal(integer_literal());
        let unsigned_produce = arena.computation_return(unsigned_zero);
        let unsigned = arena.value_nested(unsigned_produce);
        let report = {
            let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
            check_module(&mut context, &[
                declaration(
                    At(0),
                    Maybe::Present(consumer_type),
                    Maybe::Present(consumer),
                ),
                declaration(
                    At(1),
                    Maybe::Present(suspended_type),
                    Maybe::Present(use_site),
                ),
                declaration(At(2), UNSIGNED, Maybe::Present(unsigned)),
            ])
        };
        let Verdict::Checked { body, .. } = report.judged()[1].verdict()
        else {
            panic!(
                "the nested computation checks at the thunk type: {:?}",
                report.judged()[1].verdict()
            );
        };
        let elaboration = &report.nested_elaborations()[&ConstantIndex::from(1_usize)];
        assert_eq!(
            elaboration.decisions().get(&suspended),
            Some(&Nesting::Suspended),
            "at a thunk-typed parameter it is suspended"
        );
        assert!(elaboration.binds().is_empty(), "a suspension mints no bind");
        let Some(&gandr_core_term::Value::Thunk(call_body)) = arena.value(body)
        else {
            panic!("the use site stays a thunk");
        };
        let Some(&gandr_core_term::Computation::Application(_, argument)) =
            arena.computation(call_body)
        else {
            panic!("the call stands as written");
        };
        assert_eq!(
            arena.value(argument),
            Some(&gandr_core_term::Value::Thunk(produce)),
            "the argument is the thunk of the written computation"
        );
        assert_eq!(
            report.judged()[2].verdict(),
            Verdict::Refused(CheckRefusal::NotSynthesisable {
                form: CheckingForm::Nested(unsigned),
            }),
            "with no type expected there is nothing to decide by, and it is refused by name"
        );
    }

    #[test]
    fn a_run_in_a_definition_s_own_value_is_unenclosed()
    {
        let mut arena = CoreArena::new();
        let (function, identity) = integer_function(&mut arena);
        let integer = arena.value_type_base(BaseType::Integer);
        let zero = arena.value_literal(integer_literal());
        let computation = call(&mut arena, ConstantIndex::from(0_usize), zero);
        let nested = arena.value_nested(computation);
        let report = {
            let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
            check_module(&mut context, &[
                declaration(At(0), Maybe::Present(function), Maybe::Present(identity)),
                declaration(At(1), Maybe::Present(integer), Maybe::Present(nested)),
            ])
        };
        let refusal = CheckRefusal::UnenclosedRun { at: nested };
        assert_eq!(
            report.judged()[1].verdict(),
            Verdict::Refused(refusal),
            "the call checks at the integer, but no computation encloses it to run before"
        );
        assert_eq!(refusal.classify(), FailureClass::MalformedSource);
        let failure = &report.failures()[&ConstantIndex::from(1_usize)];
        assert!(
            failure.obligations().is_empty(),
            "no rule of the judgement is pending"
        );
        assert_eq!(
            failure.pursuit().at(),
            CoreNode::Term(TermNode::Value(nested))
        );
        assert!(
            !report
                .definitions()
                .contains_key(&ConstantIndex::from(1_usize)),
            "a refused body defines nothing"
        );
    }

    /// The answers of `supported`, positions and type ids, in order.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: one position and underlying type-id answer per consultation,
    ///   in the same order and retaining absence reasons.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — repeated, absent and interrupted consultation reads
    ///   are compared with exact position/type pairs; the observer exposes
    ///   wrong order, missing answers or loss of an absence.
    /// - witness: `module::tests::the_support_holds_each_consulted_answer_once_in_position_order`
    /// - witness: `module::tests::a_refusal_cuts_the_support_where_the_run_stopped`
    #[spec(ensures: |ret| ret.iter().copied().eq(supported.support().consulted().iter()
        .map(|entry| (entry.constant(), entry.answer().map(crate::formation::FormedValueType::id)))))]
    fn answers(
        supported: &super::Supported
    ) -> Vec<(
        ConstantIndex,
        Maybe<ValueTypeId, crate::context::signature_table::Absent>,
    )>
    {
        supported
            .support()
            .consulted()
            .iter()
            .map(|consulted| {
                (
                    consulted.constant(),
                    consulted
                        .answer()
                        .map(crate::formation::FormedValueType::id),
                )
            })
            .collect()
    }

    #[test]
    fn the_support_holds_each_consulted_answer_once_in_position_order()
    {
        let mut arena = CoreArena::new();
        let integer = arena.value_type_base(BaseType::Integer);
        let returns_integer = arena.comp_type_returner(integer);
        let inner = arena.comp_type_arrow(integer, returns_integer);
        let outer = arena.comp_type_arrow(integer, inner);
        let function_type = arena.value_type_thunk(outer);
        let suspended_type = arena.value_type_thunk(returns_integer);
        let zero = arena.value_literal(integer_literal());
        let x = arena.value_constant(ConstantIndex::from(0_usize));
        let f = arena.value_constant(ConstantIndex::from(1_usize));
        let unknown = arena.value_constant(ConstantIndex::from(7_usize));
        // thunk ((force f) x) x: reads f, then x, then x again.
        let forced = arena.computation_force(f);
        let once = arena.computation_application(forced, x);
        let twice = arena.computation_application(once, x);
        let suspended = arena.value_thunk(twice);
        let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        let _x = check_declaration(
            &mut context,
            &declaration(At(0), Maybe::Present(integer), Maybe::Present(zero)),
        );
        let _f = check_declaration(
            &mut context,
            &declaration(At(1), Maybe::Present(function_type), HOLE),
        );
        let _read = check_declaration(
            &mut context,
            &declaration(At(2), UNSIGNED, Maybe::Present(x)),
        );
        let literal = super::check_declaration_supported(
            &mut context,
            &declaration(At(3), UNSIGNED, Maybe::Present(zero)),
        );
        assert_eq!(
            answers(&literal),
            [],
            "a judgement that reads no constant consults nothing, whatever ran before it"
        );
        let applied = super::check_declaration_supported(
            &mut context,
            &declaration(
                At(4),
                Maybe::Present(suspended_type),
                Maybe::Present(suspended),
            ),
        );
        assert!(
            matches!(applied.verdict(), Verdict::Checked { .. }),
            "the application checks"
        );
        assert_eq!(
            answers(&applied),
            [
                (ConstantIndex::from(0_usize), Maybe::Present(integer)),
                (ConstantIndex::from(1_usize), Maybe::Present(function_type)),
            ],
            "f read first and x read twice are each held once, ascending by position"
        );
        let missing = super::check_declaration_supported(
            &mut context,
            &declaration(At(5), UNSIGNED, Maybe::Present(unknown)),
        );
        assert_eq!(
            answers(&missing),
            [(
                ConstantIndex::from(7_usize),
                Maybe::Absent(crate::context::signature_table::Absent::Untyped)
            )],
            "an unadmitted position is consulted and answers its absence"
        );
    }

    #[test]
    fn a_refusal_cuts_the_support_where_the_run_stopped()
    {
        let mut arena = CoreArena::new();
        let integer = arena.value_type_base(BaseType::Integer);
        let returns_integer = arena.comp_type_returner(integer);
        let inner = arena.comp_type_arrow(integer, returns_integer);
        let outer = arena.comp_type_arrow(integer, inner);
        let function_type = arena.value_type_thunk(outer);
        let suspended_type = arena.value_type_thunk(returns_integer);
        let zero = arena.value_literal(integer_literal());
        let text = arena.value_literal(text_literal());
        let s = arena.value_constant(ConstantIndex::from(0_usize));
        let f = arena.value_constant(ConstantIndex::from(1_usize));
        let x = arena.value_constant(ConstantIndex::from(2_usize));
        // thunk ((force f) s) x: s is a string, so the run stops before x.
        let forced = arena.computation_force(f);
        let once = arena.computation_application(forced, s);
        let twice = arena.computation_application(once, x);
        let suspended = arena.value_thunk(twice);
        let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        let module = [
            declaration(At(0), UNSIGNED, Maybe::Present(text)),
            declaration(At(1), Maybe::Present(function_type), HOLE),
            declaration(At(2), Maybe::Present(integer), Maybe::Present(zero)),
        ];
        for offered in &module {
            let _judged = check_declaration(&mut context, offered);
        }
        let string = context.atom(Atom::String).id();
        let refused = super::check_declaration_supported(
            &mut context,
            &declaration(
                At(3),
                Maybe::Present(suspended_type),
                Maybe::Present(suspended),
            ),
        );
        assert!(
            matches!(
                refused.verdict(),
                Verdict::Refused(CheckRefusal::TypeMismatch(Mismatch::Value { at, .. })) if at == s
            ),
            "the string argument is refused at the value bridge"
        );
        assert_eq!(
            answers(&refused),
            [
                (ConstantIndex::from(0_usize), Maybe::Present(string)),
                (ConstantIndex::from(1_usize), Maybe::Present(function_type)),
            ],
            "the support holds what the run consulted before the refusal and nothing after it"
        );
    }

    #[test]
    fn an_adopted_answer_is_read_as_if_judged()
    {
        let mut arena = CoreArena::new();
        let integer = arena.value_type_base(BaseType::Integer);
        let small = arena.value_type_universe(
            gandr_core_term::Sort::Ground(gandr_kernel_term::GroundSort::Value),
            gandr_kernel_strata::Level::zero(),
        );
        let code = arena.value_quote(integer);
        let adopted = arena.value_constant(ConstantIndex::from(0_usize));
        let untyped = arena.value_constant(ConstantIndex::from(1_usize));
        let decoded = arena.value_type_element(adopted, gandr_kernel_strata::Level::zero());
        let zero = arena.value_literal(integer_literal());
        let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        let formed =
            crate::formation::form_value_type(&mut context, small).expect("the universe forms");
        assert_eq!(
            context.adopt(
                ConstantIndex::from(0_usize),
                Maybe::Present(formed),
                Maybe::Present(code)
            ),
            Ok(()),
            "a first adoption takes any position"
        );
        assert_eq!(
            context.adopt(
                ConstantIndex::from(1_usize),
                Maybe::Absent(crate::context::signature_table::Absent::Untyped),
                Maybe::Absent(crate::code::unfolding::Absent::Rigid)
            ),
            Ok(()),
            "an adopted absence is admitted"
        );
        assert!(
            matches!(
                check_declaration(&mut context, &declaration(At(2), UNSIGNED, Maybe::Present(adopted))),
                Verdict::Synthesised { synthesised, .. } if synthesised.produced().id() == small
            ),
            "a later declaration reads the adopted type"
        );
        assert_eq!(
            check_declaration(
                &mut context,
                &declaration(At(3), UNSIGNED, Maybe::Present(untyped))
            ),
            Verdict::Refused(CheckRefusal::UnknownConstant {
                at: untyped,
                constant: ConstantIndex::from(1_usize),
            }),
            "a later declaration finds no type at an adopted absence"
        );
        assert_eq!(
            context.adopt(
                ConstantIndex::from(2_usize),
                Maybe::Absent(crate::context::signature_table::Absent::Untyped),
                Maybe::Absent(crate::code::unfolding::Absent::Rigid)
            ),
            Err(CheckRefusal::AdmissionOrder {
                constant: ConstantIndex::from(2_usize),
                admitted: ConstantIndex::from(3_usize),
            }),
            "an adoption out of order is refused with both positions"
        );
        assert_eq!(
            context
                .signature(ConstantIndex::from(2_usize))
                .map(crate::formation::FormedValueType::id),
            Maybe::Present(small),
            "the refused adoption left the table as it was"
        );
        assert!(
            matches!(
                check_declaration(
                    &mut context,
                    &declaration(At(4), Maybe::Present(decoded), Maybe::Present(zero))
                ),
                Verdict::Checked { .. }
            ),
            "a decode of the adopted code unfolds to the adopted body"
        );
    }

    /// The abstract type at `position`, of `kind`, represented by
    /// `representation`, sealing the `extent` declarations after it, minted at
    /// component `component` of ascription zero; its origin `position + 100`.
    ///
    /// # Specification
    /// - requires: adding the origin offset one hundred does not overflow.
    /// - ensures: the abstract type is offered at the fixture position with the
    ///   distinct origin.
    /// - panics: the position lies outside the offset domain.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a sealed module observes each premise of abstract
    ///   type formation and the reach of its seal.
    /// - witness: `module::tests::an_abstract_type_forms_at_a_value_universe_and_mints_its_site`
    /// - witness: `module::tests::a_sealed_member_checks_at_the_representation_inside`
    #[spec(
        requires: position.0.checked_add(100).is_some(),
        ensures: |ret| usize::from(ret.constant()) == position.0
            && matches!(ret.content(), &crate::DeclarationContent::Abstract(held)
                if held.kind() == kind && held.representation() == representation),
    )]
    fn sealed(
        position: At,
        kind: ValueTypeId,
        representation: ValueTypeId,
        extent: SealExtent,
        component: ComponentOrdinal,
    ) -> Declaration
    {
        Declaration::abstract_type(
            ConstantIndex::from(position.0),
            AbstractType::new(
                kind,
                representation,
                extent,
                SealSite::new(SealingSite::from(0_usize), component),
            ),
            OriginToken::from(position.0.checked_add(100).unwrap()),
        )
    }

    #[test]
    fn an_abstract_type_forms_at_a_value_universe_and_mints_its_site()
    {
        let mut arena = CoreArena::new();
        let integer = arena.value_type_base(BaseType::Integer);
        let small = arena.value_type_universe(Sort::Ground(GroundSort::Value), Level::zero());
        let module = [
            sealed(At(0), small, integer, 0_usize.into(), 0_usize.into()),
            sealed(At(1), integer, integer, 0_usize.into(), 1_usize.into()),
            sealed(At(2), small, small, 0_usize.into(), 2_usize.into()),
        ];
        let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        let report = check_module(&mut context, &module);
        let verdicts: Vec<_> = report.judged().iter().map(super::Judged::verdict).collect();
        assert_eq!(
            verdicts,
            [
                Verdict::Data,
                Verdict::Refused(CheckRefusal::AbstractKindNotUniverse(integer)),
                Verdict::Refused(CheckRefusal::RepresentationAboveKind {
                    representation: small,
                    kind: small,
                }),
            ],
            "a kind at a value universe forms; a kind that is no universe and a representation above its kind are refused by name"
        );
        assert_eq!(
            report.seal_table().sites(),
            [SealSite::new(
                SealingSite::from(0_usize),
                ComponentOrdinal::from(0_usize)
            )],
            "only the abstract type that formed minted its site"
        );
        assert_eq!(
            report.abstract_types().keys().copied().collect::<Vec<_>>(),
            [ConstantIndex::from(0_usize)],
            "and only it is retained for readmission"
        );
        assert_eq!(
            context.abstract_level(ConstantIndex::from(0_usize)),
            Ok(Level::zero()),
            "its atom inhabits its kind's universe"
        );
    }

    #[test]
    fn a_repeated_sealing_site_is_refused_and_mints_nothing()
    {
        let mut arena = CoreArena::new();
        let integer = arena.value_type_base(BaseType::Integer);
        let small = arena.value_type_universe(Sort::Ground(GroundSort::Value), Level::zero());
        let module = [
            sealed(At(0), small, integer, 0_usize.into(), 0_usize.into()),
            sealed(At(1), small, integer, 0_usize.into(), 0_usize.into()),
        ];
        let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        let report = check_module(&mut context, &module);
        let site = SealSite::new(SealingSite::from(0_usize), ComponentOrdinal::from(0_usize));
        assert_eq!(
            report.judged()[1].verdict(),
            Verdict::Refused(CheckRefusal::SealSiteRepeated(site)),
            "a second abstract type at one site is refused naming the site"
        );
        assert_eq!(
            (report.seal_table().sites(), report.abstract_types().len()),
            ([site].as_slice(), 1),
            "the refused one minted no second atom and was not retained"
        );
    }

    #[test]
    fn an_atom_naming_no_abstract_type_is_refused()
    {
        let mut arena = CoreArena::new();
        let zero = arena.value_literal(integer_literal());
        let named = arena.value_type_abstract(ConstantIndex::from(0_usize));
        let module = [
            declaration(At(0), UNSIGNED, Maybe::Present(zero)),
            declaration(At(1), Maybe::Present(named), HOLE),
        ];
        let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        let report = check_module(&mut context, &module);
        assert_eq!(
            report.judged()[1].verdict(),
            Verdict::Refused(CheckRefusal::NotAnAbstractType(ConstantIndex::from(
                0_usize
            ))),
            "an atom at a value declaration's position is no type"
        );
    }

    /// `module Counter :> #{ type T, seed : T } { type T = Integer ; def seed
    /// = 7 ; }` as the lowering admits it: the atom, the body member, the
    /// witness exporting it at the component type, then two clients.
    #[test]
    fn a_sealed_member_checks_at_the_representation_inside()
    {
        let mut arena = CoreArena::new();
        let integer = arena.value_type_base(BaseType::Integer);
        let small = arena.value_type_universe(Sort::Ground(GroundSort::Value), Level::zero());
        let seven = arena.value_literal(integer_literal());
        let atom = arena.value_type_abstract(ConstantIndex::from(0_usize));
        let member = arena.value_constant(ConstantIndex::from(1_usize));
        let export = arena.value_constant(ConstantIndex::from(2_usize));
        let module = [
            sealed(At(0), small, integer, 2_usize.into(), 0_usize.into()),
            declaration(At(1), Maybe::Present(integer), Maybe::Present(seven)),
            declaration(At(2), Maybe::Present(atom), Maybe::Present(member)),
            declaration(At(3), Maybe::Present(atom), Maybe::Present(export)),
            declaration(At(4), Maybe::Present(integer), Maybe::Present(export)),
            declaration(At(5), Maybe::Present(atom), Maybe::Present(seven)),
        ];
        let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        let report = check_module(&mut context, &module);
        let verdicts: Vec<_> = report.judged().iter().map(super::Judged::verdict).collect();
        assert!(
            matches!(verdicts[2], Verdict::Checked { .. }),
            "inside the seal the member's Integer is the atom's representation"
        );
        assert!(
            matches!(verdicts[3], Verdict::Checked { .. }),
            "outside, the export reads at the atom, which is itself"
        );
        assert_eq!(
            verdicts[4],
            Verdict::Refused(CheckRefusal::TypeMismatch(Mismatch::Value {
                at: export,
                synthesised: atom,
                expected: integer,
            })),
            "outside, the atom is not its representation, and the mismatch names it"
        );
        assert!(
            matches!(verdicts[5], Verdict::Refused(CheckRefusal::TypeMismatch(_))),
            "nor does a literal of the representation inhabit it"
        );
    }
}
