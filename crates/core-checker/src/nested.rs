//! The fourth bridge: a computation written where a value is read.
//!
//! Three bridges between the sorts are the lowering's, each read off the
//! syntax: a value at an application's head is forced, a computation at a
//! function's body is thunked, and a value type at a function's result gains a
//! returner. A computation written anywhere else a value is read —
//! `Succ(plus(n, p))` — reaches the checker as a nested computation, because
//! what it means depends on a type the syntax does not carry. This bridge has
//! three rules.
//!
//! **Direction: the expected type decides.** Against a thunk type `U C` the
//! nested computation is suspended, as a written thunk is, and checks at `C`;
//! against the unknown type it is suspended too, as a written thunk checks
//! there. Against any other type `A` it runs: it must synthesise a returner
//! `F^e A'` whose `A'` crosses the value bridge to `A`. With no expected type —
//! a case's scrutinee, an application's head, an unsigned definition — there
//! is nothing to decide by, and the judgement refuses it by name,
//! [`CheckRefusal::NotSynthesisable`] with [`CheckingForm::Nested`], rather
//! than guessing. A written `run c` always runs and synthesises the value `c`
//! returns.
//!
//! **Order: written order, before the innermost enclosing computation.** A
//! run's region is the innermost computation whose values it stands in; an
//! application's head shares its spine's region, so `f(g(x), h(y))` runs `g`
//! and then `h` before the whole call. A thunk's body, a case arm, a lambda's
//! body and each half of a bind are regions of their own, so a run never
//! leaves a suspension or a branch. The runs of a region bind around it in
//! the order they are written, the first outermost, and a run nested in
//! another run's computation runs inside that computation, before it.
//!
//! **Where: the checker's elaboration.** The judgement records each decision
//! where it makes it; once the body is accepted, [`elaborate`] rebuilds it
//! with every suspension a thunk and every run a bind wrapped around its
//! region, the run's place taken by the bind's variable, and the judgement
//! runs again over the rebuilt body. The second run gives the explicit
//! spelling's verdict exactly — the bind's effect row joins its region's, and
//! a body type that would mention the bound value is a dependent bind — and
//! the verdict carries the rebuilt body, which is what the context defines,
//! the evaluator runs and the kernel re-derives: neither ever meets a nested
//! computation. A run with no computation around it — in a definition's own
//! value, or under static content — has nowhere to run and is refused as
//! [`CheckRefusal::UnenclosedRun`]. Each minted bind is reported beside the
//! run it was minted for, so a consumer reads the nested call's own span at
//! the bind and no diagnostic names the minted variable.
//!
//! The lowering decided every other bridge because the checker returned
//! verdicts, not terms, and every position's sort was read off the syntax. A
//! computation in value position is the position that recorded decision named
//! for its reversal: whether it is suspended or run is the expected type's,
//! which only the checker holds, so the insertion moved here and the checker
//! now answers the elaborated body. The alternatives were a run inserted by
//! the lowering wherever the written form is a call, which guesses wrong at
//! every thunk-typed parameter, and keeping the refusal, which makes every
//! non-tail call a statement. The record also fenced effect sequencing: none
//! is inserted outside an explicit opt-in, and a run inferred here sequences
//! a computation the source did not mark. Each decision carries the
//! returner's [`Purity`], and the `explicit-runs` lint, with its `effects`
//! option, is the opt-in made checkable: a module that holds effect order to
//! be written asks for every effectful run to be. The judgement runs twice
//! over a body holding a run, and a body without one runs once. Reversal: a
//! checker that mints as it judges — a bidirectional elaborator answering
//! terms from every rule — makes the second run unnecessary.
//!
//! [`CheckRefusal::NotSynthesisable`]: crate::CheckRefusal::NotSynthesisable
//! [`CheckingForm::Nested`]: crate::CheckingForm::Nested
//! [`CheckRefusal::UnenclosedRun`]: crate::CheckRefusal::UnenclosedRun

use alloc::collections::BTreeMap;
use alloc::vec::Vec;

use anodized::spec;
use gandr_core_term::Carried;
use gandr_core_term::ComputationId;
use gandr_core_term::CoreArena;
use gandr_core_term::Unenclosed;
use gandr_core_term::ValueId;
use gandr_core_term::effect::Purity;

/// How the judgement decided a computation written where a value is read.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Nesting
{
    /// Checked against a thunk type, or the unknown type: suspended.
    Suspended,
    /// Run before its region, its returner performing effects or none.
    Ran(Purity),
}

/// What elaborating one declaration's body did: every decision the judgement
/// made, every node the rebuild carried over from one it was built from, and
/// every bind minted beside the run it was minted for.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct NestedElaboration
{
    /// Each nested computation and written run, by node, as decided.
    decisions: BTreeMap<ValueId, Nesting>,
    /// Each rebuilt node beside the node it was built from, in rebuild order.
    carried: Vec<Carried>,
    /// Each run beside the bind minted for it, in minting order.
    binds: Vec<(ValueId, ComputationId)>,
}

impl NestedElaboration
{
    /// Each nested computation and written run of the declaration's body, by
    /// node, as the judgement decided it.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn decisions(&self) -> &BTreeMap<ValueId, Nesting>
    {
        &self.decisions
    }

    /// Each node the rebuild minted beside the node it was built from, the
    /// nodes it was built from first.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn carried(&self) -> &[Carried]
    {
        &self.carried
    }

    /// Each run beside the bind minted for it, in minting order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn binds(&self) -> &[(ValueId, ComputationId)]
    {
        &self.binds
    }
}

/// Rebuild `body` with every computation written where a value is read
/// elaborated as `decisions` decided it.
///
/// # Specification
/// - requires: `body` is live in `arena`, and `decisions` holds what the
///   judgement decided for every nested computation and written run of it.
/// - ensures: the elaborated body, with no nested computation or written run
///   reachable through its terms, beside what the rebuild did; `body` itself
///   when it holds none.
/// - provides: the body the second run judges and the verdict carries.
/// - fails: the first run, in written order, standing in no computation's
///   values; the caller refuses it as
///   [`CheckRefusal::UnenclosedRun`](crate::CheckRefusal::UnenclosedRun).
/// - panics: none.
///
/// # Errors
/// [`Unenclosed`] as above.
///
/// # Adequacy
/// - hypothesis: L3 — a run before a constructor's return, a suspension at a
///   thunk-typed argument and a run in a definition's own value separate the
///   two elaborations and the refusal.
/// - witness: `module::tests::a_nested_run_elaborates_into_a_bind_before_its_region`
/// - witness: `module::tests::a_nested_computation_is_decided_by_its_expected_type`
/// - witness: `module::tests::a_run_in_a_definition_s_own_value_is_unenclosed`
#[spec(ensures: |ret| match ret {
    | Ok((_, ref elaboration)) => elaboration.decisions == *decisions,
    | Err(unenclosed) => decisions.contains_key(&unenclosed.run()),
})]
pub fn elaborate(
    arena: &mut CoreArena,
    body: ValueId,
    decisions: &BTreeMap<ValueId, Nesting>,
) -> Result<(ValueId, NestedElaboration), Unenclosed>
{
    let nesting = decisions
        .iter()
        .map(|(&at, &decided)| {
            (at, match decided {
                | Nesting::Suspended => gandr_core_term::Nesting::Thunk,
                | Nesting::Ran(_) => gandr_core_term::Nesting::Run,
            })
        })
        .collect();
    let mut carried = Vec::new();
    let mut binds = Vec::new();
    let elaborated =
        gandr_core_term::elaborate_nested_traced(arena, body, &nesting, &mut carried, &mut binds)?;
    Ok((elaborated, NestedElaboration {
        decisions: decisions.clone(),
        carried,
        binds,
    }))
}
