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
//! an application's head, an unsigned definition — there is nothing to decide
//! by, and the judgement refuses it by name, [`CheckRefusal::NotSynthesisable`]
//! with [`CheckingForm::Nested`], rather than guessing. The synthesis positions
//! where no thunk can stand decide by their own sort: a case's, a split's and a
//! list case's scrutinee is never a thunk, nor is the path an element transport
//! follows, so a nested computation there runs, as `case n >= 5 { … }` reads
//! the comparison's answer and `cong(loopOn, sect[<](q))` carries the recursive
//! call's path. A written `run c` always runs and synthesises the value `c`
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
//! run it was minted for, and every rebuilt node beside the node it was
//! rebuilt from, so a consumer publishes a refusal of the second run at the
//! written node that elaborated — the nested call's own span at its bind —
//! and no diagnostic names the minted variable.
//!
//! **A reduct the bridge crossed by runs where it crossed.** A model the value
//! bridge carried to a model of a theory its own includes stands, before the
//! elaboration, as a run of the reduct applied to it ([`cross`]); the run is
//! decided pure and binds before its region as any other, so the second run
//! and the kernel read the application.
//!
//! **What a type reads stays readable.** A pure run whose value a type after
//! it reads — a dependent pair's first component under its second's type, a
//! dependent function's argument under the types after it — stands as the
//! value it returns, `⟨c⟩`, rather than a bind's variable: the variable is
//! opaque, so `#{f(Base), cong(f, loop)}` at `#{point : Int, around :
//! Path(Int, point, point)}` would check its second component at `Path(Int,
//! x, x)` for a fresh `x`, which `f(Base)`'s path does not reach. A returned
//! value is what a compound endpoint already is, and it computes the same
//! value as the bind for a computation that performs nothing. An effectful
//! run still binds, in written order. The alternative was a bind whose
//! variable the body's types unfold to its computation, a let the core does
//! not have. Reversal: such a let.
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
    /// Run purely where a type after it reads it: it stands as the value it
    /// returns, `⟨c⟩`, rather than a bind's variable.
    Returned,
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
    /// Each value the value bridge carried by a map between models, with the
    /// crossing.
    crossings: BTreeMap<ValueId, gandr_core_term::Crossing>,
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
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a body whose nested runs elaborate into binds reports
    ///   the rebuilt body beside the written one it stands for.
    /// - witness: `module::tests::a_nested_run_elaborates_into_a_bind_before_its_region`
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

    /// Each value the value bridge carried by a map between models, by node,
    /// with the crossing the elaboration applied to it: the map and its
    /// carriers.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn crossings(&self) -> &BTreeMap<ValueId, gandr_core_term::Crossing>
    {
        &self.crossings
    }

    /// This elaboration, read after a crossing: `crossings` its crossings and
    /// `carried` the crossing's rebuild, standing before its own.
    ///
    /// # Specification
    /// - requires: `carried` is what [`cross`] carried to build the body this
    ///   elaboration rebuilt.
    /// - ensures: the crossings are `crossings`, and the carried pairs the
    ///   crossing's, then this elaboration's.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`cross`].
    /// - witness: `module::tests::a_model_crosses_to_an_included_theory_s_by_its_reduct`
    #[spec(captures: [ahead = carried.len(), own = self.carried.len(), count = crossings.len()],
        ensures: |ret| ret.carried.len() == ahead.saturating_add(own) && ret.crossings.len() == count)]
    #[must_use]
    pub(crate) fn after_crossing(
        mut self,
        crossings: BTreeMap<ValueId, gandr_core_term::Crossing>,
        mut carried: Vec<Carried>,
    ) -> Self
    {
        carried.append(&mut self.carried);
        self.carried = carried;
        self.crossings = crossings;
        self
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
                Nesting::Suspended => gandr_core_term::Nesting::Thunk,
                Nesting::Ran(_) => gandr_core_term::Nesting::Run,
                Nesting::Returned => gandr_core_term::Nesting::Returned,
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
        crossings: BTreeMap::new(),
    }))
}

/// Rebuild `body` with the map `crossings` gives each value it names applied
/// to its carriers and that value as a run, and read `decisions` over the
/// rebuilt body.
///
/// # Specification
/// - requires: `body` is live in `arena`; `crossings` and `decisions` are what
///   the judgement recorded over it.
/// - ensures: the rebuilt body, every node the rebuild carried over beside the
///   node it was built from, and `decisions` keyed by what each node stands as
///   in the rebuilt body, with each run the rebuild minted decided a pure run;
///   `body`, nothing carried and `decisions` unchanged when `crossings` names
///   nothing it reaches.
/// - provides: the body and decisions [`elaborate`] reads where the value
///   bridge crossed by a map between models.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a monoid's model passed where a semigroup's is asked,
///   beside a nested call, elaborates the reduct into a bind and keeps the
///   call's decision.
/// - witness: `module::tests::a_model_crosses_to_an_included_theory_s_by_its_reduct`
#[spec(ensures: |ret| ret.2.len() >= decisions.len())]
pub fn cross(
    arena: &mut CoreArena,
    body: ValueId,
    crossings: &BTreeMap<ValueId, gandr_core_term::Crossing>,
    decisions: &BTreeMap<ValueId, Nesting>,
) -> (ValueId, Vec<Carried>, BTreeMap<ValueId, Nesting>)
{
    let (mut carried, mut runs) = (Vec::new(), Vec::new());
    let crossed = gandr_core_term::cross_reducts(arena, body, crossings, &mut carried, &mut runs);
    let rebuilt: BTreeMap<ValueId, ValueId> = carried
        .iter()
        .filter_map(|&pair| match pair {
            Carried::Value(held, written) => Some((held, written)),
            Carried::Computation(..) | Carried::ValueType(..) | Carried::CompType(..) => None,
        })
        .collect();
    let mut read: BTreeMap<ValueId, Nesting> = decisions
        .iter()
        .map(|(&at, &decided)| (rebuilt.get(&at).copied().unwrap_or(at), decided))
        .collect();
    read.extend(
        runs.into_iter()
            .map(|run| (run, Nesting::Ran(Purity::Pure))),
    );
    (crossed, carried, read)
}
