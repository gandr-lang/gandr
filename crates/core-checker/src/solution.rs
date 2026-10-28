//! Refinement by solution: an index equation solved where one of its sides is
//! a variable.
//!
//! A case on an indexed family binds one equation per index past each arm's
//! fields. The arm's goal and the binders after the scrutinee's index keep that
//! index as written. An arm whose result stands at its own constructor's index
//! is then refused. The solution step reads an equation with a variable side as
//! the substitution of the other side for the variable.
//!
//! The step writes the substitution into the term, as a motive generalises an
//! elimination. The arm's body moves into a thunk over the binders after the
//! variable that it reads. The thunk stands at the solved side. One transport
//! along the equation carries it to the variable. A case on a variable
//! generalises its later binders the same way, through its motive.
//!
//! The judgement checks the refined term in place of the written one and
//! records the pair. The kernel checks the refined term as any other term. The
//! core body keeps the term as written, so the evaluator and the machine run
//! it unchanged. A typed run keeps each typing inside the refined term as its
//! written term's, read in the written context ([`Written`]).
//!
//! A binder of a recursion's staged argument is not generalised. The bridge
//! crosses no staged type, so no transport's motive names one (#3631).
//!
//! # References
//!
//! - `Cockx-2018-elaborating_dependent_copattern_matching` — exemplar: § 4.2,
//!   the solution step of the unifier, an equivalence of telescopes that
//!   instantiates one variable.
//! - Conor `McBride`, _Elimination with a Motive_, TYPES 2000, LNCS 2277,
//!   doi:10.1007/3-540-45842-5_13 — the generalisation of the goal over the
//!   binders after the solved variable.
//! - `vault:01a178aa-a2df-7df1-b34d-3a0211d0b6cb` — exemplar: §
//!   elim-refine-with-abstraction, one transport per solved equation.

use alloc::collections::BTreeMap;
use alloc::vec::Vec;

use anodized::spec;
use gandr_core_term::BinderDepth;
use gandr_core_term::Binders;
use gandr_core_term::Carried;
use gandr_core_term::CompType;
use gandr_core_term::CompTypeId;
use gandr_core_term::Computation;
use gandr_core_term::ComputationId;
use gandr_core_term::CoreArena;
use gandr_core_term::Value;
use gandr_core_term::ValueId;
use gandr_core_term::ValueType;
use gandr_core_term::ValueTypeId;
use gandr_core_term::Zone;
use gandr_core_term::hole::TermId;
use gandr_kernel_term::DeBruijnIndex;
use quenchant_shape::shape::Maybe;

use crate::context::CheckingContext;
use crate::judgement::Typing;
use crate::refusal::CheckRefusal;
use crate::refusal::CoreNode;
use crate::refusal::TermNode;
use crate::refusal::TypeNode;

/// Why a refinement keeps a term as written.
pub mod unrefined
{
    /// The reason the term is checked as written.
    #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub enum Absent
    {
        /// The term or its type does not have the form the step reads.
        Unshaped,
        /// No equation has a variable side the step solves, or no binder after
        /// the scrutinee is read at it.
        Unsolved,
    }
}

/// A term refined in the place of a written one, and what reads it back as
/// written.
#[derive(Clone, Debug)]
pub struct Refined
{
    /// The refined term.
    pub term: ComputationId,
    /// Each written node the refinement rewrote, beside its rewrite, in the
    /// order the refinement made them.
    pub carried: Vec<Carried>,
    /// Each lambda the refinement minted for a generalised binder, beside the
    /// place of the binder it stands for.
    pub generalising: Vec<(ComputationId, BinderDepth)>,
}

/// What reads a refined term back as written: the written node of each
/// rewrite, the binder each generalising lambda stands for, and each such
/// binder open now.
///
/// A refined term binds a copy of each generalised binder, so a term inside it
/// is judged under more binders than its written context holds. A typing read
/// back replaces each open copy by the binder it stands for and keys the
/// written node, so a type the typed run keeps reads in the written context.
#[derive(Clone, Debug, Default)]
pub struct Written
{
    /// Each value a refinement rewrote, beside the written value it stands for.
    values: BTreeMap<ValueId, ValueId>,
    /// Each computation a refinement rewrote, beside the written computation
    /// it stands for.
    computations: BTreeMap<ComputationId, ComputationId>,
    /// Each lambda a refinement minted for a generalised binder, beside the
    /// place of the binder it stands for.
    generalising: BTreeMap<ComputationId, BinderDepth>,
    /// Each generalised binder open now, by its place, beside the place of the
    /// binder it stands for, ascending by place.
    standing: Vec<(BinderDepth, BinderDepth)>,
}

impl Written
{
    /// Record what reads `refined` back as written.
    ///
    /// A substitution's trace reports an entry it carries under a binder beside
    /// the node it carries it to, after the subject's node that the entry
    /// replaces. So a rewrite keeps the first node it is reported from.
    ///
    /// # Specification
    /// - requires: `refined`'s rewrites are in the order the refinement made
    ///   them.
    /// - ensures: each rewrite of `refined` stands for the written node its
    ///   first source stands for, and each of its generalising lambdas for its
    ///   binder.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a refined case reads its arm's written terms at the
    ///   arm's own type and depth.
    /// - witness: `tests::native_formers::a_refined_arm_types_its_written_terms_in_their_own_context_3483`
    #[spec(ensures: refined.generalising.iter().all(|&(lambda, place)| self.generalising.get(&lambda) == Some(&place)))]
    pub fn record(
        &mut self,
        refined: &Refined,
    )
    {
        for &pair in &refined.carried {
            match pair {
                Carried::Value(held, rewritten) => {
                    let written = self.value(held);
                    let _kept = self.values.entry(rewritten).or_insert(written);
                },
                Carried::Computation(held, rewritten) => {
                    let written = self.computation(held);
                    let _kept = self.computations.entry(rewritten).or_insert(written);
                },
                Carried::ValueType(..) | Carried::CompType(..) => {},
            }
        }
        self.generalising
            .extend(refined.generalising.iter().copied());
    }

    /// The written value `at` stands for.
    ///
    /// # Specification
    /// - ensures: the value a refinement rewrote into `at`, read back to the
    ///   term as written, or `at` when none did.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::record`].
    /// - witness: `tests::native_formers::a_refined_arm_elaborates_its_nested_call_where_it_is_written_3483`
    #[spec(ensures: |ret| self.values.get(&at).map_or(ret == at, |&origin| ret == origin))]
    #[must_use]
    pub fn value(
        &self,
        at: ValueId,
    ) -> ValueId
    {
        self.values.get(&at).copied().unwrap_or(at)
    }

    /// The written computation `at` stands for.
    ///
    /// # Specification
    /// - ensures: the computation a refinement rewrote into `at`, read back to
    ///   the term as written, or `at` when none did.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::record`].
    /// - witness: `tests::native_formers::a_refined_arm_types_its_written_terms_in_their_own_context_3483`
    #[spec(ensures: |ret| self.computations.get(&at).map_or(ret == at, |&origin| ret == origin))]
    #[must_use]
    pub fn computation(
        &self,
        at: ComputationId,
    ) -> ComputationId
    {
        self.computations.get(&at).copied().unwrap_or(at)
    }

    /// Open the binder of `lambda` at `place`.
    ///
    /// # Specification
    /// - requires: `place` is the depth of the context the binder extends.
    /// - ensures: no binder at or past `place` stands open. When `lambda` is a
    ///   generalising lambda, its binder stands at `place` for the binder it
    ///   copies.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::record`].
    /// - witness: `tests::native_formers::a_refined_arm_types_its_written_terms_in_their_own_context_3483`
    #[spec(ensures: self.standing.last().is_none_or(|&(open, _)| open <= place)
        && (self.generalising.contains_key(&lambda) == self.standing.last().is_some_and(|&(open, _)| open == place)))]
    pub fn open(
        &mut self,
        lambda: ComputationId,
        place: BinderDepth,
    )
    {
        self.close(place);
        if let Some(&stands_for) = self.generalising.get(&lambda) {
            self.standing.push((place, stands_for));
        }
    }

    /// Close every binder at or past `depth`.
    ///
    /// # Specification
    /// - ensures: no binder at or past `depth` stands open, and every binder
    ///   below it stays.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::record`]: the second arm reads no copy the
    ///   first arm opened.
    /// - witness: `tests::native_formers::a_refined_arm_types_its_written_terms_in_their_own_context_3483`
    #[spec(ensures: self.standing.last().is_none_or(|&(open, _)| open < depth))]
    pub fn close(
        &mut self,
        depth: BinderDepth,
    )
    {
        while self.standing.last().is_some_and(|&(open, _)| open >= depth) {
            let _closed = self.standing.pop();
        }
    }

    /// `typing` read back as written: its term the written one, and its type
    /// read in the context without the copies open below its depth.
    ///
    /// # Specification
    /// - requires: `typing`'s type is read under `typing.depth` binders, the
    ///   copies open now among them.
    /// - ensures: the written term, and the type with each copy replaced by the
    ///   binder it stands for and each other binder by itself, at the depth
    ///   less the copies. `typing` with its written term when no copy is open
    ///   below its depth.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a term typed at a path between copies reads at the
    ///   path between the written binders, at the written depth.
    /// - witness: `tests::native_formers::a_refined_arm_types_its_written_terms_in_their_own_context_3483`
    #[spec(ensures: |ret| ret.depth <= typing.depth)]
    pub fn read_back(
        &self,
        arena: &mut CoreArena,
        typing: Typing,
    ) -> Typing
    {
        let term = match typing.term {
            TermNode::Value(at) => TermNode::Value(self.value(at)),
            TermNode::Computation(at) => TermNode::Computation(self.computation(at)),
        };
        let open: BTreeMap<BinderDepth, BinderDepth> = self
            .standing
            .iter()
            .copied()
            .filter(|&(place, _)| place < typing.depth)
            .collect();
        if open.is_empty() {
            return Typing { term, ..typing };
        }
        // Each binder's index past the copies, by place: the count of the
        // binders inside it that are not copies.
        let (mut above, mut index, mut kept) = (
            Vec::with_capacity(usize::from(typing.depth)),
            0_u32,
            0_usize,
        );
        for place in (0 .. usize::from(typing.depth))
            .rev()
            .map(BinderDepth::from)
        {
            above.push(index);
            if !open.contains_key(&place) {
                index = index.saturating_add(1);
                kept = kept.saturating_add(1);
            }
        }
        above.reverse();
        // Each binder, innermost first, as the written binder it reads: a copy
        // the binder it stands for, which may be a copy of its own.
        let mut entries = Vec::with_capacity(usize::from(typing.depth));
        for place in (0 .. usize::from(typing.depth))
            .rev()
            .map(BinderDepth::from)
        {
            let mut read = place;
            while let Some(&stands_for) = open.get(&read) {
                read = stands_for;
            }
            let index = above.get(usize::from(read)).copied().unwrap_or_default();
            entries.push(arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(index)));
        }
        let ty = match typing.ty {
            TypeNode::Value(ty) => TypeNode::Value(
                gandr_core_term::substitute_environment_value_type(arena, ty, &entries),
            ),
            TypeNode::Computation(ty) => TypeNode::Computation(
                gandr_core_term::substitute_environment_comp_type(arena, ty, &entries),
            ),
        };
        Typing {
            term,
            ty,
            depth: BinderDepth::from(kept),
        }
    }

    /// Forget every record and every open copy.
    ///
    /// # Specification
    /// - ensures: `self` records nothing.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the witness's typed run follows two verdict runs and
    ///   reads no record of theirs.
    /// - witness: `tests::native_formers::a_refined_arm_types_its_written_terms_in_their_own_context_3483`
    #[spec(ensures: self.values.is_empty() && self.computations.is_empty() && self.generalising.is_empty() && self.standing.is_empty())]
    pub fn clear(&mut self)
    {
        *self = Self::default();
    }
}

/// Which side of an index equation the solved variable stands on.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Side
{
    /// The scrutinee's index, the equation's right side.
    Scrutinee,
    /// The constructor's stated index, the equation's left side.
    Stated,
}

/// Whether a node names a binder.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Reading
{
    /// The node names the binder.
    Reads,
    /// The node names it nowhere.
    Ignores,
}

/// A binder of a context, by its place, replaced by a value.
#[derive(Clone, Copy, Debug)]
struct Replaced
{
    /// The binder's place: the depth of the context before it.
    place: BinderDepth,
    /// The value standing for it, read at the depth the substitution targets.
    by: ValueId,
}

/// An arm's problem at one step: its context's binders, its body and goal
/// under them, and the equations still unsolved.
#[derive(Clone, Debug)]
struct Problem
{
    /// Each binder's type, read in the context before it, outermost first.
    binders: Vec<ValueTypeId>,
    /// The body, read under every binder.
    body: ComputationId,
    /// The goal, read under every binder.
    goal: CompTypeId,
    /// The places of the equations still unsolved, ascending.
    equations: Vec<BinderDepth>,
}

/// One solved equation, as the refined term writes it.
#[derive(Clone, Debug)]
struct Solved
{
    /// The depth of the context the step was taken in.
    depth: BinderDepth,
    /// The side the variable stood on.
    side: Side,
    /// The equation's place.
    equation: BinderDepth,
    /// The variable's place.
    variable: BinderDepth,
    /// The equation's carrier, read in the context before the equation.
    carrier: ValueTypeId,
    /// The transport's motive, under one binder past the step's base.
    motive: ValueTypeId,
    /// The places of the binders the thunk abstracts, ascending.
    generalised: Vec<BinderDepth>,
}

/// The arm `arm` of an indexed family's case, refined by the index equations
/// it binds, checked at `expected`.
///
/// # Specification
/// - requires: `arm` is a case's branch over `fields` fields and `equations`
///   index equations, read under the binders open now; `expected` is its branch
///   type.
/// - ensures: the refined arm when some equation has a variable side free
///   nowhere in the other side, the body does not name the equation, and the
///   goal or a binder the body reads names the variable. The refined arm binds
///   what `arm` binds. Its body transports a thunk of the body, the variable
///   replaced by the other side, along the equation, and applies it to the
///   binders it abstracts. The step repeats for the equations left. The refined
///   arm carries each written lambda to its copy, and names each lambda of a
///   thunk beside the binder it stands for. [`unrefined::Absent::Unsolved`]
///   when no equation qualifies, and [`unrefined::Absent::Unshaped`] for a
///   family indexed by nothing or an arm or a type of another form.
/// - fails: [`CheckRefusal::DanglingNode`] for a node the arena does not hold,
///   and [`CheckRefusal::MachineInvariant`] for a binder count past any index.
/// - panics: none.
///
/// # Errors
/// As `- fails:`.
///
/// # Adequacy
/// - hypothesis: L3 — an arm whose goal reads the scrutinee's index and an arm
///   that reads a binder at the index separate the goal's substitution from the
///   binder's generalisation; each refined arm checks in both checkers.
/// - witness: `tests::native_formers::an_arm_is_refined_by_its_index_equation_in_both_checkers_3483`
#[spec(ensures: |ret| ret.as_ref().map_or(true, |found| match *found {
    | Maybe::Present(ref refined) => refined.term != arm && matches!(context.arena().computation(refined.term), Some(&Computation::Lambda(_))),
    | Maybe::Absent(_) => true,
}))]
pub fn refined_arm(
    context: &mut CheckingContext<'_>,
    arm: ComputationId,
    expected: CompTypeId,
    (fields, equations): (BinderDepth, BinderDepth),
) -> Result<Maybe<Refined, unrefined::Absent>, CheckRefusal>
{
    let (fields, equations) = (usize::from(fields), usize::from(equations));
    if equations == 0 {
        return Ok(Maybe::Absent(unrefined::Absent::Unshaped));
    }
    let count = fields
        .checked_add(equations)
        .ok_or(CheckRefusal::MachineInvariant)?;
    let (mut body, mut written) = (arm, Vec::with_capacity(count));
    for _ in 0 .. count {
        let Some(&Computation::Lambda(inner)) = context.arena().computation(body)
        else {
            return Ok(Maybe::Absent(unrefined::Absent::Unshaped));
        };
        written.push(body);
        body = inner;
    }
    let mut binders = open_binders(context)?;
    let open = binders.len();
    let mut goal = expected;
    for _ in 0 .. count {
        let (domain, codomain) = match context.arena().comp_type(goal) {
            Some(&CompType::Pi { domain, codomain }) => (domain, codomain),
            Some(&CompType::Arrow { domain, codomain }) => (
                domain,
                gandr_core_term::shift_comp_type(context.arena_mut(), codomain, Binders::ONE)
                    .settle(context.arena_mut()),
            ),
            Some(_) => return Ok(Maybe::Absent(unrefined::Absent::Unshaped)),
            None => {
                return Err(CheckRefusal::DanglingNode {
                    node: CoreNode::Type(TypeNode::Computation(goal)),
                });
            },
        };
        binders.push(domain);
        goal = codomain;
    }
    let first = open
        .checked_add(fields)
        .ok_or(CheckRefusal::MachineInvariant)?;
    let mut problem = Problem {
        binders,
        body,
        goal,
        equations: (first .. first.saturating_add(equations))
            .map(BinderDepth::from)
            .collect(),
    };
    let (mut steps, mut carried) = (Vec::new(), Vec::new());
    while let Maybe::Present((solved, next)) = step(context.arena_mut(), &problem, &mut carried)? {
        steps.push(solved);
        problem = next;
    }
    if steps.is_empty() {
        return Ok(Maybe::Absent(unrefined::Absent::Unsolved));
    }
    let (mut refined, mut generalising) = (problem.body, Vec::new());
    for solved in steps.iter().rev() {
        refined = wrapped(context.arena_mut(), solved, refined, &mut generalising)?;
    }
    for &lambda in written.iter().rev() {
        refined = context.arena_mut().computation_lambda(refined);
        carried.push(Carried::Computation(lambda, refined));
    }
    Ok(Maybe::Present(Refined {
        term: refined,
        carried,
        generalising,
    }))
}

/// The case `case` on a variable, its motive generalised over the binders
/// after the variable that its arms read and whose types read the variable.
///
/// # Specification
/// - requires: `case` is read under the binders open now.
/// - ensures: when `case` is a case on a variable and an arm reads a binder
///   after it whose type reads it, the case at the motive `λs. Π (d′ : D[x :=
///   s]). M(s)`, each arm abstracting `d′` past its fields and equations and
///   reading it for `D`, applied to `D`. The refined case carries each arm's
///   written lambda to its copy, and names each lambda that binds `d′` beside
///   the binder it stands for. [`unrefined::Absent::Unsolved`] when no arm
///   reads such a binder, and [`unrefined::Absent::Unshaped`] for any other
///   term, a scrutinee that is no variable an open binder holds, or an arm of
///   another form.
/// - fails: [`CheckRefusal::DanglingNode`] for a node the arena does not hold,
///   and [`CheckRefusal::MachineInvariant`] for a binder count past any index.
/// - panics: none.
///
/// # Errors
/// As `- fails:`.
///
/// # Adequacy
/// - hypothesis: L3 — a case on a code whose arm returns a binder typed at the
///   code's decode separates the generalised binder from the scrutinee's
///   refinement; the refined case checks in both checkers.
/// - witness: `tests::native_formers::a_binder_after_the_scrutinee_is_read_at_each_arm_in_both_checkers_3483`
#[spec(ensures: |ret| ret.as_ref().map_or(true, |found| match *found {
    | Maybe::Present(ref refined) => refined.term != case,
    | Maybe::Absent(_) => true,
}))]
pub fn refined_case(
    context: &mut CheckingContext<'_>,
    case: ComputationId,
) -> Result<Maybe<Refined, unrefined::Absent>, CheckRefusal>
{
    let Some(&Computation::DataCase {
        scrutinee,
        motive,
        ref branches,
        ref arities,
        equations,
    }) = context.arena().computation(case)
    else {
        return Ok(Maybe::Absent(unrefined::Absent::Unshaped));
    };
    let (branches, arities) = (branches.clone(), arities.clone());
    let Some(&Value::Variable {
        zone: Zone::Intuitionistic,
        index,
    }) = context.arena().value(scrutinee)
    else {
        return Ok(Maybe::Absent(unrefined::Absent::Unshaped));
    };
    // A loop arm stands past the constructors' arities and binds no fields.
    if branches.len() != arities.len() {
        return Ok(Maybe::Absent(unrefined::Absent::Unshaped));
    }
    let binders = open_binders(context)?;
    let depth = BinderDepth::from(binders.len());
    // A variable no open binder holds is the case rule's to refuse.
    if usize::try_from(u32::from(index)).map_or(true, |index| index >= binders.len()) {
        return Ok(Maybe::Absent(unrefined::Absent::Unshaped));
    }
    let variable = place_of(depth, index)?;
    let arena = context.arena_mut();
    let mut seeds = Vec::with_capacity(binders.len());
    for place in 0 .. binders.len() {
        let mut read = Reading::Ignores;
        if place > usize::from(variable) {
            let at = index_at(depth, BinderDepth::from(place))?;
            for &branch in &branches {
                if reads(arena, CoreNode::Term(TermNode::Computation(branch)), at)?
                    == Reading::Reads
                {
                    read = Reading::Reads;
                }
            }
        }
        seeds.push(read);
    }
    let generalised = generalised(arena, &binders, variable, seeds)?;
    if generalised.is_empty() || staging(arena, &binders, &generalised)? == Staging::Staged {
        return Ok(Maybe::Absent(unrefined::Absent::Unsolved));
    }
    let count = generalised.len();
    let open = usize::from(depth);
    let scrutinised = BinderDepth::from(open);
    let beneath = depth_past(scrutinised, 1)?;
    // `M(s)` read past the abstracted binders, each read as its own.
    let inner = depth_past(beneath, count)?;
    let mut replaced = Vec::with_capacity(count.saturating_add(1));
    replaced.push(Replaced {
        place: scrutinised,
        by: variable_at(arena, inner, scrutinised)?,
    });
    for (position, &place) in generalised.iter().enumerate() {
        let at = depth_past(beneath, position)?;
        replaced.push(Replaced {
            place,
            by: variable_at(arena, inner, at)?,
        });
    }
    let mut generalised_motive = carried_comp_type(arena, motive, (beneath, inner), &replaced)?;
    for (position, &place) in generalised.iter().enumerate().rev() {
        let at = depth_past(beneath, position)?;
        let domain = abstracted(
            arena,
            &binders,
            (place, at),
            (variable, scrutinised),
            &generalised,
        )?;
        generalised_motive = arena.comp_type_pi(domain, generalised_motive);
    }
    let (mut arms, mut carried) = (Vec::with_capacity(branches.len()), Vec::new());
    let mut generalising = Vec::with_capacity(count.saturating_mul(branches.len()));
    let (mut written, mut renamed) = (Vec::new(), Vec::with_capacity(count));
    for (&branch, &arity) in branches.iter().zip(&arities) {
        let bound = usize::from(arity)
            .checked_add(usize::from(equations))
            .ok_or(CheckRefusal::MachineInvariant)?;
        let mut body = branch;
        written.clear();
        for _ in 0 .. bound {
            let Some(&Computation::Lambda(inner_body)) = arena.computation(body)
            else {
                return Ok(Maybe::Absent(unrefined::Absent::Unshaped));
            };
            written.push(body);
            body = inner_body;
        }
        let under = depth_past(depth, bound)?;
        let past = depth_past(under, count)?;
        renamed.clear();
        for (position, &place) in generalised.iter().enumerate() {
            renamed.push(Replaced {
                place,
                by: variable_at(arena, past, depth_past(under, position)?)?,
            });
        }
        let mut arm = carried_computation(arena, body, (under, past), &renamed, &mut carried)?;
        for &place in generalised.iter().rev() {
            arm = arena.computation_lambda(arm);
            generalising.push((arm, place));
        }
        for &lambda in written.iter().rev() {
            arm = arena.computation_lambda(arm);
            carried.push(Carried::Computation(lambda, arm));
        }
        arms.push(arm);
    }
    let mut refined = arena.computation_data_case_with_equations(
        scrutinee,
        generalised_motive,
        (arms, arities),
        equations,
    );
    for &place in &generalised {
        let argument = variable_at(arena, depth, place)?;
        refined = arena.computation_application(refined, argument);
    }
    Ok(Maybe::Present(Refined {
        term: refined,
        carried,
        generalising,
    }))
}

/// The types of the intuitionistic binders open now, outermost first, each
/// read in the context before it.
///
/// # Specification
/// - ensures: one type per open binder.
/// - fails: [`CheckRefusal::MachineInvariant`] for a binder the context does
///   not hold.
/// - panics: none.
///
/// # Errors
/// As `- fails:`.
///
/// # Adequacy
/// - hypothesis: L3 — a case on a variable reads each later binder's type from
///   the binders open now.
/// - witness: `tests::native_formers::a_binder_after_the_scrutinee_is_read_at_each_arm_in_both_checkers_3483`
#[spec(ensures: |ret| ret.as_ref().map_or(true, |found| found.len() == usize::from(context.depth(Zone::Intuitionistic))))]
fn open_binders(context: &CheckingContext<'_>) -> Result<Vec<ValueTypeId>, CheckRefusal>
{
    let depth = context.depth(Zone::Intuitionistic);
    let mut binders = Vec::with_capacity(usize::from(depth));
    for place in 0 .. usize::from(depth) {
        let index = index_at(depth, BinderDepth::from(place))?;
        binders.push(context.hypothesis(index)?);
    }
    Ok(binders)
}

/// One step of `problem`: the first equation it solves and the problem left
/// inside the thunk.
///
/// # Specification
/// - requires: `problem`'s binders, body and goal are scoped as its fields
///   state.
/// - ensures: the first unsolved equation whose right side, else left side, is
///   a variable free nowhere in the other side, which the body does not name,
///   and whose variable the goal or an abstracted binder needs, solved; the
///   problem inside the thunk past it. [`unrefined::Absent::Unsolved`] when no
///   equation qualifies.
/// - fails: as [`refined_arm`].
/// - panics: none.
///
/// # Errors
/// As `- fails:`.
///
/// # Adequacy
/// - hypothesis: L3 — an arm whose goal reads the scrutinee's index and an arm
///   that reads a binder at that index each take one step.
/// - witness: `tests::native_formers::an_arm_is_refined_by_its_index_equation_in_both_checkers_3483`
#[spec(ensures: |ret| ret.as_ref().map_or(true, |found| match *found {
    | Maybe::Present((ref solved, _)) => problem.equations.contains(&solved.equation) && solved.variable < solved.equation,
    | Maybe::Absent(reason) => reason == unrefined::Absent::Unsolved,
}))]
fn step(
    arena: &mut CoreArena,
    problem: &Problem,
    carried: &mut Vec<Carried>,
) -> Result<Maybe<(Solved, Problem), unrefined::Absent>, CheckRefusal>
{
    let depth = BinderDepth::from(problem.binders.len());
    let body = CoreNode::Term(TermNode::Computation(problem.body));
    let goal = CoreNode::Type(TypeNode::Computation(problem.goal));
    for &equation in &problem.equations {
        if reads(arena, body, index_at(depth, equation)?)? == Reading::Reads {
            continue;
        }
        let &ty = problem
            .binders
            .get(usize::from(equation))
            .ok_or(CheckRefusal::MachineInvariant)?;
        let Maybe::Present(Solution {
            side,
            variable,
            other: solution,
            carrier,
        }) = solvable(arena, ty, equation)?
        else {
            continue;
        };
        let mut seeds = Vec::with_capacity(problem.binders.len());
        for place in 0 .. problem.binders.len() {
            let mut read = Reading::Ignores;
            if place > usize::from(variable) {
                let at = index_at(depth, BinderDepth::from(place))?;
                if reads(arena, body, at)? == Reading::Reads
                    || reads(arena, goal, at)? == Reading::Reads
                {
                    read = Reading::Reads;
                }
            }
            seeds.push(read);
        }
        let mut generalised = generalised(arena, &problem.binders, variable, seeds)?;
        // The equation is the path transported along, never abstracted; a
        // problem that needs it is left to another step.
        if generalised.contains(&equation) {
            continue;
        }
        if generalised.is_empty()
            && reads(arena, goal, index_at(depth, variable)?)? == Reading::Ignores
        {
            continue;
        }
        if reads_any(arena, &problem.binders, &generalised, equation)? == Reading::Reads {
            continue;
        }
        // A stage is the kernel's own: no motive it forms names one.
        if staging(arena, &problem.binders, &generalised)? == Staging::Staged {
            continue;
        }
        generalised.sort_unstable();
        let base = match side {
            Side::Scrutinee => depth,
            Side::Stated => depth_past(depth, 1)?,
        };
        let solved = Solved {
            depth,
            side,
            equation,
            variable,
            carrier,
            motive: motive(arena, problem, (base, variable), &generalised)?,
            generalised,
        };
        let next = inside(arena, problem, &solved, (solution, equation), carried)?;
        return Ok(Maybe::Present((solved, next)));
    }
    Ok(Maybe::Absent(unrefined::Absent::Unsolved))
}

/// An index equation read as a solution.
#[derive(Clone, Copy, Debug)]
struct Solution
{
    /// The side the variable stands on.
    side: Side,
    /// The variable's place.
    variable: BinderDepth,
    /// The other side, read in the context before the equation.
    other: ValueId,
    /// The equation's carrier, read in the context before the equation.
    carrier: ValueTypeId,
}

/// The equation typed `ty` at `equation`, read as a solution.
///
/// # Specification
/// - ensures: the right side when it is a variable free nowhere in the left,
///   else the left side under the same condition;
///   [`unrefined::Absent::Unsolved`] for a type that is no path or a path with
///   no such side.
/// - fails: [`CheckRefusal::DanglingNode`] for a node the arena does not hold.
/// - panics: none.
///
/// # Errors
/// As `- fails:`.
///
/// # Adequacy
/// - hypothesis: L3 — an equation from a constructor's index to a variable
///   solves at the variable.
/// - witness: `tests::native_formers::an_arm_is_refined_by_its_index_equation_in_both_checkers_3483`
#[spec(ensures: |ret| ret.as_ref().map_or(true, |found| match *found {
    | Maybe::Present(solution) => solution.variable < equation,
    | Maybe::Absent(reason) => reason == unrefined::Absent::Unsolved,
}))]
fn solvable(
    arena: &CoreArena,
    ty: ValueTypeId,
    equation: BinderDepth,
) -> Result<Maybe<Solution, unrefined::Absent>, CheckRefusal>
{
    let Some(&ValueType::Path {
        carrier,
        left,
        right,
    }) = arena.value_type(ty)
    else {
        return Ok(Maybe::Absent(unrefined::Absent::Unsolved));
    };
    for (side, variable, other) in [(Side::Scrutinee, right, left), (Side::Stated, left, right)] {
        let Some(&Value::Variable {
            zone: Zone::Intuitionistic,
            index,
        }) = arena.value(variable)
        else {
            continue;
        };
        if reads(arena, CoreNode::Term(TermNode::Value(other)), index)? == Reading::Reads {
            continue;
        }
        return Ok(Maybe::Present(Solution {
            side,
            variable: place_of(equation, index)?,
            other,
            carrier,
        }));
    }
    Ok(Maybe::Absent(unrefined::Absent::Unsolved))
}

/// The places after `variable` whose types read it, at one remove or more,
/// and that `seeds` marks or a marked binder's type reads, ascending.
///
/// # Specification
/// - requires: `seeds` holds one reading per binder of `binders`.
/// - ensures: every place past `variable` whose type reads `variable` or such a
///   place, and that is marked or read by the type of a place in the result.
/// - fails: as [`reads`].
/// - panics: none.
///
/// # Errors
/// As `- fails:`.
///
/// # Adequacy
/// - hypothesis: L3 — a binder at the index that the arm reads is generalised,
///   and an arm that reads none generalises nothing.
/// - witness: `tests::native_formers::an_arm_is_refined_by_its_index_equation_in_both_checkers_3483`
/// - witness: `tests::native_formers::a_binder_after_the_scrutinee_is_read_at_each_arm_in_both_checkers_3483`
#[spec(ensures: |ret| ret.as_ref().map_or(true, |found| found.iter().all(|&place| place > variable)))]
fn generalised(
    arena: &CoreArena,
    binders: &[ValueTypeId],
    variable: BinderDepth,
    mut needed: Vec<Reading>,
) -> Result<Vec<BinderDepth>, CheckRefusal>
{
    let first = usize::from(variable).saturating_add(1);
    let mut depends = Vec::with_capacity(binders.len());
    for (place, &ty) in binders.iter().enumerate() {
        let mut reading = Reading::Ignores;
        if place >= first {
            let node = CoreNode::Type(TypeNode::Value(ty));
            let here = BinderDepth::from(place);
            if reads(arena, node, index_at(here, variable)?)? == Reading::Reads {
                reading = Reading::Reads;
            }
            for earlier in first .. place {
                if depends.get(earlier) == Some(&Reading::Reads)
                    && reads(arena, node, index_at(here, BinderDepth::from(earlier))?)?
                        == Reading::Reads
                {
                    reading = Reading::Reads;
                }
            }
        }
        depends.push(reading);
    }
    for place in (first .. binders.len()).rev() {
        if needed.get(place) != Some(&Reading::Reads) {
            continue;
        }
        let &ty = binders.get(place).ok_or(CheckRefusal::MachineInvariant)?;
        let node = CoreNode::Type(TypeNode::Value(ty));
        for earlier in first .. place {
            if reads(
                arena,
                node,
                index_at(BinderDepth::from(place), BinderDepth::from(earlier))?,
            )? == Reading::Reads
                && let Some(slot) = needed.get_mut(earlier)
            {
                *slot = Reading::Reads;
            }
        }
    }
    Ok((first .. binders.len())
        .filter(|&place| {
            depends.get(place) == Some(&Reading::Reads)
                && needed.get(place) == Some(&Reading::Reads)
        })
        .map(BinderDepth::from)
        .collect())
}

/// Whether the type of a binder at one of `places` names the binder at
/// `target`.
///
/// # Specification
/// - ensures: [`Reading::Reads`] exactly when one such type past `target` names
///   it.
/// - fails: as [`reads`].
/// - panics: none.
///
/// # Errors
/// As `- fails:`.
///
/// # Adequacy
/// - hypothesis: L3 — as [`step`].
/// - witness: `tests::native_formers::an_arm_is_refined_by_its_index_equation_in_both_checkers_3483`
#[spec(ensures: |ret| places.iter().any(|&place| place > target) || ret == Ok(Reading::Ignores))]
fn reads_any(
    arena: &CoreArena,
    binders: &[ValueTypeId],
    places: &[BinderDepth],
    target: BinderDepth,
) -> Result<Reading, CheckRefusal>
{
    for &place in places {
        if place <= target {
            continue;
        }
        let &ty = binders
            .get(usize::from(place))
            .ok_or(CheckRefusal::MachineInvariant)?;
        if reads(
            arena,
            CoreNode::Type(TypeNode::Value(ty)),
            index_at(place, target)?,
        )? == Reading::Reads
        {
            return Ok(Reading::Reads);
        }
    }
    Ok(Reading::Ignores)
}

/// The transport's motive for the step at `variable` taken from `base`: the
/// thunk of `Π (d′ : D[x := y]). G[x := y]`, read under the binder `y` past
/// `base`.
///
/// # Specification
/// - requires: `generalised` holds ascending places past `variable`.
/// - ensures: a thunk type under one binder past `base`.
/// - fails: as [`refined_arm`].
/// - panics: none.
///
/// # Errors
/// As `- fails:`.
///
/// # Adequacy
/// - hypothesis: L3 — the motive types the thunk at both ends of the equation,
///   and the kernel admits the transport.
/// - witness: `tests::native_formers::an_arm_is_refined_by_its_index_equation_in_both_checkers_3483`
#[spec(ensures: |ret| ret.as_ref().map_or(true, |&ty| matches!(arena.value_type(ty), Some(&ValueType::Thunk(_)))))]
fn motive(
    arena: &mut CoreArena,
    problem: &Problem,
    (base, variable): (BinderDepth, BinderDepth),
    generalised: &[BinderDepth],
) -> Result<ValueTypeId, CheckRefusal>
{
    let depth = BinderDepth::from(problem.binders.len());
    let beneath = depth_past(base, 1)?;
    let inner = depth_past(beneath, generalised.len())?;
    let mut replaced = Vec::with_capacity(generalised.len().saturating_add(1));
    replaced.push(Replaced {
        place: variable,
        by: variable_at(arena, inner, base)?,
    });
    for (position, &place) in generalised.iter().enumerate() {
        replaced.push(Replaced {
            place,
            by: variable_at(arena, inner, depth_past(beneath, position)?)?,
        });
    }
    let mut body = carried_comp_type(arena, problem.goal, (depth, inner), &replaced)?;
    for (position, &place) in generalised.iter().enumerate().rev() {
        let at = depth_past(beneath, position)?;
        let domain = abstracted(
            arena,
            &problem.binders,
            (place, at),
            (variable, base),
            generalised,
        )?;
        body = arena.comp_type_pi(domain, body);
    }
    Ok(arena.value_type_thunk(body))
}

/// The type of the binder at `place`, read at depth `at` with `variable` read
/// as the binder at `moving` and each earlier abstracted binder as its own.
///
/// # Specification
/// - requires: `at` is past `moving`, the abstracted binders standing between.
/// - ensures: the binder's type with the substitution applied.
/// - fails: as [`refined_arm`].
/// - panics: none.
///
/// # Errors
/// As `- fails:`.
///
/// # Adequacy
/// - hypothesis: L3 — a generalised binder's type reads the moving variable in
///   a transport's motive and in a case's motive.
/// - witness: `tests::native_formers::an_arm_is_refined_by_its_index_equation_in_both_checkers_3483`
/// - witness: `tests::native_formers::a_binder_after_the_scrutinee_is_read_at_each_arm_in_both_checkers_3483`
#[spec(ensures: |ret| ret.as_ref().map_or(true, |&ty| arena.value_type(ty).is_some()))]
fn abstracted(
    arena: &mut CoreArena,
    binders: &[ValueTypeId],
    (place, at): (BinderDepth, BinderDepth),
    (variable, moving): (BinderDepth, BinderDepth),
    generalised: &[BinderDepth],
) -> Result<ValueTypeId, CheckRefusal>
{
    let &ty = binders
        .get(usize::from(place))
        .ok_or(CheckRefusal::MachineInvariant)?;
    let beneath = depth_past(moving, 1)?;
    let mut replaced = Vec::with_capacity(generalised.len().saturating_add(1));
    replaced.push(Replaced {
        place: variable,
        by: variable_at(arena, at, moving)?,
    });
    for (position, &earlier) in generalised.iter().enumerate() {
        if earlier >= place {
            break;
        }
        replaced.push(Replaced {
            place: earlier,
            by: variable_at(arena, at, depth_past(beneath, position)?)?,
        });
    }
    carried_value_type(arena, ty, (place, at), &replaced)
}

/// The problem inside the thunk of `solved`: the binders it abstracts read at
/// the solution, and the body and goal with the variable replaced by it.
///
/// # Specification
/// - requires: `solved` is a step of `problem`, `solution` read in the context
///   before `equation`.
/// - ensures: a problem whose equations are `problem`'s but the one solved and
///   those abstracted. `carried` gains each body node the rewrite changed.
/// - fails: as [`refined_arm`].
/// - panics: none.
///
/// # Errors
/// As `- fails:`.
///
/// # Adequacy
/// - hypothesis: L3 — as [`step`].
/// - witness: `tests::native_formers::an_arm_is_refined_by_its_index_equation_in_both_checkers_3483`
#[spec(ensures: |ret| ret.as_ref().map_or(true, |next| next.equations.len() < problem.equations.len()))]
fn inside(
    arena: &mut CoreArena,
    problem: &Problem,
    solved: &Solved,
    (solution, equation): (ValueId, BinderDepth),
    carried: &mut Vec<Carried>,
) -> Result<Problem, CheckRefusal>
{
    let depth = solved.depth;
    let mut binders = problem.binders.clone();
    if solved.side == Side::Stated {
        let carrier = carried_value_type(arena, solved.carrier, (equation, depth), &[])?;
        let left = carried_value(arena, solution, (equation, depth), &[])?;
        let right = variable_at(arena, depth, solved.variable)?;
        binders.push(arena.value_type_path(carrier, left, right));
    }
    let base = BinderDepth::from(binders.len());
    for (position, &place) in solved.generalised.iter().enumerate() {
        let at = depth_past(base, position)?;
        binders.push(solved_binder(
            arena,
            problem,
            solved,
            (place, at),
            (solution, equation),
        )?);
    }
    let inner = BinderDepth::from(binders.len());
    let mut replaced = Vec::with_capacity(solved.generalised.len().saturating_add(1));
    replaced.push(Replaced {
        place: solved.variable,
        by: carried_value(arena, solution, (equation, inner), &[])?,
    });
    for (position, &place) in solved.generalised.iter().enumerate() {
        replaced.push(Replaced {
            place,
            by: variable_at(arena, inner, depth_past(base, position)?)?,
        });
    }
    let body = carried_computation(arena, problem.body, (depth, inner), &replaced, carried)?;
    let goal = carried_comp_type(arena, problem.goal, (depth, inner), &replaced)?;
    let equations = problem
        .equations
        .iter()
        .copied()
        .filter(|&place| {
            place != solved.equation && solved.generalised.binary_search(&place).is_err()
        })
        .collect();
    Ok(Problem {
        binders,
        body,
        goal,
        equations,
    })
}

/// The type of the abstracted binder at `place`, read at depth `at` inside the
/// thunk: the variable replaced by the solution, each earlier abstracted
/// binder by its own.
///
/// # Specification
/// - requires: as [`inside`].
/// - ensures: the binder's type at the solution.
/// - fails: as [`refined_arm`].
/// - panics: none.
///
/// # Errors
/// As `- fails:`.
///
/// # Adequacy
/// - hypothesis: L3 — a generalised binder reads the solution inside the thunk,
///   and the arm that reads it checks.
/// - witness: `tests::native_formers::an_arm_is_refined_by_its_index_equation_in_both_checkers_3483`
#[spec(ensures: |ret| ret.as_ref().map_or(true, |&ty| arena.value_type(ty).is_some()))]
fn solved_binder(
    arena: &mut CoreArena,
    problem: &Problem,
    solved: &Solved,
    (place, at): (BinderDepth, BinderDepth),
    (solution, equation): (ValueId, BinderDepth),
) -> Result<ValueTypeId, CheckRefusal>
{
    let &ty = problem
        .binders
        .get(usize::from(place))
        .ok_or(CheckRefusal::MachineInvariant)?;
    let base = match solved.side {
        Side::Scrutinee => solved.depth,
        Side::Stated => depth_past(solved.depth, 1)?,
    };
    let mut replaced = Vec::with_capacity(solved.generalised.len().saturating_add(1));
    replaced.push(Replaced {
        place: solved.variable,
        by: carried_value(arena, solution, (equation, at), &[])?,
    });
    for (position, &earlier) in solved.generalised.iter().enumerate() {
        if earlier >= place {
            break;
        }
        replaced.push(Replaced {
            place: earlier,
            by: variable_at(arena, at, depth_past(base, position)?)?,
        });
    }
    carried_value_type(arena, ty, (place, at), &replaced)
}

/// The refinement `solved` writes around `inner`, the body inside its thunk:
/// the transport of the thunk along the equation, forced and applied to the
/// binders it abstracts, read at the step's depth.
///
/// # Specification
/// - requires: `inner` is read inside the thunk of `solved`.
/// - ensures: a bind of the transport, past the reversal of the equation when
///   the variable stood on the stated side. Each lambda of the thunk joins
///   `generalising` beside the place of the binder it stands for.
/// - fails: as [`refined_arm`].
/// - panics: none.
///
/// # Errors
/// As `- fails:`.
///
/// # Adequacy
/// - hypothesis: L3 — the transported thunk, applied to the binders it
///   abstracts, checks in both checkers.
/// - witness: `tests::native_formers::an_arm_is_refined_by_its_index_equation_in_both_checkers_3483`
#[spec(
    captures: before = generalising.len(),
    ensures: |ret| ret.as_ref().map_or(true, |&refined| matches!(arena.computation(refined), Some(&Computation::Bind(..)))
        && generalising.len() == before.saturating_add(solved.generalised.len())),
)]
fn wrapped(
    arena: &mut CoreArena,
    solved: &Solved,
    inner: ComputationId,
    generalising: &mut Vec<(ComputationId, BinderDepth)>,
) -> Result<ComputationId, CheckRefusal>
{
    let depth = solved.depth;
    let (base, path) = match solved.side {
        Side::Scrutinee => (depth, variable_at(arena, depth, solved.equation)?),
        Side::Stated => {
            let base = depth_past(depth, 1)?;
            (base, variable_at(arena, base, depth)?)
        },
    };
    let mut abstraction = inner;
    for &place in solved.generalised.iter().rev() {
        abstraction = arena.computation_lambda(abstraction);
        generalising.push((abstraction, place));
    }
    let thunk = arena.value_thunk(abstraction);
    let transport = arena.computation_path_transport(solved.motive, path, thunk);
    let beneath = depth_past(base, 1)?;
    let transported = variable_at(arena, beneath, base)?;
    let mut applied = arena.computation_force(transported);
    for &place in &solved.generalised {
        let argument = variable_at(arena, beneath, place)?;
        applied = arena.computation_application(applied, argument);
    }
    let mut refined = arena.computation_bind(transport, applied);
    if solved.side == Side::Stated {
        // `e : Path(I, x, s)` reversed: `here(x)` carried along `e` in the
        // family `λz. Path(I, z, x)`.
        let past = depth_past(depth, 1)?;
        let carrier = carried_value_type(arena, solved.carrier, (solved.equation, past), &[])?;
        let moving = variable_at(arena, past, depth)?;
        let fixed = variable_at(arena, past, solved.variable)?;
        let family = arena.value_type_path(carrier, moving, fixed);
        let point = variable_at(arena, depth, solved.variable)?;
        let reflexivity = arena.value_here(point);
        let equation = variable_at(arena, depth, solved.equation)?;
        let reversed = arena.computation_path_transport(family, equation, reflexivity);
        refined = arena.computation_bind(reversed, refined);
    }
    Ok(refined)
}

/// Whether a binder's type is a stage of a recursion.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Staging
{
    /// The type is `ValueType::Staged`: admission alone mints it.
    Staged,
    /// The type carries no stage.
    Unstaged,
}

/// Whether the type of a binder at one of `places` is a stage of a
/// recursion.
///
/// # Specification
/// - ensures: [`Staging::Staged`] exactly when one such type is
///   `ValueType::Staged`.
/// - fails: [`CheckRefusal::MachineInvariant`] for a place past `binders`, and
///   [`CheckRefusal::DanglingNode`] for a type the arena does not hold.
/// - panics: none.
///
/// # Errors
/// As `- fails:`.
///
/// # Adequacy
/// - hypothesis: L2 — the witness reads the unstaged answer alone. The corpus's
///   `zip` reads the staged answer, outside the crate.
/// - witness: `tests::native_formers::an_arm_is_refined_by_its_index_equation_in_both_checkers_3483`
#[spec(ensures: |ret| !places.is_empty() || ret == Ok(Staging::Unstaged))]
fn staging(
    arena: &CoreArena,
    binders: &[ValueTypeId],
    places: &[BinderDepth],
) -> Result<Staging, CheckRefusal>
{
    for &place in places {
        let &ty = binders
            .get(usize::from(place))
            .ok_or(CheckRefusal::MachineInvariant)?;
        let Some(found) = arena.value_type(ty)
        else {
            return Err(CheckRefusal::DanglingNode {
                node: CoreNode::Type(TypeNode::Value(ty)),
            });
        };
        if matches!(*found, ValueType::Staged { .. }) {
            return Ok(Staging::Staged);
        }
    }
    Ok(Staging::Unstaged)
}

/// Whether `node` names the intuitionistic binder `index` binders out.
///
/// # Specification
/// - ensures: [`Reading::Reads`] exactly when `index` is in the node's support.
/// - fails: [`CheckRefusal::DanglingNode`] for a node the arena does not hold.
/// - panics: none.
/// - executable: none — the verdict is the support's own rank, which a
///   predicate would read again.
///
/// # Errors
/// As `- fails:`.
///
/// # Adequacy
/// - hypothesis: L3 — as [`generalised`].
/// - witness: `tests::native_formers::a_binder_after_the_scrutinee_is_read_at_each_arm_in_both_checkers_3483`
fn reads(
    arena: &CoreArena,
    node: CoreNode,
    index: DeBruijnIndex,
) -> Result<Reading, CheckRefusal>
{
    let support = match node {
        CoreNode::Term(TermNode::Value(id)) => arena.value_support(id),
        CoreNode::Term(TermNode::Computation(id)) => arena.computation_support(id),
        CoreNode::Type(TypeNode::Value(id)) => arena.value_type_support(id),
        CoreNode::Type(TypeNode::Computation(id)) => arena.comp_type_support(id),
    }
    .ok_or(CheckRefusal::DanglingNode { node })?;
    Ok(match support.rank(Zone::Intuitionistic, index) {
        Maybe::Present(_) => Reading::Reads,
        Maybe::Absent(_) => Reading::Ignores,
    })
}

/// The index, at depth `depth`, of the binder at `place`.
///
/// # Specification
/// - ensures: `depth - 1 - place`.
/// - fails: [`CheckRefusal::MachineInvariant`] for a place at or past `depth`
///   or an index past any binder count.
/// - panics: none.
///
/// # Errors
/// As `- fails:`.
///
/// # Adequacy
/// - hypothesis: L3 — as [`refined_arm`]: each refined term the witness checks
///   is read through it.
/// - witness: `tests::native_formers::an_arm_is_refined_by_its_index_equation_in_both_checkers_3483`
#[spec(ensures: |ret| ret.is_ok() == (place < depth))]
fn index_at(
    depth: BinderDepth,
    place: BinderDepth,
) -> Result<DeBruijnIndex, CheckRefusal>
{
    usize::from(depth)
        .checked_sub(usize::from(place))
        .and_then(|distance| distance.checked_sub(1))
        .and_then(|index| u32::try_from(index).ok())
        .map(DeBruijnIndex::from)
        .ok_or(CheckRefusal::MachineInvariant)
}

/// The place of the binder `index` binders out at depth `depth`.
///
/// # Specification
/// - ensures: `depth - 1 - index`.
/// - fails: [`CheckRefusal::MachineInvariant`] for an index at or past `depth`.
/// - panics: none.
///
/// # Errors
/// As `- fails:`.
///
/// # Adequacy
/// - hypothesis: L3 — as [`refined_case`]: each refined case the witness checks
///   is read through it.
/// - witness: `tests::native_formers::a_binder_after_the_scrutinee_is_read_at_each_arm_in_both_checkers_3483`
#[spec(ensures: |ret| ret.as_ref().map_or(true, |&place| place < depth))]
fn place_of(
    depth: BinderDepth,
    index: DeBruijnIndex,
) -> Result<BinderDepth, CheckRefusal>
{
    usize::try_from(u32::from(index))
        .ok()
        .and_then(|index| usize::from(depth).checked_sub(index))
        .and_then(|distance| distance.checked_sub(1))
        .map(BinderDepth::from)
        .ok_or(CheckRefusal::MachineInvariant)
}

/// The depth `count` binders past `depth`.
///
/// # Specification
/// - ensures: `depth + count`.
/// - fails: [`CheckRefusal::MachineInvariant`] past any binder count.
/// - panics: none.
///
/// # Errors
/// As `- fails:`.
///
/// # Adequacy
/// - hypothesis: L3 — as [`refined_arm`]: each refined term the witness checks
///   is read through it.
/// - witness: `tests::native_formers::an_arm_is_refined_by_its_index_equation_in_both_checkers_3483`
#[spec(ensures: |ret| ret.as_ref().map_or(true, |&past| past >= depth))]
fn depth_past(
    depth: BinderDepth,
    count: impl Into<Count>,
) -> Result<BinderDepth, CheckRefusal>
{
    usize::from(depth)
        .checked_add(count.into().0)
        .map(BinderDepth::from)
        .ok_or(CheckRefusal::MachineInvariant)
}

/// A count of binders.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[repr(transparent)]
struct Count(usize);

impl From<usize> for Count
{
    /// Wraps a raw count of binders.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(count: usize) -> Self
    {
        Self(count)
    }
}

/// The variable naming, at depth `depth`, the binder at `place`.
///
/// # Specification
/// - ensures: an intuitionistic variable at [`index_at`]'s index.
/// - fails: as [`index_at`].
/// - panics: none.
///
/// # Errors
/// As `- fails:`.
///
/// # Adequacy
/// - hypothesis: L3 — as [`refined_arm`]: each refined term the witness checks
///   is read through it.
/// - witness: `tests::native_formers::an_arm_is_refined_by_its_index_equation_in_both_checkers_3483`
#[spec(ensures: |ret| ret.as_ref().map_or(true, |&id| matches!(arena.value(id), Some(&Value::Variable { zone: Zone::Intuitionistic, .. }))))]
fn variable_at(
    arena: &mut CoreArena,
    depth: BinderDepth,
    place: BinderDepth,
) -> Result<ValueId, CheckRefusal>
{
    Ok(arena.value_variable(Zone::Intuitionistic, index_at(depth, place)?))
}

/// The environment that reads a node scoped at depth `from` at depth `to`:
/// each binder `replaced` names by its value, every other by itself.
///
/// # Specification
/// - requires: every value of `replaced` is read at `to`.
/// - ensures: one entry per binder of the context at depth `from`, innermost
///   first.
/// - fails: [`CheckRefusal::MachineInvariant`] for a binder kept as itself that
///   has no index at `to`.
/// - panics: none.
///
/// # Errors
/// As `- fails:`.
///
/// # Adequacy
/// - hypothesis: L3 — as [`refined_arm`]: each refined term the witnesses check
///   is read through it.
/// - witness: `tests::native_formers::an_arm_is_refined_by_its_index_equation_in_both_checkers_3483`
/// - witness: `tests::native_formers::a_binder_after_the_scrutinee_is_read_at_each_arm_in_both_checkers_3483`
#[spec(ensures: |ret| ret.as_ref().map_or(true, |entries| entries.len() == usize::from(from)))]
fn environment(
    arena: &mut CoreArena,
    (from, to): (BinderDepth, BinderDepth),
    replaced: &[Replaced],
) -> Result<Vec<ValueId>, CheckRefusal>
{
    let mut by = BTreeMap::new();
    for replacement in replaced {
        let _first = by.entry(replacement.place).or_insert(replacement.by);
    }
    let mut entries = Vec::with_capacity(usize::from(from));
    for index in 0 .. usize::from(from) {
        let place = usize::from(from)
            .checked_sub(index)
            .and_then(|distance| distance.checked_sub(1))
            .map(BinderDepth::from)
            .ok_or(CheckRefusal::MachineInvariant)?;
        let entry = match by.get(&place) {
            Some(&value) => value,
            None => variable_at(arena, to, place)?,
        };
        entries.push(entry);
    }
    Ok(entries)
}

/// `subject`, scoped at the first depth, read at the second through
/// [`environment`].
///
/// # Specification
/// - requires: as [`environment`].
/// - ensures: the substituted value.
/// - fails: as [`environment`].
/// - panics: none.
///
/// # Errors
/// As `- fails:`.
///
/// # Adequacy
/// - hypothesis: L3 — as [`environment`].
/// - witness: `tests::native_formers::an_arm_is_refined_by_its_index_equation_in_both_checkers_3483`
#[spec(ensures: |ret| ret.as_ref().map_or(true, |&id| arena.value(id).is_some()))]
fn carried_value(
    arena: &mut CoreArena,
    subject: ValueId,
    depths: (BinderDepth, BinderDepth),
    replaced: &[Replaced],
) -> Result<ValueId, CheckRefusal>
{
    let entries = environment(arena, depths, replaced)?;
    match gandr_core_term::substitute_environment(arena, TermId::Value(subject), &entries) {
        TermId::Value(id) => Ok(id),
        TermId::Computation(_) => Err(CheckRefusal::MachineInvariant),
    }
}

/// `subject`, scoped at the first depth, read at the second through
/// [`environment`], each node it rewrites reported in `carried`.
///
/// # Specification
/// - requires: as [`environment`].
/// - ensures: the substituted computation. `carried` gains one pair per node
///   the substitution changed, as
///   [`gandr_core_term::substitute_environment_traced`] reports it.
/// - fails: as [`environment`].
/// - panics: none.
///
/// # Errors
/// As `- fails:`.
///
/// # Adequacy
/// - hypothesis: L3 — as [`environment`]; the typed run reads each carried node
///   back to its written node.
/// - witness: `tests::native_formers::a_refined_arm_types_its_written_terms_in_their_own_context_3483`
#[spec(captures: held = carried.len(), ensures: |ret| ret.is_err() || carried.len() >= held)]
fn carried_computation(
    arena: &mut CoreArena,
    subject: ComputationId,
    depths: (BinderDepth, BinderDepth),
    replaced: &[Replaced],
    carried: &mut Vec<Carried>,
) -> Result<ComputationId, CheckRefusal>
{
    let entries = environment(arena, depths, replaced)?;
    match gandr_core_term::substitute_environment_traced(
        arena,
        TermId::Computation(subject),
        &entries,
        carried,
    ) {
        TermId::Computation(id) => Ok(id),
        TermId::Value(_) => Err(CheckRefusal::MachineInvariant),
    }
}

/// `subject`, scoped at the first depth, read at the second through
/// [`environment`].
///
/// # Specification
/// - requires: as [`environment`].
/// - ensures: the substituted value type.
/// - fails: as [`environment`].
/// - panics: none.
///
/// # Errors
/// As `- fails:`.
///
/// # Adequacy
/// - hypothesis: L3 — as [`environment`].
/// - witness: `tests::native_formers::an_arm_is_refined_by_its_index_equation_in_both_checkers_3483`
#[spec(ensures: |ret| ret.as_ref().map_or(true, |&id| arena.value_type(id).is_some()))]
fn carried_value_type(
    arena: &mut CoreArena,
    subject: ValueTypeId,
    depths: (BinderDepth, BinderDepth),
    replaced: &[Replaced],
) -> Result<ValueTypeId, CheckRefusal>
{
    let entries = environment(arena, depths, replaced)?;
    Ok(gandr_core_term::substitute_environment_value_type(
        arena, subject, &entries,
    ))
}

/// `subject`, scoped at the first depth, read at the second through
/// [`environment`].
///
/// # Specification
/// - requires: as [`environment`].
/// - ensures: the substituted computation type.
/// - fails: as [`environment`].
/// - panics: none.
///
/// # Errors
/// As `- fails:`.
///
/// # Adequacy
/// - hypothesis: L3 — as [`environment`].
/// - witness: `tests::native_formers::a_binder_after_the_scrutinee_is_read_at_each_arm_in_both_checkers_3483`
#[spec(ensures: |ret| ret.as_ref().map_or(true, |&id| arena.comp_type(id).is_some()))]
fn carried_comp_type(
    arena: &mut CoreArena,
    subject: CompTypeId,
    depths: (BinderDepth, BinderDepth),
    replaced: &[Replaced],
) -> Result<CompTypeId, CheckRefusal>
{
    let entries = environment(arena, depths, replaced)?;
    Ok(gandr_core_term::substitute_environment_comp_type(
        arena, subject, &entries,
    ))
}
