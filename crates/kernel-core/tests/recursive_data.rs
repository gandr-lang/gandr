//! Recursive nominal blocks, structural fixpoints typed by stages and gated
//! fixpoint unfolding through admission and replay.

#[cfg(test)]
mod recursive_data
{
    use anodized::spec;
    use gandr_kernel_conversion_trace::ConversionDecision;
    use gandr_kernel_core::CheckedId;
    use gandr_kernel_core::EngineClaim;
    use gandr_kernel_core::Environment;
    use gandr_kernel_core::ExpectedComputationShape;
    use gandr_kernel_core::KernelError;
    use gandr_kernel_core::KernelVerdict;
    use gandr_kernel_core::ReplayBudget;
    use gandr_kernel_core::ReplayDecline;
    use gandr_kernel_core::ReplayNode;
    use gandr_kernel_core::ReplaySides;
    use gandr_kernel_core::Unfoldings;
    use gandr_kernel_core::replay;
    use gandr_kernel_core::stage_order::below;
    use gandr_kernel_strata::Level;
    use gandr_kernel_term::CompTypeId;
    use gandr_kernel_term::ComputationId;
    use gandr_kernel_term::ConstantIndex;
    use gandr_kernel_term::ConstructorTag;
    use gandr_kernel_term::DeBruijnIndex;
    use gandr_kernel_term::FieldPosition;
    use gandr_kernel_term::FixpointEvidence;
    use gandr_kernel_term::GroundSort;
    use gandr_kernel_term::LevelSignature;
    use gandr_kernel_term::OccurrenceSite;
    use gandr_kernel_term::ParameterPosition;
    use gandr_kernel_term::Stage;
    use gandr_kernel_term::StageId;
    use gandr_kernel_term::Standing;
    use gandr_kernel_term::TermArena;
    use gandr_kernel_term::ValueId;
    use gandr_kernel_term::ValueTypeId;

    /// A block whose one field breaks one occurrence rule.
    #[derive(Clone, Copy, Debug)]
    enum Fixture
    {
        /// `U (T A → F 1)`: the family under a function's domain.
        Negative,
        /// `T A × 1`: the family under a field-local positive former.
        Nested,
        /// `U (F (T A))`: a thunked family with no domain to vary over.
        Returner,
        /// `T ⌜1⌝`: the family at an argument other than its parameter.
        NonUniform,
        /// A declaration after the block's own position.
        Later,
        /// The family in its own parameter telescope.
        Parameter,
    }

    /// A fixpoint at `Nat → F Nat` whose body exercises one stage rule.
    #[derive(Clone, Copy, Debug)]
    enum Claim
    {
        /// `λx. case x of { zero ↦ return zero; succ ↦ λp. (force rec) p }`.
        Descends,
        /// `λy. (force rec) y`: the call at the parameter itself.
        NotCase,
        /// The `succ` branch calls the self reference at the scrutinee.
        AtScrutinee,
        /// `λx. case x of { zero ↦ return zero; succ ↦ λp. case p of { zero ↦
        /// return zero; succ ↦ λq. (force rec) (succ q) } }`: a value rebuilt
        /// below the stage.
        Rebuilt,
        /// The same, calling at `succ p`: the scrutinee rebuilt.
        RebuiltAtScrutinee,
        /// The `succ` branch calls the self reference at `zero`, with its
        /// field `p` below the stage.
        NullaryUnderField,
        /// The `zero` branch calls the self reference at `zero`, with nothing
        /// below the stage.
        NullaryUnderZero,
        /// The `succ` branch hands the self reference itself, and its field,
        /// to the helper at this position, which takes any function out of
        /// `Nat`.
        Handed(ConstantIndex),
    }

    /// The motive a derived `Nat` eliminator targets.
    #[derive(Clone, Copy, Debug)]
    enum Motive
    {
        /// `F Nat`.
        Returner,
        /// `Nat → F Nat`, the motive `plus` recurses at.
        Function,
    }

    /// The trace closing one goal on alpha equality or rigid separation.
    ///
    /// # Specification
    /// trivial.
    fn shared() -> [ConversionDecision<ReplayNode>; 1]
    {
        [ConversionDecision::ComparedShared {
            left: ReplayNode::Other,
            right: ReplayNode::Other,
        }]
    }

    /// Admit `Nat`: `zero`, and `succ` over the family itself.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the returned identifier names a checked data declaration at
    ///   the environment's next position.
    /// - panics: if the strictly positive block is refused.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a direct self occurrence is admitted at the block's
    ///   own position.
    /// - witness: `recursive_data::recursive_data::recursive_blocks_are_admitted`
    #[spec(captures: position = environment.entries().len(), ensures: |ret| usize::from(ret.position()) == position)]
    fn nat(environment: &mut Environment) -> CheckedId
    {
        let position = ConstantIndex::from(environment.entries().len());
        let mut staging = environment.stage();
        let arena = staging.arena();
        let own = arena.value_type_data(position, vec![]);
        let kind = arena.value_type_universe(GroundSort::Value, Level::zero());
        let declaration = staging.data(
            LevelSignature::monomorphic(),
            vec![],
            vec![vec![], vec![own]],
            kind,
        );
        environment
            .add_decl(declaration)
            .expect("Nat is strictly positive")
    }

    /// Admit `List A`: `nil`, and `cons` over an element and the family at
    /// its parameter.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the returned identifier names a checked one-parameter data
    ///   declaration at the environment's next position.
    /// - panics: if the strictly positive, uniform block is refused.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a parameterized self occurrence at the parameter
    ///   variable is admitted.
    /// - witness: `recursive_data::recursive_data::recursive_blocks_are_admitted`
    #[spec(captures: position = environment.entries().len(), ensures: |ret| usize::from(ret.position()) == position)]
    fn list(environment: &mut Environment) -> CheckedId
    {
        let position = ConstantIndex::from(environment.entries().len());
        let mut staging = environment.stage();
        let arena = staging.arena();
        let universe = arena.value_type_universe(GroundSort::Value, Level::zero());
        let parameter = arena.value_variable(DeBruijnIndex::from(0));
        let element = arena.value_type_element(parameter, Level::zero());
        // The tail stands past the head's binder: the parameter is one out.
        let past_head = arena.value_variable(DeBruijnIndex::from(1));
        let own = arena.value_type_data(position, vec![past_head]);
        let declaration = staging.data(
            LevelSignature::monomorphic(),
            vec![universe],
            vec![vec![], vec![element, own]],
            universe,
        );
        environment
            .add_decl(declaration)
            .expect("List is strictly positive and uniform")
    }

    /// Admit `Tree`: `leaf`, and `node` over a function field `U (Nat → F
    /// Tree)`.
    ///
    /// # Specification
    /// - requires: `nat` names an admitted data declaration.
    /// - ensures: the returned identifier names a checked data declaration at
    ///   the environment's next position.
    /// - panics: if the strictly positive block is refused.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a self occurrence at a thunked function's returner is
    ///   admitted.
    /// - witness: `recursive_data::recursive_data::recursive_blocks_are_admitted`
    #[spec(captures: position = environment.entries().len(), ensures: |ret| usize::from(ret.position()) == position)]
    fn tree(
        environment: &mut Environment,
        nat: ConstantIndex,
    ) -> CheckedId
    {
        let position = ConstantIndex::from(environment.entries().len());
        let mut staging = environment.stage();
        let arena = staging.arena();
        let nat_type = arena.value_type_data(nat, vec![]);
        let own = arena.value_type_data(position, vec![]);
        let returner = arena.comp_type_returner(own);
        let branching = arena.comp_type_arrow(nat_type, returner);
        let field = arena.value_type_thunk(branching);
        let kind = arena.value_type_universe(GroundSort::Value, Level::zero());
        let declaration = staging.data(
            LevelSignature::monomorphic(),
            vec![],
            vec![vec![], vec![field]],
            kind,
        );
        environment
            .add_decl(declaration)
            .expect("Tree is strictly positive")
    }

    /// Offer a one-parameter block whose one field breaks one occurrence
    /// rule, and return its refusal.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the block is refused and leaves no entry behind.
    /// - panics: if the block is admitted.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — each fixture differs from an admitted block in one
    ///   occurrence, so its refusal names that occurrence alone.
    /// - witness: `recursive_data::recursive_data::occurrences_are_refused_by_name`
    #[spec(captures: before = environment.entries().len(), ensures: |ret| environment.entries().len() == before && matches!(ret,
        KernelError::NegativeOccurrence(_)
        | KernelError::NestedOccurrence(_)
        | KernelError::IndexOccurrence(_)
        | KernelError::NonUniformOccurrence(_)
        | KernelError::CrossBlockReference { .. }))]
    fn refusal(
        environment: &mut Environment,
        fixture: Fixture,
    ) -> KernelError
    {
        let before = environment.entries().len();
        let position = ConstantIndex::from(before);
        let mut staging = environment.stage();
        let arena = staging.arena();
        let universe = arena.value_type_universe(GroundSort::Value, Level::zero());
        let unit = arena.value_type_unit();
        let parameter = arena.value_variable(DeBruijnIndex::from(0));
        let own = arena.value_type_data(position, vec![parameter]);
        let mut parameters = vec![universe];
        let field = match fixture {
            Fixture::Negative => {
                let returner = arena.comp_type_returner(unit);
                let function = arena.comp_type_arrow(own, returner);
                arena.value_type_thunk(function)
            },
            Fixture::Nested => arena.value_type_product(&[own, unit]),
            Fixture::Returner => {
                let returner = arena.comp_type_returner(own);
                arena.value_type_thunk(returner)
            },
            Fixture::NonUniform => {
                let code = arena.value_quote(unit);
                arena.value_type_data(position, vec![code])
            },
            Fixture::Later => {
                let later = before.checked_add(1).expect("a later position");
                arena.value_type_data(ConstantIndex::from(later), vec![])
            },
            Fixture::Parameter => {
                parameters.push(own);
                unit
            },
        };
        let declaration = staging.data(
            LevelSignature::monomorphic(),
            parameters,
            vec![vec![field]],
            universe,
        );
        environment
            .add_decl(declaration)
            .expect_err("the occurrence is refused")
    }

    /// `λx. case x [F Nat] of { zero ↦ on_zero; succ ↦ on_successor }`.
    ///
    /// # Specification
    /// trivial.
    fn case_on_argument(
        arena: &mut TermArena,
        returner: CompTypeId,
        on_zero: ComputationId,
        on_successor: ComputationId,
    ) -> ComputationId
    {
        let argument = arena.value_variable(DeBruijnIndex::from(0));
        let case = arena.computation_data_case(argument, returner, vec![on_zero, on_successor]);
        arena.computation_lambda(case)
    }

    /// `λx. case x of { zero ↦ return zero; succ ↦ λp. case p of { zero ↦
    /// return zero; succ ↦ λq. (force rec) (succ v) } }`, `v` the variable
    /// `field` under `q` 0, `p` 1, `x` 2, `rec` 3.
    ///
    /// # Specification
    /// trivial.
    fn two_deep(
        arena: &mut TermArena,
        (nat_type, returner, returned): (ValueTypeId, CompTypeId, ComputationId),
        field: DeBruijnIndex,
    ) -> ComputationId
    {
        let field = arena.value_variable(field);
        let rebuilt = arena.value_constructor(nat_type, ConstructorTag::from(1), vec![field]);
        let recursive = arena.value_variable(DeBruijnIndex::from(3));
        let forced = arena.computation_force(recursive);
        let called = arena.computation_application(forced, rebuilt);
        let on_inner = arena.computation_lambda(called);
        let inner_scrutinee = arena.value_variable(DeBruijnIndex::from(0));
        let inner =
            arena.computation_data_case(inner_scrutinee, returner, vec![returned, on_inner]);
        let on_outer = arena.computation_lambda(inner);
        case_on_argument(arena, returner, returned, on_outer)
    }

    /// `(force rec) argument`, `rec` the variable `recursive`.
    ///
    /// # Specification
    /// trivial.
    fn call(
        arena: &mut TermArena,
        recursive: DeBruijnIndex,
        argument: ValueId,
    ) -> ComputationId
    {
        let recursive = arena.value_variable(recursive);
        let forced = arena.computation_force(recursive);
        arena.computation_application(forced, argument)
    }

    /// Offer `fix rec. M` at `Nat → F Nat` with the body a claim names and the
    /// evidence given.
    ///
    /// # Specification
    /// - requires: `nat` names the admitted `Nat`, and a handed claim's
    ///   position names [`apply`]'s definition.
    /// - ensures: admitted when the evidence is partial or every call stands
    ///   below the fixpoint's stage; otherwise refused as `StageNotBelow`.
    /// - panics: none.
    ///
    /// # Errors
    /// The kernel's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — each refused claim differs from an admitted one in
    ///   the one argument its call takes.
    /// - witness: `recursive_data::recursive_data::a_recursion_descends_on_its_first_parameter`
    /// - witness: `recursive_data::recursive_data::a_call_on_a_value_rebuilt_below_the_stage_is_admitted`
    /// - witness: `recursive_data::recursive_data::a_nullary_argument_needs_a_value_below_the_stage`
    /// - witness: `recursive_data::recursive_data::a_self_reference_never_stands_for_an_unstaged_function`
    #[spec(ensures: |ret| ret.is_ok() == (evidence == FixpointEvidence::Partial
            || matches!(claim, Claim::Descends | Claim::Rebuilt | Claim::NullaryUnderField))
        && (ret.is_ok() || matches!(ret, Err(KernelError::StageNotBelow { .. }))))]
    fn claim(
        environment: &mut Environment,
        nat: ConstantIndex,
        claim: Claim,
        evidence: FixpointEvidence,
    ) -> Result<CheckedId, KernelError>
    {
        let mut staging = environment.stage();
        let arena = staging.arena();
        let nat_type = arena.value_type_data(nat, vec![]);
        let returner = arena.comp_type_returner(nat_type);
        let classifier = arena.comp_type_arrow(nat_type, returner);
        let zero = arena.value_constructor(nat_type, ConstructorTag::from(0), vec![]);
        let returned = arena.computation_return(zero);
        // Under the fixpoint's body: `rec` is 0. Under its λ: `x` 0, `rec`
        // 1. Under the `succ` branch's field: `p` 0, `x` 1, `rec` 2.
        let body = match claim {
            Claim::Descends => {
                let field = arena.value_variable(DeBruijnIndex::from(0));
                let called = call(arena, DeBruijnIndex::from(2), field);
                let on_successor = arena.computation_lambda(called);
                case_on_argument(arena, returner, returned, on_successor)
            },
            Claim::NotCase => {
                let argument = arena.value_variable(DeBruijnIndex::from(0));
                let called = call(arena, DeBruijnIndex::from(1), argument);
                arena.computation_lambda(called)
            },
            Claim::AtScrutinee => {
                let scrutinee = arena.value_variable(DeBruijnIndex::from(1));
                let called = call(arena, DeBruijnIndex::from(2), scrutinee);
                let on_successor = arena.computation_lambda(called);
                case_on_argument(arena, returner, returned, on_successor)
            },
            Claim::Rebuilt => two_deep(
                arena,
                (nat_type, returner, returned),
                DeBruijnIndex::from(0),
            ),
            Claim::RebuiltAtScrutinee => two_deep(
                arena,
                (nat_type, returner, returned),
                DeBruijnIndex::from(1),
            ),
            Claim::NullaryUnderField => {
                let called = call(arena, DeBruijnIndex::from(2), zero);
                let on_successor = arena.computation_lambda(called);
                case_on_argument(arena, returner, returned, on_successor)
            },
            Claim::NullaryUnderZero => {
                let called = call(arena, DeBruijnIndex::from(1), zero);
                let on_successor = arena.computation_lambda(returned);
                case_on_argument(arena, returner, called, on_successor)
            },
            Claim::Handed(apply) => {
                let helper = arena.value_constant(apply);
                let forced = arena.computation_force(helper);
                let recursive = arena.value_variable(DeBruijnIndex::from(2));
                let handed = arena.computation_application(forced, recursive);
                let field = arena.value_variable(DeBruijnIndex::from(0));
                let called = arena.computation_application(handed, field);
                let on_successor = arena.computation_lambda(called);
                case_on_argument(arena, returner, returned, on_successor)
            },
        };
        let fixpoint = arena.computation_fixpoint(body, evidence);
        let declared = arena.value_type_thunk(classifier);
        let value = arena.value_thunk(fixpoint);
        let declaration = staging.def(LevelSignature::monomorphic(), declared, value);
        environment.add_decl(declaration)
    }

    /// Admit `apply : U (U (Nat → F Nat) → Nat → F Nat)`, `λg. λx. (force g)
    /// x`: a helper that may call its function at any natural number.
    ///
    /// # Specification
    /// - requires: `nat` names the admitted `Nat`.
    /// - ensures: the returned identifier names the admitted definition.
    /// - panics: if the kernel refuses it.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a helper over unstaged functions, which a self
    ///   reference never stands for.
    /// - witness: `recursive_data::recursive_data::a_self_reference_never_stands_for_an_unstaged_function`
    #[spec(captures: position = environment.entries().len(), ensures: |ret| usize::from(ret.position()) == position)]
    fn apply(
        environment: &mut Environment,
        nat: ConstantIndex,
    ) -> CheckedId
    {
        let mut staging = environment.stage();
        let arena = staging.arena();
        let nat_type = arena.value_type_data(nat, vec![]);
        let returner = arena.comp_type_returner(nat_type);
        let function = arena.comp_type_arrow(nat_type, returner);
        let thunked = arena.value_type_thunk(function);
        let applying = arena.comp_type_arrow(thunked, function);
        let declared = arena.value_type_thunk(applying);
        // Under λg λx: `x` 0, `g` 1.
        let argument = arena.value_variable(DeBruijnIndex::from(0));
        let called = call(arena, DeBruijnIndex::from(1), argument);
        let inner = arena.computation_lambda(called);
        let outer = arena.computation_lambda(inner);
        let value = arena.value_thunk(outer);
        let declaration = staging.def(LevelSignature::monomorphic(), declared, value);
        environment
            .add_decl(declaration)
            .expect("apply checks without a fixpoint")
    }

    /// Offer the loop `fix rec. force rec` at `F 1` with the evidence given.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: admitted exactly when the evidence is partial; a structural
    ///   one, with no arrow to recurse on, is refused wanting one.
    /// - panics: none.
    ///
    /// # Errors
    /// The kernel's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a fixpoint at a non-function type checks as partial
    ///   and opens no stage when structural.
    /// - witness: `recursive_data::recursive_data::a_structural_fixpoint_needs_an_arrow_to_recurse_on`
    #[spec(ensures: |ret| ret.is_ok() == (evidence == FixpointEvidence::Partial)
        && (ret.is_ok() || matches!(ret, Err(KernelError::ComputationShapeMismatch { expected: ExpectedComputationShape::Arrow, .. }))))]
    fn loop_at_unit(
        environment: &mut Environment,
        evidence: FixpointEvidence,
    ) -> Result<CheckedId, KernelError>
    {
        let mut staging = environment.stage();
        let arena = staging.arena();
        let unit = arena.value_type_unit();
        let returner = arena.comp_type_returner(unit);
        let recursive = arena.value_variable(DeBruijnIndex::from(0));
        let forced = arena.computation_force(recursive);
        let fixpoint = arena.computation_fixpoint(forced, evidence);
        let declared = arena.value_type_thunk(returner);
        let value = arena.value_thunk(fixpoint);
        let declaration = staging.def(LevelSignature::monomorphic(), declared, value);
        environment.add_decl(declaration)
    }

    /// Admit `Nat`'s eliminator derived at a closed motive `C`:
    /// `λm_z. λm_s. fix rec. λx. case x [C] of { zero ↦ force m_z; succ ↦ λp.
    /// (force m_s) p (thunk ((force rec) p)) }`.
    ///
    /// # Specification
    /// - requires: `nat` names the admitted `Nat`.
    /// - ensures: the eliminator is admitted at `U C → U (Nat → U C → C) → Nat
    ///   → C`.
    /// - panics: if the kernel refuses it.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a direct field's hypothesis replays as descent.
    /// - witness: `recursive_data::recursive_data::derived_eliminators_are_admitted`
    #[spec(captures: position = environment.entries().len(), ensures: |ret| usize::from(ret.position()) == position)]
    fn nat_eliminator(
        environment: &mut Environment,
        nat: ConstantIndex,
        motive: Motive,
    ) -> CheckedId
    {
        let mut staging = environment.stage();
        let arena = staging.arena();
        let nat_type = arena.value_type_data(nat, vec![]);
        let returner = arena.comp_type_returner(nat_type);
        let motive = match motive {
            Motive::Returner => returner,
            Motive::Function => arena.comp_type_arrow(nat_type, returner),
        };
        let hypothesis = arena.value_type_thunk(motive);
        let after_field = arena.comp_type_arrow(hypothesis, motive);
        let successor = arena.comp_type_arrow(nat_type, after_field);
        let zero_method = arena.value_type_thunk(motive);
        let successor_method = arena.value_type_thunk(successor);
        let target = arena.comp_type_arrow(nat_type, motive);
        let after_zero = arena.comp_type_arrow(successor_method, target);
        let classifier = arena.comp_type_arrow(zero_method, after_zero);
        // `zero`: `x` 0, `rec` 1, `m_s` 2, `m_z` 3.
        let zero_handler = arena.value_variable(DeBruijnIndex::from(3));
        let on_zero = arena.computation_force(zero_handler);
        // `succ`: `p` 0, `x` 1, `rec` 2, `m_s` 3.
        let field = arena.value_variable(DeBruijnIndex::from(0));
        let recursive = arena.value_variable(DeBruijnIndex::from(2));
        let successor_handler = arena.value_variable(DeBruijnIndex::from(3));
        let forced_recursive = arena.computation_force(recursive);
        let call = arena.computation_application(forced_recursive, field);
        let induction = arena.value_thunk(call);
        let forced_handler = arena.computation_force(successor_handler);
        let with_field = arena.computation_application(forced_handler, field);
        let applied = arena.computation_application(with_field, induction);
        let on_successor = arena.computation_lambda(applied);
        let argument = arena.value_variable(DeBruijnIndex::from(0));
        let case = arena.computation_data_case(argument, motive, vec![on_zero, on_successor]);
        let over_argument = arena.computation_lambda(case);
        let fixpoint =
            arena.computation_fixpoint(over_argument, FixpointEvidence::StructuralDescent);
        let over_successor = arena.computation_lambda(fixpoint);
        let over_zero = arena.computation_lambda(over_successor);
        let declared = arena.value_type_thunk(classifier);
        let value = arena.value_thunk(over_zero);
        let declaration = staging.def(LevelSignature::monomorphic(), declared, value);
        environment
            .add_decl(declaration)
            .expect("Nat's derived eliminator")
    }

    /// Admit `plus m n` by `Nat`'s eliminator at `Nat → F Nat`.
    ///
    /// # Specification
    /// - requires: `eliminator` names `Nat`'s eliminator at `Nat → F Nat`.
    /// - ensures: `plus` is admitted at `Nat → Nat → F Nat`.
    /// - panics: if the kernel refuses it.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a definition by eliminator applies it to methods
    ///   whose hypothesis is a thunked function.
    /// - witness: `recursive_data::recursive_data::derived_eliminators_are_admitted`
    #[spec(captures: position = environment.entries().len(), ensures: |ret| usize::from(ret.position()) == position)]
    fn plus(
        environment: &mut Environment,
        nat: ConstantIndex,
        eliminator: ConstantIndex,
    ) -> CheckedId
    {
        let mut staging = environment.stage();
        let arena = staging.arena();
        let nat_type = arena.value_type_data(nat, vec![]);
        let returner = arena.comp_type_returner(nat_type);
        let motive = arena.comp_type_arrow(nat_type, returner);
        let classifier = arena.comp_type_arrow(nat_type, motive);
        let innermost = arena.value_variable(DeBruijnIndex::from(0));
        let first = arena.value_variable(DeBruijnIndex::from(1));
        // `m_z = thunk (λn. return n)`.
        let identity = arena.computation_return(innermost);
        let on_zero = arena.computation_lambda(identity);
        let zero_method = arena.value_thunk(on_zero);
        // `m_s = thunk (λp. λih. λn. r ← (force ih) n; return (succ r))`.
        let forced = arena.computation_force(first);
        let call = arena.computation_application(forced, innermost);
        let successor = arena.value_constructor(nat_type, ConstructorTag::from(1), vec![innermost]);
        let returned = arena.computation_return(successor);
        let bound = arena.computation_bind(call, returned);
        let over_n = arena.computation_lambda(bound);
        let over_hypothesis = arena.computation_lambda(over_n);
        let over_field = arena.computation_lambda(over_hypothesis);
        let successor_method = arena.value_thunk(over_field);
        // `λm. (force elim) m_z m_s m`.
        let constant = arena.value_constant(eliminator);
        let head = arena.computation_force(constant);
        let with_zero = arena.computation_application(head, zero_method);
        let with_successor = arena.computation_application(with_zero, successor_method);
        let applied = arena.computation_application(with_successor, innermost);
        let over_m = arena.computation_lambda(applied);
        let declared = arena.value_type_thunk(classifier);
        let value = arena.value_thunk(over_m);
        let declaration = staging.def(LevelSignature::monomorphic(), declared, value);
        environment
            .add_decl(declaration)
            .expect("plus by eliminator")
    }

    /// Admit `List`'s eliminator derived at `F Nat`, over its parameter.
    ///
    /// # Specification
    /// - requires: `list` and `nat` name the admitted `List` and `Nat`.
    /// - ensures: the eliminator is admitted at `Π (A : Type). U (F Nat) → U
    ///   (El A → List A → U (F Nat) → F Nat) → List A → F Nat`.
    /// - panics: if the kernel refuses it.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — descent replays through a parameterized family, at
    ///   the second of two fields.
    /// - witness: `recursive_data::recursive_data::derived_eliminators_are_admitted`
    #[spec(captures: position = environment.entries().len(), ensures: |ret| usize::from(ret.position()) == position)]
    fn list_eliminator(
        environment: &mut Environment,
        list: ConstantIndex,
        nat: ConstantIndex,
    ) -> CheckedId
    {
        let mut staging = environment.stage();
        let arena = staging.arena();
        let universe = arena.value_type_universe(GroundSort::Value, Level::zero());
        let parameter = arena.value_variable(DeBruijnIndex::from(0));
        let element = arena.value_type_element(parameter, Level::zero());
        let list_type = arena.value_type_data(list, vec![parameter]);
        let nat_type = arena.value_type_data(nat, vec![]);
        let returner = arena.comp_type_returner(nat_type);
        let hypothesis = arena.value_type_thunk(returner);
        let after_tail = arena.comp_type_arrow(hypothesis, returner);
        let after_element = arena.comp_type_arrow(list_type, after_tail);
        let cons = arena.comp_type_arrow(element, after_element);
        let nil_method = arena.value_type_thunk(returner);
        let cons_method = arena.value_type_thunk(cons);
        let target = arena.comp_type_arrow(list_type, returner);
        let after_nil = arena.comp_type_arrow(cons_method, target);
        let over_parameter = arena.comp_type_arrow(nil_method, after_nil);
        let classifier = arena.comp_type_pi(universe, over_parameter);
        // `nil`: `x` 0, `rec` 1, `m_cons` 2, `m_nil` 3.
        let nil_handler = arena.value_variable(DeBruijnIndex::from(3));
        let on_nil = arena.computation_force(nil_handler);
        // `cons`: `t` 0, `a` 1, `x` 2, `rec` 3, `m_cons` 4.
        let tail = arena.value_variable(DeBruijnIndex::from(0));
        let head = arena.value_variable(DeBruijnIndex::from(1));
        let recursive = arena.value_variable(DeBruijnIndex::from(3));
        let cons_handler = arena.value_variable(DeBruijnIndex::from(4));
        let forced_recursive = arena.computation_force(recursive);
        let call = arena.computation_application(forced_recursive, tail);
        let induction = arena.value_thunk(call);
        let forced_handler = arena.computation_force(cons_handler);
        let with_head = arena.computation_application(forced_handler, head);
        let with_tail = arena.computation_application(with_head, tail);
        let applied = arena.computation_application(with_tail, induction);
        let over_head = arena.computation_lambda(applied);
        let on_cons = arena.computation_lambda(over_head);
        let argument = arena.value_variable(DeBruijnIndex::from(0));
        let case = arena.computation_data_case(argument, returner, vec![on_nil, on_cons]);
        let over_argument = arena.computation_lambda(case);
        let fixpoint =
            arena.computation_fixpoint(over_argument, FixpointEvidence::StructuralDescent);
        let over_cons = arena.computation_lambda(fixpoint);
        let over_nil = arena.computation_lambda(over_cons);
        let over_type = arena.computation_lambda(over_nil);
        let declared = arena.value_type_thunk(classifier);
        let value = arena.value_thunk(over_type);
        let declaration = staging.def(LevelSignature::monomorphic(), declared, value);
        environment
            .add_decl(declaration)
            .expect("List's derived eliminator")
    }

    /// Admit `length` by `List`'s eliminator at `F Nat`.
    ///
    /// # Specification
    /// - requires: `eliminator` names `List`'s eliminator at `F Nat`.
    /// - ensures: `length` is admitted at `Π (A : Type). List A → F Nat`.
    /// - panics: if the kernel refuses it.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a definition by eliminator instantiates its parameter
    ///   before its methods.
    /// - witness: `recursive_data::recursive_data::derived_eliminators_are_admitted`
    #[spec(captures: position = environment.entries().len(), ensures: |ret| usize::from(ret.position()) == position)]
    fn length(
        environment: &mut Environment,
        list: ConstantIndex,
        nat: ConstantIndex,
        eliminator: ConstantIndex,
    ) -> CheckedId
    {
        let mut staging = environment.stage();
        let arena = staging.arena();
        let universe = arena.value_type_universe(GroundSort::Value, Level::zero());
        let innermost = arena.value_variable(DeBruijnIndex::from(0));
        let outer = arena.value_variable(DeBruijnIndex::from(1));
        let list_type = arena.value_type_data(list, vec![innermost]);
        let nat_type = arena.value_type_data(nat, vec![]);
        let returner = arena.comp_type_returner(nat_type);
        let measured = arena.comp_type_arrow(list_type, returner);
        let classifier = arena.comp_type_pi(universe, measured);
        // `m_nil = thunk (return zero)`.
        let zero = arena.value_constructor(nat_type, ConstructorTag::from(0), vec![]);
        let returned_zero = arena.computation_return(zero);
        let nil_method = arena.value_thunk(returned_zero);
        // `m_cons = thunk (λa. λt. λih. r ← force ih; return (succ r))`.
        let forced = arena.computation_force(innermost);
        let successor = arena.value_constructor(nat_type, ConstructorTag::from(1), vec![innermost]);
        let returned = arena.computation_return(successor);
        let bound = arena.computation_bind(forced, returned);
        let over_hypothesis = arena.computation_lambda(bound);
        let over_tail = arena.computation_lambda(over_hypothesis);
        let over_head = arena.computation_lambda(over_tail);
        let cons_method = arena.value_thunk(over_head);
        // `λA. λxs. (force elim) A m_nil m_cons xs`: `xs` 0, `A` 1.
        let constant = arena.value_constant(eliminator);
        let head = arena.computation_force(constant);
        let with_type = arena.computation_application(head, outer);
        let with_nil = arena.computation_application(with_type, nil_method);
        let with_cons = arena.computation_application(with_nil, cons_method);
        let applied = arena.computation_application(with_cons, innermost);
        let over_list = arena.computation_lambda(applied);
        let over_type = arena.computation_lambda(over_list);
        let declared = arena.value_type_thunk(classifier);
        let value = arena.value_thunk(over_type);
        let declaration = staging.def(LevelSignature::monomorphic(), declared, value);
        environment
            .add_decl(declaration)
            .expect("length by eliminator")
    }

    /// Admit `Tree`'s eliminator derived at `F Nat`, whose `node` hypothesis
    /// runs the function field before recursing:
    /// `thunk (λy. t ← (force f) y; (force rec) t)`.
    ///
    /// # Specification
    /// - requires: `tree` and `nat` name the admitted `Tree` and `Nat`.
    /// - ensures: the eliminator is admitted at `U (F Nat) → U (U (Nat → F
    ///   Tree) → U (Nat → F Nat) → F Nat) → Tree → F Nat`.
    /// - panics: if the kernel refuses it.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — descent replays through a function field's result
    ///   under its own binder and a bind.
    /// - witness: `recursive_data::recursive_data::derived_eliminators_are_admitted`
    #[spec(captures: position = environment.entries().len(), ensures: |ret| usize::from(ret.position()) == position)]
    fn tree_eliminator(
        environment: &mut Environment,
        tree: ConstantIndex,
        nat: ConstantIndex,
    ) -> CheckedId
    {
        let mut staging = environment.stage();
        let arena = staging.arena();
        let tree_type = arena.value_type_data(tree, vec![]);
        let nat_type = arena.value_type_data(nat, vec![]);
        let returner = arena.comp_type_returner(nat_type);
        let tree_returner = arena.comp_type_returner(tree_type);
        let branching = arena.comp_type_arrow(nat_type, tree_returner);
        let field_type = arena.value_type_thunk(branching);
        let induction_type = arena.comp_type_arrow(nat_type, returner);
        let hypothesis = arena.value_type_thunk(induction_type);
        let after_field = arena.comp_type_arrow(hypothesis, returner);
        let node = arena.comp_type_arrow(field_type, after_field);
        let leaf_method = arena.value_type_thunk(returner);
        let node_method = arena.value_type_thunk(node);
        let target = arena.comp_type_arrow(tree_type, returner);
        let after_leaf = arena.comp_type_arrow(node_method, target);
        let classifier = arena.comp_type_arrow(leaf_method, after_leaf);
        // `leaf`: `x` 0, `rec` 1, `m_node` 2, `m_leaf` 3.
        let leaf_handler = arena.value_variable(DeBruijnIndex::from(3));
        let on_leaf = arena.computation_force(leaf_handler);
        // Under the bind: `t` 0, `y` 1, `f` 2, `x` 3, `rec` 4.
        let result = arena.value_variable(DeBruijnIndex::from(0));
        let recursive = arena.value_variable(DeBruijnIndex::from(4));
        let forced_recursive = arena.computation_force(recursive);
        let call = arena.computation_application(forced_recursive, result);
        // Under `λy`: `y` 0, `f` 1.
        let point = arena.value_variable(DeBruijnIndex::from(0));
        let branch_field = arena.value_variable(DeBruijnIndex::from(1));
        let forced_field = arena.computation_force(branch_field);
        let run = arena.computation_application(forced_field, point);
        let bound = arena.computation_bind(run, call);
        let over_point = arena.computation_lambda(bound);
        let induction = arena.value_thunk(over_point);
        // `node`: `f` 0, `x` 1, `rec` 2, `m_node` 3.
        let field = arena.value_variable(DeBruijnIndex::from(0));
        let node_handler = arena.value_variable(DeBruijnIndex::from(3));
        let forced_handler = arena.computation_force(node_handler);
        let with_field = arena.computation_application(forced_handler, field);
        let applied = arena.computation_application(with_field, induction);
        let on_node = arena.computation_lambda(applied);
        let argument = arena.value_variable(DeBruijnIndex::from(0));
        let case = arena.computation_data_case(argument, returner, vec![on_leaf, on_node]);
        let over_argument = arena.computation_lambda(case);
        let fixpoint =
            arena.computation_fixpoint(over_argument, FixpointEvidence::StructuralDescent);
        let over_node = arena.computation_lambda(fixpoint);
        let over_leaf = arena.computation_lambda(over_node);
        let declared = arena.value_type_thunk(classifier);
        let value = arena.value_thunk(over_leaf);
        let declaration = staging.def(LevelSignature::monomorphic(), declared, value);
        environment
            .add_decl(declaration)
            .expect("Tree's derived eliminator")
    }

    /// `fix rec. λx. case x [F Nat] of { zero ↦ return zero; succ ↦ λp. r ←
    /// (force rec) p; return (succ (succ r)) }`, carrying `evidence`.
    ///
    /// # Specification
    /// trivial.
    fn double(
        arena: &mut TermArena,
        nat: ConstantIndex,
        evidence: FixpointEvidence,
    ) -> ComputationId
    {
        let nat_type = arena.value_type_data(nat, vec![]);
        let returner = arena.comp_type_returner(nat_type);
        let zero = arena.value_constructor(nat_type, ConstructorTag::from(0), vec![]);
        let on_zero = arena.computation_return(zero);
        let field = arena.value_variable(DeBruijnIndex::from(0));
        let recursive = arena.value_variable(DeBruijnIndex::from(2));
        let forced = arena.computation_force(recursive);
        let call = arena.computation_application(forced, field);
        let once = arena.value_constructor(nat_type, ConstructorTag::from(1), vec![field]);
        let twice = arena.value_constructor(nat_type, ConstructorTag::from(1), vec![once]);
        let returned = arena.computation_return(twice);
        let bound = arena.computation_bind(call, returned);
        let on_successor = arena.computation_lambda(bound);
        let body = case_on_argument(arena, returner, on_zero, on_successor);
        arena.computation_fixpoint(body, evidence)
    }

    /// The numerals `0 … 4` over the admitted `Nat`.
    ///
    /// # Specification
    /// trivial.
    fn numerals(
        arena: &mut TermArena,
        nat: ConstantIndex,
    ) -> [ValueId; 5]
    {
        let nat_type = arena.value_type_data(nat, vec![]);
        let zero = arena.value_constructor(nat_type, ConstructorTag::from(0), vec![]);
        let one = arena.value_constructor(nat_type, ConstructorTag::from(1), vec![zero]);
        let two = arena.value_constructor(nat_type, ConstructorTag::from(1), vec![one]);
        let three = arena.value_constructor(nat_type, ConstructorTag::from(1), vec![two]);
        let four = arena.value_constructor(nat_type, ConstructorTag::from(1), vec![three]);
        [zero, one, two, three, four]
    }

    #[test]
    fn recursive_blocks_are_admitted()
    {
        let mut environment = Environment::new();
        let nat = nat(&mut environment);
        let list = list(&mut environment);
        let tree = tree(&mut environment, nat.position());
        for admitted in [nat, list, tree] {
            assert!(environment.audit(admitted).axioms().is_empty());
        }
    }

    /// A field may name the one before it: `Box : Type₁ { put : (a : Type₀,
    /// x : El a) }` admits; a `put` whose second field is an element of the
    /// code its first gives checks, and one whose second field is a code
    /// instead is refused at that field's type.
    #[test]
    fn dependent_fields_are_admitted()
    {
        let mut environment = Environment::new();
        let position = ConstantIndex::from(environment.entries().len());
        let mut staging = environment.stage();
        let arena = staging.arena();
        let small = arena.value_type_universe(GroundSort::Value, Level::zero());
        let one = Level::zero().succ().expect("the successor of zero");
        let large = arena.value_type_universe(GroundSort::Value, one);
        let code = arena.value_variable(DeBruijnIndex::from(0));
        let element = arena.value_type_element(code, Level::zero());
        let declaration = staging.data(
            LevelSignature::monomorphic(),
            vec![],
            vec![vec![small, element]],
            large,
        );
        let boxed = environment
            .add_decl(declaration)
            .expect("a field may name the one before it");
        assert_eq!(boxed.position(), position);
        assert!(environment.audit(boxed).axioms().is_empty());
        let put = |environment: &mut Environment, quoted: bool| {
            let mut staging = environment.stage();
            let arena = staging.arena();
            let datatype = arena.value_type_data(position, vec![]);
            let unit = arena.value_type_unit();
            let code = arena.value_quote(unit);
            let second = if quoted { code } else { arena.value_unit() };
            let constructor =
                arena.value_constructor(datatype, ConstructorTag::from(0), vec![code, second]);
            let declaration = staging.def(LevelSignature::monomorphic(), datatype, constructor);
            environment.add_decl(declaration).map(|_admitted| ())
        };
        assert_eq!(
            put(&mut environment, false),
            Ok(()),
            "the unit value is an element of the unit's code"
        );
        assert!(
            matches!(
                put(&mut environment, true),
                Err(KernelError::ValueTypeMismatch(_))
            ),
            "a code is no element of the unit's code"
        );
    }

    #[test]
    fn occurrences_are_refused_by_name()
    {
        let mut environment = Environment::new();
        let field = OccurrenceSite::Field {
            tag: ConstructorTag::from(0),
            field: FieldPosition::from(0),
        };
        assert_eq!(
            refusal(&mut environment, Fixture::Negative),
            KernelError::NegativeOccurrence(field)
        );
        assert_eq!(
            refusal(&mut environment, Fixture::Nested),
            KernelError::NestedOccurrence(field)
        );
        assert_eq!(
            refusal(&mut environment, Fixture::Returner),
            KernelError::NestedOccurrence(field)
        );
        assert_eq!(
            refusal(&mut environment, Fixture::NonUniform),
            KernelError::NonUniformOccurrence(field)
        );
        assert_eq!(
            refusal(&mut environment, Fixture::Later),
            KernelError::CrossBlockReference {
                site: field,
                index: ConstantIndex::from(1_usize),
            }
        );
        assert_eq!(
            refusal(&mut environment, Fixture::Parameter),
            KernelError::IndexOccurrence(OccurrenceSite::Parameter(ParameterPosition::from(1)))
        );
    }

    #[test]
    fn a_recursion_descends_on_its_first_parameter()
    {
        let mut environment = Environment::new();
        let nat = nat(&mut environment).position();
        let admitted = claim(
            &mut environment,
            nat,
            Claim::Descends,
            FixpointEvidence::StructuralDescent,
        )
        .expect("a call at the scrutinised constructor's field descends");
        assert!(environment.audit(admitted).axioms().is_empty());
        let root = Stage::At(StageId::from(0_usize));
        for fixture in [Claim::NotCase, Claim::AtScrutinee] {
            assert_eq!(
                claim(
                    &mut environment,
                    nat,
                    fixture,
                    FixpointEvidence::StructuralDescent
                ),
                Err(KernelError::StageNotBelow {
                    found: Standing::Staged(root),
                    bound: below(root),
                }),
                "{fixture:?}"
            );
            claim(&mut environment, nat, fixture, FixpointEvidence::Partial)
                .expect("a fixpoint without a claim checks as partial");
        }
    }

    #[test]
    fn a_structural_fixpoint_needs_an_arrow_to_recurse_on()
    {
        let mut environment = Environment::new();
        assert!(matches!(
            loop_at_unit(&mut environment, FixpointEvidence::StructuralDescent),
            Err(KernelError::ComputationShapeMismatch {
                expected: ExpectedComputationShape::Arrow,
                ..
            })
        ));
        loop_at_unit(&mut environment, FixpointEvidence::Partial)
            .expect("a loop at F 1 checks as partial");
    }

    #[test]
    fn a_call_on_a_value_rebuilt_below_the_stage_is_admitted()
    {
        let mut environment = Environment::new();
        let nat = nat(&mut environment).position();
        let admitted = claim(
            &mut environment,
            nat,
            Claim::Rebuilt,
            FixpointEvidence::StructuralDescent,
        )
        .expect("succ q stands below x = succ (succ q)");
        assert!(environment.audit(admitted).axioms().is_empty());
        // `succ p` is `x` itself: its field `p` stands at the outer case's
        // stage, one below the fixpoint's, where two are wanted.
        let root = Stage::At(StageId::from(0_usize));
        assert_eq!(
            claim(
                &mut environment,
                nat,
                Claim::RebuiltAtScrutinee,
                FixpointEvidence::StructuralDescent
            ),
            Err(KernelError::StageNotBelow {
                found: Standing::Staged(Stage::At(StageId::from(1_usize))),
                bound: below(below(root)),
            })
        );
    }

    #[test]
    fn a_nullary_argument_needs_a_value_below_the_stage()
    {
        let mut environment = Environment::new();
        let nat = nat(&mut environment).position();
        let admitted = claim(
            &mut environment,
            nat,
            Claim::NullaryUnderField,
            FixpointEvidence::StructuralDescent,
        )
        .expect("the field p shows the stage holds a value");
        assert!(environment.audit(admitted).axioms().is_empty());
        // Under `zero` nothing in scope stands below the stage, which may be
        // the first: `rec zero` there need not terminate.
        let root = Stage::At(StageId::from(0_usize));
        assert_eq!(
            claim(
                &mut environment,
                nat,
                Claim::NullaryUnderZero,
                FixpointEvidence::StructuralDescent
            ),
            Err(KernelError::StageNotBelow {
                found: Standing::Top,
                bound: below(root),
            })
        );
        claim(
            &mut environment,
            nat,
            Claim::NullaryUnderZero,
            FixpointEvidence::Partial,
        )
        .expect("a fixpoint without a claim checks as partial");
    }

    #[test]
    fn a_nullary_argument_is_judged_in_each_branch_s_own_scope()
    {
        // `succ` first: the branch whose field shows the stage holds a value
        // is checked before the one with nothing below it, so an answer for
        // `rec zero` kept from the first would wrongly serve the second.
        let mut environment = Environment::new();
        let position = ConstantIndex::from(environment.entries().len());
        let mut staging = environment.stage();
        let arena = staging.arena();
        let own = arena.value_type_data(position, vec![]);
        let kind = arena.value_type_universe(GroundSort::Value, Level::zero());
        let declaration = staging.data(
            LevelSignature::monomorphic(),
            vec![],
            vec![vec![own], vec![]],
            kind,
        );
        let swapped = environment
            .add_decl(declaration)
            .expect("a successor-first Nat is strictly positive")
            .position();
        let mut staging = environment.stage();
        let arena = staging.arena();
        let nat_type = arena.value_type_data(swapped, vec![]);
        let returner = arena.comp_type_returner(nat_type);
        let classifier = arena.comp_type_arrow(nat_type, returner);
        let zero = arena.value_constructor(nat_type, ConstructorTag::from(1), vec![]);
        // Under the `succ` branch's field: `p` 0, `x` 1, `rec` 2; under the
        // `zero` branch: `x` 0, `rec` 1.
        let under_field = call(arena, DeBruijnIndex::from(2), zero);
        let on_successor = arena.computation_lambda(under_field);
        let on_zero = call(arena, DeBruijnIndex::from(1), zero);
        let argument = arena.value_variable(DeBruijnIndex::from(0));
        let case = arena.computation_data_case(argument, returner, vec![on_successor, on_zero]);
        let body = arena.computation_lambda(case);
        let fixpoint = arena.computation_fixpoint(body, FixpointEvidence::StructuralDescent);
        let declared = arena.value_type_thunk(classifier);
        let value = arena.value_thunk(fixpoint);
        let declaration = staging.def(LevelSignature::monomorphic(), declared, value);
        let root = Stage::At(StageId::from(0_usize));
        assert_eq!(
            environment.add_decl(declaration).map(|_admitted| ()),
            Err(KernelError::StageNotBelow {
                found: Standing::Top,
                bound: below(root),
            })
        );
    }

    #[test]
    fn a_self_reference_never_stands_for_an_unstaged_function()
    {
        let mut environment = Environment::new();
        let nat = nat(&mut environment).position();
        let apply = apply(&mut environment, nat).position();
        // `apply rec p` hands `rec` to a function that may call it at any
        // natural number, `x` itself among them: `rec`'s domain stands below
        // the stage, and `apply`'s at none.
        let root = Stage::At(StageId::from(0_usize));
        assert_eq!(
            claim(
                &mut environment,
                nat,
                Claim::Handed(apply),
                FixpointEvidence::StructuralDescent
            ),
            Err(KernelError::StageNotBelow {
                found: Standing::Top,
                bound: below(root),
            })
        );
        claim(
            &mut environment,
            nat,
            Claim::Handed(apply),
            FixpointEvidence::Partial,
        )
        .expect("a fixpoint without a claim checks as partial");
    }

    #[test]
    fn derived_eliminators_are_admitted()
    {
        let mut environment = Environment::new();
        let nat = nat(&mut environment).position();
        let list = list(&mut environment).position();
        let tree = tree(&mut environment, nat).position();
        let by_nat = nat_eliminator(&mut environment, nat, Motive::Function);
        let plus = plus(&mut environment, nat, by_nat.position());
        let by_nat_value = nat_eliminator(&mut environment, nat, Motive::Returner);
        let by_list = list_eliminator(&mut environment, list, nat);
        let length = length(&mut environment, list, nat, by_list.position());
        let by_tree = tree_eliminator(&mut environment, tree, nat);
        for admitted in [by_nat, plus, by_nat_value, by_list, length, by_tree] {
            assert!(environment.audit(admitted).axioms().is_empty());
        }
    }

    #[test]
    fn a_fixpoint_computes_at_a_constructor_and_replays()
    {
        let mut environment = Environment::new();
        let nat = nat(&mut environment).position();
        let mut arena = environment.arena().clone();
        let doubling = double(&mut arena, nat, FixpointEvidence::StructuralDescent);
        let [_, _, two, three, four] = numerals(&mut arena, nat);
        let applied = arena.computation_application(doubling, two);
        let expected = arena.computation_return(four);
        let wrong = arena.computation_return(three);
        let unfoldings = Unfoldings::default();
        assert_eq!(
            replay(
                &mut arena,
                &unfoldings,
                ReplaySides::Computations(applied, expected),
                EngineClaim::Convertible,
                shared(),
                ReplayBudget::default()
            ),
            KernelVerdict::Convertible
        );
        assert_eq!(
            replay(
                &mut arena,
                &unfoldings,
                ReplaySides::Computations(applied, wrong),
                EngineClaim::NotConvertible,
                shared(),
                ReplayBudget::default()
            ),
            KernelVerdict::NotConvertible
        );
        // At a neutral argument the fixpoint is stuck, and bare it is inert:
        // an unfolding there would never stop, and the budget would decline.
        let variable = arena.value_variable(DeBruijnIndex::from(0));
        let stuck = arena.computation_application(doubling, variable);
        for standing in [stuck, doubling] {
            assert_eq!(
                replay(
                    &mut arena,
                    &unfoldings,
                    ReplaySides::Computations(standing, standing),
                    EngineClaim::Convertible,
                    shared(),
                    ReplayBudget::default()
                ),
                KernelVerdict::Convertible
            );
        }
    }

    #[test]
    fn a_partial_fixpoint_declines_at_its_gate()
    {
        let mut environment = Environment::new();
        let nat = nat(&mut environment).position();
        let mut arena = environment.arena().clone();
        let doubling = double(&mut arena, nat, FixpointEvidence::Partial);
        let [_, _, two, three, four] = numerals(&mut arena, nat);
        let applied = arena.computation_application(doubling, two);
        let expected = arena.computation_return(four);
        let wrong = arena.computation_return(three);
        let recursive = arena.value_variable(DeBruijnIndex::from(0));
        let forced = arena.computation_force(recursive);
        let looping = arena.computation_fixpoint(forced, FixpointEvidence::Partial);
        let observed = arena.computation_bind(looping, expected);
        let unfoldings = Unfoldings::default();
        for (left, right, claim) in [
            (applied, expected, EngineClaim::Convertible),
            (applied, wrong, EngineClaim::NotConvertible),
            (observed, expected, EngineClaim::Convertible),
        ] {
            assert_eq!(
                replay(
                    &mut arena,
                    &unfoldings,
                    ReplaySides::Computations(left, right),
                    claim,
                    shared(),
                    ReplayBudget::default()
                ),
                KernelVerdict::Declined(ReplayDecline::PartialFixpoint)
            );
        }
        let variable = arena.value_variable(DeBruijnIndex::from(0));
        let stuck = arena.computation_application(doubling, variable);
        assert_eq!(
            replay(
                &mut arena,
                &unfoldings,
                ReplaySides::Computations(stuck, stuck),
                EngineClaim::Convertible,
                shared(),
                ReplayBudget::default()
            ),
            KernelVerdict::Convertible
        );
    }
}
