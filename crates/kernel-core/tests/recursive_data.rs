//! Recursive nominal blocks, structural fixpoints typed by stages and gated
//! fixpoint unfolding through admission and replay.

extern crate alloc;

#[cfg(test)]
mod recursive_data
{
    use alloc::collections::BTreeMap;

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
    use gandr_kernel_term::FieldLabel;
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

    /// Where a one-parameter block's one field places the family `T A`, `A`
    /// its parameter, beside `List`, whose parameter is strictly positive,
    /// and `Test`, whose parameter is consumed.
    #[derive(Clone, Copy, Debug, Eq, PartialEq)]
    enum Placement
    {
        /// `T A`.
        Direct,
        /// `U (F (T A))`: the returner's result.
        Returned,
        /// `U (Π (x : 1). F (T A))`: a dependent function's codomain.
        Codomain,
        /// `T A × 1`.
        Product,
        /// `T A + 1`.
        Sum,
        /// `{ x : T A }`.
        Record,
        /// `[T A]`.
        List,
        /// `Σ (x : 1). T A`.
        Sigma,
        /// `U (F (T A) & F 1)`.
        With,
        /// `List ⌜T A⌝`: through a strictly positive parameter.
        Nested,
        /// `U (T A → F 1)`: under a function's domain, one stage below.
        Domain,
        /// `U (U (T A → F 1) → F 1)`: under two domains.
        TwoDomains,
        /// `T ⌜1⌝`: at an argument other than its parameter.
        NonUniform,
        /// `U (T ⌜1⌝ → F 1)`: at another argument under a domain.
        NonUniformDomain,
        /// `Test ⌜T A⌝`: through a consumed parameter.
        Consumed,
        /// `U (Test ⌜T A⌝ → F 1)`: through a consumed parameter under a
        /// domain.
        ConsumedDomain,
        /// `Lift (T A)`: the family lifted, a type no stage reaches.
        Lifted,
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

    /// `U (domain → returns)`: a thunked function from `domain`.
    ///
    /// # Specification
    /// trivial.
    fn consuming(
        arena: &mut TermArena,
        domain: ValueTypeId,
        returns: CompTypeId,
    ) -> ValueTypeId
    {
        let function = arena.comp_type_arrow(domain, returns);
        arena.value_type_thunk(function)
    }

    /// Admit `Test A`: `test` over one function `U (El A → F 1)`, so the
    /// parameter stands under a domain and is not strictly positive.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the returned identifier names a checked one-parameter data
    ///   declaration at the environment's next position.
    /// - panics: if the declaration is refused.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a family nested through `Test`'s parameter is refused
    ///   where one nested through `List`'s is admitted.
    /// - witness: `recursive_data::recursive_data::accessibility_is_decided_on_every_former`
    #[spec(captures: position = environment.entries().len(), ensures: |ret| usize::from(ret.position()) == position)]
    fn consumed(environment: &mut Environment) -> CheckedId
    {
        let mut staging = environment.stage();
        let arena = staging.arena();
        let universe = arena.value_type_universe(GroundSort::Value, Level::zero());
        let parameter = arena.value_variable(DeBruijnIndex::from(0));
        let element = arena.value_type_element(parameter, Level::zero());
        let unit = arena.value_type_unit();
        let returns = arena.comp_type_returner(unit);
        let field = consuming(arena, element, returns);
        let declaration = staging.data(
            LevelSignature::monomorphic(),
            vec![universe],
            vec![vec![field]],
            universe,
        );
        environment.add_decl(declaration).expect("Test is admitted")
    }

    /// Admit `List` and `Test`, then offer a one-parameter block whose one
    /// field places the family as `placement` names.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the block, at position 2, or its refusal, one of the
    ///   occurrence refusals.
    /// - panics: if `List` or `Test` is refused.
    ///
    /// # Errors
    /// The kernel's refusal of the block.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — each placement differs from `T A` in one former, so
    ///   its verdict is that former's.
    /// - witness: `recursive_data::recursive_data::accessibility_is_decided_on_every_former`
    #[spec(ensures: |ret| ret.as_ref().map_or_else(|error| matches!(error,
        KernelError::NegativeOccurrence(_)
        | KernelError::NestedOccurrence(_)
        | KernelError::IndexOccurrence(_)
        | KernelError::NonUniformOccurrence(_)
        | KernelError::CrossBlockReference { .. }), |id| usize::from(id.position()) == 2))]
    fn placed(placement: Placement) -> Result<CheckedId, KernelError>
    {
        let mut environment = Environment::new();
        let list = list(&mut environment).position();
        let consumed = consumed(&mut environment).position();
        let position = ConstantIndex::from(environment.entries().len());
        let mut staging = environment.stage();
        let arena = staging.arena();
        let universe = arena.value_type_universe(GroundSort::Value, Level::zero());
        let unit = arena.value_type_unit();
        let returns = arena.comp_type_returner(unit);
        let parameter = arena.value_variable(DeBruijnIndex::from(0));
        let own = arena.value_type_data(position, vec![parameter]);
        // Past one binder the parameter is one out.
        let past = arena.value_variable(DeBruijnIndex::from(1));
        let own_past = arena.value_type_data(position, vec![past]);
        let code = arena.value_quote(own);
        let one = arena.value_quote(unit);
        let mut parameters = vec![universe];
        let field = match placement {
            Placement::Direct => own,
            Placement::Returned => {
                let returner = arena.comp_type_returner(own);
                arena.value_type_thunk(returner)
            },
            Placement::Codomain => {
                let returner = arena.comp_type_returner(own_past);
                let function = arena.comp_type_pi(unit, returner);
                arena.value_type_thunk(function)
            },
            Placement::Product => arena.value_type_product(&[own, unit]),
            Placement::Sum => arena.value_type_sum(&[own, unit]),
            Placement::Record => arena
                .value_type_record(BTreeMap::from([(FieldLabel::from(String::from("x")), own)])),
            Placement::List => arena.value_type_list(own),
            Placement::Sigma => arena.value_type_sigma(unit, own_past),
            Placement::With => {
                let first = arena.comp_type_returner(own);
                let both = arena.comp_type_with(first, returns);
                arena.value_type_thunk(both)
            },
            Placement::Nested => arena.value_type_data(list, vec![code]),
            Placement::Domain => consuming(arena, own, returns),
            Placement::TwoDomains => {
                let inner = consuming(arena, own, returns);
                consuming(arena, inner, returns)
            },
            Placement::NonUniform => arena.value_type_data(position, vec![one]),
            Placement::NonUniformDomain => {
                let other = arena.value_type_data(position, vec![one]);
                consuming(arena, other, returns)
            },
            Placement::Consumed => arena.value_type_data(consumed, vec![code]),
            Placement::ConsumedDomain => {
                let tested = arena.value_type_data(consumed, vec![code]);
                consuming(arena, tested, returns)
            },
            Placement::Lifted => arena.value_type_lift(own, Level::zero()),
            Placement::Later => {
                let later = usize::from(position)
                    .checked_add(1)
                    .expect("a later position");
                arena.value_type_data(ConstantIndex::from(later), vec![])
            },
            Placement::Parameter => {
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
        environment.add_decl(declaration)
    }

    /// What a consumer of `Chain` applies the test a link holds to.
    #[derive(Clone, Copy, Debug, Eq, PartialEq)]
    enum Consumer
    {
        /// The chain before the link, one stage below it.
        Before,
        /// The link itself: Curry's consumer.
        Itself,
        /// The link itself, through a helper that takes the test at its
        /// declared type.
        Handed,
    }

    /// Admit `Chain`, `start` and `link : (prev : Chain, test : U (Chain → F
    /// 1))`, and `apply : U (U (Chain → F 1) → Chain → F 1)`, `λg. λx.
    /// (force g) x`; then offer `λc. case c of { start ↦ return (); link ↦
    /// λprev test. … }`, applying `test` to what `consumer` names.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the consumer is admitted exactly when it applies the test to
    ///   the chain before the link, and otherwise refused as `StageNotBelow`.
    /// - panics: if `Chain` or `apply` is refused.
    ///
    /// # Errors
    /// The kernel's refusal of the consumer.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the consumers differ only in the value the test is
    ///   applied to.
    /// - witness: `recursive_data::recursive_data::a_negative_occurrence_below_the_stage_declares`
    /// - witness: `recursive_data::recursive_data::currys_consumer_is_refused_at_its_call`
    #[spec(ensures: |ret| ret.is_ok() == (consumer == Consumer::Before)
        && (ret.is_ok() || matches!(ret, Err(KernelError::StageNotBelow { .. }))))]
    fn chain(consumer: Consumer) -> Result<CheckedId, KernelError>
    {
        let mut environment = Environment::new();
        let chain = ConstantIndex::from(environment.entries().len());
        let mut staging = environment.stage();
        let arena = staging.arena();
        let kind = arena.value_type_universe(GroundSort::Value, Level::zero());
        let own = arena.value_type_data(chain, vec![]);
        let unit = arena.value_type_unit();
        let returns = arena.comp_type_returner(unit);
        let test = consuming(arena, own, returns);
        let declaration = staging.data(
            LevelSignature::monomorphic(),
            vec![],
            vec![vec![], vec![own, test]],
            kind,
        );
        environment
            .add_decl(declaration)
            .expect("Chain is stratified");
        let mut staging = environment.stage();
        let arena = staging.arena();
        let own = arena.value_type_data(chain, vec![]);
        let unit = arena.value_type_unit();
        let returns = arena.comp_type_returner(unit);
        let test = consuming(arena, own, returns);
        let tested = arena.comp_type_arrow(own, returns);
        let handing = arena.comp_type_arrow(test, tested);
        let declared = arena.value_type_thunk(handing);
        let argument = arena.value_variable(DeBruijnIndex::from(0));
        let applied = call(arena, DeBruijnIndex::from(1), argument);
        let body = arena.computation_lambda(applied);
        let body = arena.computation_lambda(body);
        let value = arena.value_thunk(body);
        let declaration = staging.def(LevelSignature::monomorphic(), declared, value);
        let apply = environment
            .add_decl(declaration)
            .expect("apply is admitted")
            .position();
        let mut staging = environment.stage();
        let arena = staging.arena();
        let own = arena.value_type_data(chain, vec![]);
        let unit = arena.value_type_unit();
        let returns = arena.comp_type_returner(unit);
        let done = arena.value_unit();
        let on_start = arena.computation_return(done);
        // Under the link's fields: `test` 0, `prev` 1, `c` 2.
        let applied = match consumer {
            Consumer::Before => {
                let prev = arena.value_variable(DeBruijnIndex::from(1));
                call(arena, DeBruijnIndex::from(0), prev)
            },
            Consumer::Itself => {
                let link = arena.value_variable(DeBruijnIndex::from(2));
                call(arena, DeBruijnIndex::from(0), link)
            },
            Consumer::Handed => {
                let helper = arena.value_constant(apply);
                let forced = arena.computation_force(helper);
                let test = arena.value_variable(DeBruijnIndex::from(0));
                let handed = arena.computation_application(forced, test);
                let link = arena.value_variable(DeBruijnIndex::from(2));
                arena.computation_application(handed, link)
            },
        };
        let on_link = arena.computation_lambda(applied);
        let on_link = arena.computation_lambda(on_link);
        let scrutinee = arena.value_variable(DeBruijnIndex::from(0));
        let case = arena.computation_data_case(scrutinee, returns, vec![on_start, on_link]);
        let body = arena.computation_lambda(case);
        let declared = consuming(arena, own, returns);
        let value = arena.value_thunk(body);
        let declaration = staging.def(LevelSignature::monomorphic(), declared, value);
        environment.add_decl(declaration)
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

    /// Every placeable former admits the family it places, at a strictly
    /// positive position and under domains alike; what no stage reaches is
    /// refused by the occurrence it is.
    #[test]
    fn accessibility_is_decided_on_every_former()
    {
        for placement in [
            Placement::Direct,
            Placement::Returned,
            Placement::Codomain,
            Placement::Product,
            Placement::Sum,
            Placement::Record,
            Placement::List,
            Placement::Sigma,
            Placement::With,
            Placement::Nested,
            Placement::Domain,
            Placement::TwoDomains,
        ] {
            let admitted = placed(placement);
            assert!(admitted.is_ok(), "{placement:?}: {admitted:?}");
        }
        let field = OccurrenceSite::Field {
            tag: ConstructorTag::from(0),
            field: FieldPosition::from(0),
        };
        for (placement, refusal) in [
            (
                Placement::NonUniform,
                KernelError::NonUniformOccurrence(field),
            ),
            (
                Placement::NonUniformDomain,
                KernelError::NegativeOccurrence(field),
            ),
            (Placement::Consumed, KernelError::NestedOccurrence(field)),
            (
                Placement::ConsumedDomain,
                KernelError::NegativeOccurrence(field),
            ),
            (Placement::Lifted, KernelError::IndexOccurrence(field)),
            (Placement::Later, KernelError::CrossBlockReference {
                site: field,
                index: ConstantIndex::from(3_usize),
            }),
            (
                Placement::Parameter,
                KernelError::IndexOccurrence(OccurrenceSite::Parameter(ParameterPosition::from(1))),
            ),
        ] {
            assert_eq!(placed(placement).map(drop), Err(refusal), "{placement:?}");
        }
    }

    /// `Chain`'s test consumes the family under a domain, so a link's test
    /// takes chains one stage below the link: the block declares, and a
    /// consumer applying the test to the chain before the link is admitted.
    #[test]
    fn a_negative_occurrence_below_the_stage_declares()
    {
        let admitted = chain(Consumer::Before);
        assert!(admitted.is_ok(), "{admitted:?}");
    }

    /// Curry's consumer applies a link's test to the link itself, at no
    /// stage the test takes: refused at the call, written directly or
    /// through a helper.
    #[test]
    fn currys_consumer_is_refused_at_its_call()
    {
        for consumer in [Consumer::Itself, Consumer::Handed] {
            let refused = chain(consumer);
            assert!(
                matches!(
                    refused,
                    Err(KernelError::StageNotBelow {
                        found: Standing::Top,
                        ..
                    })
                ),
                "{consumer:?}: {refused:?}"
            );
        }
    }

    /// Admit `Rose`, `node : (kids : List ⌜Rose⌝)`: the family nested through
    /// `List`'s strictly positive parameter.
    ///
    /// # Specification
    /// - requires: `list` names the admitted `List`.
    /// - ensures: the returned identifier names a checked data declaration at
    ///   the environment's next position.
    /// - panics: if the block is refused.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a family nested through a strictly positive parameter
    ///   declares.
    /// - witness: `recursive_data::recursive_data::a_nested_occurrence_through_a_strictly_positive_parameter_declares`
    #[spec(captures: position = environment.entries().len(), ensures: |ret| usize::from(ret.position()) == position)]
    fn rose(
        environment: &mut Environment,
        list: ConstantIndex,
    ) -> CheckedId
    {
        let rose = ConstantIndex::from(environment.entries().len());
        let mut staging = environment.stage();
        let arena = staging.arena();
        let kind = arena.value_type_universe(GroundSort::Value, Level::zero());
        let own = arena.value_type_data(rose, vec![]);
        let code = arena.value_quote(own);
        let kids = arena.value_type_data(list, vec![code]);
        let declaration = staging.data(
            LevelSignature::monomorphic(),
            vec![],
            vec![vec![kids]],
            kind,
        );
        environment
            .add_decl(declaration)
            .expect("Rose nests through a strictly positive parameter")
    }

    /// `Rose`, `node : (kids : List ⌜Rose⌝)`, nests the family through
    /// `List`'s strictly positive parameter: the block declares, and a node
    /// with no children is a rose.
    #[test]
    fn a_nested_occurrence_through_a_strictly_positive_parameter_declares()
    {
        let mut environment = Environment::new();
        let list = list(&mut environment).position();
        let rose = rose(&mut environment, list).position();
        let mut staging = environment.stage();
        let arena = staging.arena();
        let own = arena.value_type_data(rose, vec![]);
        let code = arena.value_quote(own);
        let kids = arena.value_type_data(list, vec![code]);
        let none = arena.value_constructor(kids, ConstructorTag::from(0), vec![]);
        let sprig = arena.value_constructor(own, ConstructorTag::from(0), vec![none]);
        let declaration = staging.def(LevelSignature::monomorphic(), own, sprig);
        let defined = environment.add_decl(declaration);
        assert!(defined.is_ok(), "{defined:?}");
    }

    /// `(force head) arguments…`, applied left to right.
    ///
    /// # Specification
    /// trivial.
    fn spine(
        arena: &mut TermArena,
        head: ValueId,
        arguments: &[ValueId],
    ) -> ComputationId
    {
        let forced = arena.computation_force(head);
        arguments.iter().fold(forced, |applied, &argument| {
            arena.computation_application(applied, argument)
        })
    }

    /// Admit `map : U (Π a. Π b. U (El a → F (El b)) → List a → F (List b))`,
    /// `λa λb λg. fix m. λxs. case xs { nil ↦ return nil; cons ↦ λx λrest. y ←
    /// (force g) x; r ← (force m) rest; return (cons y r) }`.
    ///
    /// # Specification
    /// - requires: `list` names the admitted `List`.
    /// - ensures: the returned identifier names the admitted definition.
    /// - panics: if the kernel refuses it.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the generic map a rose tree's measure recurses
    ///   through.
    /// - witness: `recursive_data::recursive_data::a_type_parameter_instantiates_at_a_staged_code`
    #[spec(captures: position = environment.entries().len(), ensures: |ret| usize::from(ret.position()) == position)]
    fn map(
        environment: &mut Environment,
        list: ConstantIndex,
    ) -> CheckedId
    {
        let mut staging = environment.stage();
        let arena = staging.arena();
        let kind = arena.value_type_universe(GroundSort::Value, Level::zero());
        let declared = {
            // Under Π a Π b: `a` 1, `b` 0.
            let a = arena.value_variable(DeBruijnIndex::from(1));
            let b = arena.value_variable(DeBruijnIndex::from(0));
            let source = arena.value_type_element(a, Level::zero());
            let target = arena.value_type_element(b, Level::zero());
            let into = arena.comp_type_returner(target);
            let step = arena.comp_type_arrow(source, into);
            let step = arena.value_type_thunk(step);
            let from = arena.value_type_data(list, vec![a]);
            let to = arena.value_type_data(list, vec![b]);
            let into_list = arena.comp_type_returner(to);
            let last = arena.comp_type_arrow(from, into_list);
            let middle = arena.comp_type_arrow(step, last);
            let inner = arena.comp_type_pi(kind, middle);
            let outer = arena.comp_type_pi(kind, inner);
            arena.value_type_thunk(outer)
        };
        // Under λxs: `xs` 0, `m` 1, `g` 2, `b` 3, `a` 4; the motive binds the
        // scrutinee once more.
        let motive = {
            let b = arena.value_variable(DeBruijnIndex::from(4));
            let to = arena.value_type_data(list, vec![b]);
            arena.comp_type_returner(to)
        };
        let on_nil = {
            let b = arena.value_variable(DeBruijnIndex::from(3));
            let to = arena.value_type_data(list, vec![b]);
            let nil = arena.value_constructor(to, ConstructorTag::from(0), vec![]);
            arena.computation_return(nil)
        };
        let on_cons = {
            // Under λx λrest: `rest` 0, `x` 1, `m` 3, `g` 4.
            let head = arena.value_variable(DeBruijnIndex::from(1));
            let mapped = call(arena, DeBruijnIndex::from(4), head);
            // Under `y`: `rest` 1, `m` 4.
            let rest = arena.value_variable(DeBruijnIndex::from(1));
            let recursed = call(arena, DeBruijnIndex::from(4), rest);
            // Under `r`: `r` 0, `y` 1, `b` 7.
            let element = arena.value_variable(DeBruijnIndex::from(7));
            let to = arena.value_type_data(list, vec![element]);
            let image = arena.value_variable(DeBruijnIndex::from(1));
            let images = arena.value_variable(DeBruijnIndex::from(0));
            let cons = arena.value_constructor(to, ConstructorTag::from(1), vec![image, images]);
            let returned = arena.computation_return(cons);
            let inner = arena.computation_bind(recursed, returned);
            let outer = arena.computation_bind(mapped, inner);
            let rest_lambda = arena.computation_lambda(outer);
            arena.computation_lambda(rest_lambda)
        };
        let xs = arena.value_variable(DeBruijnIndex::from(0));
        let case = arena.computation_data_case(xs, motive, vec![on_nil, on_cons]);
        let lambda = arena.computation_lambda(case);
        let fixpoint = arena.computation_fixpoint(lambda, FixpointEvidence::StructuralDescent);
        let g_lambda = arena.computation_lambda(fixpoint);
        let b_lambda = arena.computation_lambda(g_lambda);
        let a_lambda = arena.computation_lambda(b_lambda);
        let value = arena.value_thunk(a_lambda);
        let declaration = staging.def(LevelSignature::monomorphic(), declared, value);
        environment
            .add_decl(declaration)
            .expect("map descends on its list")
    }

    /// What a rose tree's measure hands `map` beside its own claim.
    #[derive(Clone, Copy, Debug, Eq, PartialEq)]
    enum Children
    {
        /// The node's own field, at the stage the case bound it.
        Field,
        /// A one-element list of the node itself, at the plain `List ⌜Rose⌝`.
        Forged,
    }

    /// Offer `size : U (Rose → F Nat)`, `fix s. λt. case t { node ↦ λkids. _ ←
    /// (force map) ⌜Rose⌝ ⌜Nat⌝ s children; return 1 }`: the claim handed to
    /// `map` is the self binder, as a source's unapplied claim lowers, and the
    /// codes the plain ones a source writes.
    ///
    /// # Specification
    /// - requires: `nat`, `list`, `rose` and `map` name the admitted
    ///   declarations of those names.
    /// - ensures: admitted exactly for the node's own field.
    /// - panics: none.
    ///
    /// # Errors
    /// The kernel's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the field and the forged list differ in the one
    ///   argument whose type stages `map`'s element.
    /// - witness: `recursive_data::recursive_data::a_type_parameter_instantiates_at_a_staged_code`
    /// - witness: `recursive_data::recursive_data::a_claim_at_the_scrutinee_through_map_is_refused`
    #[spec(ensures: |ret| ret.is_ok() == (children == Children::Field))]
    fn size(
        environment: &mut Environment,
        (nat, list, rose, map): (ConstantIndex, ConstantIndex, ConstantIndex, ConstantIndex),
        children: Children,
    ) -> Result<CheckedId, KernelError>
    {
        let mut staging = environment.stage();
        let arena = staging.arena();
        let nat_type = arena.value_type_data(nat, vec![]);
        let rose_type = arena.value_type_data(rose, vec![]);
        let returner = arena.comp_type_returner(nat_type);
        let classifier = arena.comp_type_arrow(rose_type, returner);
        let rose_code = arena.value_quote(rose_type);
        let nat_code = arena.value_quote(nat_type);
        let zero = arena.value_constructor(nat_type, ConstructorTag::from(0), vec![]);
        let one = arena.value_constructor(nat_type, ConstructorTag::from(1), vec![zero]);
        let counted = arena.computation_return(one);
        // The node's arm under `kids` 0, `t` 1, `s` 2.
        let listed = match children {
            Children::Field => arena.value_variable(DeBruijnIndex::from(0)),
            Children::Forged => {
                let kids = arena.value_type_data(list, vec![rose_code]);
                let nil = arena.value_constructor(kids, ConstructorTag::from(0), vec![]);
                let node = arena.value_variable(DeBruijnIndex::from(1));
                arena.value_constructor(kids, ConstructorTag::from(1), vec![node, nil])
            },
        };
        let claim = arena.value_variable(DeBruijnIndex::from(2));
        let head = arena.value_constant(map);
        let mapped = spine(arena, head, &[rose_code, nat_code, claim, listed]);
        let on_node = arena.computation_bind(mapped, counted);
        let on_node = arena.computation_lambda(on_node);
        let node = arena.value_variable(DeBruijnIndex::from(0));
        let case = arena.computation_data_case(node, returner, vec![on_node]);
        let lambda = arena.computation_lambda(case);
        let fixpoint = arena.computation_fixpoint(lambda, FixpointEvidence::StructuralDescent);
        let declared = arena.value_type_thunk(classifier);
        let value = arena.value_thunk(fixpoint);
        let declaration = staging.def(LevelSignature::monomorphic(), declared, value);
        environment.add_decl(declaration)
    }

    /// Admit `apply_at : U (Π a. Π b. U (El a → F (El b)) → El a → F (El b))`,
    /// `λa λb λf λx. (force f) x`: a function applied at one type parameter.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the returned identifier names the admitted definition.
    /// - panics: if the kernel refuses it.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the generic helper a recursion hands its claim and
    ///   its argument to.
    /// - witness: `recursive_data::recursive_data::a_type_parameter_instantiates_at_a_staged_code`
    #[spec(captures: position = environment.entries().len(), ensures: |ret| usize::from(ret.position()) == position)]
    fn apply_at(environment: &mut Environment) -> CheckedId
    {
        let mut staging = environment.stage();
        let arena = staging.arena();
        let kind = arena.value_type_universe(GroundSort::Value, Level::zero());
        // Under Π a Π b: `a` 1, `b` 0.
        let a = arena.value_variable(DeBruijnIndex::from(1));
        let b = arena.value_variable(DeBruijnIndex::from(0));
        let source = arena.value_type_element(a, Level::zero());
        let target = arena.value_type_element(b, Level::zero());
        let into = arena.comp_type_returner(target);
        let function = arena.comp_type_arrow(source, into);
        let thunked = arena.value_type_thunk(function);
        let applying = arena.comp_type_arrow(thunked, function);
        let inner = arena.comp_type_pi(kind, applying);
        let outer = arena.comp_type_pi(kind, inner);
        let declared = arena.value_type_thunk(outer);
        // Under λa λb λf λx: `x` 0, `f` 1.
        let argument = arena.value_variable(DeBruijnIndex::from(0));
        let called = call(arena, DeBruijnIndex::from(1), argument);
        let value = (0_u8 .. 4).fold(called, |body, _binder| arena.computation_lambda(body));
        let value = arena.value_thunk(value);
        let declaration = staging.def(LevelSignature::monomorphic(), declared, value);
        environment
            .add_decl(declaration)
            .expect("apply_at checks without a fixpoint")
    }

    /// Offer `count : U (Nat → F Nat)`, `fix c. λn. case n { zero ↦ return
    /// zero; succ ↦ λp. (force apply_at) ⌜Nat⌝ ⌜Nat⌝ c v }`, `v` the variable
    /// `handed` under `p` 0, `n` 1, `c` 2.
    ///
    /// # Specification
    /// - requires: `nat` and `apply_at` name the admitted declarations of those
    ///   names.
    /// - ensures: admitted exactly for the predecessor `p`.
    /// - panics: none.
    ///
    /// # Errors
    /// The kernel's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the predecessor and the parameter differ in the stage
    ///   they instantiate `apply_at`'s parameter at.
    /// - witness: `recursive_data::recursive_data::a_type_parameter_instantiates_at_a_staged_code`
    /// - witness: `recursive_data::recursive_data::a_claim_at_the_scrutinee_through_map_is_refused`
    #[spec(ensures: |ret| ret.is_ok() == (handed == DeBruijnIndex::from(0)))]
    fn count(
        environment: &mut Environment,
        (nat, apply_at): (ConstantIndex, ConstantIndex),
        handed: DeBruijnIndex,
    ) -> Result<CheckedId, KernelError>
    {
        let mut staging = environment.stage();
        let arena = staging.arena();
        let nat_type = arena.value_type_data(nat, vec![]);
        let returner = arena.comp_type_returner(nat_type);
        let classifier = arena.comp_type_arrow(nat_type, returner);
        let nat_code = arena.value_quote(nat_type);
        let zero = arena.value_constructor(nat_type, ConstructorTag::from(0), vec![]);
        let returned = arena.computation_return(zero);
        let claim = arena.value_variable(DeBruijnIndex::from(2));
        let handed = arena.value_variable(handed);
        let head = arena.value_constant(apply_at);
        let counted = spine(arena, head, &[nat_code, nat_code, claim, handed]);
        let on_successor = arena.computation_lambda(counted);
        let body = case_on_argument(arena, returner, returned, on_successor);
        let fixpoint = arena.computation_fixpoint(body, FixpointEvidence::StructuralDescent);
        let declared = arena.value_type_thunk(classifier);
        let value = arena.value_thunk(fixpoint);
        let declaration = staging.def(LevelSignature::monomorphic(), declared, value);
        environment.add_decl(declaration)
    }

    /// A type argument is the plain code on the wire, and the kernel
    /// re-derives its stage from the argument that holds it: a rose tree's
    /// children instantiate `map`'s element at their stage, and a predecessor
    /// `apply_at`'s parameter at its own, so the claim handed beside them takes
    /// them (#393).
    #[test]
    fn a_type_parameter_instantiates_at_a_staged_code()
    {
        let mut environment = Environment::new();
        let nat = nat(&mut environment).position();
        let list = list(&mut environment).position();
        let rose = rose(&mut environment, list).position();
        let map = map(&mut environment, list).position();
        let sized = size(&mut environment, (nat, list, rose, map), Children::Field);
        assert!(sized.is_ok(), "{sized:?}");
        let apply_at = apply_at(&mut environment).position();
        let counted = count(&mut environment, (nat, apply_at), DeBruijnIndex::from(0));
        assert!(counted.is_ok(), "{counted:?}");
    }

    /// The node itself in a list of its own holds it at no stage, so `map`'s
    /// element stays the plain code and the claim refuses at the top; the
    /// parameter itself handed to `apply_at` instantiates it at the parameter's
    /// own stage, which the claim's bound does not reach.
    #[test]
    fn a_claim_at_the_scrutinee_through_map_is_refused()
    {
        let mut environment = Environment::new();
        let nat = nat(&mut environment).position();
        let list = list(&mut environment).position();
        let rose = rose(&mut environment, list).position();
        let map = map(&mut environment, list).position();
        let root = Stage::At(StageId::from(0_usize));
        assert_eq!(
            size(&mut environment, (nat, list, rose, map), Children::Forged).map(drop),
            Err(KernelError::StageNotBelow {
                found: Standing::Top,
                bound: below(root),
            })
        );
        let apply_at = apply_at(&mut environment).position();
        assert_eq!(
            count(&mut environment, (nat, apply_at), DeBruijnIndex::from(1)).map(drop),
            Err(KernelError::StageNotBelow {
                found: Standing::Staged(root),
                bound: below(root),
            })
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

    /// Admit `Empty` and `T = Mk (U (Empty → F T))`, then offer `fix rec. λt.
    /// (force rec) (Mk (thunk (λx. fix y. force y)))` at `T → F T` claiming
    /// `evidence`, the inner fixpoint partial.
    ///
    /// # Specification
    /// trivial.
    fn thunked_call(
        environment: &mut Environment,
        evidence: FixpointEvidence,
    ) -> Result<CheckedId, KernelError>
    {
        let empty = ConstantIndex::from(environment.entries().len());
        let mut staging = environment.stage();
        let arena = staging.arena();
        let kind = arena.value_type_universe(GroundSort::Value, Level::zero());
        let declaration = staging.data(LevelSignature::monomorphic(), vec![], vec![], kind);
        let _empty = environment.add_decl(declaration)?;
        let position = ConstantIndex::from(environment.entries().len());
        let mut staging = environment.stage();
        let arena = staging.arena();
        let empty_type = arena.value_type_data(empty, vec![]);
        let own = arena.value_type_data(position, vec![]);
        let into = arena.comp_type_returner(own);
        let branch = arena.comp_type_arrow(empty_type, into);
        let field = arena.value_type_thunk(branch);
        let kind = arena.value_type_universe(GroundSort::Value, Level::zero());
        let declaration = staging.data(
            LevelSignature::monomorphic(),
            vec![],
            vec![vec![field]],
            kind,
        );
        let _family = environment.add_decl(declaration)?;
        let mut staging = environment.stage();
        let arena = staging.arena();
        let own = arena.value_type_data(position, vec![]);
        let into = arena.comp_type_returner(own);
        let arrow = arena.comp_type_arrow(own, into);
        // Under λx, fix y: `y` 0.
        let y = arena.value_variable(DeBruijnIndex::from(0));
        let forced = arena.computation_force(y);
        let diverging = arena.computation_fixpoint(forced, FixpointEvidence::Partial);
        let lambda = arena.computation_lambda(diverging);
        let thunked = arena.value_thunk(lambda);
        let built = arena.value_constructor(own, ConstructorTag::from(0), vec![thunked]);
        // Under λt: `t` 0, `rec` 1.
        let called = call(arena, DeBruijnIndex::from(1), built);
        let body = arena.computation_lambda(called);
        let fixpoint = arena.computation_fixpoint(body, evidence);
        let declared = arena.value_type_thunk(arrow);
        let value = arena.value_thunk(fixpoint);
        let declaration = staging.def(LevelSignature::monomorphic(), declared, value);
        environment.add_decl(declaration)
    }

    #[test]
    fn a_thunked_field_shows_no_value_below_the_stage_598()
    {
        // #598: `Mk`'s one recursive field is thunked, and the thunk never
        // returns, so `Mk (…)` holds no value below the stage and nothing in
        // scope shows the stage is above the first: `rec (Mk …)` calls itself
        // forever.
        let mut environment = Environment::new();
        let root = Stage::At(StageId::from(0_usize));
        assert_eq!(
            thunked_call(&mut environment, FixpointEvidence::StructuralDescent).map(|_admitted| ()),
            Err(KernelError::StageNotBelow {
                found: Standing::Top,
                bound: below(root),
            })
        );
        let mut environment = Environment::new();
        thunked_call(&mut environment, FixpointEvidence::Partial)
            .expect("a fixpoint without a claim checks as partial");
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

    /// Where the second constructor of a universe names its decoder.
    #[derive(Clone, Copy, Debug, Eq, PartialEq)]
    enum Decoded
    {
        /// `PiC : (a : U, b : U (El(el a) → F U))`: at the field before, one
        /// stage below the decoder's.
        Below,
        /// `Odd : (b : U (El(el base) → F U))`, `base : U` a definition after
        /// the decoder: at a code no case put below the decoder's stage.
        Level,
        /// `Neg : (b : U (Lift U → F 1))`: no decoder, the family lifted
        /// under a domain, which no stage reaches.
        Negative,
    }

    /// Offer a universe `U` — `NatC`, and a second constructor `decoded`
    /// names — and its decoder `el : U (U → F Type)`, `fix self. λu. case u
    /// of { NatC ↦ return ⌜1⌝; _ ↦ λ…. return ⌜1⌝ }`, as one block; for
    /// [`Decoded::Level`], with `base = NatC` after the decoder.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the kernel's verdict on the block, which leaves the
    ///   environment as it was on a refusal.
    /// - panics: none.
    ///
    /// # Errors
    /// The kernel's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the three blocks differ only in the second
    ///   constructor's fields, so each verdict is that field's.
    /// - witness: `recursive_data::recursive_data::a_mutual_block_is_admitted`
    /// - witness: `recursive_data::recursive_data::a_mutual_block_is_refused_whole`
    #[spec(captures: before = environment.entries().len(), ensures: |ret| ret.as_ref().map_or_else(
        |_| environment.entries().len() == before,
        |ids| ids.len() >= 2 && environment.entries().len() == before.saturating_add(ids.len()),
    ))]
    fn universe(
        environment: &mut Environment,
        decoded: Decoded,
    ) -> Result<Vec<CheckedId>, KernelError>
    {
        let family = ConstantIndex::from(environment.entries().len());
        let decoder = ConstantIndex::from(usize::from(family).saturating_add(1));
        let base = ConstantIndex::from(usize::from(family).saturating_add(2));
        let mut staging = environment.stage();
        let arena = staging.arena();
        let kind = arena.value_type_universe(GroundSort::Value, Level::zero());
        let own = arena.value_type_data(family, vec![]);
        let returner = arena.comp_type_returner(own);
        let named = arena.value_constant(decoder);
        let forced = arena.computation_force(named);
        let decoding = |arena: &mut TermArena, argument: ValueId| {
            let call = arena.computation_application(forced, argument);
            let code = arena.value_returned(call);
            let decoded = arena.value_type_element(code, Level::zero());
            let arrow = arena.comp_type_arrow(decoded, returner);
            arena.value_type_thunk(arrow)
        };
        let fields = match decoded {
            Decoded::Below => {
                let earlier = arena.value_variable(DeBruijnIndex::from(0));
                vec![own, decoding(arena, earlier)]
            },
            Decoded::Level => {
                let named = arena.value_constant(base);
                vec![decoding(arena, named)]
            },
            Decoded::Negative => {
                let unit = arena.value_type_unit();
                let into = arena.comp_type_returner(unit);
                let lifted = arena.value_type_lift(own, Level::zero());
                let arrow = arena.comp_type_arrow(lifted, into);
                vec![arena.value_type_thunk(arrow)]
            },
        };
        let arity = fields.len();
        let universe = staging.data(
            LevelSignature::monomorphic(),
            vec![],
            vec![vec![], fields],
            kind,
        );
        let mut staging = environment.stage();
        let arena = staging.arena();
        let own = arena.value_type_data(family, vec![]);
        let types = arena.value_type_universe(GroundSort::Value, Level::zero());
        let returns = arena.comp_type_returner(types);
        let classifier = arena.comp_type_arrow(own, returns);
        let declared = arena.value_type_thunk(classifier);
        let unit = arena.value_type_unit();
        let code = arena.value_quote(unit);
        let answer = arena.computation_return(code);
        let mut arm = answer;
        for _field in 0 .. arity {
            arm = arena.computation_lambda(arm);
        }
        let body = case_on_argument(arena, returns, answer, arm);
        let fixpoint = arena.computation_fixpoint(body, FixpointEvidence::StructuralDescent);
        let value = arena.value_thunk(fixpoint);
        let decoding = staging.def(LevelSignature::monomorphic(), declared, value);
        let mut members = vec![universe, decoding];
        if decoded == Decoded::Level {
            let mut staging = environment.stage();
            let arena = staging.arena();
            let own = arena.value_type_data(family, vec![]);
            let nat_code = arena.value_constructor(own, ConstructorTag::from(0), vec![]);
            members.push(staging.def(LevelSignature::monomorphic(), own, nat_code));
        }
        environment.add_block(members)
    }

    /// A universe whose constructor names its decoder at the field before is
    /// admitted with the decoder as one block, the decoder's case reading its
    /// own constant in the field as its self binder; an artifact of the block
    /// replays.
    #[test]
    fn a_mutual_block_is_admitted()
    {
        let mut environment = Environment::new();
        let admitted = universe(&mut environment, Decoded::Below).expect("the block is admitted");
        assert_eq!(
            admitted
                .iter()
                .map(|id| usize::from(id.position()))
                .collect::<Vec<_>>(),
            vec![0, 1]
        );
        let marked = environment
            .entries()
            .iter()
            .map(|entry| {
                gandr_kernel_term::MarkedDeclaration::new(
                    gandr_kernel_term::AdmissionMark::Checked,
                    entry.declaration().clone(),
                )
            })
            .collect::<Vec<_>>();
        let replayed = Environment::replay(environment.arena().clone(), &marked)
            .expect("the block replays as one");
        assert_eq!(replayed.entries().len(), 2);
    }

    /// A block one member of which is refused is refused whole, the
    /// environment unchanged: the decoder at a place that does not descend
    /// below its own stage, and the family lifted under a function's domain.
    #[test]
    fn a_mutual_block_is_refused_whole()
    {
        let mut environment = Environment::new();
        let level = universe(&mut environment, Decoded::Level);
        assert!(
            matches!(level, Err(KernelError::StageNotBelow { .. })),
            "{level:?}"
        );
        let negative = universe(&mut environment, Decoded::Negative);
        assert!(
            matches!(negative, Err(KernelError::NegativeOccurrence(_))),
            "{negative:?}"
        );
        assert!(environment.entries().is_empty());
    }

    /// A family named through a definition of its block stands where the
    /// definition is named: `Bad` holding `U (hidden → F 1)` with `hidden =
    /// Bad` is refused as `Bad` holding `U (Bad → F 1)` is, the walk reading
    /// the definition's body, and the environment is unchanged (#602).
    #[test]
    fn a_definition_of_the_block_is_read_through_602()
    {
        let mut environment = Environment::new();
        let family = ConstantIndex::from(0_usize);
        let hidden = ConstantIndex::from(1_usize);
        let mut staging = environment.stage();
        let arena = staging.arena();
        let kind = arena.value_type_universe(GroundSort::Value, Level::zero());
        let named = arena.value_constant(hidden);
        let decoded = arena.value_type_element(named, Level::zero());
        let unit = arena.value_type_unit();
        let into = arena.comp_type_returner(unit);
        let arrow = arena.comp_type_arrow(decoded, into);
        let consumer = arena.value_type_thunk(arrow);
        let bad = staging.data(
            LevelSignature::monomorphic(),
            vec![],
            vec![vec![consumer]],
            kind,
        );
        let mut staging = environment.stage();
        let arena = staging.arena();
        let types = arena.value_type_universe(GroundSort::Value, Level::zero());
        let own = arena.value_type_data(family, vec![]);
        let quoted = arena.value_quote(own);
        let naming = staging.def(LevelSignature::monomorphic(), types, quoted);
        let verdict = environment.add_block(vec![bad, naming]);
        assert_eq!(
            verdict,
            Err(KernelError::NegativeOccurrence(OccurrenceSite::Field {
                tag: ConstructorTag::from(0_usize),
                field: FieldPosition::from(0_usize),
            }))
        );
        assert!(environment.entries().is_empty());
    }

    /// Where a rose tree's recursion over its block's two families calls
    /// itself.
    #[derive(Clone, Copy, Debug, Eq, PartialEq)]
    enum Rose
    {
        /// At the node's list of children, and a list's head and tail: each a
        /// field one stage below its scrutinee.
        Below,
        /// At the node itself: the scrutinee, at the fixpoint's own stage.
        Level,
    }

    /// Admit `Rose`, `Node : (kids : Forest) → Rose`, and `Forest`, `Nil`
    /// and `Cons : (head : Rose, tail : Forest) → Forest`, as one block; then
    /// offer the recursion over both, `fix self. λx. case x of { t ↦ case t of
    /// { Node ↦ λkids. self (inr kids) }; ts ↦ case ts of { Nil ↦ return ();
    /// Cons ↦ λhead tail. _ ← self (inl head); self (inr tail) } }`, at
    /// `U (Rose + Forest → F 1)`, `rose` naming where the node's arm calls.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the kernel's verdict on the block, then on the recursion,
    ///   admitted at the position after the block's two families.
    /// - panics: none.
    ///
    /// # Errors
    /// The kernel's refusal of the block or of the recursion.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the two recursions differ only in the node arm's
    ///   argument, so each verdict is that argument's stage.
    /// - witness: `recursive_data::recursive_data::a_mutual_recursion_descends_through_its_block_s_families`
    #[spec(ensures: |ret| ret.as_ref().map_or_else(|_| true, |id| usize::from(id.position()) == 2))]
    fn forest(rose: Rose) -> Result<CheckedId, KernelError>
    {
        let mut environment = Environment::new();
        let tree = ConstantIndex::from(0_usize);
        let forest = ConstantIndex::from(1_usize);
        let mut staging = environment.stage();
        let arena = staging.arena();
        let kind = arena.value_type_universe(GroundSort::Value, Level::zero());
        let forests = arena.value_type_data(forest, vec![]);
        let node = staging.data(
            LevelSignature::monomorphic(),
            vec![],
            vec![vec![forests]],
            kind,
        );
        let mut staging = environment.stage();
        let arena = staging.arena();
        let kind = arena.value_type_universe(GroundSort::Value, Level::zero());
        let trees = arena.value_type_data(tree, vec![]);
        let forests = arena.value_type_data(forest, vec![]);
        let list = staging.data(
            LevelSignature::monomorphic(),
            vec![],
            vec![vec![], vec![trees, forests]],
            kind,
        );
        let _block = environment.add_block(vec![node, list])?;
        let mut staging = environment.stage();
        let arena = staging.arena();
        let trees = arena.value_type_data(tree, vec![]);
        let forests = arena.value_type_data(forest, vec![]);
        let unit = arena.value_type_unit();
        let returns = arena.comp_type_returner(unit);
        // `force self (inj v)`, `self` the variable at `own`.
        let call = |arena: &mut TermArena, own: u32, summand: usize, argument: u32| {
            let head = arena.value_variable(DeBruijnIndex::from(own));
            let forced = arena.computation_force(head);
            let argument = arena.value_variable(DeBruijnIndex::from(argument));
            let injected =
                arena.value_injection(gandr_kernel_term::Summand::from(summand), argument);
            arena.computation_application(forced, injected)
        };
        // Under `self, x, t, kids`: the children, or the node `t` itself.
        let node_arm = match rose {
            Rose::Below => call(arena, 3, 1, 0),
            Rose::Level => call(arena, 3, 0, 1),
        };
        let node_arm = arena.computation_lambda(node_arm);
        let scrutinee = arena.value_variable(DeBruijnIndex::from(0_u32));
        let on_tree = arena.computation_data_case(scrutinee, returns, vec![node_arm]);
        let unit_value = arena.value_unit();
        let on_nil = arena.computation_return(unit_value);
        // Under `self, x, ts, head, tail`, then the bind's binder.
        let on_head = call(arena, 4, 0, 1);
        let on_tail = call(arena, 5, 1, 1);
        let on_cons = arena.computation_bind(on_head, on_tail);
        let on_cons = arena.computation_lambda(on_cons);
        let on_cons = arena.computation_lambda(on_cons);
        let scrutinee = arena.value_variable(DeBruijnIndex::from(0_u32));
        let on_forest = arena.computation_data_case(scrutinee, returns, vec![on_nil, on_cons]);
        let scrutinee = arena.value_variable(DeBruijnIndex::from(0_u32));
        let cased = arena.computation_case(scrutinee, &[on_tree, on_forest]);
        let body = arena.computation_lambda(cased);
        let fixpoint = arena.computation_fixpoint(body, FixpointEvidence::StructuralDescent);
        let value = arena.value_thunk(fixpoint);
        let both = arena.value_type_sum(&[trees, forests]);
        let arrow = arena.comp_type_arrow(both, returns);
        let declared = arena.value_type_thunk(arrow);
        let size = staging.def(LevelSignature::monomorphic(), declared, value);
        environment.add_decl(size)
    }

    /// A recursion at the sum of a mutual block's two families opens one
    /// stage for both: a node's children and a list's head and tail each
    /// stand one stage below their scrutinee, so the calls on them are
    /// admitted, and a call on the node itself is refused.
    #[test]
    fn a_mutual_recursion_descends_through_its_block_s_families()
    {
        let below = forest(Rose::Below);
        assert!(below.is_ok(), "{below:?}");
        let level = forest(Rose::Level);
        assert!(
            matches!(level, Err(KernelError::StageNotBelow { .. })),
            "{level:?}"
        );
    }
}
