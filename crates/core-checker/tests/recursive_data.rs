//! Recursive data, fixpoints and derived eliminators through the checker, the
//! normaliser and the kernel.

extern crate alloc;

#[cfg(test)]
mod recursive_data
{
    use alloc::collections::BTreeMap;
    use alloc::sync::Arc;

    use anodized::spec;
    use gandr_core_checker::CheckBudget;
    use gandr_core_checker::CheckRefusal;
    use gandr_core_checker::CheckingContext;
    use gandr_core_checker::CheckingForm;
    use gandr_core_checker::Declaration;
    use gandr_core_checker::ModuleReport;
    use gandr_core_checker::OriginToken;
    use gandr_core_checker::Verdict;
    use gandr_core_checker::bridge;
    use gandr_core_checker::bridge::Outcome;
    use gandr_core_checker::check_module;
    use gandr_core_checker::eliminator;
    use gandr_core_checker::eliminator::DerivationRefusal;
    use gandr_core_nbe::Definitions;
    use gandr_core_nbe::DomainArena;
    use gandr_core_nbe::Fuel;
    use gandr_core_nbe::LoweredChain;
    use gandr_core_nbe::MachineSettings;
    use gandr_core_nbe::MachineVerdict;
    use gandr_core_nbe::Problem;
    use gandr_core_nbe::ReadbackMode;
    use gandr_core_nbe::ResharingMemo;
    use gandr_core_nbe::TraceNode;
    use gandr_core_term::Binders;
    use gandr_core_term::CertificateEquality;
    use gandr_core_term::CompTypeId;
    use gandr_core_term::ComputationId;
    use gandr_core_term::CoreArena;
    use gandr_core_term::DataSignature;
    use gandr_core_term::DefinitionChain;
    use gandr_core_term::DefinitionalEnvironment;
    use gandr_core_term::Sort;
    use gandr_core_term::Transparency;
    use gandr_core_term::ValueId;
    use gandr_core_term::ValueTypeId;
    use gandr_core_term::Zone;
    use gandr_kernel_conversion_trace::ConversionDecision;
    use gandr_kernel_conversion_trace::TraceLog;
    use gandr_kernel_core::EngineClaim;
    use gandr_kernel_core::Environment;
    use gandr_kernel_core::KernelError;
    use gandr_kernel_core::KernelVerdict;
    use gandr_kernel_core::ReplayBudget;
    use gandr_kernel_core::ReplayNode;
    use gandr_kernel_core::ReplaySides;
    use gandr_kernel_core::Unfoldable;
    use gandr_kernel_core::Unfoldings;
    use gandr_kernel_strata::Level;
    use gandr_kernel_term::ConstantIndex;
    use gandr_kernel_term::ConstructorTag;
    use gandr_kernel_term::DeBruijnIndex;
    use gandr_kernel_term::DescentRefusal;
    use gandr_kernel_term::FieldPosition;
    use gandr_kernel_term::FixpointEvidence;
    use gandr_kernel_term::GlobalIndex;
    use gandr_kernel_term::GroundSort;
    use gandr_kernel_term::LevelSignature;
    use gandr_kernel_term::OccurrenceSite;
    use gandr_kernel_term::ParameterPosition;
    use quenchant_shape::shape::Maybe;

    /// The admission positions of the program module.
    mod at
    {
        /// `Nat`: `zero`, `succ Nat`.
        pub(super) const NAT: usize = 0;
        /// `List A`: `nil`, `cons (El A) (List A)`.
        pub(super) const LIST: usize = 1;
        /// `Tree`: `leaf`, `node (U (Nat → F Tree))`.
        pub(super) const TREE: usize = 2;
        /// `IsNat (n : Nat)`: `here`.
        pub(super) const IS_NAT: usize = 3;
        /// `IsTree (t : Tree)`: `here`.
        pub(super) const IS_TREE: usize = 4;
        /// `elim_Nat[Nat → F Nat]`.
        pub(super) const ELIM_NAT_FUNCTION: usize = 5;
        /// `plus : Nat → Nat → F Nat`.
        pub(super) const PLUS: usize = 6;
        /// `elim_List[F Nat]`.
        pub(super) const ELIM_LIST_NAT: usize = 7;
        /// `length : Π A. List A → F Nat`.
        pub(super) const LENGTH: usize = 8;
        /// `elim_List[List A → F (List A)]`.
        pub(super) const ELIM_LIST_APPEND: usize = 9;
        /// `append : Π A. List A → List A → F (List A)`.
        pub(super) const APPEND: usize = 10;
        /// `elim_List[Π B. U (El A → F (El B)) → F (List B)]`.
        pub(super) const ELIM_LIST_MAP: usize = 11;
        /// `map : Π A B. U (El A → F (El B)) → List A → F (List B)`.
        pub(super) const MAP: usize = 12;
        /// `elim_Tree[F Nat]`.
        pub(super) const ELIM_TREE: usize = 13;
        /// `depth : Tree → F Nat`, along the branches at `zero`.
        pub(super) const DEPTH: usize = 14;
        /// `elim_Nat[F (IsNat x)]`, at a motive that names its scrutinee.
        pub(super) const ELIM_NAT_DEPENDENT: usize = 15;
        /// `witness : Π n. F (IsNat n)`.
        pub(super) const WITNESS: usize = 16;
    }

    /// A data declaration at its source position.
    ///
    /// # Specification
    /// trivial.
    fn data(
        constant: ConstantIndex,
        signature: DataSignature,
    ) -> Declaration
    {
        Declaration::data(constant, Arc::new(signature), origin(constant))
    }

    /// The origin a declaration at `constant` carries.
    ///
    /// # Specification
    /// trivial.
    fn origin(constant: ConstantIndex) -> OriginToken
    {
        OriginToken::from(usize::from(constant))
    }

    /// A definition at its source position.
    ///
    /// # Specification
    /// trivial.
    fn definition(
        constant: ConstantIndex,
        declared: ValueTypeId,
        body: ValueId,
    ) -> Declaration
    {
        Declaration::new(
            constant,
            Maybe::Present(declared),
            Maybe::Present(body),
            origin(constant),
        )
    }

    /// The intuitionistic variable at `index`.
    ///
    /// # Specification
    /// trivial.
    fn var(
        arena: &mut CoreArena,
        index: DeBruijnIndex,
    ) -> ValueId
    {
        arena.value_variable(Zone::Intuitionistic, index)
    }

    /// The universe of small value types.
    ///
    /// # Specification
    /// trivial.
    fn kind(arena: &mut CoreArena) -> ValueTypeId
    {
        arena.value_type_universe(Sort::Ground(GroundSort::Value), Level::zero())
    }

    /// `Nat`.
    ///
    /// # Specification
    /// trivial.
    fn nat(arena: &mut CoreArena) -> ValueTypeId
    {
        arena.value_type_data(ConstantIndex::from(at::NAT), vec![])
    }

    /// `List a`, at the element code `a`.
    ///
    /// # Specification
    /// trivial.
    fn list(
        arena: &mut CoreArena,
        element: ValueId,
    ) -> ValueTypeId
    {
        arena.value_type_data(ConstantIndex::from(at::LIST), vec![element])
    }

    /// The numerals zero through four, each as `succ (… zero)`.
    ///
    /// # Specification
    /// trivial.
    fn numerals(arena: &mut CoreArena) -> [ValueId; 5]
    {
        let nat = nat(arena);
        let zero = arena.value_constructor(nat, ConstructorTag::from(0_usize), vec![]);
        let one = arena.value_constructor(nat, ConstructorTag::from(1_usize), vec![zero]);
        let two = arena.value_constructor(nat, ConstructorTag::from(1_usize), vec![one]);
        let three = arena.value_constructor(nat, ConstructorTag::from(1_usize), vec![two]);
        let four = arena.value_constructor(nat, ConstructorTag::from(1_usize), vec![three]);
        [zero, one, two, three, four]
    }

    /// The list of `elements` at the element code `code`.
    ///
    /// # Specification
    /// trivial.
    fn list_of(
        arena: &mut CoreArena,
        code: ValueId,
        elements: &[ValueId],
    ) -> ValueId
    {
        let datatype = list(arena, code);
        let mut built = arena.value_constructor(datatype, ConstructorTag::from(0_usize), vec![]);
        for &element in elements.iter().rev() {
            built = arena.value_constructor(datatype, ConstructorTag::from(1_usize), vec![
                element, built,
            ]);
        }
        built
    }

    /// `(force head) arguments…`.
    ///
    /// # Specification
    /// trivial.
    fn call(
        arena: &mut CoreArena,
        head: ValueId,
        arguments: &[ValueId],
    ) -> ComputationId
    {
        let mut built = arena.computation_force(head);
        for &argument in arguments {
            built = arena.computation_application(built, argument);
        }
        built
    }

    /// `thunk (λ… body)` under `binders` lambdas.
    ///
    /// # Specification
    /// trivial.
    fn function(
        arena: &mut CoreArena,
        binders: Binders,
        body: ComputationId,
    ) -> ValueId
    {
        let mut built = body;
        for _binder in 0 .. u32::from(binders) {
            built = arena.computation_lambda(built);
        }
        arena.value_thunk(built)
    }

    /// A derived eliminator, declared at `constant`.
    ///
    /// # Specification
    /// - requires: `signature` is the one declared at `family`; `motive` is
    ///   scoped under its parameters and a scrutinee.
    /// - ensures: the eliminator's declaration.
    /// - panics: if the fold refuses.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — every eliminator of the program module is judged and
    ///   readmitted.
    /// - witness: `recursive_data::recursive_data::derived_eliminators_are_admitted_and_readmitted`
    #[spec(ensures: |ret| ret.constant() == constant)]
    fn derived(
        arena: &mut CoreArena,
        constant: ConstantIndex,
        family: ConstantIndex,
        signature: &DataSignature,
        motive: CompTypeId,
    ) -> Declaration
    {
        let derived = eliminator::derive(arena, family, signature, motive)
            .expect("the fold derives the eliminator");
        definition(constant, derived.declared(), derived.body())
    }

    /// The signatures of `Nat`, `List A`, `Tree`, `IsNat` and `IsTree`.
    ///
    /// # Specification
    /// trivial.
    fn signatures(arena: &mut CoreArena) -> [DataSignature; 5]
    {
        let kind = kind(arena);
        let nat = nat(arena);
        let element_code = var(arena, DeBruijnIndex::from(0));
        let element = arena.value_type_element(element_code, Level::zero());
        let tail = list(arena, element_code);
        let tree = arena.value_type_data(ConstantIndex::from(at::TREE), vec![]);
        let into_tree = arena.comp_type_returner(tree);
        let branches = arena.comp_type_arrow(nat, into_tree);
        let branches = arena.value_type_thunk(branches);
        [
            DataSignature::new(vec![], vec![vec![], vec![nat]], kind),
            DataSignature::new(vec![kind], vec![vec![], vec![element, tail]], kind),
            DataSignature::new(vec![], vec![vec![], vec![branches]], kind),
            DataSignature::new(vec![nat], vec![vec![]], kind),
            DataSignature::new(vec![tree], vec![vec![]], kind),
        ]
    }

    /// The program module: the three recursive families, two indexed by them,
    /// and `plus`, `length`, `append`, `map`, `depth` and a dependent
    /// `witness`, each written by its derived eliminator.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: one declaration per position of [`at`], in order.
    /// - panics: if a fold refuses.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the module is checked, normalised and readmitted by
    ///   the witnesses.
    /// - witness: `recursive_data::recursive_data::derived_eliminators_are_admitted_and_readmitted`
    #[spec(ensures: |ret| ret.len() == at::WITNESS + 1)]
    fn program(arena: &mut CoreArena) -> Vec<Declaration>
    {
        let [
            nat_signature,
            list_signature,
            tree_signature,
            is_nat_signature,
            is_tree_signature,
        ] = signatures(arena);
        let mut declarations = vec![
            data(ConstantIndex::from(at::NAT), nat_signature.clone()),
            data(ConstantIndex::from(at::LIST), list_signature.clone()),
            data(ConstantIndex::from(at::TREE), tree_signature.clone()),
            data(ConstantIndex::from(at::IS_NAT), is_nat_signature),
            data(ConstantIndex::from(at::IS_TREE), is_tree_signature),
        ];
        let nat = nat(arena);
        let returns_nat = arena.comp_type_returner(nat);
        let [zero, ..] = numerals(arena);

        // plus m n = elim_Nat[Nat → F Nat] (λk. k) (λp ih k. succ (ih k)) m n
        let nat_to_nat = arena.comp_type_arrow(nat, returns_nat);
        declarations.push(derived(
            arena,
            ConstantIndex::from(at::ELIM_NAT_FUNCTION),
            ConstantIndex::from(at::NAT),
            &nat_signature,
            nat_to_nat,
        ));
        let on_zero = {
            let k = var(arena, DeBruijnIndex::from(0));
            let returned = arena.computation_return(k);
            function(arena, Binders::from(1), returned)
        };
        let on_successor = {
            let hypothesis = var(arena, DeBruijnIndex::from(1));
            let k = var(arena, DeBruijnIndex::from(0));
            let recursive = call(arena, hypothesis, &[k]);
            let result = var(arena, DeBruijnIndex::from(0));
            let successor =
                arena.value_constructor(nat, ConstructorTag::from(1_usize), vec![result]);
            let returned = arena.computation_return(successor);
            let bound = arena.computation_bind(recursive, returned);
            function(arena, Binders::from(3), bound)
        };
        let plus_body = {
            let eliminator = arena.value_constant(ConstantIndex::from(at::ELIM_NAT_FUNCTION));
            let m = var(arena, DeBruijnIndex::from(1));
            let n = var(arena, DeBruijnIndex::from(0));
            let applied = call(arena, eliminator, &[on_zero, on_successor, m, n]);
            function(arena, Binders::from(2), applied)
        };
        let plus_type = {
            let inner = arena.comp_type_arrow(nat, returns_nat);
            let outer = arena.comp_type_arrow(nat, inner);
            arena.value_type_thunk(outer)
        };
        declarations.push(definition(
            ConstantIndex::from(at::PLUS),
            plus_type,
            plus_body,
        ));

        // length A xs = elim_List[F Nat] A zero (λa t ih. succ ih) xs
        declarations.push(derived(
            arena,
            ConstantIndex::from(at::ELIM_LIST_NAT),
            ConstantIndex::from(at::LIST),
            &list_signature,
            returns_nat,
        ));
        let on_nil = {
            let returned = arena.computation_return(zero);
            arena.value_thunk(returned)
        };
        let on_cons = {
            let hypothesis = var(arena, DeBruijnIndex::from(0));
            let recursive = arena.computation_force(hypothesis);
            let result = var(arena, DeBruijnIndex::from(0));
            let successor =
                arena.value_constructor(nat, ConstructorTag::from(1_usize), vec![result]);
            let returned = arena.computation_return(successor);
            let bound = arena.computation_bind(recursive, returned);
            function(arena, Binders::from(3), bound)
        };
        let length_body = {
            let eliminator = arena.value_constant(ConstantIndex::from(at::ELIM_LIST_NAT));
            let code = var(arena, DeBruijnIndex::from(1));
            let xs = var(arena, DeBruijnIndex::from(0));
            let applied = call(arena, eliminator, &[code, on_nil, on_cons, xs]);
            function(arena, Binders::from(2), applied)
        };
        let length_type = {
            let code = var(arena, DeBruijnIndex::from(0));
            let elements = list(arena, code);
            let counted = arena.comp_type_arrow(elements, returns_nat);
            let kind = kind(arena);
            let generic = arena.comp_type_pi(kind, counted);
            arena.value_type_thunk(generic)
        };
        declarations.push(definition(
            ConstantIndex::from(at::LENGTH),
            length_type,
            length_body,
        ));

        // append A xs ys = elim_List[List A → F (List A)] A (λzs. zs)
        //                    (λa t ih zs. cons a (ih zs)) xs ys
        let appending = {
            let code = var(arena, DeBruijnIndex::from(1));
            let elements = list(arena, code);
            let returned = arena.comp_type_returner(elements);
            arena.comp_type_arrow(elements, returned)
        };
        declarations.push(derived(
            arena,
            ConstantIndex::from(at::ELIM_LIST_APPEND),
            ConstantIndex::from(at::LIST),
            &list_signature,
            appending,
        ));
        let on_nil = {
            let zs = var(arena, DeBruijnIndex::from(0));
            let returned = arena.computation_return(zs);
            function(arena, Binders::from(1), returned)
        };
        let on_cons = {
            // Under `A xs ys` and `a t ih zs`: zs 0, ih 1, a 3, A 6.
            let hypothesis = var(arena, DeBruijnIndex::from(1));
            let zs = var(arena, DeBruijnIndex::from(0));
            let recursive = call(arena, hypothesis, &[zs]);
            // Under the bind as well: r 0, a 4, A 7.
            let code = var(arena, DeBruijnIndex::from(7));
            let datatype = list(arena, code);
            let head = var(arena, DeBruijnIndex::from(4));
            let rest = var(arena, DeBruijnIndex::from(0));
            let cons =
                arena.value_constructor(datatype, ConstructorTag::from(1_usize), vec![head, rest]);
            let returned = arena.computation_return(cons);
            let bound = arena.computation_bind(recursive, returned);
            function(arena, Binders::from(4), bound)
        };
        let append_body = {
            let eliminator = arena.value_constant(ConstantIndex::from(at::ELIM_LIST_APPEND));
            let code = var(arena, DeBruijnIndex::from(2));
            let xs = var(arena, DeBruijnIndex::from(1));
            let ys = var(arena, DeBruijnIndex::from(0));
            let applied = call(arena, eliminator, &[code, on_nil, on_cons, xs, ys]);
            function(arena, Binders::from(3), applied)
        };
        let append_type = {
            let code = var(arena, DeBruijnIndex::from(0));
            let elements = list(arena, code);
            let returned = arena.comp_type_returner(elements);
            let second = arena.comp_type_arrow(elements, returned);
            let first = arena.comp_type_arrow(elements, second);
            let kind = kind(arena);
            let generic = arena.comp_type_pi(kind, first);
            arena.value_type_thunk(generic)
        };
        declarations.push(definition(
            ConstantIndex::from(at::APPEND),
            append_type,
            append_body,
        ));

        // map A B f xs = elim_List[Π B. U (El A → F (El B)) → F (List B)] A
        //                  (λB g. nil) (λa t ih B g. b ← g a; r ← ih B g;
        //                  cons b r) xs B f
        let mapping = {
            // Under `A x B`: A 2, B 0.
            let source = var(arena, DeBruijnIndex::from(2));
            let source = arena.value_type_element(source, Level::zero());
            let target = var(arena, DeBruijnIndex::from(0));
            let target_element = arena.value_type_element(target, Level::zero());
            let into_target = arena.comp_type_returner(target_element);
            let step = arena.comp_type_arrow(source, into_target);
            let step = arena.value_type_thunk(step);
            let mapped = list(arena, target);
            let mapped = arena.comp_type_returner(mapped);
            let after = arena.comp_type_arrow(step, mapped);
            let kind = kind(arena);
            arena.comp_type_pi(kind, after)
        };
        declarations.push(derived(
            arena,
            ConstantIndex::from(at::ELIM_LIST_MAP),
            ConstantIndex::from(at::LIST),
            &list_signature,
            mapping,
        ));
        let on_nil = {
            let code = var(arena, DeBruijnIndex::from(1));
            let datatype = list(arena, code);
            let nil = arena.value_constructor(datatype, ConstructorTag::from(0_usize), vec![]);
            let returned = arena.computation_return(nil);
            function(arena, Binders::from(2), returned)
        };
        let on_cons = {
            // Under `a t ih B g`: g 0, B 1, ih 2, a 4.
            let step = var(arena, DeBruijnIndex::from(0));
            let head = var(arena, DeBruijnIndex::from(4));
            let image = call(arena, step, &[head]);
            // Under `b`: b 0, g 1, B 2, ih 3.
            let hypothesis = var(arena, DeBruijnIndex::from(3));
            let code = var(arena, DeBruijnIndex::from(2));
            let step = var(arena, DeBruijnIndex::from(1));
            let rest = call(arena, hypothesis, &[code, step]);
            // Under `r`: r 0, b 1, B 3.
            let code = var(arena, DeBruijnIndex::from(3));
            let datatype = list(arena, code);
            let mapped_head = var(arena, DeBruijnIndex::from(1));
            let mapped_rest = var(arena, DeBruijnIndex::from(0));
            let cons = arena.value_constructor(datatype, ConstructorTag::from(1_usize), vec![
                mapped_head,
                mapped_rest,
            ]);
            let returned = arena.computation_return(cons);
            let inner = arena.computation_bind(rest, returned);
            let outer = arena.computation_bind(image, inner);
            function(arena, Binders::from(5), outer)
        };
        let map_body = {
            // Under `A B f xs`: xs 0, f 1, B 2, A 3.
            let eliminator = arena.value_constant(ConstantIndex::from(at::ELIM_LIST_MAP));
            let source = var(arena, DeBruijnIndex::from(3));
            let target = var(arena, DeBruijnIndex::from(2));
            let step = var(arena, DeBruijnIndex::from(1));
            let xs = var(arena, DeBruijnIndex::from(0));
            let applied = call(arena, eliminator, &[
                source, on_nil, on_cons, xs, target, step,
            ]);
            function(arena, Binders::from(4), applied)
        };
        let map_type = {
            // Under `A B`: A 1, B 0.
            let source = var(arena, DeBruijnIndex::from(1));
            let source_element = arena.value_type_element(source, Level::zero());
            let target = var(arena, DeBruijnIndex::from(0));
            let target_element = arena.value_type_element(target, Level::zero());
            let into_target = arena.comp_type_returner(target_element);
            let step = arena.comp_type_arrow(source_element, into_target);
            let step = arena.value_type_thunk(step);
            let sources = list(arena, source);
            let targets = list(arena, target);
            let returned = arena.comp_type_returner(targets);
            let over = arena.comp_type_arrow(sources, returned);
            let after = arena.comp_type_arrow(step, over);
            let kind = kind(arena);
            let inner = arena.comp_type_pi(kind, after);
            let outer = arena.comp_type_pi(kind, inner);
            arena.value_type_thunk(outer)
        };
        declarations.push(definition(ConstantIndex::from(at::MAP), map_type, map_body));

        // depth t = elim_Tree[F Nat] zero (λf ih. succ (ih zero)) t
        declarations.push(derived(
            arena,
            ConstantIndex::from(at::ELIM_TREE),
            ConstantIndex::from(at::TREE),
            &tree_signature,
            returns_nat,
        ));
        let on_leaf = {
            let returned = arena.computation_return(zero);
            arena.value_thunk(returned)
        };
        let on_node = {
            let hypothesis = var(arena, DeBruijnIndex::from(0));
            let recursive = call(arena, hypothesis, &[zero]);
            let result = var(arena, DeBruijnIndex::from(0));
            let successor =
                arena.value_constructor(nat, ConstructorTag::from(1_usize), vec![result]);
            let returned = arena.computation_return(successor);
            let bound = arena.computation_bind(recursive, returned);
            function(arena, Binders::from(2), bound)
        };
        let depth_body = {
            let eliminator = arena.value_constant(ConstantIndex::from(at::ELIM_TREE));
            let tree = var(arena, DeBruijnIndex::from(0));
            let applied = call(arena, eliminator, &[on_leaf, on_node, tree]);
            function(arena, Binders::from(1), applied)
        };
        let depth_type = {
            let tree = arena.value_type_data(ConstantIndex::from(at::TREE), vec![]);
            let measured = arena.comp_type_arrow(tree, returns_nat);
            arena.value_type_thunk(measured)
        };
        declarations.push(definition(
            ConstantIndex::from(at::DEPTH),
            depth_type,
            depth_body,
        ));

        // witness n = elim_Nat[F (IsNat x)] here (λp ih. here) n
        let naming = {
            let scrutinee = var(arena, DeBruijnIndex::from(0));
            let indexed = arena.value_type_data(ConstantIndex::from(at::IS_NAT), vec![scrutinee]);
            arena.comp_type_returner(indexed)
        };
        declarations.push(derived(
            arena,
            ConstantIndex::from(at::ELIM_NAT_DEPENDENT),
            ConstantIndex::from(at::NAT),
            &nat_signature,
            naming,
        ));
        let on_zero = {
            let indexed = arena.value_type_data(ConstantIndex::from(at::IS_NAT), vec![zero]);
            let here = arena.value_constructor(indexed, ConstructorTag::from(0_usize), vec![]);
            let returned = arena.computation_return(here);
            arena.value_thunk(returned)
        };
        let on_successor = {
            // Under `p ih`: p 1.
            let predecessor = var(arena, DeBruijnIndex::from(1));
            let successor =
                arena.value_constructor(nat, ConstructorTag::from(1_usize), vec![predecessor]);
            let indexed = arena.value_type_data(ConstantIndex::from(at::IS_NAT), vec![successor]);
            let here = arena.value_constructor(indexed, ConstructorTag::from(0_usize), vec![]);
            let returned = arena.computation_return(here);
            function(arena, Binders::from(2), returned)
        };
        let witness_body = {
            let eliminator = arena.value_constant(ConstantIndex::from(at::ELIM_NAT_DEPENDENT));
            let n = var(arena, DeBruijnIndex::from(0));
            let applied = call(arena, eliminator, &[on_zero, on_successor, n]);
            function(arena, Binders::from(1), applied)
        };
        let witness_type = {
            let n = var(arena, DeBruijnIndex::from(0));
            let indexed = arena.value_type_data(ConstantIndex::from(at::IS_NAT), vec![n]);
            let returned = arena.comp_type_returner(indexed);
            let every = arena.comp_type_pi(nat, returned);
            arena.value_type_thunk(every)
        };
        declarations.push(definition(
            ConstantIndex::from(at::WITNESS),
            witness_type,
            witness_body,
        ));
        declarations
    }

    /// Check `declarations` and readmit what the checker accepted.
    ///
    /// # Specification
    /// - requires: declaration ids refer to `arena`.
    /// - ensures: each source position has a producer verdict and a boundary
    ///   outcome.
    /// - panics: only if a called judgement violates its contract.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the witnesses inspect exact outcomes on both sides.
    /// - witness: `recursive_data::recursive_data::derived_eliminators_are_admitted_and_readmitted`
    #[spec(ensures: |ret| ret.0.judged().len() == declarations.len() && ret.1.readmitted().len() == declarations.len())]
    fn run(
        arena: &mut CoreArena,
        declarations: &[Declaration],
    ) -> (ModuleReport, bridge::Readmission)
    {
        let report = check_module(
            &mut CheckingContext::new(arena, CheckBudget::DEFAULT),
            declarations,
        );
        let crossed = bridge::readmit(arena, &report);
        (report, crossed)
    }

    /// The normaliser's definitions over a checked module's bodies.
    ///
    /// # Specification
    /// trivial.
    fn lowered(report: &ModuleReport) -> LoweredChain
    {
        let mut chain = DefinitionChain::new();
        for (entry, &constant) in report.definitions().keys().enumerate() {
            chain
                .define(
                    constant,
                    GlobalIndex::from(u32::try_from(entry).expect("a small module")),
                    Transparency::Manifest,
                    &[],
                )
                .expect("module positions ascend");
        }
        LoweredChain::lower(chain, |defined| {
            report
                .definitions()
                .get(&defined.constant())
                .copied()
                .ok_or_else(|| defined.constant())
        })
        .expect("every body is held")
    }

    /// Normalise `term` against the module's definitions and compare it with
    /// `expected`.
    ///
    /// One round evaluates to weak head and reads back, spending each head
    /// constant's body; the body is re-applied to its spine as written, so the
    /// rounds repeat until a readback reproduces its input.
    ///
    /// # Specification
    /// - requires: both live in `arena`; `term` is closed.
    /// - ensures: the syntactic equality of the normal form with `expected`.
    /// - panics: if evaluation or readback fault, or no round settles.
    ///
    /// # Termination
    /// - reason: the `for` loop over a fixed number of rounds, not recursion.
    /// - measure: the rounds left.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — each program's result is compared with its exact
    ///   expected value and with a near miss.
    /// - witness: `recursive_data::recursive_data::definitions_by_eliminator_normalise`
    #[spec(requires: arena.computation(term).is_some() && arena.computation(expected).is_some())]
    fn normalises_to(
        arena: &mut CoreArena,
        report: &ModuleReport,
        term: ComputationId,
        expected: ComputationId,
    ) -> CertificateEquality
    {
        let chain = lowered(report);
        let environment = DefinitionalEnvironment::new();
        let definitions = Definitions::new(&chain, &environment, environment.root());
        let fuel = Fuel::from(1_u32 << 20_u32);
        let mut focus = term;
        for _round in 0_u32 .. 16_u32 {
            let mut domain = DomainArena::new();
            let evaluated =
                gandr_core_nbe::eval_computation(arena, &mut domain, definitions, fuel, focus)
                    .expect("a closed program evaluates");
            let read = gandr_core_nbe::readback_computation(
                arena,
                &mut domain,
                definitions,
                ReadbackMode::Unfolding,
                fuel,
                evaluated,
            )
            .expect("its normal form reads back");
            let before = arena.value_thunk(focus);
            let after = arena.value_thunk(read);
            if gandr_core_term::equal_certificate_syntax(arena, before, after)
                == CertificateEquality::Equal
            {
                let expected = arena.value_thunk(expected);
                return gandr_core_term::equal_certificate_syntax(arena, after, expected);
            }
            focus = read;
        }
        panic!("the program settles within the rounds")
    }

    #[test]
    fn recursive_blocks_are_admitted_in_both_checkers()
    {
        let mut arena = CoreArena::new();
        let [nat, list, tree, ..] = signatures(&mut arena);
        let declarations = vec![
            data(ConstantIndex::from(at::NAT), nat),
            data(ConstantIndex::from(at::LIST), list),
            data(ConstantIndex::from(at::TREE), tree),
        ];
        let (report, crossed) = run(&mut arena, &declarations);
        for (position, (judged, readmitted)) in
            report.judged().iter().zip(crossed.readmitted()).enumerate()
        {
            assert_eq!(judged.verdict(), Verdict::Data, "{position}");
            assert!(
                matches!(readmitted.outcome(), Outcome::Data { admitted, .. } if admitted.position() == ConstantIndex::from(position)),
                "{:?}",
                readmitted.outcome()
            );
        }
        assert!(crossed.audit().axioms().is_empty());
    }

    /// The occurrence each refused declaration carries.
    #[derive(Clone, Copy, Debug, Eq, PartialEq)]
    enum Fixture
    {
        /// `U (T A → F 1)`: the family under a function's domain.
        Negative,
        /// `T A × 1`: the family inside another former.
        Nested,
        /// `U (F (T A))`: the family under a returner, not a function.
        Returner,
        /// `T ⌜1⌝`: the family at another argument than its parameter.
        NonUniform,
        /// A family declared after this one.
        Later,
        /// The family in its own parameter telescope.
        Parameter,
    }

    /// Offer the fixture's one-parameter, one-field declaration to the
    /// checker at position 0.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the checker's verdict on the declaration.
    /// - panics: only if a called judgement violates its contract.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — each fixture differs from an admitted family in one
    ///   occurrence.
    /// - witness: `recursive_data::recursive_data::occurrences_are_refused_by_name_in_both_checkers`
    #[spec(ensures: |ret| ret != Verdict::Data)]
    fn checker_refusal(fixture: Fixture) -> Verdict
    {
        let mut arena = CoreArena::new();
        let position = ConstantIndex::from(0);
        let universe = kind(&mut arena);
        let unit = arena.value_type_unit();
        let parameter = var(&mut arena, DeBruijnIndex::from(0));
        let own = arena.value_type_data(position, vec![parameter]);
        let mut parameters = vec![universe];
        let field = match fixture {
            | Fixture::Negative => {
                let returner = arena.comp_type_returner(unit);
                let function = arena.comp_type_arrow(own, returner);
                arena.value_type_thunk(function)
            },
            | Fixture::Nested => arena.value_type_product(own, unit),
            | Fixture::Returner => {
                let returner = arena.comp_type_returner(own);
                arena.value_type_thunk(returner)
            },
            | Fixture::NonUniform => {
                let code = arena.value_quote(unit);
                arena.value_type_data(position, vec![code])
            },
            | Fixture::Later => arena.value_type_data(ConstantIndex::from(1), vec![]),
            | Fixture::Parameter => {
                parameters.push(own);
                unit
            },
        };
        let declaration = Declaration::data(
            position,
            Arc::new(DataSignature::new(parameters, vec![vec![field]], universe)),
            origin(position),
        );
        let report = check_module(
            &mut CheckingContext::new(&mut arena, CheckBudget::DEFAULT),
            &[declaration],
        );
        report.judged()[0].verdict()
    }

    /// Offer the fixture's declaration to the kernel, as the checker's
    /// fixture states it.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the kernel's refusal, one of the occurrence refusals.
    /// - panics: if the kernel admits it.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the kernel names the occurrence the checker names.
    /// - witness: `recursive_data::recursive_data::occurrences_are_refused_by_name_in_both_checkers`
    #[spec(ensures: |ret| matches!(ret, KernelError::NegativeOccurrence(_)
        | KernelError::NestedOccurrence(_)
        | KernelError::IndexOccurrence(_)
        | KernelError::NonUniformOccurrence(_)
        | KernelError::CrossBlockReference { .. }))]
    fn kernel_refusal(fixture: Fixture) -> KernelError
    {
        let mut environment = Environment::new();
        let position = ConstantIndex::from(0);
        let mut staging = environment.stage();
        let arena = staging.arena();
        let universe = arena.value_type_universe(GroundSort::Value, Level::zero());
        let unit = arena.value_type_unit();
        let parameter = arena.value_variable(DeBruijnIndex::from(0));
        let own = arena.value_type_data(position, vec![parameter]);
        let mut parameters = vec![universe];
        let field = match fixture {
            | Fixture::Negative => {
                let returner = arena.comp_type_returner(unit);
                let function = arena.comp_type_arrow(own, returner);
                arena.value_type_thunk(function)
            },
            | Fixture::Nested => arena.value_type_product(own, unit),
            | Fixture::Returner => {
                let returner = arena.comp_type_returner(own);
                arena.value_type_thunk(returner)
            },
            | Fixture::NonUniform => {
                let code = arena.value_quote(unit);
                arena.value_type_data(position, vec![code])
            },
            | Fixture::Later => arena.value_type_data(ConstantIndex::from(1), vec![]),
            | Fixture::Parameter => {
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

    #[test]
    fn occurrences_are_refused_by_name_in_both_checkers()
    {
        let field = OccurrenceSite::Field {
            tag: ConstructorTag::from(0_usize),
            field: FieldPosition::from(0_usize),
        };
        let telescope = OccurrenceSite::Parameter(ParameterPosition::from(1_usize));
        for (fixture, checker, kernel) in [
            (
                Fixture::Negative,
                CheckRefusal::NegativeOccurrence(field),
                KernelError::NegativeOccurrence(field),
            ),
            (
                Fixture::Nested,
                CheckRefusal::NestedOccurrence(field),
                KernelError::NestedOccurrence(field),
            ),
            (
                Fixture::Returner,
                CheckRefusal::NestedOccurrence(field),
                KernelError::NestedOccurrence(field),
            ),
            (
                Fixture::NonUniform,
                CheckRefusal::NonUniformOccurrence(field),
                KernelError::NonUniformOccurrence(field),
            ),
            (
                Fixture::Later,
                CheckRefusal::CrossBlockReference {
                    site: field,
                    index: ConstantIndex::from(1),
                },
                KernelError::CrossBlockReference {
                    site: field,
                    index: ConstantIndex::from(1),
                },
            ),
            (
                Fixture::Parameter,
                CheckRefusal::IndexOccurrence(telescope),
                KernelError::IndexOccurrence(telescope),
            ),
        ] {
            assert_eq!(
                checker_refusal(fixture),
                Verdict::Refused(checker),
                "{fixture:?}"
            );
            assert_eq!(
                checker.classify(),
                gandr_core_term::FailureClass::MalformedSource
            );
            assert_eq!(kernel_refusal(fixture), kernel, "{fixture:?}");
        }
    }

    /// A body a descent claim is tested on, as the kernel's witnesses name
    /// them.
    #[derive(Clone, Copy, Debug, Eq, PartialEq)]
    enum Claim
    {
        /// `λx. case x of { zero ↦ zero; succ p ↦ rec p }`.
        Descends,
        /// `λx. rec x`: no case.
        NotCase,
        /// `force rec`: no λ.
        Bare,
        /// `λx. case x of { zero ↦ zero; succ ↦ zero }`: no field binder.
        MissingField,
        /// `λx. case x of { …; succ p ↦ force rec }`: `rec` not applied.
        Unguarded,
        /// `λx. case x of { …; succ p ↦ rec x }`: no descent.
        AtScrutinee,
    }

    /// `fix rec. M` at `Nat → F Nat`, beside `Nat` at position 0, as the
    /// claim names `M`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the module of `Nat` and the definition, and the fixpoint's
    ///   id.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — each claim differs from the descending one in one
    ///   rule of the walk.
    /// - witness: `recursive_data::recursive_data::descent_claims_replay_or_are_refused_by_name`
    #[spec(ensures: |ret| ret.0.len() == 2)]
    fn claimed(
        arena: &mut CoreArena,
        claim: Claim,
        evidence: FixpointEvidence,
    ) -> (Vec<Declaration>, ComputationId)
    {
        let [nat_signature, ..] = signatures(arena);
        let nat = nat(arena);
        let returner = arena.comp_type_returner(nat);
        let classifier = arena.comp_type_arrow(nat, returner);
        let [zero, ..] = numerals(arena);
        let returned = arena.computation_return(zero);
        let case_on_argument = |arena: &mut CoreArena, on_successor: ComputationId| {
            let argument = var(arena, DeBruijnIndex::from(0));
            let case =
                arena.computation_data_case(argument, returner, vec![returned, on_successor]);
            arena.computation_lambda(case)
        };
        // Under the body: `rec` 0. Under its λ: `x` 0, `rec` 1. Under the
        // `succ` field: `p` 0, `x` 1, `rec` 2.
        let body = match claim {
            | Claim::Descends => {
                let recursive = var(arena, DeBruijnIndex::from(2));
                let field = var(arena, DeBruijnIndex::from(0));
                let call = call(arena, recursive, &[field]);
                let on_successor = arena.computation_lambda(call);
                case_on_argument(arena, on_successor)
            },
            | Claim::NotCase => {
                let recursive = var(arena, DeBruijnIndex::from(1));
                let argument = var(arena, DeBruijnIndex::from(0));
                let call = call(arena, recursive, &[argument]);
                arena.computation_lambda(call)
            },
            | Claim::Bare => {
                let recursive = var(arena, DeBruijnIndex::from(0));
                arena.computation_force(recursive)
            },
            | Claim::MissingField => case_on_argument(arena, returned),
            | Claim::Unguarded => {
                let recursive = var(arena, DeBruijnIndex::from(2));
                let forced = arena.computation_force(recursive);
                let on_successor = arena.computation_lambda(forced);
                case_on_argument(arena, on_successor)
            },
            | Claim::AtScrutinee => {
                let recursive = var(arena, DeBruijnIndex::from(2));
                let scrutinee = var(arena, DeBruijnIndex::from(1));
                let call = call(arena, recursive, &[scrutinee]);
                let on_successor = arena.computation_lambda(call);
                case_on_argument(arena, on_successor)
            },
        };
        let fixpoint = arena.computation_fixpoint(body, evidence);
        let declared = arena.value_type_thunk(classifier);
        let value = arena.value_thunk(fixpoint);
        (
            vec![
                data(ConstantIndex::from(at::NAT), nat_signature),
                definition(ConstantIndex::from(1_usize), declared, value),
            ],
            fixpoint,
        )
    }

    #[test]
    fn descent_claims_replay_or_are_refused_by_name()
    {
        let mut arena = CoreArena::new();
        let (declarations, _) = claimed(
            &mut arena,
            Claim::Descends,
            FixpointEvidence::StructuralDescent,
        );
        let (report, crossed) = run(&mut arena, &declarations);
        assert!(matches!(
            report.judged()[1].verdict(),
            Verdict::Checked { .. }
        ));
        assert!(
            matches!(crossed.readmitted()[1].outcome(), Outcome::Defined { .. }),
            "{:?}",
            crossed.readmitted()[1].outcome()
        );
        assert!(crossed.audit().axioms().is_empty());
        for (claim, reason) in [
            (Claim::NotCase, DescentRefusal::NotCaseOnArgument),
            (Claim::Bare, DescentRefusal::NotCaseOnArgument),
            (Claim::MissingField, DescentRefusal::BranchNotOverFields),
            (Claim::Unguarded, DescentRefusal::UnguardedSelfReference),
            (Claim::AtScrutinee, DescentRefusal::NonDescendingCall),
        ] {
            let mut arena = CoreArena::new();
            let (declarations, fixpoint) =
                claimed(&mut arena, claim, FixpointEvidence::StructuralDescent);
            let (report, _) = run(&mut arena, &declarations);
            assert_eq!(
                report.judged()[1].verdict(),
                Verdict::Refused(CheckRefusal::DescentNotReplayed {
                    at: fixpoint,
                    reason,
                }),
                "{claim:?}"
            );
        }
        // Without a claim the same fixpoints check, as partial, and cross.
        for claim in [Claim::NotCase, Claim::Bare] {
            let mut arena = CoreArena::new();
            let (declarations, _) = claimed(&mut arena, claim, FixpointEvidence::Partial);
            let (report, crossed) = run(&mut arena, &declarations);
            assert!(
                matches!(report.judged()[1].verdict(), Verdict::Checked { .. }),
                "{claim:?}"
            );
            assert!(
                matches!(crossed.readmitted()[1].outcome(), Outcome::Defined { .. }),
                "{claim:?}"
            );
        }
    }

    #[test]
    fn a_fixpoint_checks_at_every_computation_type()
    {
        // `fix rec. force rec` at `F 1`: a loop, which only a partial
        // fixpoint may write.
        let looping = |evidence: FixpointEvidence| {
            let mut arena = CoreArena::new();
            let unit_type = arena.value_type_unit();
            let returner = arena.comp_type_returner(unit_type);
            let recursive = var(&mut arena, DeBruijnIndex::from(0));
            let forced = arena.computation_force(recursive);
            let fixpoint = arena.computation_fixpoint(forced, evidence);
            let declared = arena.value_type_thunk(returner);
            let value = arena.value_thunk(fixpoint);
            // At an application's head a fixpoint stands where a type must be
            // synthesised: `(fix rec. λx. return x) ()`.
            let unit = arena.value_unit();
            let bound = var(&mut arena, DeBruijnIndex::from(0));
            let returned = arena.computation_return(bound);
            let identity = arena.computation_lambda(returned);
            let headed = arena.computation_fixpoint(identity, evidence);
            let applied = arena.computation_application(headed, unit);
            let applied = arena.value_thunk(applied);
            let declarations = [
                definition(ConstantIndex::from(0), declared, value),
                definition(ConstantIndex::from(1), declared, applied),
            ];
            let (report, crossed) = run(&mut arena, &declarations);
            (
                (report.judged()[0].verdict(), fixpoint),
                (report.judged()[1].verdict(), headed),
                crossed.readmitted()[0].outcome().clone(),
            )
        };
        let ((checked, _), (synthesised, headed), crossed) = looping(FixpointEvidence::Partial);
        assert!(matches!(checked, Verdict::Checked { .. }), "{checked:?}");
        assert!(matches!(crossed, Outcome::Defined { .. }), "{crossed:?}");
        assert_eq!(
            synthesised,
            Verdict::Refused(CheckRefusal::NotSynthesisable {
                form: CheckingForm::Fixpoint(headed),
            })
        );
        let ((claimed, fixpoint), ..) = looping(FixpointEvidence::StructuralDescent);
        assert_eq!(
            claimed,
            Verdict::Refused(CheckRefusal::DescentNotReplayed {
                at: fixpoint,
                reason: DescentRefusal::NotOverData,
            })
        );
    }

    #[test]
    fn derived_eliminators_are_admitted_and_readmitted()
    {
        let mut arena = CoreArena::new();
        let declarations = program(&mut arena);
        let (report, crossed) = run(&mut arena, &declarations);
        for (position, (judged, readmitted)) in
            report.judged().iter().zip(crossed.readmitted()).enumerate()
        {
            if position <= at::IS_TREE {
                assert_eq!(judged.verdict(), Verdict::Data, "{position}");
            }
            else {
                assert!(
                    matches!(judged.verdict(), Verdict::Checked { .. }),
                    "{position}: {:?}",
                    judged.verdict()
                );
            }
            assert!(
                matches!(readmitted.outcome(),
                    Outcome::Data { admitted, .. } | Outcome::Defined { admitted, .. }
                        if admitted.position() == ConstantIndex::from(position)),
                "{position}: {:?}",
                readmitted.outcome()
            );
        }
        assert!(crossed.audit().axioms().is_empty());
        assert!(crossed.audit().unchecked_admissions().is_empty());
        // A motive naming its scrutinee has no hypothesis at a function field.
        let [_, _, tree_signature, ..] = signatures(&mut arena);
        let scrutinee = var(&mut arena, DeBruijnIndex::from(0));
        let indexed = arena.value_type_data(ConstantIndex::from(at::IS_TREE), vec![scrutinee]);
        let naming = arena.comp_type_returner(indexed);
        assert_eq!(
            eliminator::derive(
                &mut arena,
                ConstantIndex::from(at::TREE),
                &tree_signature,
                naming
            ),
            Err(DerivationRefusal::DependentMotiveAtFunctionField(
                OccurrenceSite::Field {
                    tag: ConstructorTag::from(1_usize),
                    field: FieldPosition::from(0_usize),
                }
            ))
        );
    }

    #[test]
    fn definitions_by_eliminator_normalise()
    {
        let mut arena = CoreArena::new();
        let declarations = program(&mut arena);
        let (report, _) = run(&mut arena, &declarations);
        let unit_type = arena.value_type_unit();
        let unit_code = arena.value_quote(unit_type);
        let unit = arena.value_unit();
        let numerals = numerals(&mut arena);
        let returned: Vec<ComputationId> = numerals
            .iter()
            .map(|&n| arena.computation_return(n))
            .collect();

        let plus = arena.value_constant(ConstantIndex::from(at::PLUS));
        let sum = call(&mut arena, plus, &[numerals[2], numerals[2]]);
        assert_eq!(
            normalises_to(&mut arena, &report, sum, returned[4]),
            CertificateEquality::Equal
        );
        assert_ne!(
            normalises_to(&mut arena, &report, sum, returned[3]),
            CertificateEquality::Equal
        );

        let length = arena.value_constant(ConstantIndex::from(at::LENGTH));
        let pair = list_of(&mut arena, unit_code, &[unit, unit]);
        let counted = call(&mut arena, length, &[unit_code, pair]);
        assert_eq!(
            normalises_to(&mut arena, &report, counted, returned[2]),
            CertificateEquality::Equal
        );

        let append = arena.value_constant(ConstantIndex::from(at::APPEND));
        let single = list_of(&mut arena, unit_code, &[unit]);
        let joined = call(&mut arena, append, &[unit_code, single, single]);
        let expected = arena.computation_return(pair);
        assert_eq!(
            normalises_to(&mut arena, &report, joined, expected),
            CertificateEquality::Equal
        );
        let wrong = arena.computation_return(single);
        assert_ne!(
            normalises_to(&mut arena, &report, joined, wrong),
            CertificateEquality::Equal
        );

        let map = arena.value_constant(ConstantIndex::from(at::MAP));
        let constant = {
            let returned = arena.computation_return(unit);
            function(&mut arena, Binders::from(1), returned)
        };
        let mapped = call(&mut arena, map, &[unit_code, unit_code, constant, pair]);
        let expected = arena.computation_return(pair);
        assert_eq!(
            normalises_to(&mut arena, &report, mapped, expected),
            CertificateEquality::Equal
        );

        let depth = arena.value_constant(ConstantIndex::from(at::DEPTH));
        let tree_type = arena.value_type_data(ConstantIndex::from(at::TREE), vec![]);
        let leaf = arena.value_constructor(tree_type, ConstructorTag::from(0_usize), vec![]);
        let leaves = {
            let returned = arena.computation_return(leaf);
            function(&mut arena, Binders::from(1), returned)
        };
        let node = arena.value_constructor(tree_type, ConstructorTag::from(1_usize), vec![leaves]);
        let deeper = {
            let returned = arena.computation_return(node);
            function(&mut arena, Binders::from(1), returned)
        };
        let root = arena.value_constructor(tree_type, ConstructorTag::from(1_usize), vec![deeper]);
        let measured = call(&mut arena, depth, &[root]);
        assert_eq!(
            normalises_to(&mut arena, &report, measured, returned[2]),
            CertificateEquality::Equal
        );
    }

    /// The kernel's reading of a normaliser decision, through the positions
    /// the module's declarations crossed to.
    ///
    /// # Specification
    /// trivial.
    fn replayed_decision(
        positions: &BTreeMap<ConstantIndex, ConstantIndex>,
        decision: ConversionDecision<TraceNode>,
    ) -> ConversionDecision<ReplayNode>
    {
        let node = |node: TraceNode| match node {
            | TraceNode::Constant(constant) => match positions.get(&constant) {
                | Some(&position) => ReplayNode::Constant(position),
                | None => ReplayNode::Other,
            },
            | TraceNode::Value(_) | TraceNode::Computation(_) => ReplayNode::Other,
        };
        match decision {
            | ConversionDecision::ReduceLeft { redex } => {
                ConversionDecision::ReduceLeft { redex: node(redex) }
            },
            | ConversionDecision::ReduceRight { redex } => {
                ConversionDecision::ReduceRight { redex: node(redex) }
            },
            | ConversionDecision::ConstShortcut { constant } => ConversionDecision::ConstShortcut {
                constant: node(constant),
            },
            | ConversionDecision::Unfold { constant } => ConversionDecision::Unfold {
                constant: node(constant),
            },
            | ConversionDecision::Postpone { constant } => ConversionDecision::Postpone {
                constant: node(constant),
            },
            | ConversionDecision::Freeze { constant, side } => ConversionDecision::Freeze {
                constant: node(constant),
                side,
            },
            | ConversionDecision::EtaExpand { side, variable } => ConversionDecision::EtaExpand {
                side,
                variable: node(variable),
            },
            | ConversionDecision::Force { thunk } => {
                ConversionDecision::Force { thunk: node(thunk) }
            },
            | ConversionDecision::ComparedShared { left, right } => {
                ConversionDecision::ComparedShared {
                    left: node(left),
                    right: node(right),
                }
            },
            | ConversionDecision::Decompose => ConversionDecision::Decompose,
            | ConversionDecision::NegativeSubgoal { position } => {
                ConversionDecision::NegativeSubgoal { position }
            },
        }
    }

    #[test]
    fn the_kernel_replays_a_conversion_through_a_definition_by_eliminator()
    {
        let mut arena = CoreArena::new();
        let declarations = program(&mut arena);
        let (report, crossed) = run(&mut arena, &declarations);
        let positions: BTreeMap<ConstantIndex, ConstantIndex> = crossed
            .readmitted()
            .iter()
            .filter_map(|entry| match *entry.outcome() {
                | Outcome::Defined { admitted, .. } | Outcome::Data { admitted, .. } => {
                    Some((entry.constant(), admitted.position()))
                },
                | _ => None,
            })
            .collect();
        // The normaliser decides `plus 2 2 ≡ 4` and `plus 2 2 ≢ 3` with a
        // trace.
        let plus = arena.value_constant(ConstantIndex::from(at::PLUS));
        let [_, _, two, three, four] = numerals(&mut arena);
        let sum = call(&mut arena, plus, &[two, two]);
        let four = arena.computation_return(four);
        let three = arena.computation_return(three);
        let chain = lowered(&report);
        let environment = DefinitionalEnvironment::new();
        let definitions = Definitions::new(&chain, &environment, environment.root());
        let fuel = Fuel::from(1_u32 << 20_u32);
        let decided = |arena: &CoreArena, right: ComputationId| {
            let mut domain = DomainArena::new();
            let left = gandr_core_nbe::eval_computation(arena, &mut domain, definitions, fuel, sum)
                .expect("the sum evaluates");
            let right =
                gandr_core_nbe::eval_computation(arena, &mut domain, definitions, fuel, right)
                    .expect("the numeral evaluates");
            let mut log = TraceLog::new();
            let report = gandr_core_nbe::decide::<_, ResharingMemo>(
                arena,
                &mut domain,
                definitions,
                MachineSettings::default(),
                Problem::computations(left, right),
                &mut log,
            )
            .expect("the machine answers");
            let trace: Vec<ConversionDecision<ReplayNode>> = log
                .decisions()
                .map(|&decision| replayed_decision(&positions, decision))
                .collect();
            (report.verdict(), trace)
        };
        let (agreed, agreed_trace) = decided(&arena, four);
        let (apart, apart_trace) = decided(&arena, three);
        assert_eq!(agreed, MachineVerdict::Convertible);
        assert_eq!(apart, MachineVerdict::NotConvertible);
        // The kernel replays both traces over the exported declarations.
        let artifact = gandr_kernel_term::decode(crossed.export(BTreeMap::new()).as_image())
            .expect("the export decodes");
        let mut kernel = artifact.arena().clone();
        let unfoldings = Unfoldings::new(
            artifact
                .declarations()
                .iter()
                .map(|entry| match *entry.declaration().content() {
                    | gandr_kernel_term::DeclarationContent::Def { body, .. } => {
                        Unfoldable::Body(body)
                    },
                    | _ => Unfoldable::Opaque,
                })
                .collect(),
        );
        let nat = positions[&ConstantIndex::from(at::NAT)];
        let nat_type = kernel.value_type_data(nat, vec![]);
        let kernel_numeral = |kernel: &mut gandr_kernel_term::TermArena, n: usize| {
            let mut built =
                kernel.value_constructor(nat_type, ConstructorTag::from(0_usize), vec![]);
            for _step in 0 .. n {
                built =
                    kernel.value_constructor(nat_type, ConstructorTag::from(1_usize), vec![built]);
            }
            built
        };
        let two = kernel_numeral(&mut kernel, 2);
        let four = kernel_numeral(&mut kernel, 4);
        let three = kernel_numeral(&mut kernel, 3);
        let plus = kernel.value_constant(positions[&ConstantIndex::from(at::PLUS)]);
        let forced = kernel.computation_force(plus);
        let partial = kernel.computation_application(forced, two);
        let sum = kernel.computation_application(partial, two);
        let four = kernel.computation_return(four);
        let three = kernel.computation_return(three);
        assert_eq!(
            gandr_kernel_core::replay(
                &mut kernel,
                &unfoldings,
                ReplaySides::Computations(sum, four),
                EngineClaim::Convertible,
                agreed_trace,
                ReplayBudget::default(),
            ),
            KernelVerdict::Convertible
        );
        assert_eq!(
            gandr_kernel_core::replay(
                &mut kernel,
                &unfoldings,
                ReplaySides::Computations(sum, three),
                EngineClaim::NotConvertible,
                apart_trace,
                ReplayBudget::default(),
            ),
            KernelVerdict::NotConvertible
        );
    }

    #[test]
    fn the_export_is_deterministic()
    {
        let image = || {
            let mut arena = CoreArena::new();
            let declarations = program(&mut arena);
            let (_, crossed) = run(&mut arena, &declarations);
            let encoded = crossed.export(BTreeMap::new());
            encoded.as_image().as_ref().to_vec()
        };
        let first = image();
        assert!(!first.is_empty());
        assert_eq!(first, image());
    }
}
