//! Recursive data, fixpoints and derived eliminators through the checker, the
//! normaliser and the kernel.

use alloc::collections::BTreeMap;
use alloc::sync::Arc;

use anodized::spec;
use gandr_core_checker::CheckBudget;
use gandr_core_checker::CheckRefusal;
use gandr_core_checker::CheckingContext;
use gandr_core_checker::Declaration;
use gandr_core_checker::ExpectedShape;
use gandr_core_checker::ModuleReport;
use gandr_core_checker::ModuleRun;
use gandr_core_checker::OriginToken;
use gandr_core_checker::TermNode;
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
use gandr_kernel_term::FieldLabel;
use gandr_kernel_term::FieldPosition;
use gandr_kernel_term::FixpointEvidence;
use gandr_kernel_term::GlobalIndex;
use gandr_kernel_term::GroundSort;
use gandr_kernel_term::LevelSignature;
use gandr_kernel_term::OccurrenceSite;
use gandr_kernel_term::ParameterPosition;
use gandr_kernel_term::Standing;
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
/// - requires: `signature` is the one declared at `family`; `motive` is scoped
///   under its parameters and a scrutinee.
/// - ensures: the eliminator's declaration.
/// - panics: if the fold refuses.
///
/// # Adequacy
/// - hypothesis: L3 — every eliminator of the program module is judged and
///   readmitted.
/// - witness: `tests::recursive_data::derived_eliminators_are_admitted_and_readmitted`
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
    // The tail stands past the head's binder: the element code is one out.
    let past_head = var(arena, DeBruijnIndex::from(1));
    let tail = list(arena, past_head);
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
/// - hypothesis: L3 — the module is checked, normalised and readmitted by the
///   witnesses.
/// - witness: `tests::recursive_data::derived_eliminators_are_admitted_and_readmitted`
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
        let successor = arena.value_constructor(nat, ConstructorTag::from(1_usize), vec![result]);
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
        let successor = arena.value_constructor(nat, ConstructorTag::from(1_usize), vec![result]);
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
        let successor = arena.value_constructor(nat, ConstructorTag::from(1_usize), vec![result]);
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
/// - witness: `tests::recursive_data::derived_eliminators_are_admitted_and_readmitted`
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
/// - hypothesis: L3 — each program's result is compared with its exact expected
///   value and with a near miss.
/// - witness: `tests::recursive_data::definitions_by_eliminator_normalise`
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

/// Every placement, with the checker's verdict on its block and the
/// kernel's.
///
/// # Specification
/// trivial.
fn placements() -> [(Placement, Verdict, Result<(), KernelError>); 19]
{
    let field = OccurrenceSite::Field {
        tag: ConstructorTag::from(0_usize),
        field: FieldPosition::from(0_usize),
    };
    let telescope = OccurrenceSite::Parameter(ParameterPosition::from(1_usize));
    let later = ConstantIndex::from(3_usize);
    [
        (Placement::Direct, Verdict::Data, Ok(())),
        (Placement::Returned, Verdict::Data, Ok(())),
        (Placement::Codomain, Verdict::Data, Ok(())),
        (Placement::Product, Verdict::Data, Ok(())),
        (Placement::Sum, Verdict::Data, Ok(())),
        (Placement::Record, Verdict::Data, Ok(())),
        (Placement::List, Verdict::Data, Ok(())),
        (Placement::Sigma, Verdict::Data, Ok(())),
        (Placement::With, Verdict::Data, Ok(())),
        (Placement::Nested, Verdict::Data, Ok(())),
        (Placement::Domain, Verdict::Data, Ok(())),
        (Placement::TwoDomains, Verdict::Data, Ok(())),
        (
            Placement::NonUniform,
            Verdict::Refused(CheckRefusal::NonUniformOccurrence(field)),
            Err(KernelError::NonUniformOccurrence(field)),
        ),
        (
            Placement::NonUniformDomain,
            Verdict::Refused(CheckRefusal::NegativeOccurrence(field)),
            Err(KernelError::NegativeOccurrence(field)),
        ),
        (
            Placement::Consumed,
            Verdict::Refused(CheckRefusal::NestedOccurrence(field)),
            Err(KernelError::NestedOccurrence(field)),
        ),
        (
            Placement::ConsumedDomain,
            Verdict::Refused(CheckRefusal::NegativeOccurrence(field)),
            Err(KernelError::NegativeOccurrence(field)),
        ),
        (
            Placement::Lifted,
            Verdict::Refused(CheckRefusal::IndexOccurrence(field)),
            Err(KernelError::IndexOccurrence(field)),
        ),
        (
            Placement::Later,
            Verdict::Refused(CheckRefusal::CrossBlockReference {
                site: field,
                index: later,
            }),
            Err(KernelError::CrossBlockReference {
                site: field,
                index: later,
            }),
        ),
        (
            Placement::Parameter,
            Verdict::Refused(CheckRefusal::IndexOccurrence(telescope)),
            Err(KernelError::IndexOccurrence(telescope)),
        ),
    ]
}

/// `U (domain → returns)`: a thunked function from `domain`.
///
/// # Specification
/// trivial.
fn consuming(
    arena: &mut CoreArena,
    domain: ValueTypeId,
    returns: CompTypeId,
) -> ValueTypeId
{
    let function = arena.comp_type_arrow(domain, returns);
    arena.value_type_thunk(function)
}

/// `List` at 0, `Test` at 1 and a one-parameter block at 2 whose one
/// field places the family as `placement` names, checked and readmitted.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the checker's report on the three declarations and their
///   readmission.
/// - panics: only if a called judgement violates its contract.
///
/// # Adequacy
/// - hypothesis: L3 — each placement differs from `T A` in one former, so its
///   verdict is that former's.
/// - witness: `tests::recursive_data::accessibility_is_decided_on_every_former`
/// - witness: `tests::recursive_data::readmission_agrees_with_the_checker_on_every_occurrence_class`
#[spec(ensures: |ret| ret.0.judged().len() == 3)]
fn checker_placed(placement: Placement) -> (ModuleReport, bridge::Readmission)
{
    let mut arena = CoreArena::new();
    let list = ConstantIndex::from(0_usize);
    let consumed = ConstantIndex::from(1_usize);
    let position = ConstantIndex::from(2_usize);
    let universe = kind(&mut arena);
    let unit = arena.value_type_unit();
    let returns = arena.comp_type_returner(unit);
    let parameter = var(&mut arena, DeBruijnIndex::from(0));
    let element = arena.value_type_element(parameter, Level::zero());
    // Past one binder the parameter is one out.
    let past = var(&mut arena, DeBruijnIndex::from(1));
    let tail = arena.value_type_data(list, vec![past]);
    let tested = consuming(&mut arena, element, returns);
    let own = arena.value_type_data(position, vec![parameter]);
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
        Placement::Record => {
            arena.value_type_record(BTreeMap::from([(FieldLabel::from(String::from("x")), own)]))
        },
        Placement::List => arena.value_type_list(own),
        Placement::Sigma => arena.value_type_sigma(unit, own_past),
        Placement::With => {
            let first = arena.comp_type_returner(own);
            let both = arena.comp_type_with(&[first, returns]);
            arena.value_type_thunk(both)
        },
        Placement::Nested => arena.value_type_data(list, vec![code]),
        Placement::Domain => consuming(&mut arena, own, returns),
        Placement::TwoDomains => {
            let inner = consuming(&mut arena, own, returns);
            consuming(&mut arena, inner, returns)
        },
        Placement::NonUniform => arena.value_type_data(position, vec![one]),
        Placement::NonUniformDomain => {
            let other = arena.value_type_data(position, vec![one]);
            consuming(&mut arena, other, returns)
        },
        Placement::Consumed => arena.value_type_data(consumed, vec![code]),
        Placement::ConsumedDomain => {
            let tested = arena.value_type_data(consumed, vec![code]);
            consuming(&mut arena, tested, returns)
        },
        Placement::Lifted => arena.value_type_lift(own, Level::zero()),
        Placement::Later => arena.value_type_data(ConstantIndex::from(3_usize), vec![]),
        Placement::Parameter => {
            parameters.push(own);
            unit
        },
    };
    let declarations = [
        data(
            list,
            DataSignature::new(vec![universe], vec![vec![], vec![element, tail]], universe),
        ),
        data(
            consumed,
            DataSignature::new(vec![universe], vec![vec![tested]], universe),
        ),
        data(
            position,
            DataSignature::new(parameters, vec![vec![field]], universe),
        ),
    ];
    run(&mut arena, &declarations)
}

/// Offer the kernel `List`, `Test` and the placement's block, as
/// [`checker_placed`] states them.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the kernel's verdict on the placement's block.
/// - panics: if the kernel refuses `List` or `Test`.
///
/// # Errors
/// The kernel's refusal of the block.
///
/// # Adequacy
/// - hypothesis: L3 — the kernel decides each placement as the checker does.
/// - witness: `tests::recursive_data::readmission_agrees_with_the_checker_on_every_occurrence_class`
#[spec(ensures: |ret| ret.as_ref().err().is_none_or(|error| matches!(error,
        KernelError::NegativeOccurrence(_)
        | KernelError::NestedOccurrence(_)
        | KernelError::IndexOccurrence(_)
        | KernelError::NonUniformOccurrence(_)
        | KernelError::CrossBlockReference { .. })))]
fn kernel_placed(placement: Placement) -> Result<(), KernelError>
{
    let mut environment = Environment::new();
    let list = ConstantIndex::from(0_usize);
    let consumed = ConstantIndex::from(1_usize);
    let position = ConstantIndex::from(2_usize);
    let mut staging = environment.stage();
    let arena = staging.arena();
    let universe = arena.value_type_universe(GroundSort::Value, Level::zero());
    let parameter = arena.value_variable(DeBruijnIndex::from(0));
    let element = arena.value_type_element(parameter, Level::zero());
    let past = arena.value_variable(DeBruijnIndex::from(1));
    let tail = arena.value_type_data(list, vec![past]);
    let declaration = staging.data(
        LevelSignature::monomorphic(),
        vec![universe],
        vec![vec![], vec![element, tail]],
        universe,
    );
    environment.add_decl(declaration).expect("List is admitted");
    let mut staging = environment.stage();
    let arena = staging.arena();
    let universe = arena.value_type_universe(GroundSort::Value, Level::zero());
    let parameter = arena.value_variable(DeBruijnIndex::from(0));
    let element = arena.value_type_element(parameter, Level::zero());
    let unit = arena.value_type_unit();
    let returns = arena.comp_type_returner(unit);
    let function = arena.comp_type_arrow(element, returns);
    let tested = arena.value_type_thunk(function);
    let declaration = staging.data(
        LevelSignature::monomorphic(),
        vec![universe],
        vec![vec![tested]],
        universe,
    );
    environment.add_decl(declaration).expect("Test is admitted");
    let mut staging = environment.stage();
    let arena = staging.arena();
    let universe = arena.value_type_universe(GroundSort::Value, Level::zero());
    let unit = arena.value_type_unit();
    let returns = arena.comp_type_returner(unit);
    let parameter = arena.value_variable(DeBruijnIndex::from(0));
    let own = arena.value_type_data(position, vec![parameter]);
    let past = arena.value_variable(DeBruijnIndex::from(1));
    let own_past = arena.value_type_data(position, vec![past]);
    let code = arena.value_quote(own);
    let one = arena.value_quote(unit);
    let mut parameters = vec![universe];
    let consumer = |arena: &mut gandr_kernel_term::TermArena, domain| {
        let function = arena.comp_type_arrow(domain, returns);
        arena.value_type_thunk(function)
    };
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
        Placement::Record => {
            arena.value_type_record(BTreeMap::from([(FieldLabel::from(String::from("x")), own)]))
        },
        Placement::List => arena.value_type_list(own),
        Placement::Sigma => arena.value_type_sigma(unit, own_past),
        Placement::With => {
            let first = arena.comp_type_returner(own);
            let both = arena.comp_type_with(&[first, returns]);
            arena.value_type_thunk(both)
        },
        Placement::Nested => arena.value_type_data(list, vec![code]),
        Placement::Domain => consumer(arena, own),
        Placement::TwoDomains => {
            let inner = consumer(arena, own);
            consumer(arena, inner)
        },
        Placement::NonUniform => arena.value_type_data(position, vec![one]),
        Placement::NonUniformDomain => {
            let other = arena.value_type_data(position, vec![one]);
            consumer(arena, other)
        },
        Placement::Consumed => arena.value_type_data(consumed, vec![code]),
        Placement::ConsumedDomain => {
            let tested = arena.value_type_data(consumed, vec![code]);
            consumer(arena, tested)
        },
        Placement::Lifted => arena.value_type_lift(own, Level::zero()),
        Placement::Later => arena.value_type_data(ConstantIndex::from(3_usize), vec![]),
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
    environment.add_decl(declaration).map(drop)
}

/// Every placeable former admits the family it places, at a strictly
/// positive position and under domains alike; what no stage reaches is
/// refused by the occurrence it is, as malformed source.
#[test]
fn accessibility_is_decided_on_every_former()
{
    for (placement, verdict, _) in placements() {
        let (report, _) = checker_placed(placement);
        let judged = report.judged()[2].verdict();
        assert_eq!(judged, verdict, "{placement:?}");
        if let Verdict::Refused(refusal) = judged {
            assert_eq!(
                refusal.classify(),
                gandr_core_term::FailureClass::MalformedSource
            );
        }
    }
}

/// The kernel decides every placement as the checker does: a block the
/// checker admits is readmitted, and one it refuses the kernel refuses by
/// the same occurrence.
#[test]
fn readmission_agrees_with_the_checker_on_every_occurrence_class()
{
    for (placement, _, kernel) in placements() {
        let (report, crossed) = checker_placed(placement);
        assert_eq!(kernel_placed(placement), kernel, "{placement:?}");
        let readmitted = crossed.readmitted()[2].outcome();
        let judged = report.judged()[2].verdict();
        assert_eq!(
            judged == Verdict::Data,
            matches!(readmitted, Outcome::Data { admitted, .. } if admitted.position() == ConstantIndex::from(2_usize)),
            "{placement:?}: {judged:?} crossed as {readmitted:?}"
        );
    }
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

/// `Chain`, `start` and `link : (prev : Chain, test : U (Chain → F 1))`;
/// `apply : U (U (Chain → F 1) → Chain → F 1)`, `λg. λx. (force g) x`;
/// and at `U (Chain → F 1)` the consumer `λc. case c of { start ↦ return
/// (); link ↦ λprev test. … }`, applying `test` to what `consumer` names.
///
/// # Specification
/// trivial.
fn chain(
    arena: &mut CoreArena,
    consumer: Consumer,
) -> [Declaration; 3]
{
    let chain = ConstantIndex::from(0_usize);
    let apply = ConstantIndex::from(1_usize);
    let consuming_at = ConstantIndex::from(2_usize);
    let kind = kind(arena);
    let own = arena.value_type_data(chain, vec![]);
    let unit = arena.value_type_unit();
    let returns = arena.comp_type_returner(unit);
    let test = consuming(arena, own, returns);
    let tested = arena.comp_type_arrow(own, returns);
    let handing = arena.comp_type_arrow(test, tested);
    let handing = arena.value_type_thunk(handing);
    let handed = {
        let head = var(arena, DeBruijnIndex::from(1));
        let argument = var(arena, DeBruijnIndex::from(0));
        let applied = call(arena, head, &[argument]);
        function(arena, Binders::from(2), applied)
    };
    let done = arena.value_unit();
    let on_start = arena.computation_return(done);
    // Under the link's fields: `test` 0, `prev` 1, `c` 2.
    let held = var(arena, DeBruijnIndex::from(0));
    let applied = match consumer {
        Consumer::Before => {
            let prev = var(arena, DeBruijnIndex::from(1));
            call(arena, held, &[prev])
        },
        Consumer::Itself => {
            let link = var(arena, DeBruijnIndex::from(2));
            call(arena, held, &[link])
        },
        Consumer::Handed => {
            let helper = arena.value_constant(apply);
            let link = var(arena, DeBruijnIndex::from(2));
            call(arena, helper, &[held, link])
        },
    };
    let on_link = arena.computation_lambda(applied);
    let on_link = arena.computation_lambda(on_link);
    let scrutinee = var(arena, DeBruijnIndex::from(0));
    let case = arena.computation_data_case(scrutinee, returns, vec![on_start, on_link]);
    let body = function(arena, Binders::from(1), case);
    [
        data(
            chain,
            DataSignature::new(vec![], vec![vec![], vec![own, test]], kind),
        ),
        definition(apply, handing, handed),
        definition(consuming_at, test, body),
    ]
}

/// `Chain`'s test consumes the family under a domain, so a link's test
/// takes chains one stage below the link: the block declares, and a
/// consumer applying the test to the chain before the link is admitted
/// and readmitted.
#[test]
fn a_negative_occurrence_below_the_stage_declares()
{
    let mut arena = CoreArena::new();
    let declarations = chain(&mut arena, Consumer::Before);
    let (report, crossed) = run(&mut arena, &declarations);
    assert_eq!(report.judged()[0].verdict(), Verdict::Data);
    assert!(
        matches!(report.judged()[2].verdict(), Verdict::Checked { .. }),
        "{:?}",
        report.judged()[2].verdict()
    );
    for (position, readmitted) in crossed.readmitted().iter().enumerate() {
        assert!(
            matches!(readmitted.outcome(), Outcome::Data { admitted, .. } | Outcome::Defined { admitted, .. } if admitted.position() == ConstantIndex::from(position)),
            "{position}: {:?}",
            readmitted.outcome()
        );
    }
}

/// Curry's consumer applies a link's test to the link itself, at no
/// stage the test takes: refused at the call, written directly or
/// through a helper, and nothing of it crosses.
#[test]
fn currys_consumer_is_refused_at_its_call()
{
    for consumer in [Consumer::Itself, Consumer::Handed] {
        let mut arena = CoreArena::new();
        let declarations = chain(&mut arena, consumer);
        let (report, crossed) = run(&mut arena, &declarations);
        assert!(
            matches!(
                report.judged()[2].verdict(),
                Verdict::Refused(CheckRefusal::StageNotBelow {
                    found: Standing::Top,
                    ..
                })
            ),
            "{consumer:?}: {:?}",
            report.judged()[2].verdict()
        );
        assert!(
            !matches!(crossed.readmitted()[2].outcome(), Outcome::Defined { .. }),
            "{consumer:?}"
        );
    }
}

/// `Rose`, `node : (kids : List ⌜Rose⌝)`, nests the family through
/// `List`'s strictly positive parameter: the block declares, a node with
/// no children is a rose, and both are readmitted.
#[test]
fn a_nested_occurrence_through_a_strictly_positive_parameter_declares()
{
    let mut arena = CoreArena::new();
    let [nat, list_signature, ..] = signatures(&mut arena);
    let rose = ConstantIndex::from(2_usize);
    let sprig = ConstantIndex::from(3_usize);
    let kind = kind(&mut arena);
    let own = arena.value_type_data(rose, vec![]);
    let code = arena.value_quote(own);
    let kids = list(&mut arena, code);
    let none = arena.value_constructor(kids, ConstructorTag::from(0_usize), vec![]);
    let node = arena.value_constructor(own, ConstructorTag::from(0_usize), vec![none]);
    let declarations = [
        data(ConstantIndex::from(at::NAT), nat),
        data(ConstantIndex::from(at::LIST), list_signature),
        data(rose, DataSignature::new(vec![], vec![vec![kids]], kind)),
        definition(sprig, own, node),
    ];
    let (report, crossed) = run(&mut arena, &declarations);
    assert_eq!(report.judged()[2].verdict(), Verdict::Data);
    assert!(
        matches!(report.judged()[3].verdict(), Verdict::Checked { .. }),
        "{:?}",
        report.judged()[3].verdict()
    );
    for (position, readmitted) in crossed.readmitted().iter().enumerate() {
        assert!(
            matches!(readmitted.outcome(), Outcome::Data { admitted, .. } | Outcome::Defined { admitted, .. } if admitted.position() == ConstantIndex::from(position)),
            "{position}: {:?}",
            readmitted.outcome()
        );
    }
}

/// A family's field may name a type or a constant only from an earlier
/// position: an abstract type, or the element of a constant code, at a
/// later position is a cross-block reference, and at the family's own
/// position an index occurrence.
#[test]
fn a_field_naming_its_own_or_a_later_position_is_refused_by_name()
{
    let field = OccurrenceSite::Field {
        tag: ConstructorTag::from(0_usize),
        field: FieldPosition::from(0_usize),
    };
    let position = ConstantIndex::from(0);
    let later = ConstantIndex::from(1);
    let named = |abstract_type, target| {
        let mut arena = CoreArena::new();
        let universe = kind(&mut arena);
        let field = if abstract_type {
            arena.value_type_abstract(target)
        }
        else {
            let code = arena.value_constant(target);
            arena.value_type_element(code, Level::zero())
        };
        let declaration = Declaration::data(
            position,
            Arc::new(DataSignature::new(vec![], vec![vec![field]], universe)),
            origin(position),
        );
        let report = check_module(
            &mut CheckingContext::new(&mut arena, CheckBudget::DEFAULT),
            &[declaration],
        );
        report.judged()[0].verdict()
    };
    for (abstract_type, what) in [(true, "an abstract type"), (false, "a constant's element")] {
        assert_eq!(
            named(abstract_type, later),
            Verdict::Refused(CheckRefusal::CrossBlockReference {
                site: field,
                index: later,
            }),
            "{what} at a later position is a cross-block reference"
        );
        assert_eq!(
            named(abstract_type, position),
            Verdict::Refused(CheckRefusal::IndexOccurrence(field)),
            "{what} at the family's own position is an index occurrence"
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
        // At an application's head a fixpoint checks against the arrow from
        // its argument's synthesised type: `(fix rec. λx. return x) ()`.
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
            report.judged()[1].verdict(),
            crossed.readmitted()[0].outcome().clone(),
            crossed.readmitted()[1].outcome().clone(),
        )
    };
    let ((checked, _), applied, crossed, crossed_applied) = looping(FixpointEvidence::Partial);
    assert!(matches!(checked, Verdict::Checked { .. }), "{checked:?}");
    assert!(matches!(crossed, Outcome::Defined { .. }), "{crossed:?}");
    assert!(matches!(applied, Verdict::Checked { .. }), "{applied:?}");
    assert!(
        matches!(crossed_applied, Outcome::Defined { .. }),
        "the kernel replays the applied fixpoint's rule: {crossed_applied:?}"
    );
    // A structural claim at `F 1` has no arrow whose domain a stage could
    // refine.
    let ((claimed, fixpoint), ..) = looping(FixpointEvidence::StructuralDescent);
    assert!(
        matches!(
            claimed,
            Verdict::Refused(CheckRefusal::ShapeMismatch {
                at: TermNode::Computation(at),
                wanted: ExpectedShape::Arrow,
                ..
            }) if at == fixpoint
        ),
        "{claimed:?}"
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

/// A function field into another type is a plain field: `Box(U (Integer
/// → F Integer))` takes no hypothesis there, so a motive naming its
/// scrutinee derives, where at a function field into the family it is
/// refused.
#[test]
fn a_function_field_into_another_type_takes_no_hypothesis()
{
    let mut arena = CoreArena::new();
    let kind = kind(&mut arena);
    let integer = arena.value_type_base(gandr_kernel_term::BaseType::Integer);
    let returns = arena.comp_type_returner(integer);
    let arrow = arena.comp_type_arrow(integer, returns);
    let field = arena.value_type_thunk(arrow);
    let position = ConstantIndex::from(0_usize);
    let signature = DataSignature::new(vec![], vec![vec![field]], kind);
    let own = arena.value_type_data(position, vec![]);
    let scrutinee = var(&mut arena, DeBruijnIndex::from(0));
    let naming = arena.value_type_path(own, scrutinee, scrutinee);
    let naming = arena.comp_type_returner(naming);
    let derived = eliminator::derive(&mut arena, position, &signature, naming);
    assert!(
        derived.is_ok(),
        "a function into the integers is no recursive field: {derived:?}"
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
    decision.map(|node: TraceNode| match node {
        TraceNode::Constant(constant) => match positions.get(&constant) {
            Some(&position) => ReplayNode::Constant(position),
            None => ReplayNode::Other,
        },
        TraceNode::Value(_) | TraceNode::Computation(_) => ReplayNode::Other,
    })
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
            Outcome::Defined { admitted, .. } | Outcome::Data { admitted, .. } => {
                Some((entry.constant(), admitted.position()))
            },
            Outcome::Assumed { .. }
            | Outcome::Marked(_)
            | Outcome::Static
            | Outcome::Suspended
            | Outcome::Refused(_)
            | Outcome::Rejected(_) => None,
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
        let right = gandr_core_nbe::eval_computation(arena, &mut domain, definitions, fuel, right)
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
                gandr_kernel_term::DeclarationContent::Def { body, .. } => Unfoldable::Body(body),
                gandr_kernel_term::DeclarationContent::Data { .. }
                | gandr_kernel_term::DeclarationContent::Codata { .. }
                | gandr_kernel_term::DeclarationContent::Axiom { .. }
                | gandr_kernel_term::DeclarationContent::AbstractType { .. } => Unfoldable::Opaque,
            })
            .collect(),
    );
    let nat = positions[&ConstantIndex::from(at::NAT)];
    let nat_type = kernel.value_type_data(nat, vec![]);
    let kernel_numeral = |kernel: &mut gandr_kernel_term::TermArena, n: usize| {
        let mut built = kernel.value_constructor(nat_type, ConstructorTag::from(0_usize), vec![]);
        for _step in 0 .. n {
            built = kernel.value_constructor(nat_type, ConstructorTag::from(1_usize), vec![built]);
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

/// Where the second constructor of a universe names its decoder.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Decoded
{
    /// `PiC : (a : U, b : U (El(el a) → F U))`: at the field before.
    Below,
    /// `Odd : (b : U (El(el later) → F U))`, `later : U` a definition
    /// after the decoder: at a code no case put below the decoder's stage.
    Level,
    /// `Ahead : (a : U, b : U (El(later a) → F U))`: a definition after
    /// the decoder, which the decoder's own body names.
    Ahead,
}

/// A universe `U` — `NatC` and the constructor `decoded` names — its
/// decoder `el : U (U → F Type)`, `fix self. λu. case u of { NatC ↦
/// return ⌜1⌝; _ ↦ λ…. return ⌜1⌝ }`, and a definition `later` after it:
/// the code `NatC` for [`Decoded::Level`], and for [`Decoded::Ahead`] the
/// function the decoder's second arm calls.
///
/// # Specification
/// trivial.
fn universe(
    arena: &mut CoreArena,
    decoded: Decoded,
) -> Vec<Declaration>
{
    let family = ConstantIndex::from(0);
    let decoder = ConstantIndex::from(1);
    let later = ConstantIndex::from(2);
    let kind = kind(arena);
    let own = arena.value_type_data(family, vec![]);
    let returner = arena.comp_type_returner(own);
    let decoding = |arena: &mut CoreArena, named: ConstantIndex, argument: ValueId| {
        let head = arena.value_constant(named);
        let forced = arena.computation_force(head);
        let call = arena.computation_application(forced, argument);
        let code = arena.value_returned(call);
        let decoded = arena.value_type_element(code, Level::zero());
        let arrow = arena.comp_type_arrow(decoded, returner);
        arena.value_type_thunk(arrow)
    };
    let nat_code = arena.value_constructor(own, ConstructorTag::from(0_usize), vec![]);
    let fields = match decoded {
        Decoded::Below => {
            let earlier = var(arena, DeBruijnIndex::from(0));
            vec![own, decoding(arena, decoder, earlier)]
        },
        Decoded::Level => {
            let named = arena.value_constant(later);
            vec![decoding(arena, decoder, named)]
        },
        Decoded::Ahead => {
            let earlier = var(arena, DeBruijnIndex::from(0));
            vec![own, decoding(arena, later, earlier)]
        },
    };
    let arity = fields.len();
    let types = kind;
    let returns = arena.comp_type_returner(types);
    let classifier = arena.comp_type_arrow(own, returns);
    let declared = arena.value_type_thunk(classifier);
    let unit = arena.value_type_unit();
    let code = arena.value_quote(unit);
    let answer = arena.computation_return(code);
    let mut arm = match decoded {
        Decoded::Below | Decoded::Level => answer,
        Decoded::Ahead => {
            let head = arena.value_constant(later);
            let forced = arena.computation_force(head);
            arena.computation_application(forced, nat_code)
        },
    };
    for _field in 0 .. arity {
        arm = arena.computation_lambda(arm);
    }
    let scrutinee = var(arena, DeBruijnIndex::from(0));
    let case = arena.computation_data_case(scrutinee, returns, vec![answer, arm]);
    let lambda = arena.computation_lambda(case);
    let fixpoint = arena.computation_fixpoint(lambda, FixpointEvidence::StructuralDescent);
    let body = arena.value_thunk(fixpoint);
    let mut declarations = vec![
        data(
            family,
            DataSignature::new(vec![], vec![vec![], fields], kind),
        ),
        definition(decoder, declared, body),
    ];
    match decoded {
        Decoded::Ahead => {
            let ignored = arena.computation_lambda(answer);
            let constant = arena.value_thunk(ignored);
            declarations.push(definition(later, declared, constant));
        },
        Decoded::Level => declarations.push(definition(later, own, nat_code)),
        Decoded::Below => {},
    }
    declarations
}

/// A universe whose constructor names its decoder at the field before is
/// judged and readmitted with the decoder as one block; at a place that
/// does not descend below the decoder's stage both checkers refuse it;
/// and a decoder whose body names a later definition of its block is
/// refused as a forward reference — the foresight its family's fields
/// rest on does not reach its body.
#[test]
fn a_mutual_block_is_admitted_in_both_checkers()
{
    let mut arena = CoreArena::new();
    let declarations = universe(&mut arena, Decoded::Below);
    let (report, crossed) = run(&mut arena, &declarations);
    assert_eq!(report.judged()[0].verdict(), Verdict::Data);
    assert!(
        matches!(report.judged()[1].verdict(), Verdict::Checked { .. }),
        "{:?}",
        report.judged()[1].verdict()
    );
    assert!(
        matches!(crossed.readmitted()[0].outcome(), Outcome::Data { admitted, .. } if admitted.position() == ConstantIndex::from(0)),
        "{:?}",
        crossed.readmitted()[0].outcome()
    );
    assert!(
        matches!(crossed.readmitted()[1].outcome(), Outcome::Defined { admitted, .. } if admitted.position() == ConstantIndex::from(1)),
        "{:?}",
        crossed.readmitted()[1].outcome()
    );
    let mut arena = CoreArena::new();
    let declarations = universe(&mut arena, Decoded::Level);
    let (report, _) = run(&mut arena, &declarations);
    assert_eq!(
        report.judged()[0].verdict(),
        report.judged()[1].verdict(),
        "the family is refused with its decoder: the block is one admission"
    );
    assert!(
        matches!(
            report.judged()[1].verdict(),
            Verdict::Refused(CheckRefusal::StageNotBelow { .. })
        ),
        "{:?}",
        report.judged()[1].verdict()
    );
    let mut arena = CoreArena::new();
    let declarations = universe(&mut arena, Decoded::Ahead);
    let (report, _) = run(&mut arena, &declarations);
    assert!(
        matches!(
            report.judged()[1].verdict(),
            Verdict::Refused(CheckRefusal::UnknownConstant { .. })
        ),
        "{:?}",
        report.judged()[1].verdict()
    );
    assert_eq!(
        report.judged()[0].verdict(),
        report.judged()[1].verdict(),
        "the family is refused with its decoder"
    );
}

/// Where a rose tree's recursion over its block's two families calls
/// itself.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Rose
{
    /// At the node's forest of children, and a forest's head and tail:
    /// each a field one stage below its scrutinee.
    Below,
    /// At the node itself: the scrutinee, at the fixpoint's own stage.
    Level,
}

/// `Rose`, `Node : (kids : Forest) → Rose`, and `Forest`, `Nil` and
/// `Cons : (head : Rose, tail : Forest) → Forest`, one block; then the
/// recursion over both, `fix self. λx. case x of { t ↦ case t of { Node ↦
/// λkids. self (inr kids) }; ts ↦ case ts of { Nil ↦ return (); Cons ↦
/// λhead tail. _ ← self (inl head); self (inr tail) } }`, at `U (Rose +
/// Forest → F 1)`, `rose` naming where the node's arm calls.
///
/// # Specification
/// trivial.
fn forest(
    arena: &mut CoreArena,
    rose: Rose,
) -> Vec<Declaration>
{
    let tree = ConstantIndex::from(0_usize);
    let forest = ConstantIndex::from(1_usize);
    let size = ConstantIndex::from(2_usize);
    let kind = kind(arena);
    let trees = arena.value_type_data(tree, vec![]);
    let forests = arena.value_type_data(forest, vec![]);
    let unit = arena.value_type_unit();
    let returns = arena.comp_type_returner(unit);
    // `force self (inj v)`, `self` the variable at `own`.
    let call = |arena: &mut CoreArena, own: u32, summand: usize, argument: u32| {
        let head = var(arena, DeBruijnIndex::from(own));
        let forced = arena.computation_force(head);
        let argument = var(arena, DeBruijnIndex::from(argument));
        let injected = arena.value_injection(gandr_kernel_term::Summand::from(summand), argument);
        arena.computation_application(forced, injected)
    };
    // Under `self, x, t, kids`: the children, or the node `t` itself.
    let node_arm = match rose {
        Rose::Below => call(arena, 3, 1, 0),
        Rose::Level => call(arena, 3, 0, 1),
    };
    let node_arm = arena.computation_lambda(node_arm);
    let scrutinee = var(arena, DeBruijnIndex::from(0_u32));
    let on_tree = arena.computation_data_case(scrutinee, returns, vec![node_arm]);
    let unit_value = arena.value_unit();
    let on_nil = arena.computation_return(unit_value);
    // Under `self, x, ts, head, tail`, then the bind's binder.
    let on_head = call(arena, 4, 0, 1);
    let on_tail = call(arena, 5, 1, 1);
    let on_cons = arena.computation_bind(on_head, on_tail);
    let on_cons = arena.computation_lambda(on_cons);
    let on_cons = arena.computation_lambda(on_cons);
    let scrutinee = var(arena, DeBruijnIndex::from(0_u32));
    let on_forest = arena.computation_data_case(scrutinee, returns, vec![on_nil, on_cons]);
    let scrutinee = var(arena, DeBruijnIndex::from(0_u32));
    let cased = arena.computation_case(scrutinee, &[on_tree, on_forest]);
    let body = arena.computation_lambda(cased);
    let fixpoint = arena.computation_fixpoint(body, FixpointEvidence::StructuralDescent);
    let value = arena.value_thunk(fixpoint);
    let both = arena.value_type_sum(&[trees, forests]);
    let arrow = arena.comp_type_arrow(both, returns);
    let declared = arena.value_type_thunk(arrow);
    vec![
        data(tree, DataSignature::new(vec![], vec![vec![forests]], kind)),
        data(
            forest,
            DataSignature::new(vec![], vec![vec![], vec![trees, forests]], kind),
        ),
        definition(size, declared, value),
    ]
}

/// A recursion at the sum of a mutual block's two families opens one
/// stage for both: a node's children and a forest's head and tail each
/// stand one stage below their scrutinee, so the calls on them are
/// admitted and readmitted, and a call on the node itself is refused.
#[test]
fn a_mutual_recursion_descends_through_its_block_s_families_in_both_checkers()
{
    let mut arena = CoreArena::new();
    let declarations = forest(&mut arena, Rose::Below);
    let (report, crossed) = run(&mut arena, &declarations);
    assert!(
        matches!(report.judged()[2].verdict(), Verdict::Checked { .. }),
        "{:?}",
        report.judged()[2].verdict()
    );
    assert!(
        matches!(crossed.readmitted()[2].outcome(), Outcome::Defined { admitted, .. } if admitted.position() == ConstantIndex::from(2)),
        "{:?}",
        crossed.readmitted()[2].outcome()
    );
    let mut arena = CoreArena::new();
    let declarations = forest(&mut arena, Rose::Level);
    let (report, _) = run(&mut arena, &declarations);
    assert!(
        matches!(
            report.judged()[2].verdict(),
            Verdict::Refused(CheckRefusal::StageNotBelow { .. })
        ),
        "{:?}",
        report.judged()[2].verdict()
    );
}

/// #776: a run judged in two stretches, the first ending where a mutual block
/// ends, a checkpoint taken between them and the second resumed over a copy of
/// the arena, reports what one run reports and mints the same arena — a block
/// left open at the checkpoint closed by the next declaration, and a refused
/// block still open at the checkpoint refused whole when the resumed run
/// finishes.
#[test]
fn a_run_resumed_from_a_checkpoint_judges_as_one_run_776()
{
    /// What builds a case's declarations into an arena.
    type Build = fn(&mut CoreArena) -> Vec<Declaration>;
    let cases: [(Build, usize); 2] = [
        (|arena| forest(arena, Rose::Below), 2_usize),
        (|arena| universe(arena, Decoded::Level), 3_usize),
    ];
    for (build, leading) in cases {
        let mut whole_arena = CoreArena::new();
        let declarations = build(&mut whole_arena);
        let mut split_arena = whole_arena.clone();
        let whole = check_module(
            &mut CheckingContext::new(&mut whole_arena, CheckBudget::DEFAULT),
            &declarations,
        );
        let (first, second) = declarations.split_at(leading);
        let mut run = ModuleRun::new();
        let checkpoint = {
            let mut context = CheckingContext::new(&mut split_arena, CheckBudget::DEFAULT);
            run.judge(&mut context, first, |_, _, _| {});
            context.checkpoint()
        };
        let mut resumed_arena = split_arena.clone();
        let mut context = CheckingContext::resume(&mut resumed_arena, checkpoint);
        run.judge(&mut context, second, |_, _, _| {});
        let resumed = run.finish(&mut context);
        assert_eq!(whole, resumed, "the resumed run reports as one run");
        assert_eq!(whole_arena, resumed_arena, "and mints the same arena");
    }
}

/// A block whose first family consumes its second where no stage reaches
/// it, `Left` holding `U (Lift Right → F 1)` and `Right` holding a
/// `Left`, is refused whole: the second family's own field is positive,
/// but the block is one admission, and the kernel refuses it as one.
#[test]
fn a_mutual_block_is_refused_whole_in_both_checkers()
{
    let mut arena = CoreArena::new();
    let left = ConstantIndex::from(0_usize);
    let right = ConstantIndex::from(1_usize);
    let kind = kind(&mut arena);
    let lefts = arena.value_type_data(left, vec![]);
    let rights = arena.value_type_data(right, vec![]);
    let unit = arena.value_type_unit();
    let returns = arena.comp_type_returner(unit);
    let lifted = arena.value_type_lift(rights, Level::zero());
    let consuming = arena.comp_type_arrow(lifted, returns);
    let consumer = arena.value_type_thunk(consuming);
    let declarations = [
        data(left, DataSignature::new(vec![], vec![vec![consumer]], kind)),
        data(right, DataSignature::new(vec![], vec![vec![lefts]], kind)),
    ];
    let (report, crossed) = run(&mut arena, &declarations);
    let field = OccurrenceSite::Field {
        tag: ConstructorTag::from(0_usize),
        field: FieldPosition::from(0_usize),
    };
    for entry in report.judged() {
        assert_eq!(
            entry.verdict(),
            Verdict::Refused(CheckRefusal::NegativeOccurrence(field)),
            "the block is refused whole"
        );
    }
    assert!(
        crossed
            .readmitted()
            .iter()
            .all(|entry| !matches!(entry.outcome(), Outcome::Data { .. })),
        "and nothing of it crosses"
    );
}

/// A family named through a definition of its block stands where the
/// definition is named: `Bad` holding `U (hidden → F 1)` with `hidden =
/// Bad` is refused, with `hidden`, as `Bad` holding `U (Bad → F 1)` is,
/// and nothing of the block crosses (#602).
#[test]
fn a_definition_of_the_block_is_read_through_602()
{
    let mut arena = CoreArena::new();
    let family = ConstantIndex::from(0_usize);
    let hidden = ConstantIndex::from(1_usize);
    let kind = kind(&mut arena);
    let named = arena.value_constant(hidden);
    let decoded = arena.value_type_element(named, Level::zero());
    let unit = arena.value_type_unit();
    let returns = arena.comp_type_returner(unit);
    let consuming = arena.comp_type_arrow(decoded, returns);
    let consumer = arena.value_type_thunk(consuming);
    let own = arena.value_type_data(family, vec![]);
    let quoted = arena.value_quote(own);
    let declarations = [
        data(
            family,
            DataSignature::new(vec![], vec![vec![consumer]], kind),
        ),
        definition(hidden, kind, quoted),
    ];
    let (report, crossed) = run(&mut arena, &declarations);
    let field = OccurrenceSite::Field {
        tag: ConstructorTag::from(0_usize),
        field: FieldPosition::from(0_usize),
    };
    for entry in report.judged() {
        assert_eq!(
            entry.verdict(),
            Verdict::Refused(CheckRefusal::NegativeOccurrence(field)),
            "the block is refused whole"
        );
    }
    assert!(
        crossed.readmitted().iter().all(|entry| !matches!(
            entry.outcome(),
            Outcome::Data { .. } | Outcome::Defined { .. }
        )),
        "and nothing of it crosses"
    );
}
