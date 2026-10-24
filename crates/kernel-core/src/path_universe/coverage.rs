//! Closed-code coverage and the iterative shadow of transport's beta rules.

use alloc::collections::BTreeSet;
use alloc::vec::Vec;

use anodized::spec;
use gandr_kernel_check_memo::NullMemo;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::ConstructorTag;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::Summand;
use gandr_kernel_term::TermArena;
use gandr_kernel_term::Value;
use gandr_kernel_term::ValueId;
use gandr_kernel_term::ValueType;
use gandr_kernel_term::ValueTypeId;

use super::Allowance;
use super::Direction;
use super::PathError;
use super::PatternPosition;
use crate::encoding::ContentTable;
use crate::env::Entries;
use crate::flow_universe::data_signature;
use crate::replay::EngineClaim;
use crate::replay::KernelVerdict;
use crate::replay::ReplayBudget;
use crate::replay::ReplaySides;
use crate::replay::Unfoldings;
use crate::rewrite::BinderDepth;
use crate::rewrite::shift_value;

/// Inspect quoted first-order shapes or finite guarded session graphs.
///
/// # Specification
/// - requires: the code root belongs to `arena`.
/// - ensures: outer formers are Base, Product (the unit among them), a Sum of
///   at least one summand, a List of a code among them, a data type
///   [`data_signature`] reads from `entries` and reached again nowhere inside
///   its own fields, or Session; session graph structure and guards check. The
///   empty sum is refused, as the retired empty type was. Native formation
///   separately checks session payload codes in an empty term context.
/// - provides: code-shape inspection, never a checking verdict.
/// - fails: `UnsupportedCode`, `UnsupportedType`, `Session`, `Arena` or
///   `Budget`.
/// - panics: none.
///
/// # Errors
/// As `fails`.
///
/// # Termination
/// - reason: a worklist over the finite type graph, each node expanded once; a
///   data type's declaration is held open until its fields are walked.
/// - measure: the nodes not yet expanded.
///
/// # Adequacy
/// - hypothesis: L3 — Bool, product, list and data codes admit; thunk codes and
///   a data type holding itself refuse.
/// - witness: `path_universe::tests::a_non_equivalence_is_refused`
/// - witness: `path_universe::tests::a_list_code_covers_one_cell_over_a_rigid_tail`
/// - witness: `path_universe::coverage::tests::a_data_code_covers_as_its_constructors`
/// - witness: `session::tests::session_codes_are_closed_and_contractive`
#[spec(
    captures: before = allowance.0,
    ensures: |ret| allowance.0 <= before && match ret {
        Ok(root) => allowance.0 < before && matches!(arena.value(code), Some(&Value::Quote(quoted)) if root == quoted),
        Err(PathError::UnsupportedCode(named)) => named == code && !matches!(arena.value(code), Some(&Value::Quote(_))),
        Err(PathError::UnsupportedType(root)) => arena.value_type(root).is_some_and(|node| !matches!(node, &ValueType::Base(_) | &ValueType::Product(..) | &ValueType::Session { .. } | &ValueType::List(_)) && node.summands().is_none_or(<[_]>::is_empty)),
        Err(PathError::Budget) => allowance.0 == 0,
        Err(PathError::Arena | PathError::Session(_)) => true,
        Err(_) => false,
    },
)]
pub(super) fn code(
    arena: &TermArena,
    code: ValueId,
    entries: &Entries,
    allowance: &mut Allowance,
) -> Result<ValueTypeId, PathError>
{
    let Some(&Value::Quote(root)) = arena.value(code)
    else {
        return Err(PathError::UnsupportedCode(code));
    };
    let mut pending = Vec::from([Walk::Visit(root)]);
    // The data declarations whose fields are being walked.
    let mut open = BTreeSet::new();
    let mut seen = BTreeSet::new();
    while let Some(next) = pending.pop() {
        allowance.charge()?;
        let id = match next {
            Walk::Visit(id) => id,
            Walk::Close(declaration) => {
                if !open.remove(&declaration) {
                    return Err(PathError::Arena);
                }
                continue;
            },
        };
        let node = arena.value_type(id).ok_or(PathError::Arena)?;
        // A first visit walks the whole of any cycle through the node, so a
        // recursive type meets its own open declaration before a repeat is
        // skipped.
        if let &ValueType::Data { declaration, .. } = node
            && open.contains(&declaration)
        {
            return Err(PathError::UnsupportedType(id));
        }
        if !seen.insert(id) {
            continue;
        }
        match node {
            &ValueType::Base(_) => {},
            &ValueType::Session {
                ref graph,
                payloads,
            } => {
                crate::session::validate_graph(arena, graph, payloads)
                    .map_err(PathError::Session)?;
                // Ordinary formation checks payload codes in an empty
                // telescope.
            },
            &ValueType::Sum(ref parts) if parts.is_empty() => {
                return Err(PathError::UnsupportedType(id));
            },
            &ValueType::Sum(ref parts) | &ValueType::Product(ref parts) => {
                pending.extend(parts.iter().rev().copied().map(Walk::Visit));
            },
            &ValueType::List(element) => pending.push(Walk::Visit(element)),
            &ValueType::Data { .. } => {
                let (declaration, constructors) =
                    data_signature(arena, entries, id).ok_or(PathError::UnsupportedType(id))?;
                open.insert(declaration);
                pending.push(Walk::Close(declaration));
                pending.extend(
                    constructors
                        .iter()
                        .flatten()
                        .rev()
                        .copied()
                        .map(Walk::Visit),
                );
            },
            &ValueType::Record(_)
            | &ValueType::PathUniverse(..)
            | &ValueType::FlowUniverse(..)
            | &ValueType::Path { .. }
            | &ValueType::Flow { .. }
            | &ValueType::Bridge { .. }
            | &ValueType::Sigma { .. }
            | &ValueType::Thunk(_)
            | &ValueType::Universe { .. }
            | &ValueType::Lift { .. }
            | &ValueType::Element { .. }
            | &ValueType::Abstract(_)
            | &ValueType::StaticPi { .. }
            | &ValueType::Staged { .. } => return Err(PathError::UnsupportedType(id)),
        }
    }
    Ok(root)
}

/// Code validation work.
enum Walk
{
    /// Visit one type.
    Visit(ValueTypeId),
    /// Close this data declaration: its fields have all been visited.
    Close(ConstantIndex),
}

/// A canonical constructor pattern with fresh rigid variables at base leaves
/// and list tails.
#[derive(Clone, Copy)]
struct Pattern
{
    /// The symbolic value; base and tail variables occur exactly once each.
    value: ValueId,
    /// The number of independent base variables bound outside this pattern.
    binders: BinderDepth,
}

/// A postorder coverage instruction.
#[derive(Clone, Copy)]
enum Cover
{
    /// Expand one type's constructor patterns.
    Visit(ValueTypeId),
    /// Join the patterns of this many summands with their distinct injection
    /// tags.
    Sum(usize),
    /// Form every tuple of this many components' patterns, renaming base
    /// variables apart.
    Product(usize),
    /// Form every application of this constructor of this data type to this
    /// many fields' patterns, renaming base variables apart.
    Constructor(ValueTypeId, ConstructorTag, usize),
    /// Join the patterns of this many constructors and close this data
    /// declaration, which opened them.
    Data(ConstantIndex, usize),
    /// The empty list, then each element pattern on top consed onto a fresh
    /// tail.
    List,
}

/// Enumerate constructor coverage without enumerating base inhabitants.
///
/// # Specification
/// - requires: `root` is a validated closed first-order type over `entries`.
/// - ensures: exactly one pattern per constructor choice; every base position
///   is a distinct rigid variable, including repeated base types in products. A
///   list unfolds one cell: the empty list, then each element pattern consed
///   onto a fresh rigid tail, the element read past the tail's binder. A data
///   type covers as its constructors in tag order, each applied to its fields'
///   patterns crossed as a product's.
/// - provides: a symbolic universal boundary for a round-trip dialogue.
/// - fails: `Arena`, `UnsupportedType` or `Budget`.
/// - panics: none.
/// - intension: sums are first-summand-first, products are lexicographic and a
///   list's empty pattern precedes its cells.
///
/// # Errors
/// As `fails`.
///
/// # Adequacy
/// - hypothesis: L3 — both Bool branches are required; a literal sample cannot
///   establish a Base round trip, while a generic product identity is admitted.
///   A product and a sum of three cover by position with distinct variables. A
///   list of booleans covers as the empty list and two cells over one tail. A
///   shape covers as a circle over one variable and a rectangle over two.
/// - witness: `path_universe::tests::a_non_equivalence_is_refused`
/// - witness: `path_universe::coverage::tests::n_ary_codes_cover_by_position`
/// - witness: `path_universe::tests::a_list_code_covers_one_cell_over_a_rigid_tail`
/// - witness: `path_universe::coverage::tests::a_data_code_covers_as_its_constructors`
#[spec(
    captures: before = allowance.0,
    ensures: |ret| allowance.0 <= before && match ret {
        Ok(ref patterns) => allowance.0 < before
            && patterns.iter().all(|pattern| arena.value(pattern.value).is_some())
            && match arena.value_type(root) {
Some(held) if held.product_parts() == Some(&[]) => patterns.len() == 1 && patterns.first().is_some_and(|pattern| u32::from(pattern.binders) == 0 && arena.value(pattern.value).and_then(Value::components) == Some(&[])),
                Some(&ValueType::Base(_)) => patterns.len() == 1 && patterns.first().is_some_and(|pattern| u32::from(pattern.binders) == 1 && matches!(arena.value(pattern.value), Some(&Value::Variable(index)) if u32::from(index) == 0)),
                Some(&ValueType::List(_)) => patterns.len() >= 2 && patterns.first().is_some_and(|pattern| u32::from(pattern.binders) == 0 && matches!(arena.value(pattern.value), Some(&Value::ListNil))),
                Some(&ValueType::Sum(..) | &ValueType::Product(..)) => !patterns.is_empty(),
                Some(&ValueType::Data { .. }) => !patterns.is_empty() && patterns.iter().all(|pattern| matches!(arena.value(pattern.value), Some(&Value::Constructor { datatype, .. }) if datatype == root)),
                _ => false,
            },
        Err(_) => true,
    },
)]
fn patterns(
    arena: &mut TermArena,
    root: ValueTypeId,
    entries: &Entries,
    allowance: &mut Allowance,
) -> Result<Vec<Pattern>, PathError>
{
    let mut pending = Vec::from([Cover::Visit(root)]);
    let mut results = Vec::<Vec<Pattern>>::new();
    let mut table = ContentTable::new();
    // The data declarations whose constructors are being covered.
    let mut open = BTreeSet::new();
    while let Some(task) = pending.pop() {
        allowance.charge()?;
        match task {
            Cover::Visit(id) => {
                let node = arena.value_type(id).ok_or(PathError::Arena)?;
                match node {
                    &ValueType::Base(_) => results.push(Vec::from([Pattern {
                        value: arena.value_variable(DeBruijnIndex::from(0_u32)),
                        binders: BinderDepth::from(1_u32),
                    }])),
                    &ValueType::Sum(ref parts) if parts.is_empty() => {
                        return Err(PathError::UnsupportedType(id));
                    },
                    &ValueType::Sum(ref parts) => {
                        pending.push(Cover::Sum(parts.len()));
                        pending.extend(parts.iter().rev().copied().map(Cover::Visit));
                    },
                    &ValueType::Product(ref parts) => {
                        pending.push(Cover::Product(parts.len()));
                        pending.extend(parts.iter().rev().copied().map(Cover::Visit));
                    },
                    &ValueType::List(element) => {
                        pending.push(Cover::List);
                        pending.push(Cover::Visit(element));
                    },
                    &ValueType::Data { declaration, .. } => {
                        if open.contains(&declaration) {
                            return Err(PathError::UnsupportedType(id));
                        }
                        let (declaration, constructors) = data_signature(arena, entries, id)
                            .ok_or(PathError::UnsupportedType(id))?;
                        open.insert(declaration);
                        pending.push(Cover::Data(declaration, constructors.len()));
                        for (tag, fields) in constructors.iter().enumerate().rev() {
                            pending.push(Cover::Constructor(
                                id,
                                ConstructorTag::from(tag),
                                fields.len(),
                            ));
                            pending.extend(fields.iter().rev().copied().map(Cover::Visit));
                        }
                    },
                    &ValueType::Record(_)
                    | &ValueType::Session { .. }
                    | &ValueType::PathUniverse(..)
                    | &ValueType::FlowUniverse(..)
                    | &ValueType::Path { .. }
                    | &ValueType::Flow { .. }
                    | &ValueType::Bridge { .. }
                    | &ValueType::Sigma { .. }
                    | &ValueType::Thunk(_)
                    | &ValueType::Universe { .. }
                    | &ValueType::Lift { .. }
                    | &ValueType::Element { .. }
                    | &ValueType::Abstract(_)
                    | &ValueType::StaticPi { .. }
                    | &ValueType::Staged { .. } => return Err(PathError::UnsupportedType(id)),
                }
            },
            Cover::Sum(arity) => {
                let start = results.len().checked_sub(arity).ok_or(PathError::Arena)?;
                let mut joined = Vec::new();
                for (summand, branch) in results.drain(start ..).enumerate() {
                    for pattern in branch {
                        allowance.charge()?;
                        joined.push(Pattern {
                            value: arena.value_injection(Summand::from(summand), pattern.value),
                            binders: pattern.binders,
                        });
                    }
                }
                results.push(joined);
            },
            // Each step crosses the tuples so far with the next component's
            // patterns; the earlier components' base variables shift past the
            // new component's, so every variable stays distinct. A constructor
            // crosses its fields the same way and applies itself to them.
            Cover::Product(arity) | Cover::Constructor(_, _, arity) => {
                let start = results.len().checked_sub(arity).ok_or(PathError::Arena)?;
                let mut tuples = Vec::from([(Vec::<ValueId>::new(), 0_u32)]);
                for component in results.drain(start ..) {
                    let mut crossed = Vec::new();
                    for &(ref prefix, binders) in &tuples {
                        for next in &component {
                            allowance.charge()?;
                            let binders = binders
                                .checked_add(u32::from(next.binders))
                                .ok_or(PathError::Budget)?;
                            let mut values = Vec::with_capacity(prefix.len().saturating_add(1));
                            for &earlier in prefix {
                                values.push(shift_value(
                                    arena,
                                    &mut table,
                                    &mut NullMemo,
                                    earlier,
                                    BinderDepth::default(),
                                    next.binders,
                                ));
                            }
                            values.push(next.value);
                            crossed.push((values, binders));
                        }
                    }
                    tuples = crossed;
                }
                let joined = tuples
                    .into_iter()
                    .map(|(values, binders)| Pattern {
                        value: match task {
                            Cover::Constructor(datatype, tag, _) => {
                                arena.value_constructor(datatype, tag, values)
                            },
                            Cover::Visit(_)
                            | Cover::Sum(_)
                            | Cover::Product(_)
                            | Cover::Data(..)
                            | Cover::List => arena.value_tuple(&values),
                        },
                        binders: BinderDepth::from(binders),
                    })
                    .collect();
                results.push(joined);
            },
            // The constructors' patterns in tag order, the data type closed.
            Cover::Data(declaration, count) => {
                let start = results.len().checked_sub(count).ok_or(PathError::Arena)?;
                let joined = results.drain(start ..).flatten().collect();
                results.push(joined);
                if !open.remove(&declaration) {
                    return Err(PathError::Arena);
                }
            },
            // The element shifts past the tail's binder; the tail is the
            // innermost variable.
            Cover::List => {
                let elements = results.pop().ok_or(PathError::Arena)?;
                let mut joined = Vec::with_capacity(elements.len().saturating_add(1));
                joined.push(Pattern {
                    value: arena.value_list_nil(),
                    binders: BinderDepth::default(),
                });
                for element in elements {
                    allowance.charge()?;
                    let binders = u32::from(element.binders)
                        .checked_add(1)
                        .ok_or(PathError::Budget)?;
                    let head = shift_value(
                        arena,
                        &mut table,
                        &mut NullMemo,
                        element.value,
                        BinderDepth::default(),
                        BinderDepth::from(1_u32),
                    );
                    let tail = arena.value_variable(DeBruijnIndex::from(0_u32));
                    joined.push(Pattern {
                        value: arena.value_list_cons(head, tail),
                        binders: BinderDepth::from(binders),
                    });
                }
                results.push(joined);
            },
        }
    }
    results.pop().ok_or(PathError::Arena)
}

/// Construct and replay every component of one universal round-trip claim.
///
/// # Specification
/// - requires: the translators are closed and checked at opposite arrows; every
///   body `unfoldings` defines lives in `arena`; `source` is a code validated
///   over `entries`.
/// - ensures: every code-generated pattern replays `Convertible` under
///   `unfoldings`, so a translator may name a definition admitted before it; no
///   supplied dialogue chooses its own boundary, suppresses a pattern, or adds
///   one.
/// - provides: formation evidence derived by the existing kernel replay.
/// - fails: `Coverage` on dialogue cardinality, `RoundTrip` on failed replay,
///   or the code-pattern construction error.
/// - panics: none.
///
/// # Errors
/// `Coverage`, `RoundTrip`, `Arena`, `UnsupportedType`, or `Budget`.
///
/// # Adequacy
/// - hypothesis: L3 — constant true fails on the false branch; missing,
///   additional and forged dialogues cannot make formation succeed; negation
///   named by an admitted definition replays its δ-steps.
/// - witness: `path_universe::tests::a_non_equivalence_is_refused`
/// - witness: `path_universe::tests::a_translator_may_name_an_admitted_definition`
#[spec(ensures: |ret| match ret {
    Ok(()) => u64::from(budget) > 0 && !dialogues.is_empty(),
    Err(PathError::Coverage(found)) => found == direction,
    Err(PathError::RoundTrip { direction: found, pattern, verdict }) => found == direction && pattern.0 < dialogues.len() && verdict != KernelVerdict::Convertible,
    Err(PathError::Arena | PathError::UnsupportedType(_) | PathError::Budget) => true,
    Err(_) => false,
})]
pub fn round_trip(
    arena: &mut TermArena,
    (unfoldings, entries): (&Unfoldings, &Entries),
    (source, direction): (ValueTypeId, Direction),
    (forward, backward): (ValueId, ValueId),
    dialogues: &[Vec<gandr_kernel_conversion_trace::ConversionDecision<()>>],
    budget: ReplayBudget,
) -> Result<(), PathError>
{
    let patterns = patterns(arena, source, entries, &mut Allowance(u64::from(budget)))?;
    if patterns.len() != dialogues.len() {
        return Err(PathError::Coverage(direction));
    }
    for (position, (pattern, dialogue)) in patterns.into_iter().zip(dialogues).enumerate() {
        let first = arena.computation_force(forward);
        let first = arena.computation_application(first, pattern.value);
        let second = arena.computation_force(backward);
        let variable = arena.value_variable(DeBruijnIndex::from(0_u32));
        let second = arena.computation_application(second, variable);
        let composite = arena.computation_bind(first, second);
        let identity = arena.computation_return(pattern.value);
        let verdict = crate::replay::replay(
            arena,
            unfoldings,
            ReplaySides::Computations(composite, identity),
            EngineClaim::Convertible,
            dialogue.iter().copied().map(super::anchor),
            budget,
        );
        if verdict != KernelVerdict::Convertible {
            return Err(PathError::RoundTrip {
                direction,
                pattern: PatternPosition(position),
                verdict,
            });
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests
{
    use alloc::vec;
    use alloc::vec::Vec;

    use gandr_kernel_strata::Level;
    use gandr_kernel_term::BaseType;
    use gandr_kernel_term::ConstantIndex;
    use gandr_kernel_term::ConstructorTag;
    use gandr_kernel_term::GroundSort;
    use gandr_kernel_term::LevelSignature;
    use gandr_kernel_term::Summand;
    use gandr_kernel_term::TermArena;
    use gandr_kernel_term::Value;

    use super::Allowance;
    use super::patterns;
    use crate::path_universe::PathError;

    /// A product of three base types covers in one pattern whose three base
    /// variables stay distinct, first component outermost; a sum of three
    /// covers in one pattern per summand, tagged by position; the empty sum is
    /// outside the vocabulary.
    #[test]
    fn n_ary_codes_cover_by_position()
    {
        let mut arena = TermArena::new();
        let integer = arena.value_type_base(BaseType::Integer);
        let triple = arena.value_type_product(&[integer, integer, integer]);
        let covered = patterns(
            &mut arena,
            triple,
            &crate::env::NO_ENTRIES,
            &mut Allowance(u64::MAX),
        )
        .expect("a product covers");
        let [ref only] = *covered.as_slice()
        else {
            panic!("one pattern for a product of base types");
        };
        assert_eq!(3_u32, u32::from(only.binders));
        let components = arena
            .value(only.value)
            .and_then(Value::components)
            .expect("a tuple")
            .to_vec();
        let indices = components
            .iter()
            .map(|&component| match arena.value(component) {
                Some(&Value::Variable(index)) => u32::from(index),
                _ => panic!("a base position is a variable"),
            })
            .collect::<Vec<_>>();
        assert_eq!(vec![2_u32, 1_u32, 0_u32], indices);

        let unit = arena.value_type_unit();
        let choice = arena.value_type_sum(&[unit, unit, unit]);
        let covered = patterns(
            &mut arena,
            choice,
            &crate::env::NO_ENTRIES,
            &mut Allowance(u64::MAX),
        )
        .expect("a sum covers");
        let summands = covered
            .iter()
            .map(|pattern| match arena.value(pattern.value) {
                Some(&Value::Injection(summand, _)) => summand,
                _ => panic!("a sum pattern is an injection"),
            })
            .collect::<Vec<_>>();
        assert_eq!(
            vec![
                Summand::from(0_usize),
                Summand::from(1_usize),
                Summand::from(2_usize)
            ],
            summands
        );

        let empty = arena.value_type_empty();
        assert!(matches!(
            patterns(&mut arena, empty, &crate::env::NO_ENTRIES, &mut Allowance(u64::MAX)),
            Err(PathError::UnsupportedType(found)) if found == empty
        ));
    }

    /// A quoted empty sum is no code a path carries, at its root or beneath
    /// a product.
    #[test]
    fn an_empty_sum_is_no_path_code()
    {
        let mut arena = TermArena::new();
        let empty = arena.value_type_empty();
        let integer = arena.value_type_base(BaseType::Integer);
        let holding = arena.value_type_product(&[integer, empty]);
        for root in [empty, holding] {
            let quoted = arena.value_quote(root);
            assert_eq!(
                super::code(
                    &arena,
                    quoted,
                    &crate::env::NO_ENTRIES,
                    &mut Allowance(u64::MAX)
                ),
                Err(PathError::UnsupportedType(empty))
            );
        }
    }

    /// A data code covers as its constructors in tag order, each applied to
    /// its own fields' variables, first field outermost; a data type holding
    /// itself, and one the admitted prefix does not hold, is no code a path
    /// carries.
    #[test]
    fn a_data_code_covers_as_its_constructors()
    {
        let mut environment = crate::env::Environment::new();
        let mut staging = environment.stage();
        let kind = staging
            .arena()
            .value_type_universe(GroundSort::Value, Level::zero());
        let integer = staging.arena().value_type_base(BaseType::Integer);
        let staged = staging.data(
            LevelSignature::monomorphic(),
            Vec::new(),
            vec![vec![integer], vec![integer, integer]],
            kind,
        );
        let _shape = environment.add_decl(staged).expect("the shape admits");
        let mut staging = environment.stage();
        let kind = staging
            .arena()
            .value_type_universe(GroundSort::Value, Level::zero());
        let own = staging
            .arena()
            .value_type_data(ConstantIndex::from(1_usize), Vec::new());
        let staged = staging.data(
            LevelSignature::monomorphic(),
            Vec::new(),
            vec![Vec::new(), vec![own]],
            kind,
        );
        let _naturals = environment.add_decl(staged).expect("the naturals admit");
        let entries = environment.entries();
        let mut arena = environment.arena().clone();

        let shape = arena.value_type_data(ConstantIndex::from(0_usize), Vec::new());
        let quoted = arena.value_quote(shape);
        assert_eq!(
            super::code(&arena, quoted, entries, &mut Allowance(u64::MAX)),
            Ok(shape),
            "a shape is a code a path carries"
        );
        let covered =
            patterns(&mut arena, shape, entries, &mut Allowance(u64::MAX)).expect("a shape covers");
        let [ref circle, ref rectangle] = *covered.as_slice()
        else {
            panic!("one pattern per constructor");
        };
        for (pattern, tag, variables) in
            [(circle, 0_usize, vec![0_u32]), (rectangle, 1, vec![1, 0])]
        {
            let Some(&Value::Constructor {
                datatype,
                tag: found,
                ref fields,
            }) = arena.value(pattern.value)
            else {
                panic!("a constructor pattern");
            };
            assert_eq!((shape, ConstructorTag::from(tag)), (datatype, found));
            let indices = fields
                .iter()
                .map(|&field| match arena.value(field) {
                    Some(&Value::Variable(index)) => u32::from(index),
                    _ => panic!("a field of base type is a variable"),
                })
                .collect::<Vec<_>>();
            assert_eq!(
                u32::try_from(variables.len()).expect("a field count fits"),
                u32::from(pattern.binders),
                "one binder per base field"
            );
            assert_eq!(variables, indices, "the first field outermost");
        }

        let naturals = arena.value_type_data(ConstantIndex::from(1_usize), Vec::new());
        for (root, prefix) in [(naturals, entries), (shape, &crate::env::NO_ENTRIES)] {
            let quoted = arena.value_quote(root);
            assert!(
                matches!(
                    super::code(&arena, quoted, prefix, &mut Allowance(u64::MAX)),
                    Err(PathError::UnsupportedType(_))
                ),
                "a type holding itself, or one outside the prefix"
            );
        }
    }
}
