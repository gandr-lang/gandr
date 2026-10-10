//! One generic harness for three different simply-sorted binding signatures.

use gandr_theory_levitation::AdmissionError;
use gandr_theory_levitation::BindingError;
use gandr_theory_levitation::BindingJudgement;
use gandr_theory_levitation::BindingTerm;
use gandr_theory_levitation::FirstOrderJudgement;
use gandr_theory_levitation::FreeTerm;
use gandr_theory_levitation::Name;
use gandr_theory_levitation::Representability;
use gandr_theory_levitation::SignDesc;
use gandr_theory_levitation::SimplySorted;
use gandr_theory_levitation::SortDesc;
use gandr_theory_levitation::SortIndex;
use gandr_theory_levitation::SortRef;
use gandr_theory_levitation::TranslationError;
use gandr_theory_levitation::VariableIndex;

use super::DeclPolarity;
use super::op;
use super::signature;

/// A selected finite variable position.
///
/// # Specification
/// trivial.
fn v(index: VariableIndex) -> BindingTerm
{
    BindingTerm::variable(index)
}

/// An operation term; fixture names are data, never interpreter cases.
///
/// # Specification
/// trivial.
fn t<const N: usize>(
    name: Name,
    arguments: [BindingTerm; N],
) -> BindingTerm
{
    BindingTerm::operation(name, arguments)
}

/// Two sorts, only one representable, with a binder in the second argument.
///
/// # Specification
/// trivial.
fn computations() -> SignDesc<()>
{
    signature(
        "Computations",
        vec![
            SortDesc::new("V", DeclPolarity::Data).representable(),
            SortDesc::new("C", DeclPolarity::Data),
        ],
        vec![
            op("lit", vec![], SortRef::new("", "V")),
            op("halt", vec![], SortRef::new("", "C")),
            op(
                "ret",
                vec![SortRef::new("value", "V")],
                SortRef::new("", "C"),
            ),
            op(
                "bind",
                vec![
                    SortRef::new("first", "C"),
                    SortRef::new("then", "C").pi_plus([SortIndex::new("x", "V")]),
                ],
                SortRef::new("", "C"),
            ),
        ],
    )
}

/// Three sorts, two representable, with unequal mixed binder telescopes.
///
/// # Specification
/// trivial.
fn mixed() -> SignDesc<()>
{
    signature(
        "Mixed",
        vec![
            SortDesc::new("A", DeclPolarity::Data).representable(),
            SortDesc::new("B", DeclPolarity::Data).representable(),
            SortDesc::new("R", DeclPolarity::Data),
        ],
        vec![
            op("a", vec![], SortRef::new("", "A")),
            op("b", vec![], SortRef::new("", "B")),
            op("empty", vec![], SortRef::new("", "R")),
            op(
                "pack",
                vec![SortRef::new("a", "A"), SortRef::new("b", "B")],
                SortRef::new("", "R"),
            ),
            op(
                "scope",
                vec![
                    SortRef::new("body", "R").pi_plus([
                        SortIndex::new("a1", "A"),
                        SortIndex::new("b", "B"),
                        SortIndex::new("a2", "A"),
                    ]),
                    SortRef::new("alternative", "A").pi_plus([SortIndex::new("b", "B")]),
                    SortRef::new("outside", "B"),
                ],
                SortRef::new("", "R"),
            ),
        ],
    )
}

/// Independently specified inputs to both directions of the identification.
struct Fixture
{
    /// Signature data consumed by the same implementation.
    signature: SignDesc<()>,
    /// De Bruijn binding syntax.
    binding: BindingJudgement,
    /// Independently authored q/p syntax, not obtained by the forward map.
    first_order: FirstOrderJudgement,
}

/// Three hand-derived asymmetric judgements, including open references.
///
/// # Specification
/// trivial.
fn fixtures() -> Vec<Fixture>
{
    let lc_context = vec![Name::from("Tm"), Name::from("Tm")];
    let computation_context = vec![Name::from("V"), Name::from("V")];
    let mixed_context = vec![Name::from("A"), Name::from("B"), Name::from("A")];
    vec![
        Fixture {
            signature: super::lc(),
            binding: BindingJudgement {
                context: lc_context.clone(),
                sort: Name::from("Tm"),
                term: t(Name::from("lam"), [t(Name::from("app"), [
                    v(VariableIndex(1)),
                    v(VariableIndex(0)),
                ])]),
            },
            first_order: FirstOrderJudgement {
                context: lc_context,
                sort: Name::from("Tm"),
                term: FreeTerm::op("lam", [FreeTerm::op("app", [
                    FreeTerm::op("$sub_Tm", [
                        FreeTerm::op("$q_Tm", []),
                        FreeTerm::op("$p_Tm", []),
                    ]),
                    FreeTerm::op("$q_Tm", []),
                ])]),
            },
        },
        Fixture {
            signature: computations(),
            binding: BindingJudgement {
                context: computation_context.clone(),
                sort: Name::from("C"),
                term: t(Name::from("bind"), [
                    t(Name::from("ret"), [v(VariableIndex(1))]),
                    t(Name::from("ret"), [v(VariableIndex(1))]),
                ]),
            },
            first_order: FirstOrderJudgement {
                context: computation_context,
                sort: Name::from("C"),
                term: FreeTerm::op("bind", [
                    FreeTerm::op("ret", [FreeTerm::op("$sub_V", [
                        FreeTerm::op("$q_V", []),
                        FreeTerm::op("$p_V", []),
                    ])]),
                    FreeTerm::op("ret", [FreeTerm::op("$sub_V", [
                        FreeTerm::op("$q_V", []),
                        FreeTerm::op("$p_V", []),
                    ])]),
                ]),
            },
        },
        Fixture {
            signature: mixed(),
            binding: BindingJudgement {
                context: mixed_context.clone(),
                sort: Name::from("R"),
                term: t(Name::from("scope"), [
                    t(Name::from("pack"), [
                        v(VariableIndex(2)),
                        v(VariableIndex(1)),
                    ]),
                    v(VariableIndex(1)),
                    v(VariableIndex(1)),
                ]),
            },
            first_order: FirstOrderJudgement {
                context: mixed_context,
                sort: Name::from("R"),
                term: FreeTerm::op("scope", [
                    FreeTerm::op("pack", [
                        FreeTerm::op("$sub_A", [
                            FreeTerm::op("$sub_A", [
                                FreeTerm::op("$q_A", []),
                                FreeTerm::op("$p_B", []),
                            ]),
                            FreeTerm::op("$p_A", []),
                        ]),
                        FreeTerm::op("$sub_B", [
                            FreeTerm::op("$q_B", []),
                            FreeTerm::op("$p_A", []),
                        ]),
                    ]),
                    FreeTerm::op("$sub_A", [
                        FreeTerm::op("$q_A", []),
                        FreeTerm::op("$p_B", []),
                    ]),
                    FreeTerm::op("$sub_B", [
                        FreeTerm::op("$q_B", []),
                        FreeTerm::op("$p_A", []),
                    ]),
                ]),
            },
        },
    ]
}

/// A deterministic selection stream, independent of platform randomness.
#[repr(transparent)]
struct Choices(u64);

impl Choices
{
    /// Advance a wrapping seed and choose within a nonempty finite class.
    ///
    /// # Specification
    /// - requires: the class is nonempty.
    /// - ensures: the result is below its size.
    /// - panics: only an empty class violates the precondition.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — all generated terms are independently type checked;
    ///   seed diversity is test input selection, not a production claim.
    /// - witness: `tests::glf::model::three_signatures`
    fn select(
        &mut self,
        size: VariableIndex,
    ) -> VariableIndex
    {
        self.0 = self
            .0
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        VariableIndex(
            usize::try_from(self.0 >> 32)
                .expect("32-bit choice")
                .checked_rem(size.0)
                .expect("nonempty class"),
        )
    }
}

/// Nonrecursive generated syntax construction.
enum Generate
{
    /// Requested sort, context, remaining operation depth.
    Term(Name, Vec<Name>, usize),
    /// Operation after all its children.
    Close(Name, usize),
}

/// Generate a term using declarations alone, without any signature-name cases.
///
/// # Specification
/// - requires: each requested leaf sort has a variable or nullary operation.
/// - ensures: a typed term with depth at most five and arbitrary binder shapes.
/// - panics: a fixture without a leaf inhabitant violates the precondition.
///
/// # Adequacy
/// - hypothesis: L3 — the production checker validates every generated term;
///   directed independent goldens cover the generator's shared-shape residue.
/// - witness: `tests::glf::model::three_signatures`
fn generated(
    source: &SignDesc<()>,
    context: Vec<Name>,
    sort: Name,
    choices: &mut Choices,
) -> BindingJudgement
{
    let mut work = vec![Generate::Term(sort.clone(), context.clone(), 5)];
    let mut terms = Vec::new();
    while let Some(step) = work.pop() {
        match step {
            | Generate::Close(name, count) => {
                let arguments = terms.split_off(terms.len().saturating_sub(count));
                terms.push(BindingTerm::operation(name, arguments));
            },
            | Generate::Term(sort, scope, depth) => {
                let variables: Vec<_> = scope
                    .iter()
                    .rev()
                    .enumerate()
                    .filter(|&(_, found)| *found == sort)
                    .map(|(index, _)| index)
                    .collect();
                let operations: Vec<_> = source
                    .opers
                    .iter()
                    .filter(|operation| {
                        operation.arity.outputs[0].sort == sort
                            && (depth > 0 || operation.arity.inputs.is_empty())
                    })
                    .collect();
                let choice = choices
                    .select(VariableIndex(
                        variables.len().saturating_add(operations.len()),
                    ))
                    .0;
                if let Some(index) = variables.get(choice) {
                    terms.push(v(VariableIndex(*index)));
                }
                else {
                    let operation = operations[choice.saturating_sub(variables.len())];
                    work.push(Generate::Close(
                        operation.name.clone(),
                        operation.arity.inputs.len(),
                    ));
                    for port in operation.arity.inputs.iter().rev() {
                        let mut scope = scope.clone();
                        scope.extend(port.bindings.iter().map(|binder| binder.sort.clone()));
                        work.push(Generate::Term(
                            port.sort.clone(),
                            scope,
                            depth.saturating_sub(1),
                        ));
                    }
                }
            },
        }
    }
    BindingJudgement {
        context,
        sort,
        term: terms.pop().expect("generated root"),
    }
}

#[test]
fn three_signatures()
{
    for fixture in fixtures() {
        let semantics = SimplySorted::new(&fixture.signature).expect("simply sorted");
        // Both independent starting views, not just a composite on one image.
        assert_eq!(
            semantics.to_first_order(&fixture.binding),
            Ok(fixture.first_order.clone())
        );
        assert_eq!(
            semantics.from_first_order(&fixture.first_order),
            Ok(fixture.binding.clone())
        );
        let from_binding = semantics
            .to_first_order(&fixture.binding)
            .expect("forward map");
        assert_eq!(
            semantics.from_first_order(&from_binding),
            Ok(fixture.binding.clone())
        );
        let from_first_order = semantics
            .from_first_order(&fixture.first_order)
            .expect("reverse map");
        assert_eq!(
            semantics.to_first_order(&from_first_order),
            Ok(fixture.first_order)
        );
        let mut evaluation = semantics.evaluate(&fixture.binding).expect("evaluate");
        assert_eq!(evaluation.readback(), Ok(fixture.binding.clone()));
        assert_eq!(evaluation.readback(), Ok(fixture.binding.clone()));
        let mut choices = Choices(0x594f_4e45_4441);
        for iteration in 0_usize .. 256 {
            let sorts: Vec<_> = fixture
                .signature
                .sorts
                .iter()
                .filter(|sort| sort.representability == Representability::Representable)
                .map(|sort| sort.name.clone())
                .collect();
            let context: Vec<_> = sorts
                .iter()
                .cycle()
                .take(iteration % 8_usize + sorts.len())
                .cloned()
                .collect();
            let sort = fixture.signature.sorts[iteration % fixture.signature.sorts.len()]
                .name
                .clone();
            let judgement = generated(&fixture.signature, context, sort, &mut choices);
            let first_order = semantics
                .to_first_order(&judgement)
                .expect("generated first-order view");
            assert_eq!(
                semantics.from_first_order(&first_order),
                Ok(judgement.clone())
            );
            let mut evaluation = semantics.evaluate(&judgement).expect("generic evaluation");
            let quoted = evaluation.readback().expect("uncached readback");
            assert_eq!(quoted, judgement);
            assert_eq!(semantics.to_first_order(&quoted), Ok(first_order));
            assert_eq!(evaluation.readback(), Ok(quoted));
        }
    }
}

/// Apply the one generic semantics to a sorted environment.
///
/// # Specification
/// - requires: judgement and substitution are well sorted.
/// - ensures: canonical capture-avoiding substitution.
/// - panics: a typing or evaluation error violates the fixture assumptions.
///
/// # Adequacy
/// - hypothesis: L3 — directed expected trees distinguish capture and identity.
/// - witness: `tests::glf::model::substitution_laws`
fn substitute(
    semantics: &SimplySorted<'_, ()>,
    judgement: &BindingJudgement,
    target: &[Name],
    images: &[BindingTerm],
) -> BindingJudgement
{
    semantics
        .evaluate_in(judgement, target, images)
        .expect("sorted substitution")
        .readback()
        .expect("uncached substitution readback")
}

/// Oldest-first images of an identity environment.
///
/// # Specification
/// trivial.
fn identity(context: &[Name]) -> Vec<BindingTerm>
{
    (0 .. context.len())
        .rev()
        .map(|index| v(VariableIndex(index)))
        .collect()
}

/// Weaken a typed judgement by one representable sort using neutral levels.
///
/// # Specification
/// - requires: the judgement and extension sort are admitted.
/// - ensures: the same term under one additional unused context entry.
/// - panics: ill-sorted fixture input violates the precondition.
///
/// # Adequacy
/// - hypothesis: L3 — substitution cancellation and mixed binder goldens
///   distinguish capture and a missing index shift.
/// - witness: `tests::glf::model::substitution_laws`
fn weaken(
    semantics: &SimplySorted<'_, ()>,
    judgement: &BindingJudgement,
    sort: Name,
) -> BindingJudgement
{
    let mut target = judgement.context.clone();
    target.push(sort);
    let images: Vec<_> = (1 .. target.len())
        .rev()
        .map(|index| v(VariableIndex(index)))
        .collect();
    substitute(semantics, judgement, &target, &images)
}

#[test]
fn substitution_laws()
{
    for fixture in fixtures() {
        let semantics = SimplySorted::new(&fixture.signature).expect("admitted");
        let extension = fixture
            .binding
            .context
            .last()
            .expect("nonempty context")
            .clone();
        let weakened = weaken(&semantics, &fixture.binding, extension.clone());
        let mut single = identity(&fixture.binding.context);
        single.push(v(VariableIndex(0)));
        // b[p][single(a)] = b, including operations with local binders.
        assert_eq!(
            substitute(&semantics, &weakened, &fixture.binding.context, &single),
            fixture.binding
        );
        let newest = BindingJudgement {
            context: weakened.context.clone(),
            sort: extension,
            term: v(VariableIndex(0)),
        };
        // q[single(a)] = a; the prefix survives independently.
        let expected = BindingJudgement {
            context: fixture.binding.context.clone(),
            sort: newest.sort.clone(),
            term: v(VariableIndex(0)),
        };
        assert_eq!(
            substitute(&semantics, &newest, &fixture.binding.context, &single),
            expected
        );
        for position in 0 .. fixture.binding.context.len() {
            let term = BindingJudgement {
                context: fixture.binding.context.clone(),
                sort: fixture.binding.context[position].clone(),
                term: v(VariableIndex(
                    fixture
                        .binding
                        .context
                        .len()
                        .saturating_sub(position)
                        .saturating_sub(1),
                )),
            };
            assert_eq!(
                substitute(
                    &semantics,
                    &term,
                    &fixture.binding.context,
                    &identity(&fixture.binding.context)
                ),
                term
            );
        }
    }
    // A nonidentity environment with operation-valued images must be weakened
    // through both a mixed three-binder argument and its one-binder sibling.
    let source = mixed();
    let semantics = SimplySorted::new(&source).expect("mixed signature");
    let judgement = BindingJudgement {
        context: vec![Name::from("A"), Name::from("B")],
        sort: Name::from("R"),
        term: t(Name::from("scope"), [
            t(Name::from("pack"), [
                v(VariableIndex(4)),
                v(VariableIndex(3)),
            ]),
            v(VariableIndex(2)),
            v(VariableIndex(0)),
        ]),
    };
    let target = vec![Name::from("B"), Name::from("A")];
    let images = vec![v(VariableIndex(0)), t(Name::from("b"), [])];
    let expected = BindingJudgement {
        context: target.clone(),
        sort: Name::from("R"),
        term: t(Name::from("scope"), [
            t(Name::from("pack"), [
                v(VariableIndex(3)),
                t(Name::from("b"), []),
            ]),
            v(VariableIndex(1)),
            t(Name::from("b"), []),
        ]),
    };
    let actual = substitute(&semantics, &judgement, &target, &images);
    assert_eq!(actual, expected);
    // Semantic identification in the other direction: Y(Λ(value)) equals the
    // independently substituted value under the typed structural observation.
    assert_eq!(
        semantics.evaluate(&actual).expect("reevaluate").readback(),
        Ok(expected)
    );
    // q[lift(s)] = q and b[p][lift(s)] = b[s][p].
    let extension = Name::from("B");
    let mut lifted_target = target.clone();
    lifted_target.push(extension.clone());
    let mut lifted_images: Vec<_> = images
        .iter()
        .zip(&judgement.context)
        .map(|(term, sort)| {
            weaken(
                &semantics,
                &BindingJudgement {
                    context: target.clone(),
                    sort: sort.clone(),
                    term: term.clone(),
                },
                extension.clone(),
            )
            .term
        })
        .collect();
    lifted_images.push(v(VariableIndex(0)));
    let weakened = weaken(&semantics, &judgement, extension.clone());
    assert_eq!(
        substitute(&semantics, &weakened, &lifted_target, &lifted_images),
        weaken(&semantics, &actual, extension.clone())
    );
    let newest = BindingJudgement {
        context: weakened.context,
        sort: extension,
        term: v(VariableIndex(0)),
    };
    assert_eq!(
        substitute(&semantics, &newest, &lifted_target, &lifted_images).term,
        v(VariableIndex(0))
    );
}

#[test]
fn admission()
{
    for fixture in fixtures() {
        SimplySorted::new(&fixture.signature).expect("all three shapes admitted");
    }
    let dependent = super::identity_return();
    assert_eq!(
        SimplySorted::new(&dependent).expect_err("dependent sort refused"),
        AdmissionError::TermDependentSort(Name::from("VTm"))
    );
    let mut indexed = super::lc();
    indexed.opers[0].arity.inputs[0].arguments = Box::from([FreeTerm::var("x")]);
    assert_eq!(
        SimplySorted::new(&indexed).expect_err("indexed occurrence"),
        AdmissionError::IndexedOccurrence(Name::from("Tm"))
    );
    let mut result = super::lc();
    result.opers[0].arity.outputs[0].bindings = Box::from([SortIndex::new("x", "Tm")]);
    assert_eq!(
        SimplySorted::new(&result).expect_err("binding output"),
        AdmissionError::BindingResult(Name::from("lam"))
    );
    let mut malformed = super::lc();
    malformed.sorts[0].representability = Representability::Ordinary;
    let diagnostics = gandr_theory_levitation::check_desc(&malformed);
    assert_eq!(
        SimplySorted::new(&malformed).expect_err("ordinary binder"),
        AdmissionError::Signature(TranslationError::Malformed(diagnostics))
    );
    let empty = signature("Empty", vec![], vec![]);
    SimplySorted::new(&empty).expect("empty signature admitted");
}

#[test]
fn typing_boundaries()
{
    let source = mixed();
    let semantics = SimplySorted::new(&source).expect("admitted");
    let valid = BindingJudgement {
        context: vec![Name::from("A"), Name::from("B")],
        sort: Name::from("A"),
        term: v(VariableIndex(1)),
    };
    assert_eq!(semantics.check(&valid), Ok(()));
    let mut invalid = valid.clone();
    invalid.context.push(Name::from("R"));
    assert_eq!(
        semantics.check(&invalid),
        Err(BindingError::NonRepresentable(Name::from("R")))
    );
    invalid.context.pop();
    invalid.context.push(Name::from("Absent"));
    assert_eq!(
        semantics.check(&invalid),
        Err(BindingError::UnknownSort(Name::from("Absent")))
    );
    invalid = valid.clone();
    invalid.term = v(VariableIndex(2));
    assert_eq!(
        semantics.check(&invalid),
        Err(BindingError::UnboundVariable(VariableIndex(2)))
    );
    invalid.term = v(VariableIndex(0));
    assert_eq!(
        semantics.check(&invalid),
        Err(BindingError::SortMismatch {
            expected: Name::from("A"),
            actual: Name::from("B")
        })
    );
    invalid.term = t(Name::from("absent"), []);
    assert_eq!(
        semantics.check(&invalid),
        Err(BindingError::UnknownOperation(Name::from("absent")))
    );
    invalid.term = t(Name::from("a"), [v(VariableIndex(1))]);
    assert_eq!(
        semantics.check(&invalid),
        Err(BindingError::Arity(Name::from("a")))
    );
    assert_eq!(
        semantics
            .evaluate_in(&valid, &valid.context, &[])
            .expect_err("environment arity"),
        BindingError::EnvironmentArity
    );
    let images = vec![v(VariableIndex(0)), v(VariableIndex(0))];
    assert_eq!(
        semantics
            .evaluate_in(&valid, &valid.context, &images)
            .expect_err("image sort"),
        BindingError::SortMismatch {
            expected: Name::from("A"),
            actual: Name::from("B")
        }
    );
    let noncanonical = FirstOrderJudgement {
        context: vec![Name::from("A")],
        sort: Name::from("A"),
        term: FreeTerm::op("$sub_A", [FreeTerm::op("a", []), FreeTerm::op("$p_A", [])]),
    };
    assert_eq!(
        semantics.from_first_order(&noncanonical),
        Err(BindingError::NonCanonical)
    );
    let wrong_q = FirstOrderJudgement {
        context: valid.context,
        sort: valid.sort,
        term: FreeTerm::op("$q_A", []),
    };
    assert_eq!(
        semantics.from_first_order(&wrong_q),
        Err(BindingError::NonCanonical)
    );
    // Context and typing remain observable even when the naked term agrees.
    let a = BindingJudgement {
        context: vec![Name::from("A")],
        sort: Name::from("A"),
        term: v(VariableIndex(0)),
    };
    let b = BindingJudgement {
        context: vec![Name::from("B")],
        sort: Name::from("B"),
        term: v(VariableIndex(0)),
    };
    assert_eq!(semantics.check(&a), Ok(()));
    assert_eq!(semantics.check(&b), Ok(()));
    assert_ne!(a, b);
    let constant = BindingJudgement {
        context: vec![],
        sort: Name::from("A"),
        term: t(Name::from("a"), []),
    };
    assert_eq!(substitute(&semantics, &constant, &[], &[]), constant);
}

#[test]
fn deep_uncached_binders()
{
    let source = super::lc();
    let semantics = SimplySorted::new(&source).expect("LC admitted");
    let mut term = v(VariableIndex(4096));
    for _ in 0_usize .. 4096 {
        term = t(Name::from("lam"), [term]);
    }
    let judgement = BindingJudgement {
        context: vec![Name::from("Tm")],
        sort: Name::from("Tm"),
        term,
    };
    assert_eq!(
        semantics
            .evaluate(&judgement)
            .expect("deep evaluation")
            .readback(),
        Ok(judgement)
    );
}
