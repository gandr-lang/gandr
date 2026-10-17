//! Identification, both views, the kernel check and the three-signature
//! property: one evaluation and readback, one typed identification with the
//! generated first-order view, and one harness over three simply-sorted
//! signatures that share no name.
//!
//! Every property runs 256 generated cases per signature. The generator reads
//! only the signature's declarations and builds each judgement twice: as a
//! binding tree, and as its canonical first-order term written by this file's
//! own encoding of a variable as `$q` under one `$p` per newer context entry,
//! which is the independent reference the identification is compared with.

use anodized::spec;
use gandr_kernel_core::Environment;
use gandr_kernel_core::KernelError;
use gandr_kernel_core::NonInferableForm;
use gandr_kernel_term::BaseType;
use gandr_kernel_term::CompTypeId;
use gandr_kernel_term::ComputationId;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::LevelSignature;
use gandr_kernel_term::TermArena;
use gandr_kernel_term::ValueTypeId;
use gandr_theory_levitation::AdmissionError;
use gandr_theory_levitation::BindingError;
use gandr_theory_levitation::BindingJudgement;
use gandr_theory_levitation::BindingTerm;
use gandr_theory_levitation::FirstOrderJudgement;
use gandr_theory_levitation::FreeTerm;
use gandr_theory_levitation::Name;
use gandr_theory_levitation::OperDesc;
use gandr_theory_levitation::Representability;
use gandr_theory_levitation::SignDesc;
use gandr_theory_levitation::SimplySorted;
use gandr_theory_levitation::SortDesc;
use gandr_theory_levitation::SortIndex;
use gandr_theory_levitation::SortRef;
use gandr_theory_levitation::TermNode;
use gandr_theory_levitation::TermView;
use gandr_theory_levitation::TranslationError;
use gandr_theory_levitation::VariableIndex;
use gandr_theory_levitation::first_order;

use super::DeclPolarity;
use super::op;
use super::signature;

/// Generated cases per signature, for every property.
const CASES: usize = 256;

/// A variable, counted from the newest context entry.
///
/// # Specification
/// trivial.
fn v<const INDEX: usize>() -> BindingTerm
{
    BindingTerm::variable(VariableIndex::from(INDEX))
}

/// An operation term; fixture names are data, never interpreter cases.
///
/// # Specification
/// trivial.
fn t<const N: usize>(
    name: impl Into<Name>,
    arguments: [BindingTerm; N],
) -> BindingTerm
{
    BindingTerm::operation(name.into(), arguments)
}

/// Two sorts, only one representable, with a binder in an operation's second
/// argument and nullary operations of both sorts.
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

/// Three sorts, two representable, with unequal mixed binder telescopes on
/// sibling arguments.
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

/// The three simply-sorted signatures every property runs over.
///
/// # Specification
/// trivial.
fn signatures() -> [SignDesc<()>; 3]
{
    [super::lc(), computations(), mixed()]
}

/// Independently written inputs to both directions of the identification.
struct Fixture
{
    /// The signature both views are read against.
    signature: SignDesc<()>,
    /// The binding view.
    binding: BindingJudgement,
    /// The first-order view, written by hand, not by the forward map.
    first_order: FirstOrderJudgement,
}

/// One asymmetric judgement per signature, with open references across local
/// binders.
///
/// # Specification
/// trivial.
fn fixtures() -> [Fixture; 3]
{
    let lc_context = vec![Name::from("Tm"), Name::from("Tm")];
    let computation_context = vec![Name::from("V"), Name::from("V")];
    let mixed_context = vec![Name::from("A"), Name::from("B"), Name::from("A")];
    [
        Fixture {
            signature: super::lc(),
            binding: BindingJudgement {
                context: lc_context.clone(),
                sort: Name::from("Tm"),
                term: t("lam", [t("app", [v::<1>(), v::<0>()])]),
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
                term: t("bind", [t("ret", [v::<1>()]), t("ret", [v::<1>()])]),
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
                term: t("scope", [
                    t("pack", [v::<2>(), v::<1>()]),
                    v::<1>(),
                    v::<1>(),
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

/// A deterministic choice stream, independent of platform randomness.
#[repr(transparent)]
struct Choices(u64);

impl Choices
{
    /// Choose one of a nonempty slice of candidates.
    ///
    /// # Specification
    /// - requires: `candidates` is nonempty.
    /// - ensures: one of `candidates`; the stream advances once per choice.
    /// - panics: an empty slice violates the precondition.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the stream selects inputs and claims nothing about
    ///   the code under test; every generated judgement passes the production
    ///   checker, which the generator's own specification checks.
    /// - witness: `tests::glf::model::identification`
    #[spec(requires: !candidates.is_empty())]
    fn pick<'candidates, T>(
        &mut self,
        candidates: &'candidates [T],
    ) -> &'candidates T
    {
        self.0 = self
            .0
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        let position = usize::try_from(self.0 >> 32_u32).expect("a 32-bit choice fits");
        &candidates[position
            .checked_rem(candidates.len())
            .expect("a nonempty slice")]
    }
}

/// One way to fill a term position.
#[derive(Clone, Copy)]
enum Candidate<'signature>
{
    /// A variable of the wanted sort.
    Variable(VariableIndex),
    /// An operation whose result is the wanted sort.
    Operation(&'signature OperDesc),
}

/// Work for the nonrecursive generator.
enum Generate
{
    /// Fill a position of a sort, under a scope, with an operation budget.
    Term(Name, Vec<Name>, usize),
    /// Assemble an operation from its last generated arguments.
    Close(Name, usize),
}

/// One generated judgement in both views.
struct Case
{
    /// The binding view.
    binding: BindingJudgement,
    /// The first-order view, by this file's own encoding.
    first_order: FirstOrderJudgement,
}

/// The canonical first-order term of a variable: `$q` of its sort under one
/// `$p` per newer entry, oldest first, each named by the sort it crosses.
///
/// # Specification
/// - requires: `index` is in scope.
/// - ensures: a term with one `$sub` per entry newer than the variable.
/// - panics: an out-of-scope index violates the precondition.
///
/// # Adequacy
/// - hypothesis: L2 — written independently of the crate's encoding and
///   compared with it in both directions on every generated case.
/// - witness: `tests::glf::model::identification`
#[spec(requires: usize::from(index) < scope.len())]
fn encoded_variable(
    scope: &[Name],
    index: VariableIndex,
) -> FreeTerm
{
    let position = scope
        .len()
        .checked_sub(usize::from(index).saturating_add(1))
        .expect("an index in scope");
    let sort = &scope[position];
    scope[position.saturating_add(1) ..].iter().fold(
        FreeTerm::op(format!("$q_{sort}"), []),
        |term, crossed| {
            FreeTerm::op(format!("$sub_{sort}"), [
                term,
                FreeTerm::op(format!("$p_{crossed}"), []),
            ])
        },
    )
}

/// Generate a judgement from the signature's declarations alone, in both
/// views.
///
/// # Specification
/// - requires: every position the generator reaches has a variable in scope or
///   a nullary operation of its sort.
/// - ensures: a judgement at `context` and `sort` that the production checker
///   accepts, at most five operations deep, with every binder shape the
///   signature declares.
/// - panics: a fixture without a leaf inhabitant violates the precondition.
///
/// # Adequacy
/// - hypothesis: L3 — the production checker accepts every generated judgement;
///   independently written goldens cover the residue the generator shares with
///   the code under test.
/// - witness: `tests::glf::model::identification`
#[spec(ensures: |ref case| case.binding.context == case.first_order.context
    && SimplySorted::new(source).is_ok_and(|semantics| semantics.check(&case.binding).is_ok()))]
fn generated(
    source: &SignDesc<()>,
    context: Vec<Name>,
    sort: Name,
    choices: &mut Choices,
) -> Case
{
    let mut work = vec![Generate::Term(sort.clone(), context.clone(), 5)];
    let mut terms: Vec<(BindingTerm, FreeTerm)> = Vec::new();
    while let Some(step) = work.pop() {
        match step {
            Generate::Close(name, count) => {
                let (bindings, first_orders): (Vec<_>, Vec<_>) = terms
                    .split_off(terms.len().saturating_sub(count))
                    .into_iter()
                    .unzip();
                terms.push((
                    BindingTerm::operation(name.clone(), bindings),
                    FreeTerm::op(name, first_orders),
                ));
            },
            Generate::Term(wanted, scope, depth) => {
                let mut candidates: Vec<Candidate<'_>> = scope
                    .iter()
                    .rev()
                    .enumerate()
                    .filter(|&(_, found)| *found == wanted)
                    .map(|(index, _)| Candidate::Variable(VariableIndex::from(index)))
                    .collect();
                candidates.extend(
                    source
                        .opers
                        .iter()
                        .filter(|operation| {
                            operation.arity.outputs[0].sort == wanted
                                && (depth > 0 || operation.arity.inputs.is_empty())
                        })
                        .map(Candidate::Operation),
                );
                match *choices.pick(&candidates) {
                    Candidate::Variable(index) => terms.push((
                        BindingTerm::variable(index),
                        encoded_variable(&scope, index),
                    )),
                    Candidate::Operation(operation) => {
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
                    },
                }
            },
        }
    }
    let (binding, first_order) = terms.pop().expect("one generated root");
    Case {
        binding: BindingJudgement {
            context: context.clone(),
            sort: sort.clone(),
            term: binding,
        },
        first_order: FirstOrderJudgement {
            context,
            sort,
            term: first_order,
        },
    }
}

/// The generated cases of one signature: open contexts of every length from
/// one entry per representable sort to seven more, cycling through the
/// representable sorts, and each sort in turn as the result.
///
/// # Specification
/// - requires: as [`generated`].
/// - ensures: exactly `CASES` cases.
/// - panics: as [`generated`].
///
/// # Adequacy
/// - hypothesis: L3 — context length and result sort vary with the case, so
///   every sort and every context length up to eight is reached.
/// - witness: `tests::glf::model::identification`
#[spec(ensures: |ref cases| cases.len() == CASES)]
fn cases(
    source: &SignDesc<()>,
    choices: &mut Choices,
) -> Vec<Case>
{
    let representable: Vec<Name> = source
        .sorts
        .iter()
        .filter(|sort| sort.representability == Representability::Representable)
        .map(|sort| sort.name.clone())
        .collect();
    (0 .. CASES)
        .map(|case| {
            let context = representable
                .iter()
                .cycle()
                .take((case % 8).saturating_add(representable.len()))
                .cloned()
                .collect();
            let sort = source.sorts[case
                .checked_rem(source.sorts.len())
                .expect("a signature with sorts")]
            .name
            .clone();
            generated(source, context, sort, choices)
        })
        .collect()
}

#[test]
fn identification()
{
    // Both directions start from independently written input.
    for fixture in fixtures() {
        let semantics = SimplySorted::new(&fixture.signature).expect("simply sorted");
        assert_eq!(
            semantics.to_first_order(&fixture.binding),
            Ok(fixture.first_order.clone())
        );
        assert_eq!(
            semantics.from_first_order(&fixture.first_order),
            Ok(fixture.binding)
        );
    }
    // Both composites of the term map are identities on generated well-scoped
    // judgements, each composite starting from its own view.
    let mut choices = Choices(0x4944_454e_5449_4659);
    for source in signatures() {
        let semantics = SimplySorted::new(&source).expect("simply sorted");
        for case in cases(&source, &mut choices) {
            let first_order = semantics
                .to_first_order(&case.binding)
                .expect("the first-order view");
            assert_eq!(first_order, case.first_order);
            assert_eq!(
                semantics.from_first_order(&first_order),
                Ok(case.binding.clone())
            );
            let binding = semantics
                .from_first_order(&case.first_order)
                .expect("the binding view");
            assert_eq!(binding, case.binding);
            assert_eq!(semantics.to_first_order(&binding), Ok(case.first_order));
        }
    }
}

#[test]
fn both_views()
{
    let mut choices = Choices(0x424f_5448_5649_4557);
    for source in signatures() {
        let semantics = SimplySorted::new(&source).expect("simply sorted");
        for case in cases(&source, &mut choices) {
            // Λ ∘ Y = id, twice: readback caches nothing.
            let mut evaluation = semantics.evaluate(&case.binding).expect("evaluation");
            assert_eq!(evaluation.readback(), Ok(case.binding.clone()));
            assert_eq!(evaluation.readback(), Ok(case.binding.clone()));
            // Environment extension is the one non-strict point: the identity
            // environment built one image at a time reads back as the
            // reflected one.
            let images = identity(&case.binding.context);
            assert_eq!(
                substitute(&semantics, &case.binding, &case.binding.context, &images),
                case.binding
            );
            // Y commutes with every operation, `ret` and `lam` among them: the
            // value of an operation applied to generated arguments reads back
            // as the operation applied to each argument's own readback, in
            // the context its binder telescope extends.
            let operation = choices.pick(&source.opers);
            let arguments: Vec<BindingJudgement> = operation
                .arity
                .inputs
                .iter()
                .map(|port| {
                    let mut context = case.binding.context.clone();
                    context.extend(port.bindings.iter().map(|binder| binder.sort.clone()));
                    generated(&source, context, port.sort.clone(), &mut choices).binding
                })
                .collect();
            let applied = BindingJudgement {
                context: case.binding.context.clone(),
                sort: operation.arity.outputs[0].sort.clone(),
                term: BindingTerm::operation(
                    operation.name.clone(),
                    arguments.iter().map(|argument| argument.term.clone()),
                ),
            };
            let read: Vec<BindingTerm> = arguments
                .iter()
                .map(|argument| {
                    semantics
                        .evaluate(argument)
                        .expect("argument evaluation")
                        .readback()
                        .expect("argument readback")
                        .term
                })
                .collect();
            assert_eq!(
                semantics
                    .evaluate(&applied)
                    .expect("operation evaluation")
                    .readback(),
                Ok(BindingJudgement {
                    term: BindingTerm::operation(operation.name.clone(), read),
                    ..applied.clone()
                })
            );
        }
    }
}

#[test]
fn three_signatures()
{
    // No sort or operation name is shared, so no name can select a case in
    // the one implementation all three run through.
    let signatures = signatures();
    let mut names: Vec<&Name> = signatures
        .iter()
        .flat_map(|source| {
            source
                .sorts
                .iter()
                .map(|sort| &sort.name)
                .chain(source.opers.iter().map(|operation| &operation.name))
        })
        .collect();
    let declared = names.len();
    names.sort_unstable();
    names.dedup();
    assert_eq!(names.len(), declared);
    // One pair passes both views on each: from the first-order view through
    // the binding view, evaluation and readback, back to the first-order
    // view, on the independent goldens and on 256 generated cases each.
    for fixture in fixtures() {
        let semantics = SimplySorted::new(&fixture.signature).expect("simply sorted");
        let mut evaluation = semantics
            .evaluate(&fixture.binding)
            .expect("golden evaluation");
        assert_eq!(evaluation.readback(), Ok(fixture.binding));
    }
    let mut choices = Choices(0x5448_5245_4553_4947);
    for source in &signatures {
        let semantics = SimplySorted::new(source).expect("simply sorted");
        for case in cases(source, &mut choices) {
            let binding = semantics
                .from_first_order(&case.first_order)
                .expect("the binding view");
            let read = semantics
                .evaluate(&binding)
                .expect("evaluation")
                .readback()
                .expect("readback");
            assert_eq!(semantics.to_first_order(&read), Ok(case.first_order));
        }
    }
}

/// A value-type parameter of the identity-return model, interpreted in the
/// kernel by a distinct closed type.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Parameter
{
    /// Interpreted as the unit type.
    Unit,
    /// Interpreted as the integer base type.
    Integer,
    /// Interpreted as the string base type.
    String,
}

impl Parameter
{
    /// Every parameter.
    const ALL: [Self; 3] = [Self::Unit, Self::Integer, Self::String];

    /// The parameter's variable in the model's equation notation.
    ///
    /// # Specification
    /// trivial.
    fn term(self) -> FreeTerm
    {
        FreeTerm::var(match self {
            Self::Unit => "A0",
            Self::Integer => "A1",
            Self::String => "A2",
        })
    }

    /// Read a parameter back from its variable.
    ///
    /// # Specification
    /// - requires: the node is one of the three parameter variables.
    /// - ensures: the parameter whose [`Parameter::term`] it is.
    /// - panics: another node is outside the fixture's domain.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — every parameter occurs as a domain and as a result,
    ///   and the kernel refuses a collapsed pair of distinct parameters.
    /// - witness: `tests::glf::model::kernel`
    #[spec(ensures: |parameter| parameter.term().to_node() == node)]
    fn read(node: TermNode<'_>) -> Self
    {
        let TermView::Var(name) = node.view()
        else {
            panic!("a parameter is a variable");
        };
        match name.as_ref() {
            "A0" => Self::Unit,
            "A1" => Self::Integer,
            "A2" => Self::String,
            other => panic!("not a parameter: {other}"),
        }
    }

    /// The parameter's closed kernel type.
    ///
    /// # Specification
    /// trivial.
    fn kernel(
        self,
        arena: &mut TermArena,
    ) -> ValueTypeId
    {
        match self {
            Self::Unit => arena.value_type_unit(),
            Self::Integer => arena.value_type_base(BaseType::Integer),
            Self::String => arena.value_type_base(BaseType::String),
        }
    }
}

/// A closed identity-return judgement of the generated model, in its
/// equation notation: `λx₁ … λxₙ. return xᵢ : A₁ → … → Aₙ → F Aᵢ`.
struct IdentityReturn
{
    /// The computation type.
    ty: FreeTerm,
    /// The term.
    term: FreeTerm,
}

/// Generate a closed identity-return judgement from the model's own `lam` and
/// `ret`, after checking the telescopes the fold gave them.
///
/// # Specification
/// - requires: `model` is the first-order model of the identity-return
///   signature.
/// - ensures: between one and four λs over chosen parameters, returning one
///   chosen bound variable at its own parameter.
/// - panics: a model whose `lam` or `ret` lacks its generated telescope
///   violates the precondition.
///
/// # Adequacy
/// - hypothesis: L3 — the domain count, every parameter and every reachable
///   index vary, so a kernel image that drops a λ, reverses an index or
///   collapses two parameters is refused by the kernel.
/// - witness: `tests::glf::model::kernel`
#[spec(ensures: |ref judgement| matches!(judgement.term.to_node().view(), TermView::Op { .. }))]
fn identity_return_case(
    model: &SignDesc<()>,
    choices: &mut Choices,
) -> IdentityReturn
{
    let lam = model
        .opers
        .iter()
        .find(|operation| operation.name.as_ref() == "lam")
        .expect("the generated λ");
    assert_eq!(
        lam.arity.inputs[3].arguments[0].to_string(),
        "$extend_VTm(G, A)"
    );
    let ret = model
        .opers
        .iter()
        .find(|operation| operation.name.as_ref() == "ret")
        .expect("the generated return");
    assert_eq!(ret.arity.outputs[0].arguments[1].to_string(), "F(A)");
    let count = *choices.pick(&[1_usize, 2, 3, 4]);
    let domains: Vec<Parameter> = core::iter::repeat_with(|| *choices.pick(&Parameter::ALL))
        .take(count)
        .collect();
    let indices: Vec<VariableIndex> = (0 .. count).map(VariableIndex::from).collect();
    let index = *choices.pick(&indices);
    let result = *domains
        .iter()
        .rev()
        .nth(usize::from(index))
        .expect("a bound variable");
    let mut variable = FreeTerm::op("$q_VTm", []);
    for _ in 0 .. usize::from(index) {
        variable = FreeTerm::op("$sub_VTm", [variable, FreeTerm::op("$p_VTm", [])]);
    }
    let mut ty = FreeTerm::op("F", [result.term()]);
    let mut term = FreeTerm::op(ret.name.clone(), [result.term(), variable]);
    for domain in domains.into_iter().rev() {
        term = FreeTerm::op(lam.name.clone(), [domain.term(), ty.clone(), term]);
        ty = FreeTerm::op("Arrow", [domain.term(), ty]);
    }
    IdentityReturn { ty, term }
}

/// A judgement's image in the kernel's arena.
struct TrustedImage
{
    /// The computation type.
    ty: CompTypeId,
    /// The computation.
    term: ComputationId,
    /// The type after the outermost λ's domain.
    codomain: CompTypeId,
}

/// Map a closed identity-return judgement into the kernel's arena, without
/// recursion: `Arrow`, `F`, `lam`, `ret` and `$q` under `$p`s become the
/// kernel's arrow, returner, λ, return and de Bruijn variable.
///
/// # Specification
/// - requires: a judgement [`identity_return_case`] generates.
/// - ensures: the image keeps every domain, the result type and the variable's
///   index.
/// - panics: syntax outside the identity-return fragment violates the
///   precondition.
///
/// # Adequacy
/// - hypothesis: L2 — the kernel admits the image only when its λs, domains,
///   result and index agree, so a dropped λ, a reversed index or a collapsed
///   parameter is refused on some generated case.
/// - witness: `tests::glf::model::kernel`
#[spec(ensures: |ref image| arena.comp_type(image.ty).is_some()
    && arena.computation(image.term).is_some()
    && arena.comp_type(image.codomain).is_some())]
fn trusted_image(
    judgement: &IdentityReturn,
    arena: &mut TermArena,
) -> TrustedImage
{
    let mut domains = Vec::new();
    let mut ty = judgement.ty.to_node();
    let mut term = judgement.term.to_node();
    let (result, index) = loop {
        let (
            TermView::Op {
                name: former,
                args: mut type_arguments,
            },
            TermView::Op {
                name: introduction,
                args: mut arguments,
            },
        ) = (ty.view(), term.view())
        else {
            panic!("outside the identity-return fragment");
        };
        match (former.as_ref(), introduction.as_ref()) {
            ("Arrow", "lam") => {
                let domain = Parameter::read(type_arguments.next().expect("a domain"));
                assert_eq!(
                    Parameter::read(arguments.next().expect("an annotation")),
                    domain
                );
                domains.push(domain);
                ty = type_arguments.next().expect("a codomain");
                let _codomain = arguments.next().expect("a body type");
                term = arguments.next().expect("a body");
            },
            ("F", "ret") => {
                let result = Parameter::read(type_arguments.next().expect("a result"));
                assert_eq!(
                    Parameter::read(arguments.next().expect("an annotation")),
                    result
                );
                let mut variable = arguments.next().expect("a returned variable");
                let mut index = 0_u32;
                while let TermView::Op {
                    name,
                    args: mut weakening,
                } = variable.view()
                    && name.as_ref() == "$sub_VTm"
                {
                    variable = weakening.next().expect("a weakened variable");
                    index = index.saturating_add(1);
                }
                break (result, DeBruijnIndex::from(index));
            },
            _ => panic!("outside the identity-return fragment"),
        }
    };
    let result = result.kernel(arena);
    let value = arena.value_variable(index);
    let mut ty = arena.comp_type_returner(result);
    let mut term = arena.computation_return(value);
    let mut codomain = ty;
    for domain in domains.into_iter().rev() {
        codomain = ty;
        let domain = domain.kernel(arena);
        ty = arena.comp_type_arrow(domain, ty);
        term = arena.computation_lambda(term);
    }
    TrustedImage { ty, term, codomain }
}

#[test]
fn kernel()
{
    let model = first_order(&super::identity_return()).expect("identity-return translates");
    let mut choices = Choices(0x4b45_524e_454c);
    for _ in 0 .. CASES {
        let judgement = identity_return_case(&model, &mut choices);
        let mut environment = Environment::new();
        // The generated λx. return x : A → F A lands in the trusted judgement.
        let staged = {
            let mut staging = environment.stage();
            let arena = staging.arena();
            let image = trusted_image(&judgement, arena);
            let declared = arena.value_type_thunk(image.ty);
            let body = arena.value_thunk(image.term);
            staging.def(LevelSignature::monomorphic(), declared, body)
        };
        environment
            .add_decl(staged)
            .expect("the identity-return judgement is admitted");
        // The same λ where its type must be synthesized still refuses: an
        // unannotated λ checks, and never synthesizes.
        let staged = {
            let mut staging = environment.stage();
            let arena = staging.arena();
            let image = trusted_image(&judgement, arena);
            let argument = arena.value_unit();
            let application = arena.computation_application(image.term, argument);
            let declared = arena.value_type_thunk(image.codomain);
            let body = arena.value_thunk(application);
            staging.def(LevelSignature::monomorphic(), declared, body)
        };
        assert!(matches!(
            environment.add_decl(staged),
            Err(KernelError::NotInferable {
                form: NonInferableForm::Lambda
            })
        ));
    }
}

/// Apply the one generic semantics to a sorted environment.
///
/// # Specification
/// - requires: the judgement and the images are well sorted.
/// - ensures: the canonical capture-avoiding substitution.
/// - panics: a typing or evaluation error violates the fixture's assumptions.
///
/// # Adequacy
/// - hypothesis: L3 — directed expected trees distinguish capture and identity.
/// - witness: `tests::glf::model::substitution_laws`
#[spec(ensures: |ref result| result.context == target && result.sort == judgement.sort)]
fn substitute(
    semantics: &SimplySorted<'_, ()>,
    judgement: &BindingJudgement,
    target: &[Name],
    images: &[BindingTerm],
) -> BindingJudgement
{
    semantics
        .evaluate_in(judgement, target, images)
        .expect("a sorted substitution")
        .readback()
        .expect("an uncached substitution readback")
}

/// The images of an identity environment, oldest first.
///
/// # Specification
/// - ensures: one variable per context entry, the oldest at the greatest index.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a reversed identity is refused by the image sorts of a
///   mixed context, or changes the substitution's readback.
/// - witness: `tests::glf::model::substitution_laws`
#[spec(ensures: |ref images| images.len() == context.len())]
fn identity(context: &[Name]) -> Vec<BindingTerm>
{
    (0 .. context.len())
        .rev()
        .map(|index| BindingTerm::variable(VariableIndex::from(index)))
        .collect()
}

/// Weaken a judgement by one newest entry of a representable sort.
///
/// # Specification
/// - requires: the judgement and the extension sort are admitted.
/// - ensures: the same term under one more, unused, context entry.
/// - panics: ill-sorted fixture input violates the precondition.
///
/// # Adequacy
/// - hypothesis: L3 — substitution cancellation and mixed binder goldens
///   distinguish capture and a missing index shift.
/// - witness: `tests::glf::model::substitution_laws`
#[spec(ensures: |ref weakened| weakened.context.len() == judgement.context.len().saturating_add(1))]
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
        .map(|index| BindingTerm::variable(VariableIndex::from(index)))
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
            .expect("a nonempty context")
            .clone();
        let weakened = weaken(&semantics, &fixture.binding, extension.clone());
        let mut single = identity(&fixture.binding.context);
        single.push(v::<0>());
        // b[p][single(a)] = b, through operations with local binders.
        assert_eq!(
            substitute(&semantics, &weakened, &fixture.binding.context, &single),
            fixture.binding
        );
        let newest = BindingJudgement {
            context: weakened.context.clone(),
            sort: extension,
            term: v::<0>(),
        };
        // q[single(a)] = a; the prefix survives independently.
        let expected = BindingJudgement {
            context: fixture.binding.context.clone(),
            sort: newest.sort.clone(),
            term: v::<0>(),
        };
        assert_eq!(
            substitute(&semantics, &newest, &fixture.binding.context, &single),
            expected
        );
        for (position, sort) in fixture.binding.context.iter().enumerate() {
            let term = BindingJudgement {
                context: fixture.binding.context.clone(),
                sort: sort.clone(),
                term: BindingTerm::variable(VariableIndex::from(
                    fixture.binding.context.len() - position - 1,
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
    // A nonidentity environment with operation-valued images, weakened
    // through a mixed three-binder argument and its one-binder sibling.
    let source = mixed();
    let semantics = SimplySorted::new(&source).expect("the mixed signature");
    let judgement = BindingJudgement {
        context: vec![Name::from("A"), Name::from("B")],
        sort: Name::from("R"),
        term: t("scope", [
            t("pack", [v::<4>(), v::<3>()]),
            v::<2>(),
            v::<0>(),
        ]),
    };
    let target = vec![Name::from("B"), Name::from("A")];
    let images = vec![v::<0>(), t("b", [])];
    let expected = BindingJudgement {
        context: target.clone(),
        sort: Name::from("R"),
        term: t("scope", [
            t("pack", [v::<3>(), t("b", [])]),
            v::<1>(),
            t("b", []),
        ]),
    };
    let actual = substitute(&semantics, &judgement, &target, &images);
    assert_eq!(actual, expected);
    // Y(Λ(value)) reads back as the independently substituted value.
    assert_eq!(
        semantics
            .evaluate(&actual)
            .expect("reevaluation")
            .readback(),
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
    lifted_images.push(v::<0>());
    let weakened = weaken(&semantics, &judgement, extension.clone());
    assert_eq!(
        substitute(&semantics, &weakened, &lifted_target, &lifted_images),
        weaken(&semantics, &actual, extension.clone())
    );
    let newest = BindingJudgement {
        context: weakened.context,
        sort: extension,
        term: v::<0>(),
    };
    assert_eq!(
        substitute(&semantics, &newest, &lifted_target, &lifted_images).term,
        v::<0>()
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
        SimplySorted::new(&dependent).expect_err("a dependent sort is refused"),
        AdmissionError::TermDependentSort(Name::from("VTm"))
    );
    let mut indexed = super::lc();
    indexed.opers[0].arity.inputs[0].arguments = Box::from([FreeTerm::var("x")]);
    assert_eq!(
        SimplySorted::new(&indexed).expect_err("an indexed occurrence"),
        AdmissionError::IndexedOccurrence(Name::from("Tm"))
    );
    let mut indexed_binder = super::lc();
    indexed_binder.opers[0].arity.inputs[0].bindings[0].arguments = Box::from([FreeTerm::var("x")]);
    assert_eq!(
        SimplySorted::new(&indexed_binder).expect_err("an indexed binder domain"),
        AdmissionError::IndexedOccurrence(Name::from("Tm"))
    );
    let mut result = super::lc();
    result.opers[1].arity.outputs[0].bindings = Box::from([SortIndex::new("x", "Tm")]);
    assert_eq!(
        SimplySorted::new(&result).expect_err("a binding result"),
        AdmissionError::BindingResult(Name::from("app"))
    );
    let mut malformed = super::lc();
    malformed.sorts[0].representability = Representability::Ordinary;
    let diagnostics = gandr_theory_levitation::check_desc(&malformed);
    assert_eq!(
        SimplySorted::new(&malformed).expect_err("an ordinary binder domain"),
        AdmissionError::Signature(TranslationError::Malformed(diagnostics))
    );
    let empty = signature("Empty", vec![], vec![]);
    SimplySorted::new(&empty).expect("the empty signature is admitted");
}

#[test]
fn typing_boundaries()
{
    let source = mixed();
    let semantics = SimplySorted::new(&source).expect("admitted");
    let valid = BindingJudgement {
        context: vec![Name::from("A"), Name::from("B")],
        sort: Name::from("A"),
        term: v::<1>(),
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
    invalid.term = v::<2>();
    assert_eq!(
        semantics.check(&invalid),
        Err(BindingError::UnboundVariable(VariableIndex::from(2)))
    );
    invalid.term = v::<0>();
    assert_eq!(
        semantics.check(&invalid),
        Err(BindingError::SortMismatch {
            expected: Name::from("A"),
            actual: Name::from("B")
        })
    );
    invalid.term = t("absent", []);
    assert_eq!(
        semantics.check(&invalid),
        Err(BindingError::UnknownOperation(Name::from("absent")))
    );
    // The second declaration is found, not the first.
    invalid.term = t("b", []);
    assert_eq!(
        semantics.check(&invalid),
        Err(BindingError::SortMismatch {
            expected: Name::from("A"),
            actual: Name::from("B")
        })
    );
    invalid.term = t("a", [v::<1>()]);
    assert_eq!(
        semantics.check(&invalid),
        Err(BindingError::Arity(Name::from("a")))
    );
    invalid = valid.clone();
    invalid.sort = Name::from("Absent");
    assert_eq!(
        semantics.check(&invalid),
        Err(BindingError::UnknownSort(Name::from("Absent")))
    );
    assert_eq!(
        semantics
            .evaluate_in(&valid, &valid.context, &[])
            .expect_err("the environment's length"),
        BindingError::EnvironmentArity
    );
    let images = vec![v::<0>(), v::<0>()];
    assert_eq!(
        semantics
            .evaluate_in(&valid, &valid.context, &images)
            .expect_err("an image's sort"),
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
    // A weakening names the entry it crosses, takes no argument, and is the
    // last of exactly two arguments; each departure is refused alone.
    for term in [
        FreeTerm::op("$sub_A", [
            FreeTerm::op("$q_A", []),
            FreeTerm::op("$p_A", []),
        ]),
        FreeTerm::op("$sub_A", [
            FreeTerm::op("$q_A", []),
            FreeTerm::op("$p_B", [FreeTerm::op("b", [])]),
        ]),
        FreeTerm::op("$sub_A", [
            FreeTerm::op("$q_A", []),
            FreeTerm::op("$p_B", []),
            FreeTerm::op("a", []),
        ]),
    ] {
        let judgement = FirstOrderJudgement {
            context: vec![Name::from("A"), Name::from("B")],
            sort: Name::from("A"),
            term,
        };
        assert_eq!(
            semantics.from_first_order(&judgement),
            Err(BindingError::NonCanonical)
        );
    }
    // Context and typing stay observable where the bare terms agree.
    let a = BindingJudgement {
        context: vec![Name::from("A")],
        sort: Name::from("A"),
        term: v::<0>(),
    };
    let b = BindingJudgement {
        context: vec![Name::from("B")],
        sort: Name::from("B"),
        term: v::<0>(),
    };
    assert_eq!(semantics.check(&a), Ok(()));
    assert_eq!(semantics.check(&b), Ok(()));
    assert_ne!(a, b);
    let constant = BindingJudgement {
        context: vec![],
        sort: Name::from("A"),
        term: t("a", []),
    };
    assert_eq!(substitute(&semantics, &constant, &[], &[]), constant);
}

#[test]
fn deep_uncached_binders()
{
    let source = super::lc();
    let semantics = SimplySorted::new(&source).expect("LC admitted");
    let mut term = v::<4096>();
    for _ in 0_usize .. 4096 {
        term = t("lam", [term]);
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
