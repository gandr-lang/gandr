//! The corpus's `runs` items against normalisation by evaluation.
//!
//! `gandr-core-nbe` evaluates a declaration's checked core by closures over a
//! glued domain and shares no step with the runtime's tiers, so it is the
//! independent reading of what a run computes: a runtime drift that still
//! matches the outcome an item spells, or an item whose spelled answer is
//! itself wrong, shows here. Each item is run on the executor and its terminal
//! read back as a core term; the same checked core is normalised with the
//! definitions the checker unfolded, round by round as the checker reads a
//! claim back. The two agree node for node, or once the run's reading, which
//! keeps a closure's body as written, is normalised too.
//!
//! What the normaliser cannot take is counted by reason and printed: a former
//! its evaluation refuses, and an answer it holds where a run goes on — a
//! fixpoint at no gate, which a run unfolds when forced and the normaliser
//! only when applied to a canonical argument, and a certificate (a path, a
//! flow, a session statement or a recorded run), which the normaliser holds
//! as written and a run realises: a path as its maps, a recorded run with
//! its payloads evaluated.

use alloc::collections::BTreeMap;
use alloc::string::String;
use alloc::vec::Vec;
use core::convert::Infallible;
use core::fmt::Write as _;
use core::ops::ControlFlow;
use std::path::PathBuf;

use gandr_core_checker::CodeDefinitions;
use gandr_core_checker::ModuleReport;
use gandr_core_checker::Verdict;
use gandr_core_nbe::Definitions;
use gandr_core_nbe::DomainArena;
use gandr_core_nbe::DomainComp;
use gandr_core_nbe::Fuel;
use gandr_core_nbe::ReadbackMode;
use gandr_core_nbe::eval_computation;
use gandr_core_nbe::readback_computation;
use gandr_core_term::CertificateEquality;
use gandr_core_term::Computation;
use gandr_core_term::ComputationId;
use gandr_core_term::CoreArena;
use gandr_core_term::Value;
use gandr_core_term::ValueId;
use gandr_core_term::ValueType;
use gandr_core_term::equal_certificate_syntax;
use gandr_kernel_term::ConstantIndex;
use gandr_surface_corpus::Outcome;
use gandr_surface_corpus::Stated;
use gandr_surface_dispatcher::Composed;
use gandr_surface_dispatcher::Engine;
use gandr_surface_dispatcher::Pool;
use gandr_surface_dispatcher::Program;
use gandr_surface_dispatcher::Step;
use gandr_surface_dispatcher::Terminal;
use gandr_surface_dispatcher::Walk;
use gandr_surface_dispatcher::Width;
use gandr_surface_pretty::CoreNode;
use gandr_surface_pretty::CoreSource;
use gandr_surface_pretty::Form;
use gandr_surface_pretty::Name;
use gandr_surface_pretty::Spelling;
use gandr_surface_pretty::Style;
use gandr_surface_pretty::present_computation_line;
use quenchant_shape::shape::Maybe;

/// The evaluation budget each round of normalisation runs under.
const FUEL: u32 = 1_000_000_u32;

/// How many rounds of evaluation and unfolding readback a normal form may
/// take, as many as the checker allows a claim.
const ROUNDS: u32 = 64_u32;

/// Why the normaliser's answer is not compared with the run's.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum Decline
{
    /// Evaluation refused a former, named by the fault.
    Evaluation(String),
    /// Readback refused, named by the fault.
    Readback(String),
    /// A round still changed the term after the last one allowed.
    Rounds,
    /// A fixpoint at no gate: a run unfolds it when forced, the normaliser
    /// when it is applied to a canonical argument.
    Fixpoint,
    /// A path, a flow, a session statement or a recorded run: a certificate
    /// the normaliser holds as written and a run realises.
    Certificate,
}

/// How one item's two answers relate.
#[derive(Clone, Debug, Eq, PartialEq)]
enum Compared
{
    /// The run's reading is the normal form, node for node.
    Exactly,
    /// The run's reading is the normal form once each constructor's family
    /// is read without the arguments a run erases.
    Erased,
    /// The run's reading, normalised, is the normal form.
    Normalised,
    /// The run ended before it read a value, as the evaluation names it.
    Ended(String),
    /// The normaliser's answer is not compared, for the reason given.
    Declined(Decline),
    /// The two answers differ.
    Differ
    {
        /// The run's reading.
        run: ComputationId,
        /// The normal form.
        normal: ComputationId,
    },
}

/// The variant `fault`'s debug spelling names, its fields dropped: the name
/// it is counted under.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the spelling up to its first space or brace, every parenthesis it
///   opened there closed.
/// - provides: a reason that counts every fault of one kind together, whatever
///   ids it carries.
/// - panics: none.
/// - executable: none — the count's keys are the observation; the witness
///   prints them.
///
/// # Adequacy
/// - hypothesis: L3 — the corpus's declines are counted under names such as
///   `NativePrimitive(Primitive(Definition))` and `RuntimeControl(Reset)`.
/// - witness: `tests::differential::the_corpus_runs_items_agree_with_normalisation_by_evaluation`
fn variant(fault: &dyn core::fmt::Debug) -> String
{
    let spelled = format!("{fault:?}");
    let cut = spelled.find([' ', '{']).unwrap_or(spelled.len());
    let mut named = String::from(spelled.get(.. cut).unwrap_or_default());
    while named.ends_with('(') {
        named.pop();
    }
    let open = named.matches('(').count();
    let closed = named.matches(')').count();
    for _ in closed .. open {
        named.push(')');
    }
    named
}

/// The definitions the checker unfolded over `verdicts`: each accepted body
/// recorded and each data declaration presented, in admission order.
///
/// # Specification
/// - requires: `verdicts` are a module's, judged over the arena every term the
///   answer is asked about lives in.
/// - ensures: a body for each checked or synthesised declaration the verdicts
///   define, and a presentation for each data declaration they sign.
/// - provides: the unfolding environment the normaliser reads the module in.
/// - panics: none.
/// - executable: none — the table is read only through the normaliser; the
///   witness evaluates every `runs` item in it.
///
/// # Adequacy
/// - hypothesis: L2 — every `runs` item of the corpus normalises in it to what
///   its run reads.
/// - witness: `tests::differential::the_corpus_runs_items_agree_with_normalisation_by_evaluation`
fn definitions_of(verdicts: &ModuleReport) -> CodeDefinitions
{
    let mut definitions = CodeDefinitions::new();
    for judged in verdicts.judged() {
        let constant = judged.constant();
        match judged.verdict() {
            Verdict::Checked { .. } | Verdict::Synthesised { .. } => {
                if let Some(&body) = verdicts.definitions().get(&constant) {
                    definitions.define(constant, body);
                }
            },
            Verdict::Data => {
                if let Some(signature) = verdicts.data_signatures().get(&constant) {
                    definitions.present(constant, signature);
                }
            },
            Verdict::Owed(_) | Verdict::Suspended(_) | Verdict::Refused(_) => {},
        }
    }
    definitions
}

/// Whether two computations of `core` are the same term, node for node.
///
/// # Specification
/// - requires: both computations live in `core`.
/// - ensures: [`equal_certificate_syntax`] of the thunks of the two.
/// - panics: none.
/// - executable: none — the comparison is `equal_certificate_syntax`'s.
///
/// # Adequacy
/// - hypothesis: L2 — as the witness.
/// - witness: `tests::differential::the_corpus_runs_items_agree_with_normalisation_by_evaluation`
fn same(
    core: &mut CoreArena,
    left: ComputationId,
    right: ComputationId,
) -> CertificateEquality
{
    let left = core.value_thunk(left);
    let right = core.value_thunk(right);
    equal_certificate_syntax(core, left, right)
}

/// The normal form of `root`, read back round by round with every definition
/// unfolded until a round changes nothing, as the checker reads a claim back.
///
/// # Specification
/// - requires: `root` lives in `core`, and every body `definitions` unfolds.
/// - ensures: the first round's readback that equals the term it read, minted
///   into `core`.
/// - fails: the fault of a round's evaluation or readback, or
///   [`Decline::Rounds`] after [`ROUNDS`] rounds.
/// - panics: none.
/// - executable: none — the answer is the normaliser's; the witness holds it to
///   the run.
///
/// # Termination
/// - reason: a `for` loop over at most [`ROUNDS`] rounds, each under its fuel.
/// - measure: the rounds left.
///
/// # Adequacy
/// - hypothesis: L2 — as the witness.
/// - witness: `tests::differential::the_corpus_runs_items_agree_with_normalisation_by_evaluation`
fn normal_form(
    core: &mut CoreArena,
    definitions: Definitions<'_>,
    root: ComputationId,
) -> Result<ComputationId, Decline>
{
    let fuel = Fuel::from(FUEL);
    let mut current = root;
    for _round in 0 .. ROUNDS {
        let mut domain = DomainArena::new();
        let head = eval_computation(core, &mut domain, definitions, fuel, current)
            .map_err(|fault| Decline::Evaluation(variant(&fault)))?;
        let read = readback_computation(
            core,
            &mut domain,
            definitions,
            ReadbackMode::Unfolding,
            fuel,
            head,
        )
        .map_err(|fault| Decline::Readback(variant(&fault)))?;
        if same(core, read, current) == CertificateEquality::Equal {
            return Ok(read);
        }
        current = read;
    }
    Err(Decline::Rounds)
}

/// The normal form of the declaration at `constant`, run as a run starts it:
/// `return c`, or `force c` for a constant whose value is a thunk.
///
/// # Specification
/// - requires: as [`normal_form`].
/// - ensures: the normal form of `force c` when that of `return c` returns a
///   thunk, and that of `return c` otherwise.
/// - fails: as [`normal_form`].
/// - panics: none.
/// - executable: none — as [`normal_form`].
///
/// # Adequacy
/// - hypothesis: L2 — as the witness.
/// - witness: `tests::differential::the_corpus_runs_items_agree_with_normalisation_by_evaluation`
fn normalised(
    core: &mut CoreArena,
    definitions: Definitions<'_>,
    constant: ConstantIndex,
) -> Result<ComputationId, Decline>
{
    let value = core.value_constant(constant);
    let returned = core.computation_return(value);
    let read = normal_form(core, definitions, returned)?;
    match core.computation(read) {
        Some(&Computation::Return(answer))
            if matches!(core.value(answer), Some(&Value::Thunk(_))) =>
        {
            let forced = core.computation_force(value);
            normal_form(core, definitions, forced)
        },
        Some(_) | None => Ok(read),
    }
}

/// What a normal form the run reads otherwise comes to.
#[derive(Clone, Debug, Eq, PartialEq)]
enum Apart
{
    /// The normaliser holds it where a run goes on, for the reason given.
    Held(Decline),
    /// Nothing explains the difference.
    Unexplained,
}

/// What a normal form the run reads otherwise comes to.
///
/// # Specification
/// - requires: `normal` is a normal form of `core` read under `definitions`.
/// - ensures: [`Decline::Fixpoint`] when `normal` evaluates to a fixpoint at no
///   gate, [`Decline::Certificate`] when it returns a path, flow, session or
///   recorded-run former, and [`Apart::Unexplained`] for every other term.
/// - panics: none.
/// - executable: none — the classes are the corpus's; the witness counts them.
///
/// # Adequacy
/// - hypothesis: L2 — a loop the normaliser holds, a reflexive path a run
///   realises as its maps and a recorded run whose payloads a run evaluates are
///   each counted, and no other disagreement passes.
/// - witness: `tests::differential::the_corpus_runs_items_agree_with_normalisation_by_evaluation`
fn apart(
    core: &CoreArena,
    definitions: Definitions<'_>,
    normal: ComputationId,
) -> Apart
{
    let mut domain = DomainArena::new();
    if let Ok(head) = eval_computation(core, &mut domain, definitions, Fuel::from(FUEL), normal)
        && matches!(domain.computation(head), Some(&DomainComp::Fixpoint { .. }))
    {
        return Apart::Held(Decline::Fixpoint);
    }
    let Some(&Computation::Return(answer)) = core.computation(normal)
    else {
        return Apart::Unexplained;
    };
    match core.value(answer) {
        Some(
            &(Value::PathRefl(_)
            | Value::PathProduct(..)
            | Value::PathEquiv { .. }
            | Value::Here(_)
            | Value::Funext(..)
            | Value::Equiv(..)
            | Value::Univalence(..)
            | Value::Ua { .. }
            | Value::SessionRelated { .. }
            | Value::Recorded(_)
            | Value::Stay(_)
            | Value::Then(..)
            | Value::FlowProduct(..)
            | Value::Forward(_)
            | Value::FunctionFlow(..)),
        ) => Apart::Held(Decline::Certificate),
        Some(_) | None => Apart::Unexplained,
    }
}

/// `value` read as a run reads a value back: each constructor's family its
/// declaration alone, the arguments a run erases dropped, through every
/// first-order former a run reads back.
///
/// # Specification
/// - requires: `value` lives in `core`.
/// - ensures: for a constructor, a tuple, an injection, a list cell or a
///   record, the same former over its erased parts, a constructor's nominal
///   family read as `Data(declaration, [])`; `value` itself for every other
///   former.
/// - panics: none.
/// - executable: none — the reading is the run's read-back's; the witness
///   compares in it.
///
/// # Termination
/// - reason: each node is entered once, its parts pushed, and left once; the
///   arena mints a node only after its parts, so no node is its own part.
/// - measure: the nodes under `value` not yet left.
///
/// # Adequacy
/// - hypothesis: L2 — a list of a parameterised family the source ascribes
///   reads as the run reads it.
/// - witness: `tests::differential::the_corpus_runs_items_agree_with_normalisation_by_evaluation`
fn erased(
    core: &mut CoreArena,
    value: ValueId,
) -> ValueId
{
    let mut erasure: BTreeMap<ValueId, ValueId> = BTreeMap::new();
    let mut pending = vec![Visit::Enter(value)];
    while let Some(visit) = pending.pop() {
        match visit {
            Visit::Enter(node) => {
                if !erasure.contains_key(&node) {
                    pending.push(Visit::Leave(node));
                    push_parts(core, node, &mut pending);
                }
            },
            Visit::Leave(node) => {
                let rebuilt = rebuilt(core, &erasure, node);
                erasure.insert(node, rebuilt);
            },
        }
    }
    erasure.get(&value).copied().unwrap_or(value)
}

/// One step of [`erased`]'s walk.
#[derive(Clone, Copy, Debug)]
enum Visit
{
    /// Push the node's first-order parts, then leave it.
    Enter(ValueId),
    /// Rebuild the node over its erased parts.
    Leave(ValueId),
}

/// Push an entry for each first-order part of `node` onto `pending`.
///
/// # Specification
/// - requires: `node` lives in `core`.
/// - ensures: one [`Visit::Enter`] per field of a constructor, component of a
///   tuple, body of an injection, head and tail of a list cell and field of a
///   record; nothing for every other former.
/// - panics: none.
/// - executable: none — as [`erased`].
///
/// # Adequacy
/// - hypothesis: L2 — as [`erased`].
/// - witness: `tests::differential::the_corpus_runs_items_agree_with_normalisation_by_evaluation`
fn push_parts(
    core: &CoreArena,
    node: ValueId,
    pending: &mut Vec<Visit>,
)
{
    match core.value(node) {
        Some(&Value::Constructor { ref fields, .. }) => {
            pending.extend(fields.iter().map(|&field| Visit::Enter(field)));
        },
        Some(&Value::Tuple(ref components)) => {
            pending.extend(components.iter().map(|&component| Visit::Enter(component)));
        },
        Some(&Value::Injection(_, body)) => pending.push(Visit::Enter(body)),
        Some(&Value::ListCons(head, tail)) => {
            pending.extend([Visit::Enter(head), Visit::Enter(tail)]);
        },
        Some(&Value::Record(ref fields)) => {
            pending.extend(fields.values().map(|&field| Visit::Enter(field)));
        },
        Some(_) | None => {},
    }
}

/// `node` rebuilt over the erased parts `erasure` records, a constructor's
/// nominal family read without its arguments.
///
/// # Specification
/// - requires: `node` lives in `core`, and `erasure` holds every first-order
///   part [`push_parts`] pushes for it.
/// - ensures: as [`erased`] at `node`, each part read through `erasure`.
/// - panics: none.
/// - executable: none — as [`erased`].
///
/// # Adequacy
/// - hypothesis: L2 — as [`erased`].
/// - witness: `tests::differential::the_corpus_runs_items_agree_with_normalisation_by_evaluation`
fn rebuilt(
    core: &mut CoreArena,
    erasure: &BTreeMap<ValueId, ValueId>,
    node: ValueId,
) -> ValueId
{
    let read = |part: &ValueId| erasure.get(part).copied().unwrap_or(*part);
    match core.value(node) {
        Some(&Value::Constructor {
            datatype,
            tag,
            ref fields,
        }) => {
            let fields: Vec<ValueId> = fields.iter().map(read).collect();
            let family = match core.value_type(datatype) {
                Some(&ValueType::Data { declaration, .. }) => {
                    core.value_type_data(declaration, Vec::new())
                },
                Some(_) | None => datatype,
            };
            core.value_constructor(family, tag, fields)
        },
        Some(&Value::Tuple(ref components)) => {
            let components: Vec<ValueId> = components.iter().map(read).collect();
            core.value_tuple(&components)
        },
        Some(&Value::Injection(summand, body)) => {
            let body = read(&body);
            core.value_injection(summand, body)
        },
        Some(&Value::ListCons(head, tail)) => {
            let (head, tail) = (read(&head), read(&tail));
            core.value_list_cons(head, tail)
        },
        Some(&Value::Record(ref fields)) => {
            let fields = fields
                .iter()
                .map(|(label, field)| (label.clone(), read(field)))
                .collect();
            core.value_record(fields)
        },
        Some(_) | None => node,
    }
}

/// `term` with the value it returns [`erased`]; `term` itself when it
/// returns nothing.
///
/// # Specification
/// - requires: `term` lives in `core`.
/// - ensures: `return erased(v)` for `term` = `return v`, and `term` for every
///   other former.
/// - panics: none.
/// - executable: none — as [`erased`].
///
/// # Adequacy
/// - hypothesis: L2 — as [`erased`].
/// - witness: `tests::differential::the_corpus_runs_items_agree_with_normalisation_by_evaluation`
fn erased_answer(
    core: &mut CoreArena,
    term: ComputationId,
) -> ComputationId
{
    match core.computation(term) {
        Some(&Computation::Return(answer)) => {
            let answer = erased(core, answer);
            core.computation_return(answer)
        },
        Some(_) | None => term,
    }
}

/// `term` of `core` spelled on one line, every former explicit, its
/// constants by `names`.
///
/// # Specification
/// trivial.
fn spelled(
    core: &CoreArena,
    names: &[Name<'_>],
    term: ComputationId,
) -> String
{
    let source = CoreSource::new(core, names);
    present_computation_line(&source, CoreNode::Computation(term), Style {
        form: Form::Explicit,
        spelling: Spelling::Ascii,
    })
    .map_or_else(|error| format!("<{error:?}>"), |shown| shown.to_string())
}

/// How the run of the declaration at `constant` on the executor and its
/// normal form relate, both read into `core`.
///
/// # Specification
/// - requires: `core` is the arena `program`'s module was judged over, and
///   `definitions` the checker's over it.
/// - ensures: [`Compared::Ended`] for a run that ends before it reads a value
///   or that the executor declines, [`Compared::Declined`] for a normal form
///   the normaliser cannot reach or holds where a run goes on, and otherwise
///   [`Compared::Exactly`], [`Compared::Erased`], [`Compared::Normalised`] or
///   [`Compared::Differ`] as the two terms relate.
/// - panics: none.
/// - executable: none — the relation is the witness's assertion.
///
/// # Adequacy
/// - hypothesis: L2 — as the witness.
/// - witness: `tests::differential::the_corpus_runs_items_agree_with_normalisation_by_evaluation`
fn compared(
    program: &mut Program<'_>,
    core: &mut CoreArena,
    definitions: Definitions<'_>,
    constant: ConstantIndex,
) -> Compared
{
    let run = match program.read_on(constant, Engine::Executor, core) {
        Ok(Terminal::Read(run)) => run,
        Ok(Terminal::Ended(evaluation)) => {
            return Compared::Ended(variant(&evaluation));
        },
        Err(declined) => return Compared::Ended(variant(&declined)),
    };
    let normal = match normalised(core, definitions, constant) {
        Ok(normal) => normal,
        Err(decline) => return Compared::Declined(decline),
    };
    if same(core, run, normal) == CertificateEquality::Equal {
        return Compared::Exactly;
    }
    let erased_normal = erased_answer(core, normal);
    let erased_run = erased_answer(core, run);
    if same(core, erased_run, erased_normal) == CertificateEquality::Equal {
        return Compared::Erased;
    }
    if let Ok(settled) = normal_form(core, definitions, run) {
        let settled = erased_answer(core, settled);
        if same(core, settled, erased_normal) == CertificateEquality::Equal {
            return Compared::Normalised;
        }
    }
    match apart(core, definitions, normal) {
        Apart::Held(decline) => Compared::Declined(decline),
        Apart::Unexplained => Compared::Differ { run, normal },
    }
}

/// Every declaration of the model corpus that states a `runs` outcome,
/// outside the pathological twins, normalises to what its run on the executor
/// reads, node for node — each constructor's family read without the
/// arguments a run erases — or once the run's reading is normalised too. The
/// agreements are counted, the items the normaliser cannot take by reason,
/// and printed.
#[test]
fn the_corpus_runs_items_agree_with_normalisation_by_evaluation()
{
    let corpus = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../surface-corpus");
    let walk = Walk::new(vec![corpus.join("strict"), corpus.join("fixture")]);
    let mut counted: BTreeMap<String, Vec<String>> = BTreeMap::new();
    let mut differing = String::new();
    let ControlFlow::Continue(_report) = walk.visit_admitting(
        &Pool::new(Width::SERIAL),
        |step, admission| -> ControlFlow<Infallible> {
            let Step::Source {
                path,
                composed:
                    Composed::Settled {
                        report,
                        mut program,
                        ..
                    },
                ..
            } = step
            else {
                return ControlFlow::Continue(());
            };
            if path
                .components()
                .any(|component| component.as_os_str() == "pathological")
            {
                return ControlFlow::Continue(());
            }
            let runs: Vec<(ConstantIndex, String)> = report
                .declarations()
                .iter()
                .filter(|declaration| {
                    matches!(*declaration.stated(), Stated::Verdict(Outcome::Runs(_)))
                })
                .map(|declaration| (declaration.constant(), declaration.name().to_string()))
                .collect();
            if runs.is_empty() {
                return ControlFlow::Continue(());
            }
            let Maybe::Present(admission) = admission
            else {
                panic!(
                    "{}: a settled source is handed its admission",
                    path.display()
                );
            };
            let definitions = definitions_of(admission.verdicts());
            let last = admission
                .verdicts()
                .judged()
                .iter()
                .map(|judged| usize::from(judged.constant()))
                .max()
                .unwrap_or_default();
            let named: Vec<String> = (0 ..= last)
                .map(|index| match program.name(ConstantIndex::from(index)) {
                    Maybe::Present(name) => name.to_string(),
                    Maybe::Absent(_) => String::from("?"),
                })
                .collect();
            let names: Vec<Name<'_>> = named.iter().map(|name| Name::from(name.as_str())).collect();
            let item = path.strip_prefix(&corpus).unwrap_or(path).display();
            let mut core = admission.arena().clone();
            for (constant, name) in runs {
                let key =
                    match compared(&mut program, &mut core, definitions.normaliser(), constant) {
                        Compared::Exactly => String::from("agree exactly"),
                        Compared::Erased => {
                            String::from("agree, the family arguments a run erases dropped")
                        },
                        Compared::Normalised => String::from("agree once the run is normalised"),
                        Compared::Ended(evaluation) => format!("run ended {evaluation}"),
                        Compared::Declined(decline) => format!("normaliser declined {decline:?}"),
                        Compared::Differ { run, normal } => {
                            writeln!(
                                differing,
                                "{item} {name}\n    run:    {}\n    normal: {}",
                                spelled(&core, &names, run),
                                spelled(&core, &names, normal),
                            )
                            .expect("a string writes");
                            String::from("differ")
                        },
                    };
                counted
                    .entry(key)
                    .or_default()
                    .push(format!("{item} {name}"));
            }
            ControlFlow::Continue(())
        },
    );
    for (key, items) in &counted {
        println!("{:>6}  {key}", items.len());
        if !key.starts_with("agree") {
            for item in items {
                println!("          {item}");
            }
        }
    }
    assert!(
        differing.is_empty(),
        "the normaliser and the run read apart:\n{differing}"
    );
    assert!(
        counted
            .get("agree exactly")
            .is_some_and(|items| !items.is_empty()),
        "the corpus states runs the normaliser agrees with"
    );
}

/// #1677: a transport along an equivalence written in a function body,
/// `transport-list.gandr`'s `flipped_inline`, normalises to what its run reads,
/// as its twin along the named equivalence, `flipped_list`, does.
#[test]
fn a_transport_along_an_inline_equivalence_normalises_1677()
{
    let source = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../surface-corpus/fixture/model/identity/transport-list.gandr");
    let mut answers: BTreeMap<String, Compared> = BTreeMap::new();
    let ControlFlow::Continue(_report) = Walk::new(vec![source]).visit_admitting(
        &Pool::new(Width::SERIAL),
        |step, admission| -> ControlFlow<Infallible> {
            let (
                Step::Source {
                    composed:
                        Composed::Settled {
                            report,
                            mut program,
                            ..
                        },
                    ..
                },
                Maybe::Present(admission),
            ) = (step, admission)
            else {
                return ControlFlow::Continue(());
            };
            let definitions = definitions_of(admission.verdicts());
            let mut core = admission.arena().clone();
            for declaration in report.declarations() {
                let name = declaration.name().to_string();
                if name == "flipped_inline" || name == "flipped_list" {
                    let answer = compared(
                        &mut program,
                        &mut core,
                        definitions.normaliser(),
                        declaration.constant(),
                    );
                    answers.insert(name, answer);
                }
            }
            ControlFlow::Continue(())
        },
    );
    for name in ["flipped_list", "flipped_inline"] {
        assert_eq!(
            answers.get(name),
            Some(&Compared::Exactly),
            "`{name}` normalises to what its run reads"
        );
    }
}
