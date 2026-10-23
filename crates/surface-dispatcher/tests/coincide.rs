//! The two readings of a block's rules held against each other on the corpus.
//!
//! A block's rules are read twice: the operation route compiles them to the
//! first-match decision tree the machine runs, and the cell layer rewrites a
//! call to its normal form, the path certified by replaying it. The lowering
//! admits a block only when the two readings coincide on every term; the
//! first differential witnesses that they do on the corpus's own calls, under
//! whichever specification mode the suite runs in.
//!
//! The cell layer's critical pairs are read twice as well: unified as terms
//! at and below the root of two left-hand sides, and glued as diagrams along
//! shared generators at a redex, a command's cut or any node of a term. The
//! second differential witnesses that every corpus block's two families are
//! one.
//!
//! The differentials, in a `cfg(test)` module so the crate's lint wall reads
//! them as test code rather than as shipping code.
use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use core::fmt::Display;
use std::path::PathBuf;

use anodized::spec;
use gandr_surface_corpus::CorpusRoot;
use gandr_surface_corpus::Outcome;
use gandr_surface_corpus::Runner as _;
use gandr_surface_corpus::Stated;
use gandr_surface_dispatcher::Composed;
use gandr_surface_dispatcher::HostGrant;
use gandr_surface_dispatcher::Lowered;
use gandr_surface_dispatcher::LoweringCount;
use gandr_surface_dispatcher::judge_module;
use gandr_surface_dispatcher::lower_source;
use gandr_surface_grammar::built_in;
use gandr_surface_lowering::coincide::CallText;
use gandr_surface_syntax::SourceFragment;
use gandr_surface_syntax::SourceText;
use gandr_theory_cell_complexes::CellAlphabet;
use gandr_theory_cell_complexes::CellStore;
use gandr_theory_circuit_algebras::Generator;
use gandr_theory_circuit_algebras::GeneratorLabel;
use gandr_theory_circuit_algebras::GeneratorSort;
use gandr_theory_circuit_algebras::Interface;
use gandr_theory_circuit_algebras::MatchBudget;
use gandr_theory_circuit_algebras::Matching;
use gandr_theory_circuit_algebras::Overlap;
use gandr_theory_circuit_algebras::OverlapShape;
use gandr_theory_circuit_algebras::SpineReading;
use gandr_theory_circuit_algebras::Wire;
use gandr_theory_circuit_algebras::WireCount;
use gandr_theory_circuit_algebras::Wiring;
use gandr_theory_circuit_algebras::embeddings;
use gandr_theory_circuit_algebras::overlaps;
use gandr_theory_circuit_algebras::read_spine;
use gandr_theory_coherent_resolutions::OverlapKind;
use gandr_theory_coherent_resolutions::interior_overlaps_between;
use gandr_theory_coherent_resolutions::overlaps_between;
use gandr_theory_levitation::FreeTerm;
use gandr_theory_levitation::TermNode;
use gandr_theory_levitation::TermView;
use quenchant_shape::shape::Maybe;

/// Every corpus source under the strict and fixture roots, the pending
/// set aside: a pending source is not yet read whole.
///
/// # Specification
/// - requires: the corpus directories list and read.
/// - ensures: every `.gandr` file below either root with no `pending` directory
///   on its path, once each, in path order.
/// - panics: if a directory does not list.
///
/// # Adequacy
/// - hypothesis: L3 — the differential reaches the described sources of both
///   roots; a walk that missed a root reads no run through a described
///   operation and fails the non-vacuity assertion.
/// - witness: `tests::coincide::every_run_through_a_described_operation_is_its_calls_normal_form`
#[spec(ensures: |ref ret| ret.iter().all(|path|
        path.extension().is_some_and(|extension| extension == "gandr")))]
fn sources() -> BTreeSet<PathBuf>
{
    let corpus = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../surface-corpus");
    let mut directories = vec![corpus.join("strict"), corpus.join("fixture")];
    let mut found = BTreeSet::new();
    while let Some(directory) = directories.pop() {
        for entry in std::fs::read_dir(&directory).expect("the directory lists") {
            let path = entry.expect("the entry reads").path();
            if path.is_dir() {
                if !path.ends_with("pending") {
                    directories.push(path);
                }
            }
            else if path
                .extension()
                .is_some_and(|extension| extension == "gandr")
            {
                let _new = found.insert(path);
            }
        }
    }
    found
}

/// The body of the thunk `name` is defined as in `text`: the bytes between
/// `def name = thunk {`, or the `{` opening the function form of no
/// parameter `def name() -> C {`, and the brace that closes it.
///
/// # Specification
/// - ensures: absent when `text` defines no thunk of that name; otherwise the
///   text inside its braces, nested braces kept.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — as the differential: a body cut short reads no call and
///   the run is reported as no direct call.
/// - witness: `tests::coincide::every_run_through_a_described_operation_is_its_calls_normal_form`
#[spec(ensures: |ret| ret.as_deref().is_none_or(|body| text.as_ref().contains(body)))]
fn thunk_body(
    text: SourceText<'_>,
    name: SourceFragment<'_>,
) -> Option<String>
{
    let text: &str = text.as_ref();
    let thunk = format!("def {name} = thunk {{");
    let function = format!("def {name}() -> ");
    let start = if let Some(at) = text.find(&thunk) {
        at.saturating_add(thunk.len())
    }
    else {
        let at = text.find(&function)?.saturating_add(function.len());
        let codomain = text.get(at ..)?;
        let mut depth = 0_usize;
        let open = codomain.char_indices().find_map(|(offset, character)| {
            match character {
                '(' | '[' => depth = depth.saturating_add(1),
                ')' | ']' => depth = depth.saturating_sub(1),
                '{' if depth == 0 => return Some(offset),
                _ => {},
            }
            None
        })?;
        at.saturating_add(open).saturating_add(1)
    };
    let rest = text.get(start ..)?;
    let mut depth = 0_usize;
    for (offset, character) in rest.char_indices() {
        match character {
            '{' => depth = depth.saturating_add(1),
            '}' if depth == 0 => return rest.get(.. offset).map(String::from),
            '}' => depth = depth.saturating_sub(1),
            _ => {},
        }
    }
    None
}

/// The call a thunk's body is, when the body is one call delivered
/// unchanged: `become f(…)`, `f(…)`, or `run p <- f(…); return p`, the tail
/// written `p` alone as the sugared form writes it (#1327).
///
/// # Specification
/// - ensures: present only for a body of one of the three shapes, the call an
///   identifier applied to one balanced argument list, with white space between
///   tokens collapsed.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the corpus's direct calls read, every shape among them; a
///   body that does more than deliver its call reads none and fails the
///   differential by name.
/// - witness: `tests::coincide::every_run_through_a_described_operation_is_its_calls_normal_form`
#[spec(ensures: |ret| ret.as_deref().is_none_or(|call| call.ends_with(')')))]
fn direct_call(body: SourceFragment<'_>) -> Option<String>
{
    let spaced = body
        .as_ref()
        .split_whitespace()
        .collect::<Vec<_>>()
        .join(" ");
    let spaced = spaced.trim_end_matches(';').trim_end();
    let call = if let Some(call) = spaced.strip_prefix("become ") {
        call
    }
    else if let Some(bound) = spaced.strip_prefix("run ") {
        let (pattern, rest) = bound.split_once(" <- ")?;
        let (call, tail) = rest.split_once("; ")?;
        let returned = tail.strip_prefix("return ").unwrap_or(tail);
        if returned.trim_end_matches(';').trim() != pattern {
            return None;
        }
        call
    }
    else {
        spaced
    };
    let (head, arguments) = call.split_once('(')?;
    let identifier = !head.is_empty()
        && head
            .chars()
            .all(|character| character.is_alphanumeric() || character == '_');
    let mut depth = 1_usize;
    let mut closed = None;
    for (offset, character) in arguments.char_indices() {
        match character {
            '(' => depth = depth.saturating_add(1),
            ')' => {
                depth = depth.saturating_sub(1);
                if depth == 0 {
                    closed = Some(offset);
                    break;
                }
            },
            _ => {},
        }
    }
    (identifier && closed == Some(arguments.len().saturating_sub(1))).then(|| String::from(call))
}

#[test]
fn every_run_through_a_described_operation_is_its_calls_normal_form()
{
    let grammar = built_in().expect("the built-in grammar builds");
    let mut lowerings = LoweringCount::default();
    let mut compared = 0_usize;
    let mut operations: Vec<String> = Vec::new();
    let mut needle = String::new();
    for path in sources() {
        let text = std::fs::read_to_string(&path).expect("the source reads");
        let shown = path.display();
        let Lowered::Module { module, arena } =
            lower_source(&grammar, SourceText::from(text.as_str()), &mut lowerings)
                .unwrap_or_else(|fault| panic!("{shown}: {fault}"))
                .into_lowered()
        else {
            continue;
        };
        // A presentation's operations are interpreted by its models and
        // run nowhere; only a family's operations have runs to compare.
        operations.clear();
        operations.extend(
            module
                .descriptions()
                .declarations
                .iter()
                .filter(|described| matches!(described.presentation, Maybe::Absent(_)))
                .flat_map(|described| described.description.opers.iter())
                .map(|operation| String::from(operation.name.as_ref())),
        );
        if operations.is_empty() {
            continue;
        }
        let mut calls = Vec::new();
        for declaration in module.declarations() {
            let name = declaration.name();
            let Some(body) = thunk_body(
                SourceText::from(text.as_str()),
                SourceFragment::from(name.as_ref()),
            )
            else {
                continue;
            };
            let named = operations.iter().find(|operation| {
                needle.clear();
                for part in [operation.as_str(), "("] {
                    needle.push_str(part);
                }
                body.contains(needle.as_str())
            });
            let Some(operation) = named
            else {
                continue;
            };
            let call = direct_call(SourceFragment::from(body.as_str())).unwrap_or_else(|| {
                panic!(
                    "{shown}: `{name}` runs through `{operation}` but is no direct call; the \
                         differential reads a run whose body is the call it delivers"
                )
            });
            let member = module
                .declarations()
                .iter()
                .find(|member| {
                    let name = member.name();
                    call.strip_prefix(AsRef::<str>::as_ref(&name))
                        .is_some_and(|rest| rest.starts_with('('))
                })
                .unwrap_or_else(|| panic!("{shown}: `{call}` names no declaration"));
            let normal = module
                .normal_form(member, CallText::from(call.as_str()))
                .unwrap_or_else(|fault| panic!("{shown}: `{call}`: {fault}"));
            calls.push((
                declaration.constant(),
                name.to_string(),
                call,
                normal.spelling(),
            ));
        }
        let Composed::Settled {
            report,
            mut program,
            ..
        } = judge_module(
            CorpusRoot::Fixture,
            (module, SourceText::from(text.as_str())),
            arena,
            &HostGrant::UNBOUNDED,
        )
        .unwrap_or_else(|fault| panic!("{shown}: {fault}"))
        else {
            panic!("{shown}: the module was refused whole");
        };
        let mut declared = BTreeMap::new();
        for declaration in report.declarations() {
            let _first = declared
                .entry(declaration.constant())
                .or_insert(declaration);
        }
        for (constant, name, call, engine) in calls {
            let runs = declared.get(&constant).is_some_and(|declaration| {
                matches!(declaration.stated(), Stated::Verdict(Outcome::Runs(_)))
            });
            if !runs {
                continue;
            }
            let machine = program.run(constant);
            assert_eq!(
                machine.as_ref(),
                engine,
                "{shown}: `{name}` runs `{call}` to {machine} on the machine; the engine \
                     reads {engine}"
            );
            compared = compared.saturating_add(1);
        }
    }
    assert!(
        compared > 0_usize,
        "the corpus holds a run through a described operation: {compared}"
    );
}

/// An embedding of `term` into `glued` when the two are one diagram up to
/// the order of their interface ports: as many generators and wires, and an
/// embedding of one into the other, which is then a bijection on both.
///
/// # Specification
/// - ensures: present exactly when the generator and wire counts agree and the
///   matcher admits an embedding of `term` into `glued`.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — every corpus critical pair's peak meets its glued twin,
///   and a peak with a generator more or less meets none.
/// - witness: `tests::coincide::every_blocks_critical_pairs_are_its_left_sides_glued`
#[spec(ensures: |ret| ret.is_none() || (term.generators().len() == glued.generators().len()
    && term.wire_count() == glued.wire_count()))]
fn one_diagram(
    term: &Wiring,
    glued: &Wiring,
) -> Option<Matching>
{
    (term.generators().len() == glued.generators().len() && term.wire_count() == glued.wire_count())
        .then(|| embeddings(term, glued, MatchBudget::from(100_000_usize)).ok())
        .flatten()
        .filter(|matching| !matching.admitted().is_empty())
}

/// A left-hand side read as a diagram, with the wire its redexes sit on.
trait Side
{
    /// The diagram.
    ///
    /// # Specification
    /// trivial.
    fn wiring(&self) -> &Wiring;

    /// The one wire a redex sits on, when the reading rewrites at one wire
    /// only; absent when every node is a redex.
    ///
    /// # Specification
    /// trivial.
    fn anchor(&self) -> Option<Wire>;
}

impl Side for SpineReading
{
    /// The spine's diagram.
    ///
    /// # Specification
    /// trivial.
    fn wiring(&self) -> &Wiring
    {
        Self::wiring(self)
    }

    /// The cut: a command rewrites there and nowhere else.
    ///
    /// # Specification
    /// trivial.
    fn anchor(&self) -> Option<Wire>
    {
        Some(self.cut())
    }
}

impl Side for Wiring
{
    /// The term's diagram.
    ///
    /// # Specification
    /// trivial.
    fn wiring(&self) -> &Wiring
    {
        self
    }

    /// None: a term rewrites at every node.
    ///
    /// # Specification
    /// trivial.
    fn anchor(&self) -> Option<Wire>
    {
        None
    }
}

/// One step of reading a term as a diagram.
enum Step<'term>
{
    /// Read the node and every node beneath it.
    Visit(TermNode<'term>),
    /// Add the generator `label` over the last `arity` wires read, in argument
    /// order, its target a fresh wire.
    Finish(GeneratorLabel, usize),
}

/// A presented term's diagram: one generator per constructor or operation
/// node, its arguments' wires its sources and one fresh wire its target, a
/// variable an input port and the root's wire the one output port.
///
/// # Specification
/// - ensures: absent when the term holds a results tuple or an instantiation,
///   which no left-hand side holds, or reads a variable twice, which no
///   monogamous diagram does.
/// - panics: none.
///
/// # Termination
/// Each node is visited once and finished once, and a visit pushes only the
/// node's children, so the stack empties after twice the term's node count.
///
/// # Adequacy
/// - hypothesis: L3 — every presented left-hand side of the corpus that reads
///   no variable twice reads, and so does every peak its pairs unify at.
/// - witness: `tests::coincide::every_blocks_critical_pairs_are_its_left_sides_glued`
#[spec(ensures: |ref ret| ret.as_ref().is_none_or(|wiring| wiring.boundary().outputs().len() == 1))]
fn term_diagram(term: &FreeTerm) -> Option<Wiring>
{
    let mut count = 0_usize;
    let mut generators = Vec::new();
    let mut inputs = Vec::new();
    let mut read = BTreeSet::new();
    let mut delivered: Vec<Wire> = Vec::new();
    let mut pending = Vec::new();
    let mut stack = alloc::vec![Step::Visit(term.to_node())];
    while let Some(step) = stack.pop() {
        match step {
            Step::Visit(node) => {
                let (name, sort, args) = match node.view() {
                    TermView::Var(name) => {
                        if !read.insert(name) {
                            return None;
                        }
                        let wire = Wire::from(count);
                        count = count.saturating_add(1);
                        inputs.push(wire);
                        delivered.push(wire);
                        continue;
                    },
                    TermView::Ctor { name, args } => (name, GeneratorSort::Value, args),
                    TermView::Op { name, args } => (name, GeneratorSort::Operation, args),
                    TermView::Results { .. }
                    | TermView::Inst { .. }
                    | TermView::Abs { .. }
                    | TermView::Atom(_) => {
                        return None;
                    },
                };
                stack.push(Step::Finish(
                    GeneratorLabel::new(name.as_ref(), sort),
                    args.len(),
                ));
                pending.clear();
                pending.extend(args);
                stack.extend(pending.iter().rev().copied().map(Step::Visit));
            },
            Step::Finish(label, arity) => {
                let sources = delivered.split_off(delivered.len().saturating_sub(arity));
                let target = Wire::from(count);
                count = count.saturating_add(1);
                generators.push(Generator::new(label, sources, [target]));
                delivered.push(target);
            },
        }
    }
    let root = delivered.pop()?;
    Wiring::assemble(
        WireCount::from(count),
        generators,
        Interface::new(inputs, [root]),
    )
    .ok()
}

/// How many critical pairs a store's differential compared.
#[derive(Clone, Copy, Debug, Default, Eq, Ord, PartialEq, PartialOrd)]
#[repr(transparent)]
struct PairCount(usize);

/// The critical pairs of one store read both ways, each unified peak met by
/// its gluings; the count of pairs compared.
///
/// The term side is what completion decides: the root pair of two cells once,
/// then the pairs below either cell's root, a cell against itself once. The
/// circuit side glues the two left-hand sides' diagrams at a redex. A command
/// is a redex only at its cut, so where a side names its cut as its anchor the
/// gluing sends the right side's cut onto the left's; a term is a redex at
/// every node, so a side with no anchor glues anywhere. A gluing that sends a
/// cut elsewhere embeds a left-hand side where the term reading rewrites
/// nothing, the sub-diagram relation the anchor narrows, and is not compared.
/// A cell against itself drops its identity gluing, which the root diagonal
/// omits, and glues each pair below its root twice, once with either copy
/// outside. A left-hand side that copies a variable reads as no diagram, and
/// its pairs are not compared.
///
/// # Specification
/// - ensures: the number of term-side pairs, every one of them met.
/// - panics: when a peak reads as no diagram, when a peak meets no gluing at a
///   redex, or when such a gluing is left over.
///
/// # Adequacy
/// - hypothesis: L3 — every corpus block's two families are one; a pair either
///   side misses fails by the cells' names.
/// - witness: `tests::coincide::every_blocks_critical_pairs_are_its_left_sides_glued`
#[spec(ensures: |ret| store.iter().next().is_some() || ret == PairCount::default())]
fn compare_pairs<A, S>(
    shown: &impl Display,
    store: &CellStore<A>,
    diagram: impl Fn(&A::Cmd) -> Option<S>,
) -> PairCount
where
    A: CellAlphabet,
    S: Side,
{
    let read = |cmd: &A::Cmd| {
        diagram(cmd).unwrap_or_else(|| panic!("{shown}: reads as no diagram: {cmd:?}"))
    };
    let cells: Vec<_> = store.iter().collect();
    let sides: Vec<Option<S>> = cells.iter().map(|&(_, cell)| diagram(cell.lhs())).collect();
    let mut pairs = PairCount::default();
    let mut unified = Vec::new();
    let mut unmatched: Vec<usize> = Vec::new();
    for (index, (&left, left_side)) in cells.iter().zip(&sides).enumerate() {
        for (&right, right_side) in cells.iter().zip(&sides).skip(index) {
            let (&Some(ref left_side), &Some(ref right_side)) = (left_side, right_side)
            else {
                continue;
            };
            let at_redex = |overlap: &Overlap| match (left_side.anchor(), right_side.anchor()) {
                (Some(left_cut), Some(right_cut)) => {
                    overlap.right_wire(right_cut) == Some(left_cut)
                },
                (None, None) => true,
                (Some(_), None) | (None, Some(_)) => false,
            };
            let diagonal = left.0 == right.0;
            unified.clear();
            unified.extend(
                overlaps_between(left, right)
                    .into_iter()
                    .filter(|overlap| overlap.kind == OverlapKind::Confluence),
            );
            unified.extend(interior_overlaps_between(left, right));
            if !diagonal {
                unified.extend(interior_overlaps_between(right, left));
            }
            let glued = overlaps(left_side.wiring(), right_side.wiring());
            unmatched.clear();
            unmatched.extend(
                glued
                    .iter()
                    .enumerate()
                    .filter(|&(_, overlap)| {
                        (!diagonal || overlap.shape() != OverlapShape::Coincident)
                            && at_redex(overlap)
                    })
                    .map(|(position, _)| position),
            );
            let copies = if diagonal { 2_usize } else { 1_usize };
            for overlap in &unified {
                let peak = read(&overlap.peak);
                for _ in 0 .. copies {
                    let Some(twin) = unmatched.iter().position(|&position| {
                        glued
                            .get(position)
                            .is_some_and(|glued| one_diagram(peak.wiring(), glued.peak()).is_some())
                    })
                    else {
                        panic!(
                            "{shown}: cells {:?} and {:?} unify at a peak no gluing reaches: {:?}",
                            left.0, right.0, overlap.peak
                        )
                    };
                    let _twin = unmatched.swap_remove(twin);
                }
            }
            if let Some(leftover) = unmatched.first().and_then(|&position| glued.get(position)) {
                panic!(
                    "{shown}: cells {:?} and {:?} glue at a redex where no unifier meets: {:?}",
                    left.0,
                    right.0,
                    leftover.peak()
                );
            }
            pairs.0 = pairs.0.saturating_add(unified.len());
        }
    }
    pairs
}

#[test]
fn every_blocks_critical_pairs_are_its_left_sides_glued()
{
    let grammar = built_in().expect("the built-in grammar builds");
    let mut lowerings = LoweringCount::default();
    let (mut sequent, mut presented) = (PairCount::default(), PairCount::default());
    for path in sources() {
        let text = std::fs::read_to_string(&path).expect("the source reads");
        if !text.contains("rule ") {
            continue;
        }
        let shown = path.display();
        let Lowered::Module { module, .. } =
            lower_source(&grammar, SourceText::from(text.as_str()), &mut lowerings)
                .unwrap_or_else(|fault| panic!("{shown}: {fault}"))
                .into_lowered()
        else {
            continue;
        };
        for declaration in &module.cells().declarations {
            sequent.0 = sequent.0.saturating_add(
                compare_pairs(&shown, &declaration.rewriting(), |cmd| read_spine(cmd).ok()).0,
            );
            if let Maybe::Present(ref rules) = declaration.presented {
                presented.0 = presented.0.saturating_add(
                    compare_pairs(&shown, &rules.store, |term| match term.read() {
                        Maybe::Present(term) => term_diagram(&term),
                        Maybe::Absent(_) => None,
                    })
                    .0,
                );
            }
        }
    }
    assert!(
        sequent.0 > 0_usize && presented.0 > 0_usize,
        "the corpus holds overlapping rules over calls and over terms: {sequent:?}, {presented:?}"
    );
}
