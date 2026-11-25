//! The convergence sweep: each `data` block and each `theory` block that a
//! source of the repository admits, with rules, joins each of its critical
//! pairs.
//!
//! The sweep reads every `.gandr` source under `corpus/`, `library/`, the
//! strict root and the crates, that writes a rule (`==>` or `<=>`). It takes
//! each through the composition a driver runs: parse, lower, check, readmit,
//! export. A declaration that the export holds is admitted. From each one it
//! takes the rules as the kernel carries them: the presentation of a `data`
//! declaration, and the rules that [`TheoryRules::decided`] reads off the
//! value of a `theory` definition.
//!
//! The oracle is its own: no call reaches the coincidence check of the
//! lowering, the completion of the theory crates, or the decision of the
//! kernel. It reads the rules as a first-order rewriting system modulo the
//! commutativity of each symbol that a symmetry names. It finds each critical
//! pair by unification modulo that commutativity, normalizes both sides by
//! matching modulo it, and compares the two normal forms in a canonical order
//! of the commutative arguments. For commutativity alone no extended rule is
//! necessary, so the rules converge modulo the symmetries exactly when each
//! such pair joins, given that they terminate.
//!
//! A rule of a `theory` block that instantiates a variable, states a
//! condition or fires under a row is second order. The oracle reads no such
//! rule, and the sweep counts the pairs that it leaves out.
//!
//! The sweep knows the blocks whose rules part, each beside the unit that
//! removes it ([`sweeps::PARTING`]). It fails for each other block that
//! parts, and for each known block that joins.
//!
//! # References
//!
//! - `vault:01a213f1-00b3-765d-b3f9-135dd191549f` — background: the two
//!   questions on a symmetry, and the units that each answer starts.

use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use alloc::format;
use alloc::string::String;
use alloc::vec::Vec;
use std::fs;
use std::path::Path;
use std::path::PathBuf;

use gandr_core_checker::CheckBudget;
use gandr_core_checker::CheckingContext;
use gandr_core_checker::bridge;
use gandr_core_checker::check_module;
use gandr_core_term::CoreArena;
use gandr_kernel_term::DeclarationContent;
use gandr_kernel_term::MarkedDeclaration;
use gandr_kernel_term::RuleNode;
use gandr_kernel_term::TermArena;
use gandr_kernel_term::TheoryNode;
use gandr_kernel_term::TheoryRuleReading;
use gandr_kernel_term::TheoryRules;
use gandr_kernel_term::Value;
use gandr_kernel_term::ValueType;
use gandr_kernel_term::ValueTypeId;
use gandr_kernel_term::presentation_code;
use gandr_surface_dispatcher::classify;
use gandr_surface_dispatcher::lay_out;
use gandr_surface_grammar::Pbg;
use gandr_surface_lowering::LoweringBudget;
use gandr_surface_lowering::lower_unit;
use gandr_surface_lowering::namespace::Recognition;
use gandr_surface_parser::parse;
use gandr_surface_syntax::SourceText;

use crate::fixture::declarations;

/// The steps one normalization may take before the oracle calls the term
/// unnormalized: far above the few dozen that a pair of the corpus takes.
const STEPS: usize = 1 << 14;

/// The offset that keeps the variables of the inner rule of a pair apart
/// from those of the outer rule.
const APART: u32 = 1 << 16;

/// A first-order term: a symbol over its arguments, or a variable.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum Term
{
    /// A variable, by its number.
    Variable(u32),
    /// A symbol, by its place in the table, over its arguments.
    Apply(usize, Vec<Self>),
}

/// One node of a side in pre-order, as the two kernel forms write it.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug)]
enum Node
{
    /// A symbol, by its place in the table.
    Symbol(usize),
    /// A variable, by its number.
    Variable(u32),
}

/// The bindings of variables to terms.
type Bindings = BTreeMap<u32, Term>;

/// One admitted block's rules, read as a first-order rewriting system modulo
/// the commutativity of its symmetric symbols.
///
/// # Specification
/// trivial.
struct System
{
    /// The source and the declaration, for the report.
    name: String,
    /// The symbols that a symmetry names, ascending.
    symmetric: BTreeSet<usize>,
    /// The rules that rewrite, each as its two sides.
    rules: Vec<(Term, Term)>,
    /// The rules that the oracle does not read: second-order ones.
    unread: usize,
}

/// The term that `nodes` write in pre-order, each symbol over the count of
/// arguments that `arity` gives it; none when they write no one term.
///
/// # Specification
/// - requires: nothing.
/// - ensures: `Some` exactly when `nodes` are one whole term by `arity`.
/// - panics: none.
///
/// # Cost
/// - allocation: one term node for each node, growth within `nodes`
///
/// # Adequacy
/// - hypothesis: L3 — each rule of each admitted block of the repository reads
///   as one term.
/// - witness: `kernel_export::convergence::sweeps::each_admitted_block_with_rules_joins_its_critical_pairs`
fn tree<A>(
    nodes: &[Node],
    arity: A,
) -> Option<Term>
where
    A: Fn(usize) -> Option<usize>,
{
    let mut built: Vec<Term> = Vec::with_capacity(nodes.len());
    for &node in nodes.iter().rev() {
        match node {
            Node::Variable(variable) => built.push(Term::Variable(variable)),
            Node::Symbol(symbol) => {
                let count = arity(symbol)?;
                let start = built.len().checked_sub(count)?;
                let mut arguments = built.split_off(start);
                arguments.reverse();
                built.push(Term::Apply(symbol, arguments));
            },
        }
    }
    let term = built.pop()?;
    built.is_empty().then_some(term)
}

/// `term` with each argument pair of a symmetric symbol in ascending order,
/// from the leaves up: one term for each class of the commutativity.
///
/// # Specification
/// - requires: nothing.
/// - ensures: two terms that the commutativity of `symmetric` relates give one
///   result, and two that it does not relate give two.
/// - panics: none.
///
/// # Cost
/// - allocation: the rebuilt term and the walk's stacks, growth within the term
///
/// # Adequacy
/// - hypothesis: L3 — as the sweep.
/// - witness: `kernel_export::convergence::sweeps::each_admitted_block_with_rules_joins_its_critical_pairs`
fn canonical(
    term: &Term,
    symmetric: &BTreeSet<usize>,
) -> Term
{
    rebuilt(
        term,
        |symbol, mut arguments| {
            if symmetric.contains(&symbol) {
                arguments.sort_unstable();
            }
            Term::Apply(symbol, arguments)
        },
        Term::Variable,
    )
}

/// `term` rebuilt from the leaves up: each variable by `leaf`, each symbol
/// over its rebuilt arguments by `node`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the fold of `term` by `node` and `leaf`.
/// - panics: none.
///
/// # Cost
/// - allocation: the walk's two stacks, growth within the term
///
/// # Adequacy
/// - hypothesis: L3 — as the sweep.
/// - witness: `kernel_export::convergence::sweeps::each_admitted_block_with_rules_joins_its_critical_pairs`
fn rebuilt<N, L>(
    term: &Term,
    node: N,
    leaf: L,
) -> Term
where
    N: Fn(usize, Vec<Term>) -> Term,
    L: Fn(u32) -> Term,
{
    // Each entry is a subterm and whether its arguments are built.
    let mut pending: Vec<(&Term, bool)> = Vec::from([(term, false)]);
    let mut built: Vec<Term> = Vec::new();
    while let Some((at, ready)) = pending.pop() {
        match *at {
            Term::Variable(variable) => built.push(leaf(variable)),
            Term::Apply(symbol, ref arguments) => {
                if ready {
                    let start = built.len().saturating_sub(arguments.len());
                    let rebuilt_arguments = built.split_off(start);
                    built.push(node(symbol, rebuilt_arguments));
                }
                else {
                    pending.push((at, true));
                    pending.extend(arguments.iter().rev().map(|argument| (argument, false)));
                }
            },
        }
    }
    built.pop().expect("the walk builds one term")
}

/// `term` with each variable that `bindings` binds replaced by its binding,
/// once.
///
/// # Specification
/// trivial.
fn substituted(
    term: &Term,
    bindings: &Bindings,
) -> Term
{
    rebuilt(term, Term::Apply, |variable| {
        bindings
            .get(&variable)
            .cloned()
            .unwrap_or(Term::Variable(variable))
    })
}

/// `term` with each variable that `bindings` binds replaced until no bound
/// variable is left; none when a binding holds its own variable.
///
/// # Specification
/// - requires: nothing.
/// - ensures: `Some` with no variable that `bindings` binds, when the bindings
///   are idempotent after as many rounds as they hold entries.
/// - panics: none.
///
/// # Termination
/// - reason: one round for each binding, at most.
/// - measure: the bindings not yet passed.
///
/// # Adequacy
/// - hypothesis: L3 — as the sweep.
/// - witness: `kernel_export::convergence::sweeps::each_admitted_block_with_rules_joins_its_critical_pairs`
fn resolved(
    term: &Term,
    bindings: &Bindings,
) -> Option<Term>
{
    let mut current = term.clone();
    for _round in 0 ..= bindings.len() {
        if !variables(&current).any(|variable| bindings.contains_key(&variable)) {
            return Some(current);
        }
        current = substituted(&current, bindings);
    }
    None
}

/// The variables of `term`, each where it stands.
///
/// # Specification
/// trivial.
fn variables(term: &Term) -> impl Iterator<Item = u32> + '_
{
    let mut pending = Vec::from([term]);
    core::iter::from_fn(move || {
        while let Some(at) = pending.pop() {
            match *at {
                Term::Variable(variable) => return Some(variable),
                Term::Apply(_, ref arguments) => pending.extend(arguments.iter()),
            }
        }
        None
    })
}

/// The path of each symbol of `term`, in pre-order.
///
/// # Specification
/// trivial.
fn positions(term: &Term) -> Vec<Vec<usize>>
{
    let mut found = Vec::new();
    let mut pending: Vec<(&Term, Vec<usize>)> = Vec::from([(term, Vec::new())]);
    while let Some((at, path)) = pending.pop() {
        if let Term::Apply(_, ref arguments) = *at {
            for (index, argument) in arguments.iter().enumerate().rev() {
                let mut next = path.clone();
                next.push(index);
                pending.push((argument, next));
            }
            found.push(path);
        }
    }
    found
}

/// The subterm of `term` at `path`.
///
/// # Specification
/// trivial.
fn at<'term>(
    term: &'term Term,
    path: &[usize],
) -> Option<&'term Term>
{
    path.iter().try_fold(term, |at, &index| match *at {
        Term::Apply(_, ref arguments) => arguments.get(index),
        Term::Variable(_) => None,
    })
}

/// The subterm of `term` at `path`, to replace.
///
/// # Specification
/// trivial.
fn at_mut<'term>(
    term: &'term mut Term,
    path: &[usize],
) -> Option<&'term mut Term>
{
    path.iter().try_fold(term, |at, &index| match *at {
        Term::Apply(_, ref mut arguments) => arguments.get_mut(index),
        Term::Variable(_) => None,
    })
}

/// The bindings by which `pattern` matches `term` modulo the commutativity of
/// `symmetric`; none when it does not.
///
/// # Specification
/// - requires: nothing; a variable of `term` is a constant here.
/// - ensures: `Some` with bindings under which `pattern` and `term` are one
///   term modulo the commutativity, a repeated variable bound to terms equal
///   modulo it; `None` when no such bindings exist.
/// - panics: none.
///
/// # Termination
/// - reason: each turn takes one pair of subterms off its list, and a pair of
///   two applications puts back pairs of their strictly smaller arguments; a
///   symmetric pair adds one alternative of the same size.
/// - measure: the nodes of `pattern` left to match, over each alternative.
///
/// # Cost
/// - allocation: the bindings and the alternatives, growth within the pattern's
///   nodes and its symmetric nodes
///
/// # Adequacy
/// - hypothesis: L3 — as the sweep.
/// - witness: `kernel_export::convergence::sweeps::each_admitted_block_with_rules_joins_its_critical_pairs`
fn matched(
    pattern: &Term,
    term: &Term,
    symmetric: &BTreeSet<usize>,
) -> Option<Bindings>
{
    let mut alternatives: Vec<(Vec<(&Term, &Term)>, Bindings)> =
        Vec::from([(Vec::from([(pattern, term)]), Bindings::new())]);
    'alternative: while let Some((mut pending, mut bound)) = alternatives.pop() {
        while let Some((left, right)) = pending.pop() {
            match (left, right) {
                (&Term::Variable(variable), _) => match bound.get(&variable) {
                    Some(earlier) => {
                        if canonical(earlier, symmetric) != canonical(right, symmetric) {
                            continue 'alternative;
                        }
                    },
                    None => {
                        let _fresh = bound.insert(variable, right.clone());
                    },
                },
                (&Term::Apply(symbol, ref patterns), &Term::Apply(other, ref arguments))
                    if symbol == other && patterns.len() == arguments.len() =>
                {
                    if let (
                        true,
                        &[ref first, ref second],
                        &[ref left_argument, ref right_argument],
                    ) = (
                        symmetric.contains(&symbol),
                        patterns.as_slice(),
                        arguments.as_slice(),
                    ) {
                        let mut swapped = pending.clone();
                        swapped.push((first, right_argument));
                        swapped.push((second, left_argument));
                        alternatives.push((swapped, bound.clone()));
                    }
                    pending.extend(patterns.iter().zip(arguments.iter()));
                },
                (&Term::Apply(..), _) => continue 'alternative,
            }
        }
        return Some(bound);
    }
    None
}

/// A complete set of unifiers of `left` and `right` modulo the commutativity
/// of `symmetric`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: each result unifies the two terms modulo the commutativity, and
///   each unifier modulo it is an instance of one result: at each pair of
///   applications of one symmetric symbol both orders are tried.
/// - panics: none.
///
/// # Termination
/// - reason: each turn takes one equation off its list; a variable binds once,
///   the occurs check refusing a cycle, and a pair of applications puts back
///   equations of their strictly smaller arguments.
/// - measure: the unbound variables, then the nodes left, over each
///   alternative.
///
/// # Cost
/// - allocation: the bindings, the equations and the alternatives, growth
///   within the two terms and their symmetric nodes
///
/// # Adequacy
/// - hypothesis: L3 — as the sweep.
/// - witness: `kernel_export::convergence::sweeps::each_admitted_block_with_rules_joins_its_critical_pairs`
fn unifiers(
    left: &Term,
    right: &Term,
    symmetric: &BTreeSet<usize>,
) -> Vec<Bindings>
{
    let mut found = Vec::new();
    let mut alternatives: Vec<(Vec<(Term, Term)>, Bindings)> =
        Vec::from([(Vec::from([(left.clone(), right.clone())]), Bindings::new())]);
    'alternative: while let Some((mut pending, mut bound)) = alternatives.pop() {
        while let Some((first, second)) = pending.pop() {
            let (Some(first), Some(second)) = (resolved(&first, &bound), resolved(&second, &bound))
            else {
                continue 'alternative;
            };
            match (first, second) {
                (Term::Variable(one), Term::Variable(other)) if one == other => {},
                (Term::Variable(variable), term) | (term, Term::Variable(variable)) => {
                    if variables(&term).any(|inner| inner == variable) {
                        continue 'alternative;
                    }
                    let _fresh = bound.insert(variable, term);
                },
                (Term::Apply(symbol, firsts), Term::Apply(other, seconds)) => {
                    if symbol != other || firsts.len() != seconds.len() {
                        continue 'alternative;
                    }
                    if let (true, &[ref one, ref two], &[ref three, ref four]) = (
                        symmetric.contains(&symbol),
                        firsts.as_slice(),
                        seconds.as_slice(),
                    ) {
                        let mut swapped = pending.clone();
                        swapped.push((one.clone(), four.clone()));
                        swapped.push((two.clone(), three.clone()));
                        alternatives.push((swapped, bound.clone()));
                    }
                    pending.extend(firsts.into_iter().zip(seconds));
                },
            }
        }
        found.push(bound);
    }
    found
}

impl System
{
    /// The normal form of `term` under the rules, matching modulo the
    /// commutativity, in its canonical order; none when it takes more than
    /// [`STEPS`] rewrites.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: `Some` with a canonical term reached from `term` by rewrites,
    ///   at which no rule matches modulo the commutativity.
    /// - panics: none.
    ///
    /// # Termination
    /// - reason: one rewrite per turn, at most [`STEPS`] turns.
    /// - measure: the steps left.
    ///
    /// # Cost
    /// - allocation: the rewritten term and each matching's bindings, growth
    ///   within the term's nodes and the steps
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as the sweep.
    /// - witness: `kernel_export::convergence::sweeps::each_admitted_block_with_rules_joins_its_critical_pairs`
    fn normal_form(
        &self,
        term: &Term,
    ) -> Option<Term>
    {
        let mut current = canonical(term, &self.symmetric);
        'step: for _step in 0 .. STEPS {
            for path in positions(&current).iter().rev() {
                let Some(subterm) = at(&current, path)
                else {
                    continue;
                };
                for &(ref left, ref right) in &self.rules {
                    let Some(bindings) = matched(left, subterm, &self.symmetric)
                    else {
                        continue;
                    };
                    let contractum = substituted(right, &bindings);
                    if let Some(place) = at_mut(&mut current, path) {
                        *place = contractum;
                    }
                    current = canonical(&current, &self.symmetric);
                    continue 'step;
                }
            }
            return Some(current);
        }
        None
    }

    /// Each critical pair of the rules whose two sides do not join modulo the
    /// commutativity, described for the report.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: one entry for each outer rule, symbol position of its left
    ///   side, inner rule and unifier modulo the commutativity whose two
    ///   reducts have two canonical normal forms, or one that takes more than
    ///   [`STEPS`] rewrites.
    /// - panics: none.
    ///
    /// # Cost
    /// - allocation: the pairs, their normal forms and the entries, growth
    ///   within the rules and their overlaps
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as the sweep.
    /// - witness: `kernel_export::convergence::sweeps::each_admitted_block_with_rules_joins_its_critical_pairs`
    fn parted(&self) -> Vec<String>
    {
        let mut parted = Vec::new();
        for (outer, &(ref left, ref right)) in self.rules.iter().enumerate() {
            for path in positions(left) {
                let Some(overlapped) = at(left, &path)
                else {
                    continue;
                };
                for (inner, &(ref inner_left, ref inner_right)) in self.rules.iter().enumerate() {
                    let apart = |variable: u32| Term::Variable(variable.saturating_add(APART));
                    let inner_left = rebuilt(inner_left, Term::Apply, apart);
                    let inner_right = rebuilt(inner_right, Term::Apply, apart);
                    for bindings in unifiers(overlapped, &inner_left, &self.symmetric) {
                        let mut by_inner = left.clone();
                        if let Some(place) = at_mut(&mut by_inner, &path) {
                            place.clone_from(&inner_right);
                        }
                        let sides = (resolved(right, &bindings), resolved(&by_inner, &bindings));
                        let (Some(by_outer), Some(by_inner)) = sides
                        else {
                            continue;
                        };
                        let normal = (self.normal_form(&by_outer), self.normal_form(&by_inner));
                        if normal.0.is_none() || normal.0 != normal.1 {
                            parted.push(format!(
                                "rule {outer} at {path:?} with rule {inner} gives {:?} and {:?}",
                                normal.0, normal.1
                            ));
                        }
                    }
                }
            }
        }
        parted
    }
}

/// The text of each `.gandr` source under `directory` that writes a rule,
/// links not followed and build trees skipped, beside its path.
///
/// # Specification
/// - requires: `directory` is readable.
/// - ensures: each such source once.
/// - panics: when a directory or a source cannot be read.
///
/// # Cost
/// - allocation: the paths and the texts, growth within the tree
///
/// # Adequacy
/// - hypothesis: L3 — as the two sweeps that read it.
/// - witness: `kernel_export::convergence::sweeps::each_admitted_block_with_rules_joins_its_critical_pairs`
/// - witness: `rule_census::sweeps::each_refused_rule_has_its_row_in_the_census`
pub fn sources(directory: &Path) -> Vec<(PathBuf, String)>
{
    let mut found = Vec::new();
    let mut pending = Vec::from([directory.to_path_buf()]);
    while let Some(here) = pending.pop() {
        let entries = fs::read_dir(&here)
            .unwrap_or_else(|error| panic!("{}: the directory lists: {error}", here.display()));
        for entry in entries {
            let entry = entry.expect("an entry reads");
            let kind = entry.file_type().expect("an entry has a type");
            let path = entry.path();
            if kind.is_dir() && !path.ends_with("target") {
                pending.push(path);
            }
            else if !kind.is_dir()
                && !kind.is_symlink()
                && path
                    .extension()
                    .is_some_and(|extension| extension == "gandr")
            {
                let text = fs::read_to_string(&path).unwrap_or_else(|error| {
                    panic!("{}: the source reads: {error}", path.display())
                });
                if text.contains("==>") || text.contains("<=>") {
                    found.push((path, text));
                }
            }
        }
    }
    found
}

/// The declarations that the kernel admits from the source at `path`, read
/// as `text`, over the arena that holds them; none when the source does not
/// parse or the lowering refuses it whole.
///
/// # Specification
/// - requires: `text` is the source at `path`.
/// - ensures: the decoded export of what crossed, as a driver runs parse,
///   lower, check and readmission.
/// - panics: none.
///
/// # Cost
/// - allocation: the pipeline's trees, arenas and artifact, growth within the
///   source and its imports
///
/// # Adequacy
/// - hypothesis: L3 — as the sweep.
/// - witness: `kernel_export::convergence::sweeps::each_admitted_block_with_rules_joins_its_critical_pairs`
fn admitted(
    pbg: &Pbg,
    path: &Path,
    text: &str,
) -> Option<(TermArena, Vec<MarkedDeclaration>)>
{
    let laid = lay_out(pbg, path, classify(path), SourceText::from(text));
    let tree = parse(pbg, SourceText::from(laid.text.as_str()))
        .ok()?
        .into_tree();
    let mut arena = CoreArena::new();
    let module = lower_unit(
        pbg,
        &tree,
        &laid.unit,
        &mut arena,
        LoweringBudget::DEFAULT,
        Recognition::default(),
        &mut gandr_surface_lowering::coincide::Decisions::none(),
    )
    .ok()?;
    let adapted = declarations(&module, &arena);
    let verdicts = check_module(
        &mut CheckingContext::new(&mut arena, CheckBudget::DEFAULT),
        &adapted,
    );
    let readmission = bridge::readmit(&mut arena, &verdicts);
    let artifact = readmission.export(module.structured_names());
    let keys = readmission.export_names();
    let decoded = gandr_kernel_term::decode_named(artifact.as_image(), &keys).ok()?;
    Some((decoded.arena().clone(), decoded.declarations().to_vec()))
}

/// The rule systems of the admitted declarations, each named by the
/// declaration.
///
/// # Specification
/// - requires: `declarations` are admitted in order over `arena`.
/// - ensures: one system for each `data` declaration with rules and for each
///   definition whose value is a presentation, beside the fault when its rules
///   do not read as terms.
/// - panics: none.
///
/// # Cost
/// - allocation: the systems, growth within the declarations' rules
///
/// # Adequacy
/// - hypothesis: L3 — as the sweep.
/// - witness: `kernel_export::convergence::sweeps::each_admitted_block_with_rules_joins_its_critical_pairs`
fn systems(
    arena: &TermArena,
    declarations: &[MarkedDeclaration],
) -> Vec<(System, Option<String>)>
{
    let mut found = Vec::new();
    for marked in declarations {
        let declaration = marked.declaration();
        let segments: Vec<&str> = declaration
            .name()
            .segments()
            .iter()
            .map(AsRef::as_ref)
            .collect();
        let name = if segments.is_empty() {
            String::from("a declaration with no name")
        }
        else {
            segments.join(".")
        };
        match *declaration.content() {
            DeclarationContent::Data {
                ref constructors, ..
            } if !declaration.presentation().rules().is_empty() => {
                let arity = |tag: usize| constructors.get(tag).map(|fields| fields.len());
                let node = |node: &RuleNode| match *node {
                    RuleNode::Constructor(tag) => Node::Symbol(usize::from(tag)),
                    RuleNode::Variable(variable) => Node::Variable(u32::from(variable)),
                };
                let sides: Vec<(Vec<Node>, Vec<Node>)> = declaration
                    .presentation()
                    .rules()
                    .iter()
                    .map(|rule| {
                        (
                            rule.left().iter().map(node).collect(),
                            rule.right().iter().map(node).collect(),
                        )
                    })
                    .collect();
                found.push(read(name, &sides, arity, 0));
            },
            DeclarationContent::Def { declared, body } => {
                if !presents(arena, declarations, declared)
                    || !matches!(arena.value(body), Some(&Value::Constructor { .. }))
                {
                    continue;
                }
                let rules = match TheoryRules::read(arena, body) {
                    Ok(rules) => rules,
                    Err(refusal) => {
                        found.push((
                            System {
                                name,
                                symmetric: BTreeSet::new(),
                                rules: Vec::new(),
                                unread: 0,
                            },
                            Some(format!("the admitted rules do not read: {refusal:?}")),
                        ));
                        continue;
                    },
                };
                let symbols = rules.symbols();
                let arity =
                    |symbol: usize| symbols.get(symbol).map(|&(_, count)| usize::from(count));
                let node = |node: &TheoryNode| match *node {
                    TheoryNode::Symbol(symbol) => Some(Node::Symbol(usize::from(symbol))),
                    TheoryNode::Variable(variable) => Some(Node::Variable(u32::from(variable))),
                    TheoryNode::Instance(..) => None,
                };
                let mut unread = 0_usize;
                let mut sides: Vec<(Vec<Node>, Vec<Node>)> = Vec::new();
                for rule in rules.decided() {
                    let written = (
                        rule.left().iter().map(node).collect::<Option<Vec<Node>>>(),
                        rule.right().iter().map(node).collect::<Option<Vec<Node>>>(),
                    );
                    match (rule.reading(), written) {
                        (
                            TheoryRuleReading::FirstOrder | TheoryRuleReading::Symmetry,
                            (Some(left), Some(right)),
                        ) => sides.push((left, right)),
                        (
                            TheoryRuleReading::SecondOrder
                            | TheoryRuleReading::FirstOrder
                            | TheoryRuleReading::Symmetry,
                            _,
                        ) => {
                            unread = unread.saturating_add(1);
                        },
                    }
                }
                found.push(read(name, &sides, arity, unread));
            },
            DeclarationContent::Data { .. }
            | DeclarationContent::Axiom { .. }
            | DeclarationContent::LiteralIdentity { .. }
            | DeclarationContent::AbstractType { .. }
            | DeclarationContent::Codata { .. } => {},
        }
    }
    found
}

/// Whether `declared` is the presentation code: an unapplied data type whose
/// declaration among `declarations` has the code's constructor table, as the
/// kernel recognises it.
///
/// # Specification
/// - requires: `declarations` are admitted in order over `arena`.
/// - ensures: positive exactly when `declared` is that type.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — as the sweep.
/// - witness: `kernel_export::convergence::sweeps::each_admitted_block_with_rules_joins_its_critical_pairs`
fn presents(
    arena: &TermArena,
    declarations: &[MarkedDeclaration],
    declared: ValueTypeId,
) -> bool
{
    let Some(&ValueType::Data {
        declaration,
        ref arguments,
    }) = arena.value_type(declared)
    else {
        return false;
    };
    let Some(&DeclarationContent::Data {
        ref parameters,
        ref indices,
        ref constructors,
        ..
    }) = declarations
        .get(usize::from(declaration))
        .map(|entry| entry.declaration().content())
    else {
        return false;
    };
    arguments.is_empty()
        && parameters.is_empty()
        && indices.is_empty()
        && bool::from(presentation_code(arena, declaration, constructors))
}

/// The system of the rules `sides` over the arities `arity` gives, named
/// `name`, each symmetry read as the commutativity of its symbol; beside it
/// the fault when a side is no one term.
///
/// # Specification
/// - requires: nothing.
/// - ensures: a rule whose left side is one symbol over the variables `0` and
///   `1` and whose right side is that symbol over `1` and `0` is a symmetry of
///   the symbol; each other rule rewrites.
/// - panics: none.
///
/// # Cost
/// - allocation: the system's terms, growth within the sides
///
/// # Adequacy
/// - hypothesis: L3 — as the sweep.
/// - witness: `kernel_export::convergence::sweeps::each_admitted_block_with_rules_joins_its_critical_pairs`
fn read<A>(
    name: String,
    sides: &[(Vec<Node>, Vec<Node>)],
    arity: A,
    unread: usize,
) -> (System, Option<String>)
where
    A: Fn(usize) -> Option<usize> + Copy,
{
    let mut system = System {
        name,
        symmetric: BTreeSet::new(),
        rules: Vec::new(),
        unread,
    };
    let mut fault = None;
    for (index, &(ref left, ref right)) in sides.iter().enumerate() {
        let (Some(left), Some(right)) = (tree(left, arity), tree(right, arity))
        else {
            fault = Some(format!("rule {index} is no one term"));
            continue;
        };
        match (&left, &right) {
            (&Term::Apply(symbol, ref lefts), &Term::Apply(other, ref rights))
                if symbol == other
                    && *lefts == [Term::Variable(0), Term::Variable(1)]
                    && *rights == [Term::Variable(1), Term::Variable(0)] =>
            {
                let _fresh = system.symmetric.insert(symbol);
            },
            _ => system.rules.push((left, right)),
        }
    }
    (system, fault)
}

/// The sweep and its witness.
mod sweeps
{
    use alloc::collections::BTreeMap;
    use alloc::collections::BTreeSet;
    use alloc::format;
    use alloc::string::String;
    use alloc::vec::Vec;
    use std::path::Path;

    use gandr_surface_grammar::built_in;

    use super::admitted;
    use super::sources;
    use super::systems;

    /// The admitted blocks whose rules part, each by its source and its
    /// declaration, beside the unit that removes it.
    ///
    /// - `Flat` holds `pair low mid ==> low` and `pair mid low ==> mid` beside
    ///   the symmetry of `pair`. The check derives a rule that joins `low` and
    ///   `mid`, and the value that crosses does not carry it, because the
    ///   kernel compares two rules of a `theory` block as written. The unit
    ///   `theory-pairs-each-order` makes the kernel form the pair under the
    ///   symmetry, so the kernel refuses `Flat` and its pin leaves; the unit
    ///   `theory-derived-rule-under-symmetry` then admits it with the derived
    ///   rule.
    pub(super) const PARTING: [(&str, &str, &str); 3] = [
        (
            "crates/surface-lowering-base/tests/coincide/fixtures/two-turned-rules-that-tear-under-a-symmetry-theory-between.gandr",
            "Flat",
            "theory-pairs-each-order",
        ),
        (
            "crates/surface-lowering-base/tests/coincide/fixtures/two-turned-rules-that-tear-under-a-symmetry-theory-first.gandr",
            "Flat",
            "theory-pairs-each-order",
        ),
        (
            "crates/surface-lowering-base/tests/coincide/fixtures/two-turned-rules-that-tear-under-a-symmetry-theory-last.gandr",
            "Flat",
            "theory-pairs-each-order",
        ),
    ];

    #[test]
    fn each_admitted_block_with_rules_joins_its_critical_pairs()
    {
        let pbg = built_in().expect("the built-in grammar builds");
        let repository = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
        let mut texts = Vec::new();
        for root in ["corpus", "library", "crates"] {
            texts.extend(sources(&repository.join(root)));
        }
        let mut verdicts: BTreeMap<String, Vec<String>> = BTreeMap::new();
        let mut parting: BTreeMap<(String, String), Vec<String>> = BTreeMap::new();
        let (mut symmetric, mut unread) = (0_usize, 0_usize);
        for &(ref path, ref text) in &texts {
            let Some((arena, declarations)) = admitted(&pbg, path, text)
            else {
                continue;
            };
            let shown = path
                .strip_prefix(&repository)
                .unwrap_or(path)
                .to_string_lossy()
                .into_owned();
            for (system, fault) in systems(&arena, &declarations) {
                let key = format!("{} {:?} {:?}", system.name, system.symmetric, system.rules);
                let parted = verdicts.entry(key).or_insert_with(|| {
                    symmetric = symmetric.saturating_add(usize::from(!system.symmetric.is_empty()));
                    unread = unread.saturating_add(system.unread);
                    fault.into_iter().chain(system.parted()).collect()
                });
                if !parted.is_empty() {
                    parting
                        .entry((shown.clone(), system.name.clone()))
                        .or_default()
                        .extend(parted.iter().cloned());
                }
            }
        }
        let blocks = verdicts.len();
        assert!(
            blocks > 0 && symmetric > 0,
            "the repository admits a block with rules and one with a symmetry"
        );
        let known: BTreeSet<(String, String)> = PARTING
            .iter()
            .map(|&(source, name, _)| (String::from(source), String::from(name)))
            .collect();
        let new: Vec<String> = parting
            .iter()
            .filter(|&(block, _)| !known.contains(block))
            .flat_map(|(&(ref source, ref name), parted)| {
                parted
                    .iter()
                    .map(move |description| format!("{source}: {name}: {description}"))
            })
            .collect();
        let joined: Vec<String> = PARTING
            .iter()
            .filter(|&&(source, name, _)| {
                !parting.contains_key(&(String::from(source), String::from(name)))
            })
            .map(|&(source, name, unit)| format!("{source}: {name}, whose pin {unit} removes"))
            .collect();
        assert!(
            new.is_empty(),
            "admitted blocks with rules that do not join each critical pair, of {blocks} ({symmetric} with a symmetry, {unread} second-order rules unread):\n{}",
            new.join("\n")
        );
        assert!(
            joined.is_empty(),
            "known parting blocks that join or are not admitted now; remove each from `PARTING`:\n{}",
            joined.join("\n")
        );
    }
}
