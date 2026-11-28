//! The census of the refused rules: each block of a source of `corpus/` or
//! of the crates that the check refuses with `RulesUnoriented`,
//! `RulesUncompleted`, `RulesNeverComplete` or `RulesDiverge`, with the rule
//! that stops it and the form of that rule.
//!
//! The sweep reads every `.gandr` source under `corpus/` and the crates that
//! writes a rule (`==>` or `<=>`). It lays out, parses and lowers each one as
//! a driver does, and it reads the coherence fault of each cell diagnostic of
//! the four kinds. The rule that stops the block is:
//!
//! | Refusal | Rule |
//! | ------- | ---- |
//! | `RulesUnoriented` | the written rule at the span of the fault |
//! | `RulesUncompleted`, `RulesDiverge` | the rule between the two normal forms of the pair that parts |
//! | `RulesNeverComplete` | the derived rule that wraps the derived rule before it |
//!
//! A rule has one of four forms ([`Form`]): an identity, a permutation of the
//! arguments of symbols, a two-way rule that keeps the size and the
//! variables of a term, or a different form. A permutation and a rule that
//! keeps the size and the variables have finite classes. So the count of the
//! two forms is the demand for a reader of a two-way rule.
//!
//! The sweep knows each refused rule ([`sweeps::CENSUS`]). It fails for each
//! refused rule that the census does not hold, and for each row of the census
//! that it does not find.
//!
//! # References
//!
//! - `vault:01a2141e-8cac-713f-bed3-e667588da344` — background: confluence by
//!   labels, and rules in strata (§ labels-symmetry) — the two facts of a
//!   two-way rule that a labelling reads.

use alloc::borrow::ToOwned as _;
use alloc::string::String;
use alloc::string::ToString as _;
use alloc::vec::Vec;
use core::fmt;
use std::path::Path;

use gandr_surface_dispatcher::classify;
use gandr_surface_dispatcher::lay_out;
use gandr_surface_grammar::Pbg;
use gandr_surface_lowering::LoweringBudget;
use gandr_surface_lowering::coincide::CoherenceFault;
use gandr_surface_lowering::coincide::Decisions;
use gandr_surface_lowering::coincide::PairTerm;
use gandr_surface_lowering::desc_cells::CellFault;
use gandr_surface_lowering::description::DescribedDeclaration;
use gandr_surface_lowering::description::written::RuleOrientation;
use gandr_surface_lowering::lower_unit;
use gandr_surface_lowering::namespace::Recognition;
use gandr_surface_parser::parse;
use gandr_surface_syntax::ByteSpan;
use gandr_surface_syntax::SourceText;
use gandr_theory_computads::read_command;
use gandr_theory_levitation::FreeTerm;
use gandr_theory_levitation::TermView;
use quenchant_shape::shape::Maybe;

use crate::kernel_export::convergence::sources;

/// The form of a rule that the check refuses.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum Form
{
    /// The two sides are one term: `id(a) ==> id(a)`.
    Identity,
    /// The two sides are one term up to the order of the arguments of a
    /// symbol at some nodes: `plus(Zero, n) <=> plus(n, Zero)`.
    Permutation,
    /// Two sides with one count of nodes and one multiset of variables, and
    /// no permutation: `f(g(x), y) <=> f(g(y), x)`.
    KeepsSizeAndVariables,
    /// Each other rule.
    Different,
    /// A side that reads as no term: a terminal of the sequent reading, or
    /// split results.
    Unread,
}

impl fmt::Display for Form
{
    /// Writes the name of the form as the census spells it.
    ///
    /// # Specification
    /// trivial.
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        f.write_str(match *self {
            Self::Identity => "Identity",
            Self::Permutation => "Permutation",
            Self::KeepsSizeAndVariables => "KeepsSizeAndVariables",
            Self::Different => "Different",
            Self::Unread => "Unread",
        })
    }
}

/// One refused rule: the declaration that holds it, the refusal, the rule in
/// the inspection notation and its form.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct Refused
{
    /// The name of the refused declaration.
    declaration: String,
    /// The name of the refusal.
    refusal: &'static str,
    /// The two sides with the arrow between them.
    rule: String,
    /// The form of the rule.
    form: Form,
}

/// The count of the nodes of `term`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: one for each head of `term`: each variable, symbol, atom, binder
///   and instance.
/// - panics: none.
///
/// # Cost
/// - allocation: the walk's stack, growth within the term
///
/// # Adequacy
/// - hypothesis: L3 — a rule that keeps the size of a term and one that grows
///   it are in the census apart.
/// - witness: `rule_census::sweeps::each_refused_rule_has_its_row_in_the_census`
fn size(term: &FreeTerm) -> usize
{
    let mut pending = Vec::from([term.to_node()]);
    let mut count = 0_usize;
    while let Some(node) = pending.pop() {
        count = count.saturating_add(1);
        match node.view() {
            TermView::Ctor { args, .. }
            | TermView::Op { args, .. }
            | TermView::Results { args }
            | TermView::Inst { args, .. }
            | TermView::Abs { args, .. }
            | TermView::Lam { args, .. } => pending.extend(args),
            TermView::Var(_) | TermView::Atom(_) | TermView::Bound(_) => {},
        }
    }
    count
}

/// The spelling of `term` with the arguments of each constructor and each
/// operation in the order of their spellings, from the leaves up: one
/// spelling for each class of the permutations of arguments.
///
/// # Specification
/// - requires: nothing.
/// - ensures: two terms that differ only by the order of the arguments of a
///   constructor or an operation at some nodes give one spelling, and two that
///   differ in a different way give two.
/// - panics: none.
///
/// # Cost
/// - allocation: the walk's two stacks and one spelling for each node, growth
///   within the term
///
/// # Adequacy
/// - hypothesis: L3 — as [`form`].
/// - witness: `rule_census::sweeps::each_refused_rule_has_its_row_in_the_census`
fn unordered(term: &FreeTerm) -> String
{
    // Each entry is a node and whether its arguments are spelled.
    let mut pending = Vec::from([(term.to_node(), false)]);
    let mut built: Vec<String> = Vec::new();
    while let Some((node, ready)) = pending.pop() {
        let (head, args, sorted) = match node.view() {
            TermView::Var(name) => (alloc::format!("?{}", name.as_ref()), None, false),
            TermView::Atom(name) => (alloc::format!("@{}", name.as_ref()), None, false),
            TermView::Bound(name) => (alloc::format!("^{}", name.as_ref()), None, false),
            TermView::Ctor { name, args } => {
                (alloc::format!("C{}", name.as_ref()), Some(args), true)
            },
            TermView::Op { name, args } => (alloc::format!("O{}", name.as_ref()), Some(args), true),
            TermView::Inst { name, args } => {
                (alloc::format!("I{}", name.as_ref()), Some(args), false)
            },
            TermView::Abs { atom, args } => {
                (alloc::format!("A{}", atom.as_ref()), Some(args), false)
            },
            TermView::Lam { var, args } => (alloc::format!("L{}", var.as_ref()), Some(args), false),
            TermView::Results { args } => (String::from("R"), Some(args), false),
        };
        let Some(args) = args
        else {
            built.push(head);
            continue;
        };
        if ready {
            let start = built.len().saturating_sub(args.len());
            let mut spelled = built.split_off(start);
            if sorted {
                spelled.sort_unstable();
            }
            built.push(alloc::format!("{head}({})", spelled.join(",")));
        }
        else {
            pending.push((node, true));
            let at = pending.len();
            pending.extend(args.map(|child| (child, false)));
            if let Some(children) = pending.get_mut(at ..) {
                children.reverse();
            }
        }
    }
    built.pop().unwrap_or_default()
}

/// The form of the rule between `left` and `right`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: [`Form::Identity`] when the two sides are one term; else
///   [`Form::Permutation`] when they are one term up to the order of the
///   arguments of symbols ([`unordered`]); else [`Form::KeepsSizeAndVariables`]
///   when the two sides have one count of nodes and one multiset of variables;
///   else [`Form::Different`].
/// - panics: none.
///
/// # Cost
/// - allocation: the spellings and the lists of variables of both sides, growth
///   within the sides
///
/// # Adequacy
/// - hypothesis: L3 — the census holds an identity, a permutation at the root
///   and below it, a rule that keeps the size and the variables, and a rule
///   that grows or drops a variable, each with its form.
/// - witness: `rule_census::sweeps::each_refused_rule_has_its_row_in_the_census`
fn form(
    left: &FreeTerm,
    right: &FreeTerm,
) -> Form
{
    let (left_unordered, right_unordered) = (unordered(left), unordered(right));
    if left_unordered == right_unordered {
        return if left.to_string() == right.to_string() {
            Form::Identity
        }
        else {
            Form::Permutation
        };
    }
    let variables = |term: &FreeTerm| {
        let mut names: Vec<String> = term
            .to_node()
            .vars()
            .map(|name| String::from(name.as_ref()))
            .collect();
        names.sort_unstable();
        names
    };
    if size(left) == size(right) && variables(left) == variables(right) {
        Form::KeepsSizeAndVariables
    }
    else {
        Form::Different
    }
}

/// The term that `term` reads as, when it reads as one.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the reading of a command or of a term of the presented reading;
///   none for a terminal or split results.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — as the sweep.
/// - witness: `rule_census::sweeps::each_refused_rule_has_its_row_in_the_census`
fn read(term: &PairTerm) -> Option<FreeTerm>
{
    match *term {
        PairTerm::Command(ref command) => match read_command(command) {
            Maybe::Present(term) => Some(term),
            Maybe::Absent(_) => None,
        },
        PairTerm::Term(ref term) => match term.read() {
            Maybe::Present(term) => Some(term),
            Maybe::Absent(_) => None,
        },
    }
}

/// The rule between the two normal forms `left` and `right` of a pair that
/// parts, with its form.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the two sides beside `<=>` and their [`form`] when both read as
///   terms; else the spelling of the two terms and [`Form::Unread`].
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — as the sweep.
/// - witness: `rule_census::sweeps::each_refused_rule_has_its_row_in_the_census`
fn between(
    left: &PairTerm,
    right: &PairTerm,
) -> (String, Form)
{
    let rule = alloc::format!("{left} <=> {right}");
    match (read(left), read(right)) {
        (Some(left), Some(right)) => (rule, form(&left, &right)),
        (None, _) | (_, None) => (rule, Form::Unread),
    }
}

/// The written rule of `described` at `span`, with its form.
///
/// # Specification
/// - requires: `span` is the span of a coherence fault of `described`.
/// - ensures: the rule whose written sides lie in `span`, its arrow as written,
///   and its [`form`]; `…` and [`Form::Unread`] when no written rule lies
///   there.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — as the sweep.
/// - witness: `rule_census::sweeps::each_refused_rule_has_its_row_in_the_census`
fn written_at(
    described: &DescribedDeclaration,
    span: ByteSpan,
) -> (String, Form)
{
    let inside = |at: ByteSpan| span.start() <= at.start() && at.end() <= span.end();
    described
        .rules()
        .find(|rule| {
            rule.written
                .left
                .nodes
                .first()
                .is_some_and(|node| inside(node.span))
                && rule
                    .written
                    .right
                    .nodes
                    .last()
                    .is_some_and(|node| inside(node.span))
        })
        .map_or_else(
            || (String::from("…"), Form::Unread),
            |rule| {
                let arrow = match rule.written.orientation {
                    RuleOrientation::Unpinned => "<=>",
                    RuleOrientation::Pinned(_) => "==>",
                };
                (
                    alloc::format!("{} {arrow} {}", rule.face.lhs, rule.face.rhs),
                    form(&rule.face.lhs, &rule.face.rhs),
                )
            },
        )
}

/// The rules that the check refuses in the source at `path`, read as `text`;
/// none when the source does not parse or the lowering refuses it whole.
///
/// # Specification
/// - requires: `text` is the source at `path`.
/// - ensures: one entry for each cell diagnostic whose fault is `Unoriented`,
///   `Uncompleted`, `NeverCompletes` or `Diverges`, named by the declaration
///   whose description holds its span.
/// - panics: when no description of the module holds the span of such a
///   diagnostic.
///
/// # Cost
/// - allocation: the pipeline's trees, arena and module, growth within the
///   source
///
/// # Adequacy
/// - hypothesis: L3 — as the sweep.
/// - witness: `rule_census::sweeps::each_refused_rule_has_its_row_in_the_census`
fn refused(
    pbg: &Pbg,
    path: &Path,
    text: &str,
) -> Vec<Refused>
{
    let laid = lay_out(pbg, path, classify(path), SourceText::from(text));
    let laid_text = SourceText::from(laid.text.as_str());
    let Ok(parsed) = parse(pbg, laid_text)
    else {
        return Vec::new();
    };
    let tree = parsed.into_tree();
    let mut arena = gandr_core_term::CoreArena::new();
    let Ok(module) = lower_unit(
        pbg,
        &tree,
        &laid.unit,
        &mut arena,
        LoweringBudget::DEFAULT,
        Recognition::default(),
        &mut Decisions::none(),
    )
    else {
        return Vec::new();
    };
    let mut found = Vec::new();
    for diagnostic in &module.cells().diagnostics {
        let CellFault::Coherence(ref fault) = diagnostic.fault
        else {
            continue;
        };
        let span = diagnostic.span;
        let described = || {
            module
                .described()
                .find(|described| {
                    described.at.span.start() <= span.start()
                        && span.end() <= described.at.span.end()
                })
                .unwrap_or_else(|| {
                    panic!(
                        "{}: a description holds the fault at {span}",
                        path.display()
                    )
                })
        };
        let (refusal, (rule, form)) = match *fault {
            CoherenceFault::Unoriented => ("RulesUnoriented", written_at(described(), span)),
            CoherenceFault::Uncompleted {
                ref left,
                ref right,
                ..
            } => ("RulesUncompleted", between(left, right)),
            CoherenceFault::Diverges {
                ref left,
                ref right,
                ..
            } => ("RulesDiverge", between(left, right)),
            CoherenceFault::NeverCompletes { ref later, .. } => (
                "RulesNeverComplete",
                (
                    alloc::format!("{} ==> {}", later.0, later.1),
                    form(&later.0, &later.1),
                ),
            ),
            CoherenceFault::OverlapsSecondOrder { .. }
            | CoherenceFault::OverlapsCondition { .. }
            | CoherenceFault::Undecided { .. }
            | CoherenceFault::Unfinished { .. } => continue,
        };
        let named = described().named.span;
        let declaration = laid_text
            .fragment(named)
            .map_or_else(|_| named.to_string(), |name| <&str>::from(name).to_owned());
        found.push(Refused {
            declaration,
            refusal,
            rule,
            form,
        });
    }
    found
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
    use gandr_workflow_sweep::Sample;
    use gandr_workflow_sweep::SampleName;
    use gandr_workflow_sweep::SampleSize;
    use gandr_workflow_sweep::Sweep;
    use gandr_workflow_sweep::Text;

    use super::Form;
    use super::Refused;
    use super::refused;
    use super::sources;

    /// The sample of the sources that write a rule: thirty-two, ranked by the
    /// BLAKE3 digest of their text under this name, beside each source of a
    /// row of [`CENSUS`], so each run reads each row. The sample looks for a
    /// refusal that the census does not hold. Each source runs the pipeline,
    /// and the whole set took 4.4 s plain and 16 s enforcing on a hosted
    /// runner. The `sweeps` and `nightly` profiles read each source.
    const UNCENSUSED: Sample = Sample {
        name: SampleName("each_refused_rule_has_its_row_in_the_census"),
        size: SampleSize(32),
    };

    /// Each rule that the check refuses in a source of `corpus/` or of the
    /// crates: the source, the declaration, the refusal, the rule in the
    /// inspection notation, and its form.
    pub(super) const CENSUS: [(&str, &str, &str, &str, Form); 47] = [
        (
            "corpus/ledger/diagnostics/RulesDiverge.gandr",
            "Circle",
            "RulesDiverge",
            "Loop(x') <=> Unloop(x')",
            Form::KeepsSizeAndVariables,
        ),
        (
            "corpus/ledger/diagnostics/RulesNeverComplete.gandr",
            "Extrusion",
            "RulesNeverComplete",
            "nu(par(par(nil, q'), q)) ==> par(par(nil, q'), q)",
            Form::Different,
        ),
        (
            "corpus/ledger/diagnostics/RulesUncompleted.gandr",
            "Leaked",
            "RulesUncompleted",
            "yq <=> zero",
            Form::Different,
        ),
        (
            "corpus/ledger/diagnostics/RulesUnoriented.gandr",
            "Marks",
            "RulesUnoriented",
            "Aye <=> Nay",
            Form::KeepsSizeAndVariables,
        ),
        (
            "corpus/model/desc/lc/syntax.gandr",
            "LC",
            "RulesUnoriented",
            "subTm(subTm(b, pTm), liftTm(s)) <=> subTm(subTm(b, s), pTm)",
            Form::Different,
        ),
        (
            "corpus/pathological/data/rule-equation-unoriented.gandr",
            "Marks",
            "RulesUnoriented",
            "Aye <=> Nay",
            Form::KeepsSizeAndVariables,
        ),
        (
            "corpus/pathological/desc/rule-keeps-count.gandr",
            "Flicker",
            "RulesUnoriented",
            "dim ==> lit",
            Form::KeepsSizeAndVariables,
        ),
        (
            "corpus/pathological/desc/rule-symmetry-apart.gandr",
            "Torn",
            "RulesUncompleted",
            "x <=> x'",
            Form::Different,
        ),
        (
            "corpus/pathological/desc/rules-diverge-below-the-root.gandr",
            "Circle",
            "RulesDiverge",
            "Loop(x') <=> Unloop(x')",
            Form::KeepsSizeAndVariables,
        ),
        (
            "corpus/pathological/desc/rules-diverge.gandr",
            "NatApart",
            "RulesDiverge",
            "Zero <=> Succ(Zero)",
            Form::Different,
        ),
        (
            "corpus/pathological/desc/rules-never-complete.gandr",
            "Extrusion",
            "RulesNeverComplete",
            "nu(par(par(nil, q'), q)) ==> par(par(nil, q'), q)",
            Form::Different,
        ),
        (
            "corpus/pathological/desc/rules-never-complete.gandr",
            "Restriction",
            "RulesNeverComplete",
            "nu(bind a0 . par(par(nil, q'), q)) ==> par(par(nil, q'), q)",
            Form::Different,
        ),
        (
            "corpus/pathological/desc/rules-uncompleted.gandr",
            "NatSwapped",
            "RulesUncompleted",
            "plus(Zero, n') <=> plus(n', Zero)",
            Form::Permutation,
        ),
        (
            "corpus/pathological/desc/rules-unoriented.gandr",
            "NatGrow",
            "RulesUnoriented",
            "grow(n) ==> Succ(grow(n))",
            Form::Different,
        ),
        (
            "corpus/pathological/desc/second-order-rules.gandr",
            "Beta",
            "RulesUnoriented",
            "app(lam(t), u) <=> t(u)",
            Form::Different,
        ),
        (
            "corpus/pathological/effects/state.gandr",
            "StateObserved",
            "RulesUnoriented",
            "put(s, get(bind t . k(t))) <=> put(s, k(s))",
            Form::Different,
        ),
        (
            "corpus/pathological/extension/generated.gandr",
            "Leaked",
            "RulesUncompleted",
            "yq <=> zero",
            Form::Different,
        ),
        (
            "corpus/pathological/extension/zero-fiber.gandr",
            "FreeFiber",
            "RulesUncompleted",
            "zero <=> x",
            Form::Different,
        ),
        (
            "corpus/pathological/include/imported-rules.gandr",
            "Swapping",
            "RulesUncompleted",
            "mul(pair(x', y'), z) <=> mul(pair(y', x'), z)",
            Form::Permutation,
        ),
        (
            "corpus/pathological/include/rules-join.gandr",
            "Swapped",
            "RulesUncompleted",
            "plus(one, y') <=> plus(y', one)",
            Form::Permutation,
        ),
        (
            "crates/surface-diagnostics/tests/diagnostics/unformatted/a-definition-over-a-refused-indexed-family-is-refused-by-name-8345.gandr",
            "T",
            "RulesUnoriented",
            "Not(High) <=> Low",
            Form::Different,
        ),
        (
            "crates/surface-dispatcher/src/typed/fixtures/a-theory-member-answers-under-the-sorts-before-it.gandr",
            "Cat",
            "RulesUnoriented",
            "id(a) ==> id(a)",
            Form::Identity,
        ),
        (
            "crates/surface-dispatcher/tests/entry/fixtures/a-declaration-over-a-refused-datatype-is-a-note-8342.gandr",
            "Bit",
            "RulesUnoriented",
            "Not(High) <=> Low",
            Form::Different,
        ),
        (
            "crates/surface-dispatcher/tests/entry/fixtures/a-rules-refusal-reads-its-parting-pair-and-no-other-refusal-does.gandr",
            "NatApart",
            "RulesDiverge",
            "Zero <=> Succ(Zero)",
            Form::Different,
        ),
        (
            "crates/surface-format/tests/unformatted/members.gandr",
            "Nat",
            "RulesUnoriented",
            "Succ(Zero) <=> Succ(Zero)",
            Form::Identity,
        ),
        (
            "crates/surface-lowering-base/src/coincide/kept/tests/unformatted/apart.gandr",
            "NatApart",
            "RulesDiverge",
            "Zero <=> Succ(Zero)",
            Form::Different,
        ),
        (
            "crates/surface-lowering-base/src/model/tests/fixtures/a-result-sort-indexed-by-an-operation-instantiates-at-each-use-model.gandr",
            "Stepped",
            "RulesUnoriented",
            "step(a) ==> step(a)",
            Form::Identity,
        ),
        (
            "crates/surface-lowering-base/tests/coincide/fixtures/a-data-blocks-derived-rule-is-a-pattern-rule-repeated.gandr",
            "NatTwice",
            "RulesUncompleted",
            "n' <=> add(n', n')",
            Form::Different,
        ),
        (
            "crates/surface-lowering-base/tests/coincide/fixtures/a-pair-above-a-redex-of-a-symmetry-is-decided-data-first.gandr",
            "Nest",
            "RulesUncompleted",
            "y <=> Two(Z, y)",
            Form::Different,
        ),
        (
            "crates/surface-lowering-base/tests/coincide/fixtures/a-pair-above-a-redex-of-a-symmetry-is-decided-data-last.gandr",
            "Nest",
            "RulesUncompleted",
            "y <=> Two(Z, y)",
            Form::Different,
        ),
        (
            "crates/surface-lowering-base/tests/coincide/fixtures/a-pair-above-a-redex-of-a-symmetry-is-decided-theory-first.gandr",
            "Nest",
            "RulesUncompleted",
            "x' <=> x",
            Form::Different,
        ),
        (
            "crates/surface-lowering-base/tests/coincide/fixtures/a-pair-above-a-redex-of-a-symmetry-is-decided-theory-last.gandr",
            "Nest",
            "RulesUncompleted",
            "x' <=> x",
            Form::Different,
        ),
        (
            "crates/surface-lowering-base/tests/coincide/fixtures/a-permuted-call-no-order-orients-is-uncompleted.gandr",
            "Nat",
            "RulesUncompleted",
            "plus(Zero, n') <=> plus(n', Zero)",
            Form::Permutation,
        ),
        (
            "crates/surface-lowering-base/tests/coincide/fixtures/a-pinned-rule-orients-only-the-way-it-is-pinned-commuting.gandr",
            "Pair",
            "RulesUnoriented",
            "turn(a, b, c) <=> turn(b, c, a)",
            Form::Permutation,
        ),
        (
            "crates/surface-lowering-base/tests/coincide/fixtures/a-rule-that-rebuilds-its-own-call-refuses-the-block.gandr",
            "NatGrow",
            "RulesUnoriented",
            "grow(n) ==> Succ(grow(n))",
            Form::Different,
        ),
        (
            "crates/surface-lowering-base/tests/coincide/fixtures/a-rule-that-tears-under-the-symmetry-of-a-constructor-is-uncompleted-written-first.gandr",
            "Flat",
            "RulesUncompleted",
            "y' <=> x'",
            Form::Different,
        ),
        (
            "crates/surface-lowering-base/tests/coincide/fixtures/a-rule-that-tears-under-the-symmetry-of-a-constructor-is-uncompleted-written-last.gandr",
            "Flat",
            "RulesUncompleted",
            "x' <=> y'",
            Form::Different,
        ),
        (
            "crates/surface-lowering-base/tests/coincide/fixtures/scope-extrusion.gandr",
            "S",
            "RulesNeverComplete",
            "nu(par(par(nil, q'), q)) ==> par(par(nil, q'), q)",
            Form::Different,
        ),
        (
            "crates/surface-lowering-base/tests/coincide/fixtures/two-rules-written-the-other-way-round-are-refused-at-the-later-one-all-the-same.gandr",
            "NatApart",
            "RulesDiverge",
            "Succ(Zero) <=> Zero",
            Form::Different,
        ),
        (
            "crates/surface-lowering-base/tests/coincide/fixtures/two-turned-rules-that-tear-under-a-symmetry-data-between.gandr",
            "Flat",
            "RulesDiverge",
            "Low <=> Mid",
            Form::KeepsSizeAndVariables,
        ),
        (
            "crates/surface-lowering-base/tests/coincide/fixtures/two-turned-rules-that-tear-under-a-symmetry-data-first.gandr",
            "Flat",
            "RulesDiverge",
            "Mid <=> Low",
            Form::KeepsSizeAndVariables,
        ),
        (
            "crates/surface-lowering-base/tests/coincide/fixtures/two-turned-rules-that-tear-under-a-symmetry-data-last.gandr",
            "Flat",
            "RulesDiverge",
            "Low <=> Mid",
            Form::KeepsSizeAndVariables,
        ),
        (
            "crates/surface-lowering-base/tests/coincide/unformatted/a-third-cancellation-parts-the-circles-readings.gandr",
            "Circle",
            "RulesDiverge",
            "Loop(x') <=> Unloop(x')",
            Form::KeepsSizeAndVariables,
        ),
        (
            "crates/surface-lowering/tests/coincide/unformatted/a-definition-over-a-refused-indexed-family-is-refused-by-name-8345.gandr",
            "T",
            "RulesUnoriented",
            "Not(High) <=> Low",
            Form::Different,
        ),
        (
            "crates/surface-lowering/tests/coincide/unformatted/two-rules-rewriting-one-term-apart-refuse-the-block.gandr",
            "NatApart",
            "RulesDiverge",
            "Zero <=> Succ(Zero)",
            Form::Different,
        ),
        (
            "crates/surface-parser/tests/acceptance/unformatted/a-reserved-word-where-a-name-stands-6266-rule.gandr",
            "T",
            "RulesUnoriented",
            "nil <=> nil",
            Form::Identity,
        ),
        (
            "crates/surface-render-terminal/tests/render/fixtures/refused-datatype-8342.gandr",
            "Bit",
            "RulesUnoriented",
            "Not(High) <=> Low",
            Form::Different,
        ),
    ];

    #[test]
    fn each_refused_rule_has_its_row_in_the_census()
    {
        let pbg = built_in().expect("the built-in grammar builds");
        let repository = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
        let shown = |path: &Path| {
            path.strip_prefix(&repository)
                .unwrap_or(path)
                .to_string_lossy()
                .into_owned()
        };
        let mut texts = Vec::new();
        for root in ["corpus", "crates"] {
            texts.extend(sources(&repository.join(root)));
        }
        let rows: Vec<Text<'_>> = texts.iter().map(|&(_, ref text)| Text(text)).collect();
        let mut visited: BTreeSet<usize> = Sweep::asked()
            .expect("the run's sweep resolves")
            .visit_rows(UNCENSUSED, &rows)
            .into_iter()
            .map(|row| row.0)
            .collect();
        let censused: BTreeSet<&str> = CENSUS.iter().map(|&(source, ..)| source).collect();
        visited.extend(
            texts
                .iter()
                .enumerate()
                .filter(|&(_, &(ref path, _))| censused.contains(shown(path).as_str()))
                .map(|(at, _)| at),
        );
        let mut found: BTreeSet<(String, Refused)> = BTreeSet::new();
        let mut read = 0_usize;
        for &(ref path, ref text) in visited.iter().filter_map(|&at| texts.get(at)) {
            read = read.saturating_add(1);
            for row in refused(&pbg, path, text) {
                let _fresh = found.insert((shown(path), row));
            }
        }
        let known: BTreeSet<(String, Refused)> = CENSUS
            .iter()
            .map(|&(source, declaration, refusal, rule, form)| {
                (String::from(source), Refused {
                    declaration: String::from(declaration),
                    refusal,
                    rule: String::from(rule),
                    form,
                })
            })
            .collect();
        let row = |&(ref source, ref refused): &(String, Refused)| {
            format!(
                "(\"{source}\", \"{}\", \"{}\", \"{}\", Form::{}),",
                refused.declaration, refused.refusal, refused.rule, refused.form
            )
        };
        let new: Vec<String> = found.difference(&known).map(row).collect();
        let gone: Vec<String> = known.difference(&found).map(row).collect();
        let mut counts: BTreeMap<(&str, Form), usize> = BTreeMap::new();
        for &(_, ref refused) in &found {
            let count = counts.entry((refused.refusal, refused.form)).or_default();
            *count = count.saturating_add(1);
        }
        assert!(
            new.is_empty() && gone.is_empty(),
            "the census of the {read} sources that write a rule differs.\nrules the census does not hold:\n{}\nrows the sweep does not find:\n{}\ncounts: {counts:?}",
            new.join("\n"),
            gone.join("\n")
        );
    }
}
