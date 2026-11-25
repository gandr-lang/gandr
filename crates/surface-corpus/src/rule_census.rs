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
//! A rule has one of three forms ([`Form`]): a permutation of the arguments
//! of one symbol, a two-way rule that keeps the size and the variables of a
//! term, or a different form. A permutation and a rule that keeps the size
//! and the variables have finite classes. So the count of the two forms is
//! the demand for a reader of a two-way rule.
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
use std::fs;
use std::path::Path;
use std::path::PathBuf;

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

/// The form of a rule that the check refuses.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum Form
{
    /// `f x₁ … xₙ <=> f x_σ(1) … x_σ(n)`: one symbol over distinct variables
    /// on each side, in two orders.
    Permutation,
    /// Two sides with one count of nodes and one multiset of variables, and
    /// no permutation: `f (g x) y <=> f (g y) x`.
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
/// - ensures: one for each head of `term`: each variable, symbol, atom,
///   binder and instance.
/// - panics: none.
///
/// # Cost
/// - allocation: the walk's stack, growth within the term
///
/// # Adequacy
/// - hypothesis: L3 — a rule that keeps the size of a term and one that
///   grows it are in the census apart.
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

/// The symbol at the root of `term` and the names of its arguments, when
/// each argument is a variable.
///
/// # Specification
/// - requires: nothing.
/// - ensures: `Some` exactly when the root is a constructor or an operation
///   and each argument is a variable: whether it is a constructor, its name,
///   and the names of the variables in written order.
/// - panics: none.
///
/// # Cost
/// - allocation: the list of names, growth within the arguments
///
/// # Adequacy
/// - hypothesis: L3 — as [`form`].
/// - witness: `rule_census::sweeps::each_refused_rule_has_its_row_in_the_census`
fn over_variables(term: &FreeTerm) -> Option<(bool, &str, Vec<&str>)>
{
    let (constructor, name, args) = match term.view() {
        TermView::Ctor { name, args } => (true, name, args),
        TermView::Op { name, args } => (false, name, args),
        TermView::Var(_)
        | TermView::Results { .. }
        | TermView::Inst { .. }
        | TermView::Abs { .. }
        | TermView::Atom(_)
        | TermView::Lam { .. }
        | TermView::Bound(_) => return None,
    };
    let variables = args
        .map(|argument| match argument.view() {
            TermView::Var(variable) => Some(variable.as_ref()),
            TermView::Ctor { .. }
            | TermView::Op { .. }
            | TermView::Results { .. }
            | TermView::Inst { .. }
            | TermView::Abs { .. }
            | TermView::Atom(_)
            | TermView::Lam { .. }
            | TermView::Bound(_) => None,
        })
        .collect::<Option<Vec<&str>>>()?;
    Some((constructor, name.as_ref(), variables))
}

/// The form of the rule between `left` and `right`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: [`Form::Permutation`] when the two sides are one symbol over
///   distinct variables, the right side's variables a different order of the
///   left side's; else [`Form::KeepsSizeAndVariables`] when the two sides have
///   one count of nodes and one multiset of variables; else
///   [`Form::Different`].
/// - panics: none.
///
/// # Cost
/// - allocation: the lists of variables of both sides, growth within the
///   sides
///
/// # Adequacy
/// - hypothesis: L3 — the census holds a permutation, a rule that keeps the
///   size and the variables, and a rule that grows or drops a variable, each
///   with its form.
/// - witness: `rule_census::sweeps::each_refused_rule_has_its_row_in_the_census`
fn form(
    left: &FreeTerm,
    right: &FreeTerm,
) -> Form
{
    if let (Some((left_kind, left_name, left_variables)), Some((right_kind, right_name, right_variables))) =
        (over_variables(left), over_variables(right))
    {
        let mut distinct = left_variables.clone();
        distinct.sort_unstable();
        distinct.dedup();
        let mut reordered = right_variables.clone();
        reordered.sort_unstable();
        if left_kind == right_kind
            && left_name == right_name
            && distinct.len() == left_variables.len()
            && distinct == reordered
            && left_variables != right_variables
        {
            return Form::Permutation;
        }
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
/// - ensures: the reading of a command or of a term of the presented
///   reading; none for a terminal or split results.
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
/// - ensures: the rule whose written sides lie in `span`, its arrow as
///   written, and its [`form`]; `…` and [`Form::Unread`] when no written rule
///   lies there.
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
            rule.written.left.nodes.first().is_some_and(|node| inside(node.span))
                && rule.written.right.nodes.last().is_some_and(|node| inside(node.span))
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

/// Every `.gandr` file under `directory` that writes a rule, beside its text.
///
/// # Specification
/// - requires: the directory remains readable during the sweep.
/// - ensures: one entry for each `.gandr` file under `directory`, reached
///   without a symbolic link or a `target` directory, whose text holds `==>`
///   or `<=>`.
/// - panics: when a directory, an entry or a source cannot be read.
///
/// # Cost
/// - allocation: the paths and the texts, growth within the directory
///
/// # Adequacy
/// - hypothesis: L3 — as the sweep.
/// - witness: `rule_census::sweeps::each_refused_rule_has_its_row_in_the_census`
fn sources(directory: &Path) -> Vec<(PathBuf, String)>
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
                let text = fs::read_to_string(&path)
                    .unwrap_or_else(|error| panic!("{}: the source reads: {error}", path.display()));
                if text.contains("==>") || text.contains("<=>") {
                    found.push((path, text));
                }
            }
        }
    }
    found
}

/// The rules that the check refuses in the source at `path`, read as `text`;
/// none when the source does not parse or the lowering refuses it whole.
///
/// # Specification
/// - requires: `text` is the source at `path`.
/// - ensures: one entry for each cell diagnostic whose fault is
///   `Unoriented`, `Uncompleted`, `NeverCompletes` or `Diverges`, named by the
///   declaration whose description holds its span.
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
                    described.at.span.start() <= span.start() && span.end() <= described.at.span.end()
                })
                .unwrap_or_else(|| {
                    panic!("{}: a description holds the fault at {span}", path.display())
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

    use super::Form;
    use super::Refused;
    use super::refused;
    use super::sources;

    /// Each rule that the check refuses in a source of `corpus/` or of the
    /// crates: the source, the declaration, the refusal, the rule in the
    /// inspection notation, and its form.
    pub(super) const CENSUS: [(&str, &str, &str, &str, Form); 0] = [];

    #[test]
    fn each_refused_rule_has_its_row_in_the_census()
    {
        let pbg = built_in().expect("the built-in grammar builds");
        let repository = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
        let mut found: BTreeSet<(String, Refused)> = BTreeSet::new();
        let mut read = 0_usize;
        for root in ["corpus", "crates"] {
            for (path, text) in sources(&repository.join(root)) {
                read = read.saturating_add(1);
                let shown = path
                    .strip_prefix(&repository)
                    .unwrap_or(&path)
                    .to_string_lossy()
                    .into_owned();
                for row in refused(&pbg, &path, &text) {
                    let _fresh = found.insert((shown.clone(), row));
                }
            }
        }
        let known: BTreeSet<(String, Refused)> = CENSUS
            .iter()
            .map(|&(source, declaration, refusal, rule, form)| {
                (
                    String::from(source),
                    Refused {
                        declaration: String::from(declaration),
                        refusal,
                        rule: String::from(rule),
                        form,
                    },
                )
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
