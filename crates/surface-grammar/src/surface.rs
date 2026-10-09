//! The built-in surface: the named precedence table, the term, type-and-shell
//! and circuit rule assemblies, and the named-kind lists.

use alloc::vec::Vec;

use gandr_theory_graphs::Assoc;
use gandr_theory_graphs::Prec;
use gandr_theory_graphs::PrecCycle;
use gandr_theory_graphs::PrecDag;
use gandr_theory_graphs::PrecDagError;
use gandr_theory_graphs::PrecSpec;

use crate::model::Pbg;
use crate::model::PbgError;
use crate::model::PrecName;
use crate::model::PrecTable;

mod circuit;
mod term;
mod type_shell;

/// The named precedence groups, in dense id order.
const PREC_GROUPS: &[(&str, Assoc)] = &[
    ("item.singleton", Assoc::Non),
    ("expression.atom", Assoc::Non),
    ("expression.postfix", Assoc::Left),
    ("expression.unary", Assoc::Non),
    ("expression.mul", Assoc::Left),
    ("expression.add", Assoc::Left),
    ("expression.cmp", Assoc::Left),
    ("expression.and", Assoc::Left),
    ("expression.or", Assoc::Left),
    ("expression.ret", Assoc::Right),
    ("pattern.atom", Assoc::Non),
    ("pattern.as", Assoc::Left),
    ("pattern.or", Assoc::Left),
    ("type.atom", Assoc::Non),
    ("type.application", Assoc::Non),
    ("type.product", Assoc::Right),
    ("type.sum", Assoc::Right),
    ("type.union", Assoc::Right),
    ("type.intersection", Assoc::Right),
    ("type.lazy_product", Assoc::Right),
    ("type.arrow", Assoc::Right),
];

/// The tighter-than edges between named groups.
const PREC_EDGES: &[(&str, &str)] = &[
    ("expression.atom", "expression.postfix"),
    ("expression.postfix", "expression.unary"),
    ("expression.unary", "expression.mul"),
    ("expression.mul", "expression.add"),
    ("expression.add", "expression.cmp"),
    ("expression.cmp", "expression.and"),
    ("expression.and", "expression.or"),
    ("expression.or", "expression.ret"),
    ("pattern.atom", "pattern.as"),
    ("pattern.as", "pattern.or"),
    ("type.atom", "type.application"),
    ("type.application", "type.product"),
    ("type.product", "type.sum"),
    ("type.sum", "type.union"),
    ("type.sum", "type.intersection"),
    ("type.sum", "type.lazy_product"),
    ("type.union", "type.arrow"),
    ("type.intersection", "type.arrow"),
    ("type.lazy_product", "type.arrow"),
];

/// The named node kinds of the surface's tree-sitter grammar, ascending.
pub const TREE_SITTER_NAMED_KINDS: &[&str] = &[
    "acquire_statement",
    "and_expression",
    "annotation_expression",
    "argument",
    "arguments",
    "arm",
    "as_pattern",
    "at_type",
    "attribute",
    "attribute_block",
    "binary_expression",
    "bind_statement",
    "block",
    "block_comment",
    "boolean",
    "call_expression",
    "case_expression",
    "character",
    "close_expression",
    "co_expression",
    "co_field",
    "command",
    "command_name",
    "command_substitution",
    "constructor",
    "constructor_pattern",
    "def_function",
    "def_signature",
    "def_value",
    "double_quoted_string",
    "drop_expression",
    "dup_expression",
    "end_session_type",
    "environment_assignment",
    "escape_sequence",
    "expression_statement",
    "extern_block",
    "extern_function",
    "extern_type",
    "f_type",
    "file_descriptor",
    "forall_type",
    "force_expression",
    "fork_shared_statement",
    "fork_statement",
    "function_type",
    "grade",
    "hold_expression",
    "hole",
    "hole_name",
    "host_escape",
    "identifier",
    "if_expression",
    "instantiation_expression",
    "intersection_type",
    "lambda_expression",
    "lazy_product_type",
    "let_statement",
    "leta_statement",
    "line_comment",
    "list_expression",
    "list_operator",
    "list_pattern",
    "literal_pattern",
    "migrate_expression",
    "module_declaration",
    "mu_session_type",
    "negation",
    "number",
    "offer_expression",
    "offer_session_type",
    "or_expression",
    "or_pattern",
    "parameter",
    "parameters",
    "parenthesized_expression",
    "parenthesized_type",
    "pipeline",
    "primitive_type",
    "product_type",
    "projection_expression",
    "receive_session_type",
    "record_expression",
    "record_field",
    "record_pattern",
    "record_pattern_field",
    "record_type",
    "record_type_field",
    "record_update_expression",
    "recv_statement",
    "redirection",
    "redirection_operator",
    "release_statement",
    "rest_pattern",
    "ret_expression",
    "select_expression",
    "select_session_type",
    "send_expression",
    "send_session_type",
    "session_field",
    "shebang",
    "shell_block",
    "shell_list",
    "shell_word",
    "single_quoted_string",
    "source_file",
    "string",
    "subshell",
    "sum_type",
    "thunk_expression",
    "tuple_expression",
    "tuple_pattern",
    "type_abstraction",
    "type_application",
    "type_identifier",
    "type_variable",
    "typed_number",
    "u_type",
    "unary_expression",
    "union_type",
    "unit",
    "variable_expansion",
    "variable_name",
    "wildcard",
];

/// The named kinds only this grammar has: declaration, control and datatype
/// forms the tree-sitter grammar does not produce, and the reserved or folded
/// member forms inside them.
///
/// A rule may carry one as its provenance, and an
/// [`Adaptation`](crate::Adaptation) one as its surface form, without it being
/// a tree-sitter kind; [`named_kind_parity`](crate::named_kind_parity) never
/// enumerates them. Disjoint from [`TREE_SITTER_NAMED_KINDS`].
///
/// Two groups: the constructs' own rule provenances, then the member forms
/// recorded as adaptation surfaces.
pub const PBG_ONLY_KINDS: &[&str] = &[
    // construct kinds (new rule provenances)
    "break_expression",
    "codata_declaration",
    "continue_expression",
    "data_declaration",
    "for_expression",
    "glob_expression",
    "import_declaration",
    "circuit_declaration",
    "loop_expression",
    "operator_declaration",
    "pack_expression",
    "package_type",
    "path_type",
    "unpack_statement",
    "rec_block",
    "sign_declaration",
    "unknown_type",
    "while_expression",
    // reserved / folded / diverged member surfaces (adaptation surfaces)
    "bare_type_params",
    "braced_variable_expansion",
    "case_answer_type",
    "case_with_view",
    "circuit_body",
    "circuit_member",
    "circuit_signature",
    "codata_observation",
    "constructor_block_member",
    "data_generator",
    "def_rec",
    "feed_statement",
    "grade_prefix",
    "if_answer_type",
    "node_statement",
    "op_member",
    "parameterized_observation",
    "rule_member",
    "string_interpolation",
];

/// Builds the built-in surface grammar.
///
/// # Specification
/// - requires: nothing.
/// - ensures: a checked grammar over [`built_in_prec_table`]'s DAG, whose item,
///   expression, pattern and type bands are mutually incomparable and chained
///   only as [`PREC_EDGES`] declares; its forms range over tiles and holes, and
///   named kinds appear only as rule provenance.
/// - fails: a precedence or gate violation in the constant rules.
/// - panics: none.
/// - intension: the term rules, then the type-and-shell rules, then the circuit
///   rules, so mold ids follow that order.
///
/// # Errors
/// Any [`PbgError`] [`built_in_prec_table`] or [`Pbg::build`] reports.
///
/// # Adequacy
/// - hypothesis: L3 pointwise plus an external pin — the fingerprint and the
///   mold count are pinned, every precedence band is exact, every named kind is
///   realised, and the build stays under its wall-clock budget.
/// - witness: `tests::walk::pbg_fingerprint_is_stable_and_folds_precdag`
/// - witness: `tests::surface::built_in_precedence_bands_are_exact`
/// - witness: `tests::surface::named_kind_coverage_is_semantic`
/// - witness: `tests::closing_class::built_in_builds_fast_enough_for_process_per_test_suites`
#[inline]
pub fn built_in() -> Result<Pbg, PbgError>
{
    let precs = built_in_prec_table()?;
    let mut rules = term::rules(&precs)?;
    let type_shell_rules = type_shell::rules(&precs)?;
    rules.extend(type_shell_rules);
    let circuit_rules = circuit::rules(&precs)?;
    rules.extend(circuit_rules);
    Pbg::build_table(precs, rules)
}

/// Builds the built-in precedence table.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the groups of [`PREC_GROUPS`], ids in that order, with the edges
///   of [`PREC_EDGES`]; the DAG [`built_in`] builds over.
/// - fails: a malformed or cyclic constant.
/// - panics: none.
///
/// # Errors
/// [`PbgError::PrecedenceSpec`], [`PbgError::MissingPrec`],
/// [`PbgError::PrecedenceCycle`] or [`PbgError::PrecedenceDag`].
///
/// # Adequacy
/// - hypothesis: L3 pointwise — every declared chain, associativity and
///   incomparability is checked against the DAG.
/// - witness: `tests::surface::built_in_precedence_bands_are_exact`
#[inline]
pub fn built_in_prec_table() -> Result<PrecTable, PbgError>
{
    let mut spec = PrecSpec::new();
    for &(name, assoc) in PREC_GROUPS {
        spec.insert(name, assoc).map_err(PbgError::from)?;
    }
    for &(tighter, looser) in PREC_EDGES {
        let tighter_prec = lookup_prec(&spec, PrecName(tighter))?;
        let looser_prec = lookup_prec(&spec, PrecName(looser))?;
        spec.add_edge(tighter_prec, looser_prec)
            .map_err(PbgError::from)?;
    }
    let names = prec_table_names(&spec)?;
    let dag = PrecDag::build(&spec).map_err(|error| dag_error(&spec, error))?;
    Ok(PrecTable::new(dag, names))
}

/// Looks up a group of `spec` by name.
///
/// # Specification
/// - requires: nothing.
/// - ensures: returns the group named `name`.
/// - fails: a name `spec` does not hold.
/// - panics: none.
///
/// # Errors
/// [`PbgError::MissingPrec`] naming the absent group.
///
/// # Adequacy
/// - hypothesis: L3 pointwise — an absent name is refused naming it.
/// - witness: `surface::tests::precedence_helper_failures_preserve_named_context`
fn lookup_prec(
    spec: &PrecSpec,
    name: PrecName,
) -> Result<Prec, PbgError>
{
    spec.groups()
        .find_map(|(prec, candidate, _assoc)| (candidate == name.0).then_some(prec))
        .ok_or(PbgError::MissingPrec { name: name.0 })
}

/// Every constant group name with its id in `spec`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: one pair per [`PREC_GROUPS`] entry, in order.
/// - fails: a constant name `spec` does not hold.
/// - panics: none.
///
/// # Errors
/// [`PbgError::MissingPrec`].
fn prec_table_names(spec: &PrecSpec) -> Result<Vec<(PrecName, Prec)>, PbgError>
{
    PREC_GROUPS
        .iter()
        .map(|&(name, _assoc)| lookup_prec(spec, PrecName(name)).map(|prec| (PrecName(name), prec)))
        .collect()
}

/// Lifts a DAG refusal into the grammar's error domain, naming a cycle's
/// groups.
///
/// # Specification
/// - requires: nothing.
/// - ensures: a cycle becomes [`PbgError::PrecedenceCycle`] with each group's
///   constant name, in walk order; any other refusal is wrapped as
///   [`PbgError::PrecedenceDag`].
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 pointwise — a cycle through a group outside the constants
///   and one through an id outside the spec are both named.
/// - witness: `surface::tests::precedence_helper_failures_preserve_named_context`
fn dag_error(
    spec: &PrecSpec,
    error: PrecDagError,
) -> PbgError
{
    match error {
        | PrecDagError::Cycle(PrecCycle { witness }) => PbgError::PrecedenceCycle {
            witness: witness
                .into_iter()
                .map(|prec| static_prec_name(spec, prec).0)
                .collect(),
        },
        | PrecDagError::Graph(_) | PrecDagError::Inconsistent => PbgError::PrecedenceDag(error),
    }
}

/// The constant name of a group of `spec`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: a group whose name is a constant returns that constant; a group
///   with any other name returns `<unknown-precedence>`; an id `spec` does not
///   hold returns `<invalid-precedence>`.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 pointwise — one id of each kind.
/// - witness: `surface::tests::precedence_helper_failures_preserve_named_context`
fn static_prec_name(
    spec: &PrecSpec,
    prec: Prec,
) -> PrecName
{
    let Some(name) = spec.name(prec)
    else {
        return PrecName("<invalid-precedence>");
    };
    PREC_GROUPS
        .iter()
        .find(|&&(candidate, _assoc)| name == candidate)
        .map_or(PrecName("<unknown-precedence>"), |&(candidate, _assoc)| {
            PrecName(candidate)
        })
}

#[cfg(test)]
mod tests
{
    use alloc::collections::BTreeSet;
    use alloc::vec;
    use alloc::vec::Vec;

    use gandr_theory_graphs::PrecIndex;

    use super::*;

    #[test]
    fn precedence_helper_failures_preserve_named_context()
    {
        let mut spec = PrecSpec::new();
        let custom = spec
            .insert("custom", Assoc::Non)
            .expect("one custom precedence should insert");
        let invalid = Prec::new(PrecIndex::from(7));

        assert!(matches!(
            lookup_prec(&spec, PrecName("missing")),
            Err(PbgError::MissingPrec { name: "missing" })
        ));
        assert_eq!(
            PrecName("<unknown-precedence>"),
            static_prec_name(&spec, custom)
        );
        assert_eq!(
            PrecName("<invalid-precedence>"),
            static_prec_name(&spec, invalid)
        );
        assert_eq!(
            PbgError::PrecedenceCycle {
                witness: vec!["<unknown-precedence>", "<invalid-precedence>"],
            },
            dag_error(
                &spec,
                PrecDagError::Cycle(PrecCycle {
                    witness: vec![custom, invalid],
                })
            )
        );
        assert_eq!(
            PbgError::PrecedenceDag(PrecDagError::Inconsistent),
            dag_error(&spec, PrecDagError::Inconsistent)
        );
    }

    #[test]
    fn cyclic_named_precedence_spec_reports_closed_named_witness()
    {
        // Three groups spelled with constant names, each tighter than the
        // next and the last tighter than the first: the DAG refuses the spec,
        // and the grammar names the cycle group by group, closed, along edges
        // the spec actually declares.
        let names = ["expression.atom", "expression.postfix", "expression.unary"];
        let mut spec = PrecSpec::new();
        let a = spec
            .insert(names[0], Assoc::Non)
            .expect("first group inserts");
        let b = spec
            .insert(names[1], Assoc::Left)
            .expect("second group inserts");
        let c = spec
            .insert(names[2], Assoc::Right)
            .expect("third group inserts");
        spec.add_edge(a, b).expect("edge a b");
        spec.add_edge(b, c).expect("edge b c");
        spec.add_edge(c, a).expect("edge c a");

        let refusal = PrecDag::build(&spec).expect_err("a cyclic spec is refused");
        let PbgError::PrecedenceCycle { witness } = dag_error(&spec, refusal)
        else {
            panic!("a cycle is named as a precedence cycle");
        };
        assert!(witness.len() >= 2, "the witness is a walk, not a point");
        assert_eq!(witness.first(), witness.last(), "the witness is closed");
        assert!(
            witness.iter().all(|name| names.contains(name)),
            "every witness group is named by its constant: {witness:?}"
        );
        let declared: BTreeSet<(&str, &str)> = spec
            .edges()
            .filter_map(|(from, to)| Some((spec.name(from)?.into(), spec.name(to)?.into())))
            .collect();
        let walked: Vec<(&str, &str)> = witness
            .windows(2)
            .filter_map(|pair| match *pair {
                | [from, to] => Some((from, to)),
                | _ => None,
            })
            .collect();
        assert!(
            walked.iter().all(|edge| declared.contains(edge)),
            "every step of the witness is a declared edge: {walked:?}"
        );
    }
}
