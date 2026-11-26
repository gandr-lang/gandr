//! The language feature that gates each rule of the built-in grammar.
//!
//! A source that writes a form of a rule uses the language feature of that
//! rule. The feature is a row of the features ledger, named by its id. A rule
//! with no feature is in tier zero: the common core that each source can
//! write with no declaration.
//!
//! [`RULE_GATES`] has one line for each rule of the built-in grammar, in the
//! byte order of the rule names. A person writes each line. The name of the
//! rule is the key, so a change of the form of a rule changes no line, and a
//! rule with a name that the table does not hold fails the test of this
//! module until it has its line. The ledger tool holds each id against the
//! rows of the features ledger.

use crate::model::RuleName;

/// Why a rule, an attribute or a builtin row is in tier zero.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum CoreReason
{
    /// A source of the first twin of the tool chain writes the form.
    Twin,
    /// The form is a name, or a pattern that takes a value under a name or
    /// under none. The form that declares the name or holds the pattern is
    /// the gate.
    Name,
    /// The form only groups the forms that it holds, and each of them is its
    /// own gate.
    Group,
    /// The form states a record of its declaration: an expectation, a
    /// document, a spelling, or a request to a lint. The checker judges the
    /// declaration the same with the form and with none.
    Record,
}

/// What a source needs to write a form of a rule.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum RuleGate
{
    /// Nothing: the rule is in tier zero, for this reason.
    Core(CoreReason),
    /// The language feature whose row of the features ledger has this id.
    Feature(&'static str),
}

/// The gate of each rule of the built-in grammar, in the byte order of the
/// rule names.
///
/// # Specification
/// - ensures: the names are distinct and ascending, and they are the names of
///   the rules of the built-in grammar, each one time.
/// - provides: the one place where a rule gets its language feature.
/// - executable: none — the specification attribute does not support constant
///   items; the tests of this module hold the order and the cover.
///
/// # Adequacy
/// - hypothesis: L3 — the table is compared with each rule of the built-in
///   grammar, and each of the twelve forms of the first twin is in the core.
/// - witness: `gate::tests::each_rule_has_one_line_and_each_line_one_rule`
/// - witness: `gate::tests::the_forms_of_the_first_twin_are_in_the_core`
pub const RULE_GATES: [(&str, RuleGate); 164_usize] = [
    ("abort_expression", RuleGate::Feature("temporary-access")),
    ("access_expression", RuleGate::Feature("temporary-access")),
    ("acquire_expression", RuleGate::Feature("shared-endpoints")),
    ("application_expression", RuleGate::Core(CoreReason::Twin)),
    ("as_pattern", RuleGate::Feature("pattern-matching")),
    ("at_type", RuleGate::Feature("located-judgements")),
    ("attribute_block", RuleGate::Core(CoreReason::Twin)),
    ("attributed_module_member", RuleGate::Feature("modules")),
    ("become_expression", RuleGate::Feature("explicit-exits")),
    (
        "binary_expression.add.concat",
        RuleGate::Feature("native-lists"),
    ),
    (
        "binary_expression.add.minus",
        RuleGate::Feature("native-primitives"),
    ),
    (
        "binary_expression.add.plus",
        RuleGate::Feature("native-primitives"),
    ),
    (
        "binary_expression.and",
        RuleGate::Feature("native-primitives"),
    ),
    (
        "binary_expression.cmp.eq",
        RuleGate::Feature("native-primitives"),
    ),
    (
        "binary_expression.cmp.ge",
        RuleGate::Feature("native-primitives"),
    ),
    (
        "binary_expression.cmp.gt",
        RuleGate::Feature("native-primitives"),
    ),
    (
        "binary_expression.cmp.le",
        RuleGate::Feature("native-primitives"),
    ),
    (
        "binary_expression.cmp.lt",
        RuleGate::Feature("native-primitives"),
    ),
    (
        "binary_expression.cmp.ne",
        RuleGate::Feature("native-primitives"),
    ),
    ("binary_expression.cons", RuleGate::Feature("native-lists")),
    (
        "binary_expression.mul.times",
        RuleGate::Feature("native-primitives"),
    ),
    (
        "binary_expression.or",
        RuleGate::Feature("native-primitives"),
    ),
    (
        "binary_expression.pipe",
        RuleGate::Feature("several-outputs"),
    ),
    (
        "binary_expression.pipe.field",
        RuleGate::Feature("method-calls"),
    ),
    ("bind_expression", RuleGate::Feature("second-order-rules")),
    ("block", RuleGate::Feature("let-statements")),
    ("boolean.expression", RuleGate::Feature("native-primitives")),
    ("boolean.type", RuleGate::Feature("indexed-data")),
    ("break_expression", RuleGate::Feature("loops")),
    ("break_value_expression", RuleGate::Feature("loops")),
    ("bridge_type", RuleGate::Feature("bridge-types")),
    ("capability_type", RuleGate::Feature("capabilities")),
    ("character", RuleGate::Feature("text-primitives")),
    ("circuit_declaration", RuleGate::Feature("operations")),
    ("close_expression", RuleGate::Feature("session-types")),
    ("codata_declaration", RuleGate::Feature("codata")),
    ("cons_pattern", RuleGate::Feature("list-case")),
    ("constructor.expression", RuleGate::Core(CoreReason::Name)),
    ("constructor_pattern", RuleGate::Feature("pattern-matching")),
    ("continue_expression", RuleGate::Feature("loops")),
    ("data_declaration", RuleGate::Feature("nominal-data")),
    ("def_value", RuleGate::Core(CoreReason::Twin)),
    (
        "derived_rule_declaration",
        RuleGate::Feature("derived-rules"),
    ),
    ("descent_type", RuleGate::Feature("tarski-universes")),
    ("drop_expression", RuleGate::Feature("session-types")),
    ("dup_expression", RuleGate::Feature("shared-endpoints")),
    ("end_session_type", RuleGate::Feature("session-types")),
    ("equivalence_type", RuleGate::Feature("equivalence-record")),
    ("extension_type", RuleGate::Feature("extension-types")),
    ("extern_block", RuleGate::Feature("interop-boundary")),
    ("f_type", RuleGate::Feature("call-by-push-value")),
    ("f_type.result", RuleGate::Feature("effect-rows")),
    (
        "f_type.result.labelled",
        RuleGate::Feature("named-instances"),
    ),
    ("f_type.row", RuleGate::Feature("effect-rows")),
    ("f_type.row.labelled", RuleGate::Feature("named-instances")),
    (
        "flow_declaration",
        RuleGate::Feature("signature-translation"),
    ),
    ("flow_type", RuleGate::Feature("directed-paths")),
    ("for_expression", RuleGate::Feature("for-loops")),
    ("force_expression", RuleGate::Feature("thunks-and-force")),
    (
        "forget_model_expression",
        RuleGate::Feature("signature-models"),
    ),
    ("fork_expression", RuleGate::Feature("session-types")),
    ("function_type", RuleGate::Feature("dependent-functions")),
    ("glob_expression", RuleGate::Feature("globular-structures")),
    ("handle_expression", RuleGate::Feature("effect-handlers")),
    ("hold_expression", RuleGate::Feature("temporary-access")),
    ("hole", RuleGate::Feature("typed-holes")),
    ("hole.pattern", RuleGate::Feature("typed-holes")),
    ("identifier.expression", RuleGate::Core(CoreReason::Twin)),
    ("identifier.pattern", RuleGate::Core(CoreReason::Name)),
    ("if_expression", RuleGate::Feature("conditionals")),
    ("import_declaration", RuleGate::Feature("imports")),
    ("index_expression", RuleGate::Feature("places")),
    ("inner_attribute_block", RuleGate::Feature("attributes")),
    ("inner_attribute_member", RuleGate::Feature("attributes")),
    (
        "instantiation.direction.descent",
        RuleGate::Feature("structural-recursion"),
    ),
    (
        "instantiation.direction.productivity",
        RuleGate::Feature("corecursion"),
    ),
    (
        "instantiation.explicit",
        RuleGate::Feature("implicit-arguments"),
    ),
    (
        "instantiation.tail",
        RuleGate::Feature("structural-recursion"),
    ),
    (
        "instantiation.type",
        RuleGate::Feature("implicit-arguments"),
    ),
    (
        "instantiation_expression",
        RuleGate::Core(CoreReason::Group),
    ),
    ("isomorphism_type", RuleGate::Feature("equivalence-record")),
    (
        "labelled_sum_expression",
        RuleGate::Feature("products-and-sums"),
    ),
    (
        "labelled_sum_pattern",
        RuleGate::Feature("products-and-sums"),
    ),
    ("labelled_sum_type", RuleGate::Feature("products-and-sums")),
    (
        "lambda_expression",
        RuleGate::Feature("dependent-functions"),
    ),
    ("lazy_product_type", RuleGate::Feature("lazy-records")),
    ("lazy_record_expression", RuleGate::Feature("lazy-records")),
    ("lazy_record_type", RuleGate::Feature("lazy-records")),
    ("linear_function_type", RuleGate::Feature("linear-function")),
    ("list_expression", RuleGate::Feature("native-lists")),
    ("list_pattern", RuleGate::Feature("list-case")),
    ("literal_pattern", RuleGate::Feature("pattern-matching")),
    ("loop_expression", RuleGate::Feature("loops")),
    ("manifest_sort", RuleGate::Feature("signature-models")),
    ("manifest_type", RuleGate::Feature("signature-models")),
    ("match_expression", RuleGate::Feature("pattern-matching")),
    (
        "migrate_expression",
        RuleGate::Feature("located-judgements"),
    ),
    ("moded_type", RuleGate::Feature("deduced-receivers")),
    ("module_declaration", RuleGate::Feature("modules")),
    ("module_definition_member", RuleGate::Feature("modules")),
    ("module_include_member", RuleGate::Feature("model-include")),
    ("module_law_member", RuleGate::Feature("stated-laws")),
    ("module_type_member", RuleGate::Feature("modules")),
    ("mu_session_type", RuleGate::Feature("session-types")),
    ("nested_module_member", RuleGate::Feature("module-nesting")),
    ("number.expression", RuleGate::Core(CoreReason::Twin)),
    ("number.type", RuleGate::Feature("indexed-data")),
    ("offer_expression", RuleGate::Feature("session-types")),
    ("offers_declaration", RuleGate::Feature("deployment-offers")),
    ("or_pattern", RuleGate::Feature("pattern-matching")),
    (
        "pack_model_expression",
        RuleGate::Feature("signature-models"),
    ),
    ("parenthesized_expression", RuleGate::Core(CoreReason::Twin)),
    ("parenthesized_type", RuleGate::Core(CoreReason::Group)),
    (
        "path_declaration",
        RuleGate::Feature("signature-translation"),
    ),
    ("path_type", RuleGate::Feature("identity-types")),
    ("primitive_type", RuleGate::Core(CoreReason::Twin)),
    ("product_type", RuleGate::Feature("products-and-sums")),
    ("projection_expression", RuleGate::Core(CoreReason::Twin)),
    ("pub_declaration", RuleGate::Feature("visibility")),
    ("pure_expression", RuleGate::Feature("call-by-push-value")),
    ("rec_block", RuleGate::Feature("mutual-recursion")),
    ("receive_session_type", RuleGate::Feature("session-types")),
    ("record_selection_expression", RuleGate::Feature("records")),
    ("recv_expression", RuleGate::Feature("session-types")),
    ("release_expression", RuleGate::Feature("shared-endpoints")),
    (
        "representable_universe_type",
        RuleGate::Feature("signatures-as-values"),
    ),
    ("rest_pattern", RuleGate::Feature("list-case")),
    ("resume_expression", RuleGate::Feature("temporary-access")),
    ("return_expression", RuleGate::Feature("explicit-exits")),
    ("run_expression", RuleGate::Feature("nested-runs")),
    ("select_expression", RuleGate::Feature("session-types")),
    ("send_expression", RuleGate::Feature("session-types")),
    ("send_session_type", RuleGate::Feature("session-types")),
    ("splice_expression", RuleGate::Feature("tactics-over-goals")),
    ("staged_type", RuleGate::Feature("sized-types")),
    ("statement_block", RuleGate::Feature("let-statements")),
    ("string.expression", RuleGate::Core(CoreReason::Twin)),
    ("string.type", RuleGate::Feature("indexed-data")),
    ("sum_type", RuleGate::Core(CoreReason::Twin)),
    ("telescope_expression", RuleGate::Feature("records")),
    ("telescope_pattern", RuleGate::Feature("records")),
    ("telescope_type", RuleGate::Feature("records")),
    (
        "theory_declaration",
        RuleGate::Feature("signatures-as-values"),
    ),
    ("thunk_expression", RuleGate::Feature("thunks-and-force")),
    ("tuple_pattern", RuleGate::Feature("products-and-sums")),
    ("type_application", RuleGate::Feature("data-parameters")),
    (
        "type_application.juxtaposed",
        RuleGate::Feature("data-parameters"),
    ),
    ("type_identifier", RuleGate::Core(CoreReason::Name)),
    ("type_path", RuleGate::Feature("modules")),
    ("type_quote_expression", RuleGate::Feature("type-codes")),
    ("type_variable", RuleGate::Core(CoreReason::Name)),
    ("typed_number.expression", RuleGate::Core(CoreReason::Twin)),
    ("u_type", RuleGate::Feature("thunks-and-force")),
    ("unary_expression", RuleGate::Core(CoreReason::Twin)),
    ("union_type", RuleGate::Feature("union-types")),
    ("universe_flow_type", RuleGate::Feature("directed-paths")),
    ("universe_type", RuleGate::Feature("universes")),
    ("unknown_type", RuleGate::Feature("unknown-type")),
    ("view_expression", RuleGate::Feature("deduced-receivers")),
    ("while_expression", RuleGate::Feature("loops")),
    ("wildcard", RuleGate::Core(CoreReason::Name)),
    ("wildcard.expression", RuleGate::Feature("wildcards")),
    ("wildcard.type", RuleGate::Feature("wildcards")),
    ("world_declaration", RuleGate::Feature("located-judgements")),
];

/// The gate of the rule `rule`: tier zero with its reason, or the id of the
/// language feature that a source needs to write a form of the rule.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the gate of the line of [`RULE_GATES`] whose name is `rule`, and
///   nothing for a name that the table does not hold.
/// - provides: the feature of a form, for the lowering and for the syntax
///   ledger.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — each rule of the built-in grammar answers a gate, and a
///   name of no rule answers none.
/// - witness: `gate::tests::each_rule_has_one_line_and_each_line_one_rule`
/// - witness: `gate::tests::a_name_of_no_rule_has_no_gate`
#[inline]
#[must_use]
pub fn rule_gate(rule: RuleName) -> Option<RuleGate>
{
    RULE_GATES
        .binary_search_by(|&(name, _gate)| name.cmp(rule.0))
        .ok()
        .and_then(|line| RULE_GATES.get(line))
        .map(|&(_name, gate)| gate)
}

#[cfg(test)]
mod tests
{
    use alloc::vec::Vec;

    use super::CoreReason;
    use super::RULE_GATES;
    use super::RuleGate;
    use super::rule_gate;
    use crate::model::RuleName;
    use crate::surface::built_in;

    #[test]
    fn each_rule_has_one_line_and_each_line_one_rule()
    {
        let pbg = built_in().expect("the built-in grammar builds");
        let mut rules: Vec<&str> = pbg.rules().iter().map(|rule| rule.name).collect();
        rules.sort_unstable();
        rules.dedup();
        let lines: Vec<&str> = RULE_GATES.iter().map(|&(name, _gate)| name).collect();
        assert!(
            lines.is_sorted_by(|left, right| left < right),
            "the lines stand in the byte order of their names, each name one time"
        );
        assert_eq!(
            lines, rules,
            "each rule of the grammar has its line, and each line names a rule"
        );
        for rule in rules {
            assert!(
                rule_gate(RuleName(rule)).is_some(),
                "the rule `{rule}` answers its gate"
            );
        }
    }

    #[test]
    fn the_forms_of_the_first_twin_are_in_the_core()
    {
        let twin: Vec<&str> = RULE_GATES
            .iter()
            .filter(|&&(_name, gate)| gate == RuleGate::Core(CoreReason::Twin))
            .map(|&(name, _gate)| name)
            .collect();
        assert_eq!(
            twin,
            [
                "application_expression",
                "attribute_block",
                "def_value",
                "identifier.expression",
                "number.expression",
                "parenthesized_expression",
                "primitive_type",
                "projection_expression",
                "string.expression",
                "sum_type",
                "typed_number.expression",
                "unary_expression",
            ],
            "the twelve rules that the sources of the first twin use"
        );
        assert_eq!(
            rule_gate(RuleName("match_expression")),
            Some(RuleGate::Feature("pattern-matching")),
            "a form outside the core names its language feature"
        );
    }

    #[test]
    fn a_name_of_no_rule_has_no_gate()
    {
        assert_eq!(rule_gate(RuleName("no_such_rule")), None);
    }
}
