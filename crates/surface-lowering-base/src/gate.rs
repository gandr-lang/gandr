//! The language feature that gates each registered attribute and each row of
//! the builtin table.
//!
//! A source that writes an attribute, or that reads a builtin row, uses the
//! language feature of that attribute or of that row. The feature is a row of
//! the features ledger, named by its id. An attribute or a builtin row with no
//! feature is in tier zero, as a grammar rule with no feature is
//! ([`gandr_surface_grammar::RULE_GATES`]).
//!
//! [`ATTRIBUTE_GATES`] has one line for each row of the attribute registry, in
//! the order of the registry. [`BUILTIN_GATES`] has one line for each word of
//! the builtin table: the namespace of a native value, which is the text of
//! its key before the first `.`, or its whole key when it has none, and the
//! key of an atom, of a former and of a role. A person writes each line. The
//! tests of this module hold the two tables against the registry and against
//! the builtin table. The ledger tool holds each id against the rows of the
//! features ledger.

use gandr_core_term::builtin::Kind;
use gandr_core_term::builtin::Row;
use gandr_surface_grammar::CoreReason;
use gandr_surface_grammar::RuleGate;

use crate::attribute::RegisteredAttribute;

/// The gate of each registered attribute, in the order of the registry.
///
/// # Specification
/// - ensures: the names are the names of the attribute registry, in its
///   order, each one time.
/// - provides: the one place where an attribute gets its language feature.
/// - executable: none — the specification attribute does not support constant
///   items; the test of this module holds the names.
///
/// # Adequacy
/// - hypothesis: L3 — the names of the table are compared with the names of
///   the registry, and the attributes of the first twin are in the core.
/// - witness: `gate::tests::each_attribute_has_its_line_in_the_order_of_the_registry`
pub const ATTRIBUTE_GATES: [(&str, RuleGate); 26_usize] = [
    ("checks", RuleGate::Core(CoreReason::Record)),
    ("owes", RuleGate::Core(CoreReason::Record)),
    ("refuses", RuleGate::Core(CoreReason::Record)),
    ("runs", RuleGate::Core(CoreReason::Record)),
    ("normalizes", RuleGate::Core(CoreReason::Record)),
    ("decomposes", RuleGate::Feature("web-decomposition")),
    ("traces", RuleGate::Feature("traces")),
    ("reads", RuleGate::Core(CoreReason::Record)),
    ("distributes", RuleGate::Feature("exact-distributions")),
    ("doc", RuleGate::Core(CoreReason::Record)),
    ("explicit_exits", RuleGate::Core(CoreReason::Record)),
    ("explicit_runs", RuleGate::Core(CoreReason::Record)),
    ("respects", RuleGate::Feature("rule-respect")),
    ("entry", RuleGate::Feature("located-judgements")),
    ("form", RuleGate::Core(CoreReason::Record)),
    ("identity", RuleGate::Feature("atom-identity")),
    ("deprecated", RuleGate::Feature("deprecation")),
    ("format", RuleGate::Core(CoreReason::Record)),
    ("boundary", RuleGate::Feature("interop-boundary")),
    ("builtin", RuleGate::Feature("builtin-declarations")),
    ("thir", RuleGate::Feature("rust-semantics-thir")),
    ("item", RuleGate::Feature("rust-semantics-thir")),
    ("inert", RuleGate::Feature("inert-fields")),
    ("frobenius", RuleGate::Feature("circuit-spiders")),
    ("export", RuleGate::Core(CoreReason::Twin)),
    ("features", RuleGate::Core(CoreReason::Record)),
];

/// The gate of each word of the builtin table, by the kind of its rows.
///
/// # Specification
/// - ensures: each row of the builtin table has one line, by its kind and its
///   word ([`builtin_word`]), and each line has one row or more.
/// - provides: the one place where a builtin row gets its language feature.
/// - executable: none — the specification attribute does not support constant
///   items; the test of this module holds the cover.
///
/// # Adequacy
/// - hypothesis: L3 — each row of the builtin table is looked up, each line
///   is counted, and the integer widths of the first twin are in the core.
/// - witness: `gate::tests::each_builtin_row_has_one_line_and_each_line_a_row`
pub const BUILTIN_GATES: [(Kind, &str, RuleGate); 58_usize] = [
    (Kind::Native, "add", RuleGate::Feature("native-primitives")),
    (Kind::Native, "and", RuleGate::Feature("native-primitives")),
    (Kind::Native, "bool", RuleGate::Feature("native-primitives")),
    (Kind::Native, "eq", RuleGate::Feature("native-primitives")),
    (Kind::Native, "float64", RuleGate::Feature("floating-point")),
    (Kind::Native, "ge", RuleGate::Feature("native-primitives")),
    (Kind::Native, "gt", RuleGate::Feature("native-primitives")),
    (Kind::Native, "i16", RuleGate::Core(CoreReason::Twin)),
    (Kind::Native, "i32", RuleGate::Core(CoreReason::Twin)),
    (Kind::Native, "i64", RuleGate::Core(CoreReason::Twin)),
    (Kind::Native, "i8", RuleGate::Core(CoreReason::Twin)),
    (Kind::Native, "int", RuleGate::Feature("native-primitives")),
    (Kind::Native, "isize", RuleGate::Core(CoreReason::Twin)),
    (Kind::Native, "le", RuleGate::Feature("native-primitives")),
    (Kind::Native, "lt", RuleGate::Feature("native-primitives")),
    (Kind::Native, "mul", RuleGate::Feature("native-primitives")),
    (Kind::Native, "ne", RuleGate::Feature("native-primitives")),
    (Kind::Native, "neg", RuleGate::Feature("native-primitives")),
    (Kind::Native, "or", RuleGate::Feature("native-primitives")),
    (Kind::Native, "prim", RuleGate::Feature("native-primitives")),
    (Kind::Native, "string", RuleGate::Feature("text-primitives")),
    (Kind::Native, "sub", RuleGate::Feature("native-primitives")),
    (Kind::Native, "u16", RuleGate::Core(CoreReason::Twin)),
    (Kind::Native, "u32", RuleGate::Core(CoreReason::Twin)),
    (Kind::Native, "u64", RuleGate::Core(CoreReason::Twin)),
    (Kind::Native, "u8", RuleGate::Core(CoreReason::Twin)),
    (Kind::Native, "usize", RuleGate::Core(CoreReason::Twin)),
    (Kind::Atom, "bool", RuleGate::Core(CoreReason::Twin)),
    (Kind::Atom, "buf", RuleGate::Feature("buffer-tokens")),
    (Kind::Atom, "char", RuleGate::Feature("text-primitives")),
    (Kind::Atom, "f64", RuleGate::Feature("floating-point")),
    (Kind::Atom, "i16", RuleGate::Core(CoreReason::Twin)),
    (Kind::Atom, "i32", RuleGate::Core(CoreReason::Twin)),
    (Kind::Atom, "i64", RuleGate::Core(CoreReason::Twin)),
    (Kind::Atom, "i8", RuleGate::Core(CoreReason::Twin)),
    (Kind::Atom, "integer", RuleGate::Core(CoreReason::Twin)),
    (Kind::Atom, "isize", RuleGate::Core(CoreReason::Twin)),
    (Kind::Atom, "qubit", RuleGate::Feature("qubit-type")),
    (Kind::Atom, "row", RuleGate::Feature("row-kind")),
    (Kind::Atom, "string", RuleGate::Core(CoreReason::Twin)),
    (Kind::Atom, "u16", RuleGate::Core(CoreReason::Twin)),
    (Kind::Atom, "u32", RuleGate::Core(CoreReason::Twin)),
    (Kind::Atom, "u64", RuleGate::Core(CoreReason::Twin)),
    (Kind::Atom, "u8", RuleGate::Core(CoreReason::Twin)),
    (Kind::Atom, "unit", RuleGate::Core(CoreReason::Twin)),
    (Kind::Atom, "usize", RuleGate::Core(CoreReason::Twin)),
    (Kind::Atom, "void", RuleGate::Core(CoreReason::Twin)),
    (Kind::Atom, "web", RuleGate::Feature("web-decomposition")),
    (Kind::Former, "dialogue", RuleGate::Feature("traces")),
    (Kind::Former, "list", RuleGate::Feature("native-lists")),
    (Kind::Former, "prefix", RuleGate::Feature("run-prefixes")),
    (Kind::Former, "returner", RuleGate::Feature("call-by-push-value")),
    (Kind::Former, "run", RuleGate::Feature("run-prefixes")),
    (Kind::Former, "thunk", RuleGate::Feature("thunks-and-force")),
    (Kind::Role, "irArgs", RuleGate::Feature("induction-recursion")),
    (Kind::Role, "irDecode", RuleGate::Feature("induction-recursion")),
    (Kind::Role, "irPair", RuleGate::Feature("induction-recursion")),
    (Kind::Role, "irSignature", RuleGate::Feature("induction-recursion")),
];

/// The gate of the registered attribute `attribute`: tier zero with its
/// reason, or the id of the language feature that a source needs to write the
/// attribute.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the gate of the line of [`ATTRIBUTE_GATES`] whose name is the
///   name of `attribute`, and nothing for a name that the table does not hold.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — each attribute of the registry answers its gate.
/// - witness: `gate::tests::each_attribute_has_its_line_in_the_order_of_the_registry`
#[inline]
#[must_use]
pub fn attribute_gate(attribute: RegisteredAttribute) -> Option<RuleGate>
{
    ATTRIBUTE_GATES
        .iter()
        .find(|&&(name, _gate)| name == attribute.as_ref())
        .map(|&(_name, gate)| gate)
}

/// The word that keys the line of the builtin row `row` in
/// [`BUILTIN_GATES`]: the namespace of a native value, which is the text of
/// its key before the first `.`, and the whole key of each other row.
///
/// # Specification
/// trivial.
#[inline]
#[must_use]
pub fn builtin_word(row: Row) -> &'static str
{
    let key = row.key().0;
    match row.kind() {
        Kind::Native => key.split_once('.').map_or(key, |(namespace, _member)| namespace),
        Kind::Atom | Kind::Former | Kind::Role => key,
    }
}

/// The gate of the builtin row `row`: tier zero with its reason, or the id of
/// the language feature that a source needs to read the row.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the gate of the line of [`BUILTIN_GATES`] with the kind of
///   `row` and its word ([`builtin_word`]), and nothing for a row that the
///   table does not hold.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — each row of the builtin table answers its gate.
/// - witness: `gate::tests::each_builtin_row_has_one_line_and_each_line_a_row`
#[inline]
#[must_use]
pub fn builtin_gate(row: Row) -> Option<RuleGate>
{
    let (kind, word) = (row.kind(), builtin_word(row));
    BUILTIN_GATES
        .iter()
        .find(|&&(held, name, _gate)| held == kind && name == word)
        .map(|&(_kind, _name, gate)| gate)
}

#[cfg(test)]
mod tests
{
    use alloc::vec::Vec;

    use gandr_core_term::builtin::Key;
    use gandr_core_term::builtin::Kind;
    use gandr_core_term::builtin::Row;
    use gandr_surface_grammar::CoreReason;
    use gandr_surface_grammar::RuleGate;
    use quenchant_shape::shape::Maybe;

    use super::ATTRIBUTE_GATES;
    use super::BUILTIN_GATES;
    use super::attribute_gate;
    use super::builtin_gate;
    use super::builtin_word;
    use crate::attribute::AttributeRegistry;
    use crate::attribute::RegisteredAttribute;

    #[test]
    fn each_attribute_has_its_line_in_the_order_of_the_registry()
    {
        let registered = AttributeRegistry::names();
        let names: Vec<&str> = registered.iter().map(AsRef::as_ref).collect();
        let lines: Vec<&str> = ATTRIBUTE_GATES.iter().map(|&(name, _gate)| name).collect();
        assert_eq!(
            lines, names,
            "one line for each attribute, in registry order"
        );
        for &name in &registered {
            assert!(
                attribute_gate(name).is_some(),
                "the attribute `{name}` answers its gate"
            );
        }
        for name in [RegisteredAttribute::EXPORT, RegisteredAttribute::FEATURES] {
            assert!(
                matches!(attribute_gate(name), Some(RuleGate::Core(_))),
                "`{name}` is in tier zero"
            );
        }
        assert_eq!(
            attribute_gate(RegisteredAttribute::RESPECTS),
            Some(RuleGate::Feature("rule-respect")),
            "an attribute outside the core names its language feature"
        );
    }

    #[test]
    fn each_builtin_row_has_one_line_and_each_line_a_row()
    {
        let mut used: Vec<usize> = Vec::new();
        used.resize(BUILTIN_GATES.len(), 0_usize);
        for row in Row::all() {
            let (kind, word) = (row.kind(), builtin_word(row));
            let lines: Vec<usize> = BUILTIN_GATES
                .iter()
                .enumerate()
                .filter(|&(_at, &(held, name, _gate))| held == kind && name == word)
                .map(|(at, _line)| at)
                .collect();
            assert_eq!(
                lines.len(),
                1_usize,
                "the row `{}` of the kind {kind:?} has one line, by the word `{word}`",
                row.key()
            );
            for at in lines {
                if let Some(count) = used.get_mut(at) {
                    *count = count.saturating_add(1);
                }
            }
            assert!(
                builtin_gate(row).is_some(),
                "the row `{}` answers its gate",
                row.key()
            );
        }
        for (&(kind, word, _gate), count) in BUILTIN_GATES.iter().zip(&used) {
            assert!(
                *count > 0_usize,
                "the line of the word `{word}` of the kind {kind:?} has a row"
            );
        }
        let Maybe::Present(twin) = Row::named(Key("u64.wrapping_add"))
        else {
            panic!("the builtin table has the row `u64.wrapping_add`");
        };
        assert_eq!(
            builtin_gate(twin),
            Some(RuleGate::Core(CoreReason::Twin)),
            "an operation of an integer width is in tier zero"
        );
    }
}
