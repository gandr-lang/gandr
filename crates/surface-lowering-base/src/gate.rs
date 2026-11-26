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
//!
//! [`used_features`] answers the language features that one source of a unit
//! uses: the feature of the rule of each node of its tree, the feature of each
//! attribute filed on it, and the feature of each builtin row that a `builtin`
//! attribute of it binds. [`declared_features`] answers the keys that the
//! `features` attribute at the head of the source states.

use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use core::ops::Range;

use gandr_core_term::CoreArena;
use gandr_core_term::builtin::Key;
use gandr_core_term::builtin::Kind;
use gandr_core_term::builtin::Row;
use gandr_surface_grammar::CoreReason;
use gandr_surface_grammar::Pbg;
use gandr_surface_grammar::RuleGate;
use gandr_surface_grammar::RuleName;
use gandr_surface_grammar::rule_gate;
use gandr_surface_syntax::ByteOffset;
use gandr_surface_syntax::ByteSpan;
use gandr_surface_syntax::NodeLabel;
use gandr_surface_syntax::SyntaxTree;
use quenchant_shape::shape::Maybe;

use crate::attribute::AttributeTable;
use crate::attribute::RegisteredAttribute;
use crate::attribute::texts;
use crate::unit::SourceIndex;

/// The gate of each registered attribute, in the order of the registry.
///
/// # Specification
/// - ensures: the names are the names of the attribute registry, in its order,
///   each one time.
/// - provides: the one place where an attribute gets its language feature.
/// - executable: none — the specification attribute does not support constant
///   items; the test of this module holds the names.
///
/// # Adequacy
/// - hypothesis: L3 — the names of the table are compared with the names of the
///   registry, and the attributes of the first twin are in the core.
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
/// - hypothesis: L3 — each row of the builtin table is looked up, each line is
///   counted, and the integer widths of the first twin are in the core.
/// - witness: `gate::tests::each_builtin_row_has_one_line_and_each_line_a_row`
pub const BUILTIN_GATES: [(Kind, &str, RuleGate); 56_usize] = [
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
    (Kind::Former, "run", RuleGate::Feature("run-prefixes")),
    (
        Kind::Role,
        "irArgs",
        RuleGate::Feature("induction-recursion"),
    ),
    (
        Kind::Role,
        "irDecode",
        RuleGate::Feature("induction-recursion"),
    ),
    (
        Kind::Role,
        "irPair",
        RuleGate::Feature("induction-recursion"),
    ),
    (
        Kind::Role,
        "irSignature",
        RuleGate::Feature("induction-recursion"),
    ),
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
        Kind::Native => key
            .split_once('.')
            .map_or(key, |(namespace, _member)| namespace),
        Kind::Atom | Kind::Former | Kind::Role => key,
    }
}

/// The gate of the builtin row `row`: tier zero with its reason, or the id of
/// the language feature that a source needs to read the row.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the gate of the line of [`BUILTIN_GATES`] with the kind of `row`
///   and its word ([`builtin_word`]), and nothing for a row that the table does
///   not hold.
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

/// The language features that the source `source` of a unit uses, each with
/// the bytes of its first use.
///
/// # Specification
/// - requires: `tree` is the tree of the unit, read under `pbg`; `within` is
///   the bytes of the source in the unit; `table` holds the attributes of the
///   unit, and `arena` their payloads.
/// - ensures: the id of the language feature of each rule that molds a node of
///   `tree` inside `within`, of each attribute that `table` files under a key
///   of `source`, and of each builtin row whose key a `builtin` attribute of
///   `source` states. A rule, an attribute or a row of tier zero adds nothing.
///   The span of an id is the span of the node or of the attribute that starts
///   first among those that use it, and the longest of those that start there.
/// - provides: the set that the keys of [`declared_features`] are compared
///   with, and the place of a refusal.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a source of the forms of the first twin uses nothing, and
///   a form, an attribute and a builtin row outside tier zero each add their
///   feature.
/// - witness: `gandr-surface-lowering::tests::modules::a_source_uses_the_features_of_its_forms_and_of_its_attributes`
///
/// # Cost
/// - time: one pass over the nodes of the tree and one over the entries of the
///   table.
/// - allocation: the map, one element for each feature.
#[inline]
#[must_use]
pub fn used_features(
    (pbg, tree): (&Pbg, &SyntaxTree<'_>),
    (table, arena): (&AttributeTable, &CoreArena),
    source: SourceIndex,
    within: &Range<ByteOffset>,
) -> BTreeMap<&'static str, ByteSpan>
{
    let mut used: BTreeMap<&'static str, ByteSpan> = BTreeMap::new();
    let mut gated = |gate: Option<RuleGate>, span: ByteSpan| {
        if let Some(RuleGate::Feature(id)) = gate {
            let first = used.entry(id).or_insert(span);
            if (span.start(), first.end()) < (first.start(), span.end()) {
                *first = span;
            }
        }
    };
    for position in tree.positions() {
        if let Some(node) = tree.node(position)
            && within.start <= node.span().start()
            && node.span().end() <= within.end
            && let NodeLabel::Meld(mold) | NodeLabel::Tile(mold) = node.label()
            && let Ok(rule) = pbg.rule_of(mold)
        {
            gated(rule_gate(RuleName(rule.name)), node.span());
        }
    }
    for entry in table.of_source(source) {
        gated(attribute_gate(entry.name()), entry.span());
        if entry.name() == RegisteredAttribute::BUILTIN
            && let Maybe::Present(payload) = entry.payload()
            && let Maybe::Present(keys) = texts(arena, payload)
        {
            for key in keys {
                if let Maybe::Present(row) = Row::named(Key(key.as_ref())) {
                    gated(builtin_gate(row), entry.span());
                }
            }
        }
    }
    used
}

/// The language feature that the source `source` uses and does not declare,
/// with the bytes of its first use: the one whose first use starts first.
///
/// # Specification
/// - requires: as [`used_features`].
/// - ensures: nothing for a source with no `features` attribute at its head,
///   and nothing for a source that declares each feature that it uses; else the
///   feature of [`used_features`] that [`declared_features`] does not hold and
///   whose span starts first, and the first by its id among those that start at
///   one byte.
/// - provides: the refusal of a source that uses a feature that it does not
///   declare.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a source that declares what it uses, a source that
///   declares a different feature, and a source with no declaration separate
///   the answers.
/// - witness: `gandr-surface-lowering::tests::modules::a_source_is_refused_for_a_feature_that_it_does_not_declare`
///
/// # Cost
/// - time: as [`used_features`], for a source with the attribute; one pass over
///   the keys of the sources for a source with none.
#[inline]
#[must_use]
pub fn undeclared_feature(
    grammar: (&Pbg, &SyntaxTree<'_>),
    (table, arena): (&AttributeTable, &CoreArena),
    source: SourceIndex,
    within: &Range<ByteOffset>,
) -> Option<(&'static str, ByteSpan)>
{
    let declared = declared_features(table, arena, source)?;
    used_features(grammar, (table, arena), source, within)
        .into_iter()
        .filter(|&(feature, _span)| !declared.contains(feature))
        .min_by_key(|&(feature, span)| (span.start(), feature))
}

/// The keys that the source `source` of a unit declares with the attribute
/// `features` at its head.
///
/// # Specification
/// - requires: `table` holds the attributes of the unit, and `arena` their
///   payloads.
/// - ensures: nothing for a source with no `features` attribute at its head;
///   else the texts of the payload of that attribute.
/// - provides: the set that [`used_features`] is compared with.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a source with the attribute answers its keys, and a
///   source with none answers nothing.
/// - witness: `gandr-surface-lowering::tests::modules::a_source_uses_the_features_of_its_forms_and_of_its_attributes`
#[inline]
#[must_use]
pub fn declared_features<'arena>(
    table: &AttributeTable,
    arena: &'arena CoreArena,
    source: SourceIndex,
) -> Option<BTreeSet<&'arena str>>
{
    let entry = table
        .sources()
        .iter()
        .filter(|key| key.source() == source)
        .flat_map(|&key| table.entries(key))
        .find(|entry| entry.name() == RegisteredAttribute::FEATURES)?;
    let mut declared: BTreeSet<&'arena str> = BTreeSet::new();
    if let Maybe::Present(payload) = entry.payload()
        && let Maybe::Present(keys) = texts(arena, payload)
    {
        declared.extend(keys.into_iter().map(AsRef::as_ref));
    }
    Some(declared)
}

#[cfg(test)]
mod tests
{
    use alloc::vec::Vec;

    use gandr_core_term::builtin::Key;
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
        let mut used: Vec<usize> = alloc::vec![0_usize; BUILTIN_GATES.len()];
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
