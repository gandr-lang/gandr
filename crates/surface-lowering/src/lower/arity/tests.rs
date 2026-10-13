use alloc::format;
use alloc::string::String;
use alloc::vec;
use alloc::vec::Vec;

use anodized::spec;
use gandr_core_term::CompType;
use gandr_core_term::CompTypeId;
use gandr_core_term::Computation;
use gandr_core_term::ComputationId;
use gandr_core_term::CoreArena;
use gandr_core_term::Value;
use gandr_core_term::ValueId;
use gandr_core_term::ValueType;
use gandr_core_term::ValueTypeId;
use gandr_surface_grammar::NamedKind;
use gandr_surface_syntax::ByteOffset;
use gandr_surface_syntax::ByteSpan;
use gandr_surface_syntax::SourceText;

use crate::error::FormFault;
use crate::error::FragmentBoundary;
use crate::error::FragmentSort;
use crate::error::LoweringRefusal;
use crate::fixture::grammar;
use crate::fixture::parsed;
use crate::fixture::span;
use crate::form::FormName;
use crate::lower::LoweringBudget;
use crate::lower::lower_module;
use crate::module::DeclarationOutcome;
use crate::module::LoweredDeclaration;
use crate::module::LoweredModule;
use crate::namespace::Recognition;
use crate::resolve::HeadArity;
use crate::resolve::OperandCount;
use crate::resolve::SurfaceName;

/// One core node of any family, as [`shown`] walks it.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: the family of the node is kept beside its id.
/// - executable: none — the root holds no arena.
///
/// # Adequacy
/// - hypothesis: L3 — the witnesses below walk roots of all four families.
/// - witness: `lower::arity::tests::a_telescope_type_lowers_by_its_arity`
/// - witness: `lower::arity::tests::a_copattern_block_orders_its_clauses_by_its_answer`
#[derive(Clone, Copy, Debug)]
enum Root
{
    /// A value.
    Value(ValueId),
    /// A value type.
    ValueType(ValueTypeId),
    /// A computation.
    Computation(ComputationId),
    /// A computation type.
    CompType(CompTypeId),
}

/// The core term at `root`, in pre-order, one token per former, so two
/// terms minted at different arena positions compare by structure.
///
/// # Specification
/// - requires: an acyclic graph rooted in `arena`.
/// - ensures: one token per node reached, its arity written into the token for
///   the formers of any arity and its children following it in order; a former
///   outside the arity-shaped vocabulary is one diagnostic token.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L2 on the formers the witnesses reach — product, sum, record,
///   lazy product and dependent arrow, and their values, eliminations and
///   observations each yield a pinned token.
/// - witness: `lower::arity::tests::a_telescope_type_lowers_by_its_arity`
/// - witness: `lower::arity::tests::a_telescope_value_lowers_by_its_arity`
/// - witness: `lower::arity::tests::a_copattern_block_orders_its_clauses_by_its_answer`
#[spec(ensures: |ret| !ret.is_empty())]
fn shown(
    arena: &CoreArena,
    root: Root,
) -> Vec<String>
{
    let labels = |keys: alloc::vec::Vec<&str>| keys.join(",");
    let mut pending = vec![root];
    let mut tokens = Vec::new();
    while let Some(next) = pending.pop() {
        let (token, children): (String, Vec<Root>) = match next {
            | Root::ValueType(at) => match arena.value_type(at) {
                | Some(&ValueType::Base(base)) => (format!("{base:?}"), Vec::new()),
                | Some(&ValueType::Product(ref parts)) => (
                    format!("*{}", parts.len()),
                    parts.iter().map(|&part| Root::ValueType(part)).collect(),
                ),
                | Some(&ValueType::Sum(ref parts)) => (
                    format!("+{}", parts.len()),
                    parts.iter().map(|&part| Root::ValueType(part)).collect(),
                ),
                | Some(&ValueType::Record(ref fields)) => (
                    format!(
                        "#{{{}}}",
                        labels(fields.keys().map(AsRef::as_ref).collect())
                    ),
                    fields
                        .values()
                        .map(|&field| Root::ValueType(field))
                        .collect(),
                ),
                | Some(&ValueType::Thunk(inner)) => {
                    (String::from("U"), vec![Root::CompType(inner)])
                },
                | other => (format!("{other:?}"), Vec::new()),
            },
            | Root::CompType(at) => match arena.comp_type(at) {
                | Some(&CompType::Returner { result, .. }) => {
                    (String::from("F"), vec![Root::ValueType(result)])
                },
                | Some(&CompType::Arrow { domain, codomain }) => (String::from("->"), vec![
                    Root::ValueType(domain),
                    Root::CompType(codomain),
                ]),
                | Some(&CompType::Pi { domain, codomain }) => (String::from("Pi"), vec![
                    Root::ValueType(domain),
                    Root::CompType(codomain),
                ]),
                | Some(&CompType::With(first, second)) => (String::from("&"), vec![
                    Root::CompType(first),
                    Root::CompType(second),
                ]),
                | other => (format!("{other:?}"), Vec::new()),
            },
            | Root::Value(at) => match arena.value(at) {
                | Some(&Value::Tuple(ref components)) => (
                    format!("tuple{}", components.len()),
                    components
                        .iter()
                        .map(|&component| Root::Value(component))
                        .collect(),
                ),
                | Some(&Value::Injection(summand, body)) => (
                    format!("in{}", usize::from(summand)),
                    vec![Root::Value(body)],
                ),
                | Some(&Value::Record(ref fields)) => (
                    format!(
                        "record{{{}}}",
                        labels(fields.keys().map(AsRef::as_ref).collect())
                    ),
                    fields.values().map(|&field| Root::Value(field)).collect(),
                ),
                | Some(&Value::Thunk(body)) => {
                    (String::from("thunk"), vec![Root::Computation(body)])
                },
                | Some(&Value::Variable { index, .. }) => {
                    (format!("#{}", u32::from(index)), Vec::new())
                },
                | Some(&Value::Constant(constant)) => {
                    (format!("const{}", usize::from(constant)), Vec::new())
                },
                | Some(&Value::Literal(ref literal)) => (format!("{literal:?}"), Vec::new()),
                | other => (format!("{other:?}"), Vec::new()),
            },
            | Root::Computation(at) => match arena.computation(at) {
                | Some(&Computation::Return(value)) => {
                    (String::from("return"), vec![Root::Value(value)])
                },
                | Some(&Computation::Force(value)) => {
                    (String::from("force"), vec![Root::Value(value)])
                },
                | Some(&Computation::Lambda(body)) => {
                    (String::from("lambda"), vec![Root::Computation(body)])
                },
                | Some(&Computation::With(first, second)) => (String::from("with"), vec![
                    Root::Computation(first),
                    Root::Computation(second),
                ]),
                | Some(&Computation::Project(side, body)) => {
                    (format!("project-{side:?}"), vec![Root::Computation(body)])
                },
                | other => (format!("{other:?}"), Vec::new()),
            },
        };
        tokens.push(token);
        pending.extend(children.into_iter().rev());
    }

    tokens
}

/// The module the parser and the lowering make of `source`.
///
/// # Specification
/// - requires: the source parses cleanly within the default allowance.
/// - ensures: one declaration per declared name, in admission order.
/// - fails: never on accepted fixtures.
/// - panics: if the lowering refuses the module as a whole.
///
/// # Adequacy
/// - hypothesis: L3 — every witness below reads its module through here.
/// - witness: `lower::arity::tests::a_telescope_type_lowers_by_its_arity`
#[spec(ensures: |ret| !ret.declarations().is_empty())]
fn lowered<'source, Text>(
    source: Text,
    arena: &mut CoreArena,
) -> LoweredModule<'source>
where
    Text: Into<SourceText<'source>>,
{
    let pbg = grammar();
    let tree = parsed(&pbg, source.into());

    lower_module(
        &pbg,
        &tree,
        arena,
        LoweringBudget::DEFAULT,
        Recognition::default(),
    )
    .unwrap()
}

/// What the declaration `name` of `module` lowered to.
///
/// # Specification
/// - requires: `module` declares `name`.
/// - ensures: the outcome of the declaration so named.
/// - fails: never on accepted fixtures.
/// - panics: if no declaration carries the name.
///
/// # Adequacy
/// - hypothesis: L3 — the witnesses read each declaration by its name.
/// - witness: `lower::arity::tests::a_telescope_type_lowers_by_its_arity`
#[spec(ensures: |ret| module.declarations().iter().any(|declaration| declaration.outcome() == ret))]
fn outcome<'source, 'name, Name>(
    module: &LoweredModule<'source>,
    name: Name,
) -> DeclarationOutcome<'source>
where
    Name: Into<SurfaceName<'name>>,
{
    let name = name.into();
    module
        .declarations()
        .iter()
        .find(|declaration| declaration.name() == name)
        .map(LoweredDeclaration::outcome)
        .expect("the module declares the name")
}

/// The declared type of `name`, shown.
///
/// # Specification
/// - requires: `name` lowered a signature.
/// - ensures: the signature's tokens.
/// - fails: never on accepted fixtures.
/// - panics: if the declaration lowered no signature.
///
/// # Adequacy
/// - hypothesis: L3 — the type witnesses read each signature here.
/// - witness: `lower::arity::tests::a_telescope_type_lowers_by_its_arity`
#[spec(ensures: |ret| !ret.is_empty())]
fn declared<'name, Name>(
    arena: &CoreArena,
    module: &LoweredModule<'_>,
    name: Name,
) -> Vec<String>
where
    Name: Into<SurfaceName<'name>>,
{
    let name = name.into();
    match outcome(module, name) {
        | DeclarationOutcome::Completed { declared_type, .. }
        | DeclarationOutcome::Uncompleted { declared_type } => {
            shown(arena, Root::ValueType(declared_type))
        },
        | other => panic!("`{name}` lowers a signature, not {other:?}"),
    }
}

/// The body of `name`, shown.
///
/// # Specification
/// - requires: `name` lowered a body.
/// - ensures: the body's tokens.
/// - fails: never on accepted fixtures.
/// - panics: if the declaration lowered no body.
///
/// # Adequacy
/// - hypothesis: L3 — the value witnesses read each body here.
/// - witness: `lower::arity::tests::a_telescope_value_lowers_by_its_arity`
#[spec(ensures: |ret| !ret.is_empty())]
fn body<'name, Name>(
    arena: &CoreArena,
    module: &LoweredModule<'_>,
    name: Name,
) -> Vec<String>
where
    Name: Into<SurfaceName<'name>>,
{
    let name = name.into();
    match outcome(module, name) {
        | DeclarationOutcome::Completed { body, .. } | DeclarationOutcome::Bodied { body } => {
            shown(arena, Root::Value(body))
        },
        | other => panic!("`{name}` lowers a body, not {other:?}"),
    }
}

/// The refusal of the one refused declaration of `source`.
///
/// # Specification
/// - requires: exactly the last declaration of `source` is refused.
/// - ensures: that declaration's refusal.
/// - fails: never on accepted fixtures.
/// - panics: if the last declaration is not refused.
///
/// # Adequacy
/// - hypothesis: L3 — the refusal witnesses read exact refusals here.
/// - witness: `lower::arity::tests::labels_are_of_one_kind_and_written_once`
#[spec(ensures: |ret| matches!(ret.span(), quenchant_shape::shape::Maybe::Present(_)))]
fn refused<'source, Text>(source: Text) -> LoweringRefusal<'source>
where
    Text: Into<SourceText<'source>>,
{
    let mut arena = CoreArena::new();
    let module = lowered(source, &mut arena);
    match module
        .declarations()
        .last()
        .map(LoweredDeclaration::outcome)
    {
        | Some(DeclarationOutcome::Refused(refusal)) => refusal,
        | other => panic!("the last declaration is refused, not {other:?}"),
    }
}

/// The bytes `needle` covers at its `nth` occurrence in `source`.
///
/// # Specification
/// - requires: `needle` occurs at least `nth + 1` times in `source`.
/// - ensures: the span whose bytes in `source` are `needle`.
/// - fails: never on accepted fixtures.
/// - panics: if the occurrence is absent.
///
/// # Adequacy
/// - hypothesis: L3 — the refusal witnesses locate each refusal's span here.
/// - witness: `lower::arity::tests::labels_are_of_one_kind_and_written_once`
#[spec(
    ensures: |ret| {
        source
            .as_ref()
            .get(usize::from(ret.start()) .. usize::from(ret.end()))
            == Some(needle.as_ref())
    },
)]
fn at<Source, Needle, Nth>(
    source: Source,
    needle: Needle,
    nth: Nth,
) -> ByteSpan
where
    Source: AsRef<str>,
    Needle: AsRef<str>,
    Nth: Into<usize>,
{
    let (source, needle, nth) = (source.as_ref(), needle.as_ref(), nth.into());
    let start = source
        .match_indices(needle)
        .nth(nth)
        .map(|(start, _)| start)
        .expect("the needle occurs");

    span(
        ByteOffset::from(start),
        ByteOffset::from(start.saturating_add(needle.len())),
    )
}

/// The refusal a form named `form` earns for `fault` at `span`.
///
/// # Specification
/// trivial.
fn malformed(
    span: ByteSpan,
    form: NamedKind<'static>,
    fault: FormFault,
) -> LoweringRefusal<'static>
{
    LoweringRefusal::MalformedForm {
        span,
        form: FormName::from(form),
        fault,
    }
}

#[test]
fn a_telescope_type_lowers_by_its_arity()
{
    let mut arena = CoreArena::new();
    let module = lowered(
        "def none : #{} ; def one : #{Integer} ; def three : #{Integer, String, Unit,} ; def \
         labelled : #{n : Integer, s : String} ; def reordered : #{s : String, n : Integer} ;",
        &mut arena,
    );

    assert_eq!(
        declared(&arena, &module, "none"),
        ["*0"],
        "`#{{}}` is the unit"
    );
    assert_eq!(
        declared(&arena, &module, "one"),
        ["*1", "Integer"],
        "`#{{A}}` is the product of one component, not `A`"
    );
    assert_eq!(
        declared(&arena, &module, "three"),
        ["*3", "Integer", "String", "*0"],
        "a trailing comma closes the list it ends"
    );
    assert_eq!(
        declared(&arena, &module, "labelled"),
        ["#{n,s}", "Integer", "String"],
        "a labelled telescope is the record keyed by its labels"
    );
    assert_eq!(
        declared(&arena, &module, "reordered"),
        declared(&arena, &module, "labelled"),
        "and the order its fields are written in is not observable"
    );
    let source = "def bad : #{Integer : String} ;";
    assert_eq!(
        refused(source),
        malformed(
            at(source, "Integer", 0_usize),
            NamedKind("telescope_type"),
            FormFault::MisplacedTile
        ),
        "a key is a lowercase word, told from a type by its kind"
    );
    let source = "def sigma : #{k : Integer, v : k} ;";
    assert_eq!(
        refused(source),
        LoweringRefusal::UnresolvedTypeHead {
            span: at(source, "k", 1_usize),
            name: SurfaceName::from("k"),
            arity: HeadArity::Nullary,
        },
        "a later entry does not see an earlier label: there is no core Σ yet"
    );
}

#[test]
fn a_telescope_value_lowers_by_its_arity()
{
    let mut arena = CoreArena::new();
    let module = lowered(
        "def none = #{} ; def one = #{1} ; def two = #{1, \"b\"} ; def trailing = #{1, \"b\",} ; \
         def reordered = #{.1 = \"b\", .0 = 1} ; def dotted = #{.s = \"x\", .n = 3} ; def \
         shorthand = #{n = 3, s = \"x\"} ;",
        &mut arena,
    );

    assert_eq!(
        body(&arena, &module, "none"),
        ["tuple0"],
        "`#{{}}` is the unit"
    );
    assert_eq!(
        body(&arena, &module, "one").first().map(String::as_str),
        Some("tuple1"),
        "`#{{a}}` is the tuple of one"
    );
    assert_eq!(
        body(&arena, &module, "two").first().map(String::as_str),
        Some("tuple2")
    );
    assert_eq!(
        body(&arena, &module, "trailing"),
        body(&arena, &module, "two"),
        "a trailing comma closes the list it ends"
    );
    assert_eq!(
        body(&arena, &module, "reordered"),
        body(&arena, &module, "two"),
        "indexed entries are reordered by their indices"
    );
    assert_eq!(
        body(&arena, &module, "dotted").first().map(String::as_str),
        Some("record{n,s}"),
        "dotted labels make the record keyed by them"
    );
    assert_eq!(
        body(&arena, &module, "shorthand"),
        body(&arena, &module, "dotted"),
        "and the shorthand `l = e` is the same record, in either order"
    );
    let source = "def bad = #{1 2} ;";
    assert!(
        matches!(
            refused(source),
            LoweringRefusal::MalformedForm { form, .. }
                if form == FormName::from(NamedKind("telescope_expression"))
        ),
        "an entry is closed by a comma or the brace"
    );
}

#[test]
fn a_record_update_is_declined_by_name()
{
    let source = "def r = #{n = 1} ; def s = #{r | n = 2} ;";
    assert_eq!(
        refused(source),
        LoweringRefusal::OutOfFragment {
            span: at(source, "#{r | n = 2}", 0_usize),
            form: FormName::RECORD_UPDATE,
            sort: FragmentSort::Value,
            boundary: FragmentBoundary::Unadmitted,
        },
        "the update parses and is declined by its own name"
    );
}

#[test]
fn labels_are_of_one_kind_and_written_once()
{
    let source = "def gap = #{.0 = 1, .2 = 2} ;";
    assert_eq!(
        refused(source),
        malformed(
            at(source, "2", 0_usize),
            NamedKind("telescope_expression"),
            FormFault::MisplacedTile
        ),
        "the indices of a form are exactly 0 to n - 1"
    );
    let source = "def repeated = #{.0 = 1, .0 = 2} ;";
    assert_eq!(
        refused(source),
        LoweringRefusal::DuplicateDefinition {
            span: at(source, "0", 1_usize),
            name: SurfaceName::from("0"),
            first: at(source, "0", 0_usize),
        },
        "an index names one entry"
    );
    let source = "def twice = #{.n = 1, .n = 2} ;";
    assert_eq!(
        refused(source),
        LoweringRefusal::DuplicateDefinition {
            span: at(source, "n", 1_usize),
            name: SurfaceName::from("n"),
            first: at(source, "n", 0_usize),
        },
        "a label names one entry"
    );
    let source = "def mixed = #{.n = 1, .1 = 2} ;";
    assert_eq!(
        refused(source),
        malformed(
            at(source, "1", 1_usize),
            NamedKind("telescope_expression"),
            FormFault::MisplacedTile
        ),
        "a form holds one kind of entry throughout"
    );
    let source = "def mixed : #{Integer, k : String} ;";
    assert_eq!(
        refused(source),
        malformed(
            at(source, "k", 0_usize),
            NamedKind("telescope_type"),
            FormFault::MisplacedTile
        ),
        "positional and labelled entries do not mix"
    );
}

#[test]
fn a_sum_over_labels_lowers_to_the_sum_of_its_entries()
{
    let mut arena = CoreArena::new();
    let module = lowered(
        "def empty : +{} ; def one : +{Integer} ; def positional : +{Integer, String} ; def \
         labelled : +{ok : Integer, err : String} ;",
        &mut arena,
    );

    assert_eq!(
        declared(&arena, &module, "empty"),
        ["+0"],
        "`+{{}}` is the empty sum"
    );
    assert_eq!(
        declared(&arena, &module, "one"),
        ["+1", "Integer"],
        "`+{{A}}` is the sum of one summand"
    );
    assert_eq!(declared(&arena, &module, "positional"), [
        "+2", "Integer", "String"
    ]);
    assert_eq!(
        declared(&arena, &module, "labelled"),
        declared(&arena, &module, "positional"),
        "a sum keeps its written order and erases its labels"
    );
}

#[test]
fn an_injection_takes_its_index_from_its_label()
{
    let mut arena = CoreArena::new();
    let module = lowered(
        "def third = +{.2 = unit} ; def labelled = (+{.err = \"no\"} : +{ok : Integer, err : \
         String}) ; def only = (+{.only = 4} : +{only : Integer}) ;",
        &mut arena,
    );

    assert_eq!(
        body(&arena, &module, "third").first().map(String::as_str),
        Some("in2"),
        "an index past the binary sum names its summand itself"
    );
    assert_eq!(
        body(&arena, &module, "labelled")
            .first()
            .map(String::as_str),
        Some("in1"),
        "a label takes the index it has in the sum its annotation states"
    );
    assert_eq!(
        body(&arena, &module, "only").first().map(String::as_str),
        Some("in0"),
        "a one-summand sum injects at its only label"
    );
    let source = "def bare = +{.err = \"no\"} ;";
    assert_eq!(
        refused(source),
        LoweringRefusal::OutOfFragment {
            span: at(source, "+{.err = \"no\"}", 0_usize),
            form: FormName::from(NamedKind("labelled_sum_expression")),
            sort: FragmentSort::Value,
            boundary: FragmentBoundary::Unannotated,
        },
        "a label with no stated sum has no index"
    );
    let source = "def missing = (+{.gone = 1} : +{ok : Integer, err : String}) ;";
    assert!(
        matches!(refused(source), LoweringRefusal::UnresolvedName { name, span } if name == SurfaceName::from("gone") && span == at(source, "gone", 0_usize)),
        "a label the stated sum lacks is unresolved where it is written"
    );
}

#[test]
fn a_session_entry_reads_the_select_and_the_offer()
{
    let mut arena = CoreArena::new();
    let module = lowered("def value : +{ok : Integer} ;", &mut arena);
    assert_eq!(
        declared(&arena, &module, "value"),
        ["+1", "Integer"],
        "over value types the braces are the sum"
    );
    let source = "def choose : +{ok : ! Integer . end} ;";
    assert!(
        matches!(
            refused(source),
            LoweringRefusal::OutOfFragment { form, .. } if form == FormName::SELECT_SESSION_TYPE
        ),
        "over session types they are the select, declined by its name"
    );
    let source = "def menu : +U &{get : ! Integer . end, put : ? Integer . end} ;";
    assert!(
        matches!(
            refused(source),
            LoweringRefusal::OutOfFragment { form, .. } if form == FormName::OFFER_SESSION_TYPE
        ),
        "and the lazy record over session types is the offer"
    );
    let source = "def mixed : +{ok : Integer, done : end} ;";
    assert_eq!(
        refused(source),
        malformed(
            at(source, "end", 0_usize),
            NamedKind("labelled_sum_type"),
            FormFault::MisplacedTile
        ),
        "session types and value types do not mix in one form"
    );
}

#[test]
fn a_lazy_record_lowers_to_nested_with()
{
    let mut arena = CoreArena::new();
    let module = lowered(
        "def two : +U &{get : -F Integer, put : -F String} ; def binary : +U (-F Integer & -F \
         String) ; def three : +U &{a : -F Integer, b : -F String, c : -F Unit} ;",
        &mut arena,
    );

    assert_eq!(
        declared(&arena, &module, "two"),
        ["U", "&", "F", "Integer", "F", "String"],
        "a lazy record of two is the lazy product"
    );
    assert_eq!(
        declared(&arena, &module, "binary"),
        declared(&arena, &module, "two"),
        "and `C & D` is the same core type"
    );
    assert_eq!(
        declared(&arena, &module, "three"),
        ["U", "&", "F", "Integer", "&", "F", "String", "F", "*0"],
        "a lazy record of three nests to the right"
    );
    for (source, written, entries) in [
        ("def none : +U &{} ;", "&{}", 0_usize),
        (
            "def single : +U &{get : -F Integer} ;",
            "&{get : -F Integer}",
            1_usize,
        ),
    ] {
        assert_eq!(
            refused(source),
            LoweringRefusal::OutOfFragment {
                span: at(source, written, 0_usize),
                form: FormName::from(NamedKind("lazy_record_type")),
                sort: FragmentSort::CompType,
                boundary: FragmentBoundary::Arity(OperandCount::from(entries)),
            },
            "the lazy record of {entries} entries waits on an n-ary former"
        );
    }
}

#[test]
fn a_copattern_block_orders_its_clauses_by_its_answer()
{
    let mut arena = CoreArena::new();
    let module = lowered(
        "def stated(n : Integer) -> &{get : -F Integer, put : -F String} { &{.put => return \
         \"s\", .get => return n} }\ndef positional(n : Integer) -> &{-F Integer, -F String} { \
         &{.1 => return \"s\", .0 => return n} }\n",
        &mut arena,
    );
    let with = |name: &str| -> Vec<String> {
        let tokens = body(&arena, &module, name);
        tokens
            .iter()
            .position(|token| token == "with")
            .map(|start| tokens.get(start ..).unwrap_or_default().to_vec())
            .unwrap_or_default()
    };

    assert_eq!(
        with("stated").first().map(String::as_str),
        Some("with"),
        "a copattern block is the lazy pairing"
    );
    assert_eq!(
        with("stated").get(1_usize ..= 2_usize),
        Some(&[String::from("return"), String::from("#0")][..]),
        "its clauses take the order the answer states, `.get` first"
    );
    assert_eq!(
        with("positional"),
        with("stated"),
        "indexed clauses are ordered by their indices"
    );
    let source = "def unstated(n : Integer) -> -F Integer { &{.get => return n, .put => return n} \
                  }\n";
    assert!(
        matches!(refused(source), LoweringRefusal::OutOfFragment {
            boundary: FragmentBoundary::Unannotated | FragmentBoundary::WrongSort,
            ..
        }),
        "labelled clauses with no lazy record stated have no order"
    );
    let source = "def single(n : Integer) -> &{get : -F Integer, put : -F Integer} { &{.get => \
                  return n} }\n";
    assert!(
        matches!(
            refused(source),
            LoweringRefusal::OutOfFragment {
                boundary: FragmentBoundary::Arity(count),
                ..
            } if count == OperandCount::from(1_usize)
        ),
        "a block of one clause waits on an n-ary former"
    );
}

#[test]
fn an_observation_projects_along_the_nesting()
{
    let mut arena = CoreArena::new();
    let module = lowered(
        "def first(m : +U &{a : -F Integer, b : -F Integer, c : -F Integer}) -> -F Integer { \
         become m.a }\ndef middle(m : +U &{a : -F Integer, b : -F Integer, c : -F Integer}) -> \
         -F Integer { become m.b }\ndef last(m : +U &{a : -F Integer, b : -F Integer, c : -F \
         Integer}) -> -F Integer { become m.c }\n",
        &mut arena,
    );
    let observed = |name: &str| -> Vec<String> {
        body(&arena, &module, name)
            .into_iter()
            .filter(|token| token.starts_with("project") || token == "force")
            .collect()
    };

    assert_eq!(
        observed("first"),
        ["project-Left", "force"],
        "the first entry is the left of the outer pair"
    );
    assert_eq!(
        observed("middle"),
        ["project-Left", "project-Right", "force"],
        "a middle entry is the left of the right"
    );
    assert_eq!(
        observed("last"),
        ["project-Right", "project-Right", "force"],
        "and the last entry is right all the way"
    );
    let source =
        "def gone(m : +U &{a : -F Integer, b : -F Integer}) -> -F Integer { become m.z }\n";
    assert!(
        matches!(refused(source), LoweringRefusal::UnresolvedName { name, .. } if name == SurfaceName::from("z")),
        "a label the lazy record lacks is unresolved"
    );
}

#[test]
fn a_telescope_binds_each_entry_in_the_ones_after_it()
{
    let mut arena = CoreArena::new();
    let module = lowered(
        "def dependent : (a : Type, x : a) => a ; def mixed : (x : Integer, String) => Integer ; \
         def plain : (Integer, String) => Integer ;",
        &mut arena,
    );

    assert_eq!(
        declared(&arena, &module, "dependent").get(.. 2_usize),
        Some(&[String::from("U"), String::from("Pi")][..]),
        "a named entry a later entry mentions binds a dependent arrow"
    );
    assert_eq!(
        declared(&arena, &module, "mixed")
            .first()
            .map(String::as_str),
        Some("U"),
        "an unnamed entry in a telescope binds a name no source can write"
    );
    assert_eq!(
        declared(&arena, &module, "plain"),
        ["U", "->", "Integer", "->", "String", "F", "Integer"],
        "a list of unnamed entries stays the plain function space"
    );
    let source = "def twice : (x : Integer, x : String) => Integer ;";
    assert!(
        matches!(refused(source), LoweringRefusal::DuplicateDefinition { name, .. } if name == SurfaceName::from("x")),
        "a binder is written once"
    );
}
