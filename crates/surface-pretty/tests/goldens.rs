//! The printer through its public surface: every former at its exact
//! spelling, and representative types and values pinned at two page widths.
//!
//! Paired goldens present one node at the narrow page (40 columns) and the wide
//! page (100 columns). The wide page must hold exactly the one-line spelling
//! written beside the fixture — the flattened image of every document is that
//! line — and both pages are compared whole against `tests/golden/`.
//! A zero-column pair pins fallback when both separator branches are tainted.
//! Regenerate with `UPDATE_EXPECT=1` and review the diff.

use alloc::boxed::Box;
use alloc::collections::BTreeMap;
use alloc::string::String;
use alloc::sync::Arc;
use std::path::Path;

use anodized::spec;
use expect_test::expect_file;
use gandr_core_nbe::Definitions;
use gandr_core_nbe::DomainArena;
use gandr_core_nbe::Fuel;
use gandr_core_nbe::LoweredChain;
use gandr_core_nbe::ReadbackMode;
use gandr_core_nbe::eval_value;
use gandr_core_nbe::readback_value;
use gandr_core_term::CompTypeId;
use gandr_core_term::ComponentCount;
use gandr_core_term::CoreArena;
use gandr_core_term::DefinitionalEnvironment;
use gandr_core_term::Sort;
use gandr_core_term::SortParameter;
use gandr_core_term::ValueId;
use gandr_core_term::ValueTypeId;
use gandr_core_term::Zone;
use gandr_core_term::hole::HoleId;
use gandr_core_term::identity::Relation;
use gandr_core_term::primitive::Arguments;
use gandr_core_term::primitive::PRELUDE;
use gandr_core_term::session::RecordedMove;
use gandr_core_term::ua::Description;
use gandr_core_term::ua::Generator;
use gandr_core_term::ua::Sides;
use gandr_core_term::ua::Stratum;
use gandr_kernel_strata::Level;
use gandr_kernel_strata::LevelConstant;
use gandr_kernel_strata::LevelVar;
use gandr_kernel_strata::LevelVarIndex;
use gandr_kernel_term::BaseType;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::ConstructorTag;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::FieldLabel;
use gandr_kernel_term::FractionDigits;
use gandr_kernel_term::GroundSort;
use gandr_kernel_term::IntegerLiteral;
use gandr_kernel_term::Literal;
use gandr_kernel_term::Magnitude;
use gandr_kernel_term::NumericLiteral;
use gandr_kernel_term::Side;
use gandr_kernel_term::Sign;
use gandr_kernel_term::StagedPosition;
use gandr_kernel_term::StringLiteral;
use gandr_kernel_term::Summand;
use gandr_surface_pretty::Arity;
use gandr_surface_pretty::Component;
use gandr_surface_pretty::Constructors;
use gandr_surface_pretty::CoreNode;
use gandr_surface_pretty::CoreSource;
use gandr_surface_pretty::DEPTH_LIMIT;
use gandr_surface_pretty::Elided;
use gandr_surface_pretty::Fidelity;
use gandr_surface_pretty::Form;
use gandr_surface_pretty::Former;
use gandr_surface_pretty::Name;
use gandr_surface_pretty::Notation;
use gandr_surface_pretty::PageWidth;
use gandr_surface_pretty::Presentation;
use gandr_surface_pretty::Source;
use gandr_surface_pretty::Spelling;
use gandr_surface_pretty::Style;
use gandr_surface_pretty::Unreadable;
use gandr_surface_pretty::Unspelled;
use gandr_surface_pretty::present_computation;
use gandr_surface_pretty::present_computation_line;
use gandr_surface_pretty::present_definition;
use gandr_surface_pretty::present_recursive;
use gandr_surface_pretty::present_type;
use gandr_surface_pretty::present_value;
use gandr_surface_pretty::recursive;
use gandr_theory_sites::Degree;
use gandr_theory_sites::PortCount;
use gandr_theory_sites::Profile;
use gandr_theory_sites::ShapeSize;
use quenchant_shape::shape::Maybe;

/// The narrow page of every golden pair.
///
/// # Specification
/// trivial.
fn narrow() -> PageWidth
{
    PageWidth::from(40_u32)
}

/// The wide page of every golden pair.
///
/// # Specification
/// trivial.
fn wide() -> PageWidth
{
    PageWidth::from(100_u32)
}

/// What a presentation is made from.
#[derive(Clone, Copy, Debug)]
enum Root
{
    /// A type, through [`present_type`].
    Type(CoreNode),
    /// A value, through [`present_value`].
    Value(CoreNode),
    /// A definition's value, through [`present_definition`].
    Definition(CoreNode),
    /// An elaborated body, through [`present_computation`].
    Computation(CoreNode),
}

/// A golden pair: its file stem, the one-line spelling, and the fidelity
/// both pages carry.
#[derive(Clone, Copy, Debug)]
struct Pinned<'text>
{
    /// The file stem under `tests/golden/`.
    name: &'static str,
    /// The one-line spelling.
    flat: &'text str,
    /// The fidelity of both pages.
    fidelity: Fidelity,
}

/// `root` of `source` laid out at `page` in the explicit form.
///
/// # Specification
/// - requires: the fixture fits the default build and render ceilings.
/// - ensures: the selected type or value presentation has no carriage return or
///   tab; layout-owned line endings are line feeds.
/// - provides: a presentation for exact fixture observations.
/// - panics: if the presentation refuses.
///
/// # Adequacy
/// - hypothesis: L3 — finite type, value and control-string fixtures expose
///   wrong root selection or unescaped controls. Meter exhaustion is outside
///   these fixtures, whose helper deliberately treats refusal as failure.
/// - witness: `tests::goldens::every_type_former_spells_as_the_grammar_writes_it`
/// - witness: `tests::goldens::every_value_leaf_spells_as_the_surface_writes_it`
/// - witness: `tests::goldens::string_controls_stay_in_one_escaped_literal`
#[spec(ensures: |ref ret| !ret.as_ref().contains(['\r', '\t']))]
fn presented<S>(
    source: &S,
    root: Root,
    page: PageWidth,
) -> Presentation
where
    S: Source<Node = CoreNode>,
{
    presented_in(source, root, page, Form::Explicit)
}

/// `root` of `source` laid out at `page` in `style`.
///
/// # Specification
/// - requires: the fixture fits the default build and render ceilings.
/// - ensures: as [`presented`], in `style`.
/// - provides: a presentation in either form and either spelling.
/// - panics: if the presentation refuses.
///
/// # Adequacy
/// - hypothesis: L3 — as [`presented`], the sugared fixtures in both forms, and
///   the glyph fixtures in both spellings.
/// - witness: `tests::goldens::the_sugared_form_writes_every_sugar_its_shape_admits`
/// - witness: `tests::goldens::each_glyph_former_is_written_in_the_spelling_asked_782`
#[spec(ensures: |ref ret| !ret.as_ref().contains(['\r', '\t']))]
fn presented_in<S>(
    source: &S,
    root: Root,
    page: PageWidth,
    style: impl Into<Style>,
) -> Presentation
where
    S: Source<Node = CoreNode>,
{
    let style = style.into();
    match root {
        Root::Type(node) => present_type(source, node, page, style),
        Root::Value(node) => present_value(source, node, page, style),
        Root::Definition(node) => present_definition(source, node, page, style),
        Root::Computation(node) => present_computation(source, node, page, style),
    }
    .expect("a presentation within the default ceilings lays out")
}

/// Presents `root` at both pages and pins them: the wide page holds
/// exactly the one-line spelling when that fits it, since no layout costs
/// less than one line within the page; both carry the pinned fidelity;
/// and each matches its golden file, which ends in a line feed.
///
/// # Specification
/// - requires: a nonempty fixture key with no path separator, and a flat
///   spelling without a line ending or tab. The source fits default ceilings.
/// - ensures: both pages match their files and expected fidelity; a spelling
///   that fits the wide page appears there unchanged.
/// - provides: independent byte-for-byte layout observations.
/// - panics: on a layout refusal, unreadable golden or mismatched observation.
///
/// # Adequacy
/// - hypothesis: L3 — finite narrow and wide arrow, bracket and control-string
///   fixtures expose wrong breaks, omitted escapes and changed fidelity.
///   Filesystem failure and arbitrary fixture keys are not exercised.
/// - witness: `tests::goldens::arrow_chain_breaks_before_each_continuation`
/// - witness: `tests::goldens::pair_of_injections_pins_sum_notation`
/// - witness: `tests::goldens::string_controls_stay_in_one_escaped_literal`
#[spec(requires: !pinned.name.is_empty()
        && !pinned.name.contains(['/', '\\']) && !pinned.flat.contains(['\r', '\n', '\t'])
    )]
fn pin(
    source: &CoreSource<'_>,
    root: Root,
    pinned: Pinned<'_>,
)
{
    pin_in(source, root, pinned, Form::Explicit);
}

/// As [`pin`], in `form`.
///
/// # Specification
/// - requires: as [`pin`].
/// - ensures: as [`pin`], each page in `form`.
/// - provides: golden pairs of the sugared form.
/// - panics: as [`pin`].
///
/// # Adequacy
/// - hypothesis: L3 — as [`pin`].
/// - witness: `tests::goldens::the_sugared_form_breaks_its_infix_and_lists_at_the_narrow_page`
#[spec(requires: !pinned.name.is_empty()
        && !pinned.name.contains(['/', '\\']) && !pinned.flat.contains(['\r', '\n', '\t'])
    )]
fn pin_in(
    source: &CoreSource<'_>,
    root: Root,
    pinned: Pinned<'_>,
    form: Form,
)
{
    let at_narrow = presented_in(source, root, narrow(), form);
    let at_wide = presented_in(source, root, wide(), form);
    if u32::try_from(pinned.flat.chars().count())
        .is_ok_and(|width| PageWidth::from(width) <= wide())
    {
        assert_eq!(
            at_wide.as_ref(),
            pinned.flat,
            "{}: the wide page holds the one-line spelling",
            pinned.name
        );
    }
    assert_eq!(
        (at_narrow.fidelity(), at_wide.fidelity()),
        (pinned.fidelity, pinned.fidelity),
        "{}: both pages carry the fidelity",
        pinned.name
    );
    let directory = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/golden");
    expect_file![directory.join(format!("{}.narrow.txt", pinned.name))]
        .assert_eq(&format!("{at_narrow}\n"));
    expect_file![directory.join(format!("{}.wide.txt", pinned.name))]
        .assert_eq(&format!("{at_wide}\n"));
}

/// The wide-page spelling and fidelity of `root`.
///
/// # Specification
/// - requires: the fixture fits the default presentation ceilings.
/// - ensures: wide-page text contains no carriage return or tab, and carries
///   the presentation's node-derived fidelity.
/// - provides: an observation independent of the golden-file helper.
/// - panics: if presentation refuses.
///
/// # Adequacy
/// - hypothesis: L3 — exact type, literal and malformed-source observations
///   distinguish wrong spelling and fidelity. Other page widths are outside
///   this wide-page helper's evidence.
/// - witness: `tests::goldens::every_type_former_spells_as_the_grammar_writes_it`
/// - witness: `tests::goldens::every_value_leaf_spells_as_the_surface_writes_it`
/// - witness: `tests::goldens::misplaced_and_unreadable_nodes_spell_unknown`
#[spec(ensures: |ref ret| !ret.0.contains(['\r', '\t']))]
fn spelled<S>(
    source: &S,
    root: Root,
) -> (String, Fidelity)
where
    S: Source<Node = CoreNode>,
{
    let presentation = presented(source, root, wide());
    (presentation.to_string(), presentation.fidelity())
}

/// `value` evaluated and read back with every unfolding spent: the
/// normal form evaluation hands a reader, minted afresh.
///
/// # Specification
/// - requires: a held closed value whose evaluation and unfolding readback fit
///   4,096 fuel steps and the fixture arena.
/// - ensures: a live core value handle denoting the fixture's normal form.
/// - provides: the values the concrete reader sees after normalization.
/// - panics: if evaluation or readback refuses.
///
/// # Adequacy
/// - hypothesis: L3 — the finite literal, pair, injection and thunk fixtures
///   observe their evaluated presentation. Dangling inputs, fuel exhaustion and
///   arbitrary closed values are outside this fixture helper's domain.
/// - witness: `tests::goldens::every_value_leaf_spells_as_the_surface_writes_it`
/// - witness: `tests::goldens::pair_of_injections_pins_sum_notation`
/// - witness: `tests::goldens::record_value_breaks_fields_at_the_narrow_page`
#[spec(
        requires: core.value(value).is_some(),
        ensures: |ret| matches!(ret, CoreNode::Value(id) if core.value(id).is_some()),
    )]
fn normal_form(
    core: &mut CoreArena,
    value: ValueId,
) -> CoreNode
{
    let chain = LoweredChain::new();
    let environment = DefinitionalEnvironment::new();
    let definitions = Definitions::new(&chain, &environment, environment.root());
    let fuel = Fuel::from(4_096_u32);
    let mut domain = DomainArena::new();
    let evaluated =
        eval_value(core, &mut domain, definitions, fuel, value).expect("a closed value evaluates");
    let read = readback_value(
        core,
        &mut domain,
        definitions,
        ReadbackMode::Unfolding,
        fuel,
        evaluated,
    )
    .expect("a closed value reads back");
    CoreNode::Value(read)
}

/// Text a fixture writes: digits, string content, or an expected
/// spelling.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
struct Written(&'static str);

/// The integer literal of the decimal `digits`, with `sign`.
///
/// # Specification
/// - requires: nonempty ASCII decimal digits and room in the fixture arena.
/// - ensures: a held integer literal with canonical magnitude; a zero magnitude
///   is non-negative, otherwise the supplied sign is retained.
/// - provides: concrete signed literals for presentation observations.
/// - panics: if decimal construction or arena allocation refuses.
///
/// # Adequacy
/// - hypothesis: L3 — signed integer and injection fixtures observe the stored
///   literal through exact presentation. Padded digits, negative zero and
///   malformed decimal input are outside these fixtures.
/// - witness: `tests::goldens::every_value_leaf_spells_as_the_surface_writes_it`
/// - witness: `tests::goldens::pair_of_injections_pins_sum_notation`
#[spec(
        requires: !digits.0.is_empty() && digits.0.bytes().all(|byte| byte.is_ascii_digit()),
        ensures: |ret| match core.value(ret) {
            Some(&gandr_core_term::Value::Literal(Literal::Integer(ref integer))) => {
                let canonical = digits.0.trim_start_matches('0');
                integer.magnitude().as_ref() == if canonical.is_empty() { "0" } else { canonical }
                    && integer.sign() == if canonical.is_empty() { Sign::NonNegative } else { sign }
            },
            _ => false,
        },
    )]
fn integer(
    core: &mut CoreArena,
    sign: Sign,
    digits: Written,
) -> ValueId
{
    let magnitude = Magnitude::from_decimal_text(digits.0.into()).expect("decimal digits");
    core.value_literal(Literal::Integer(IntegerLiteral::new(sign, magnitude)))
}

/// The string literal holding `content`.
///
/// # Specification
/// trivial.
fn text(
    core: &mut CoreArena,
    content: Written,
) -> ValueId
{
    core.value_literal(Literal::Text(StringLiteral::new(content.0.into())))
}

/// The value universe at level zero, `Type`.
///
/// # Specification
/// trivial.
fn small_universe(core: &mut CoreArena) -> ValueTypeId
{
    core.value_type_universe(Sort::Ground(GroundSort::Value), Level::zero())
}

/// The type the intuitionistic variable `index` denotes, read at level
/// zero.
///
/// # Specification
/// - requires: room for the variable and its decoding type in the fixture
///   arena.
/// - ensures: an element type at level zero whose code is the intuitionistic
///   variable at the supplied de Bruijn index.
/// - provides: dependent types referring to their enclosing fixture binders.
/// - panics: if arena allocation refuses.
///
/// # Adequacy
/// - hypothesis: L3 — nested dependent arrows and static abstractions observe
///   the correct binder reference, distinguishing shifted indices and the wrong
///   variable zone. Other level targets are not fixture inputs.
/// - witness: `tests::goldens::long_dependent_function_type_breaks_at_the_narrow_page`
/// - witness: `tests::goldens::a_binder_skips_the_names_the_type_mentions`
/// - witness: `tests::goldens::static_operators_spell_as_the_grammar_writes_them`
#[spec(ensures: |ret| matches!(core.value_type(ret),
        Some(&gandr_core_term::ValueType::Element { code, .. }) if matches!(core.value(code),
            Some(&gandr_core_term::Value::Variable { zone: Zone::Intuitionistic, index: actual }) if actual == index)
    ))]
fn bound(
    core: &mut CoreArena,
    index: DeBruijnIndex,
) -> ValueTypeId
{
    let code = core.value_variable(Zone::Intuitionistic, index);
    core.value_type_element(code, Level::zero())
}

/// A row of a hand-built table.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
struct Row(usize);

/// A source over hand-built rows, malformed at will: a child of the wrong
/// sort, a dangling row, a cycle.
#[repr(transparent)]
struct Table(Vec<Former<'static, Row>>);

impl Source for Table
{
    type Node = Row;

    /// The row's former, or unreadable past the table.
    ///
    /// # Specification
    /// - requires: nothing; dangling rows are admissible.
    /// - ensures: the stored former at a held row, unreadable beyond the table.
    /// - provides: deliberately malformed graphs for the public reader.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — misplaced children, an empty table, a dangling child
    ///   and a cycle distinguish shifted lookup and fabricated formers. Other
    ///   hand-built graphs are outside the finite malformed-source fixtures.
    /// - witness: `tests::goldens::misplaced_and_unreadable_nodes_spell_unknown`
    #[spec(ensures: |ret| self.0.get(node.0).map_or(
            matches!(ret, Former::Unreadable(Unreadable::Dangling)),
            |held| core::mem::discriminant(held) == core::mem::discriminant(&ret),
        ))]
    fn read(
        &self,
        node: Row,
    ) -> Former<'_, Row>
    {
        self.0
            .get(node.0)
            .copied()
            .unwrap_or(Former::Unreadable(Unreadable::Dangling))
    }

    /// No component: a row holds its former alone, so a product or a sum
    /// the table holds has every component missing.
    ///
    /// # Specification
    /// trivial.
    fn component(
        &self,
        _node: Row,
        _index: Component,
    ) -> Option<Row>
    {
        None
    }

    /// No label: a row holds its former alone, so a record the table
    /// holds has every label missing.
    ///
    /// # Specification
    /// trivial.
    fn label(
        &self,
        _node: Row,
        _index: Component,
    ) -> Option<Name<'_>>
    {
        None
    }
}

/// How a table's first row is read.
#[derive(Clone, Copy, Debug)]
enum Reading
{
    /// As a type, through [`present_type`].
    AsType,
    /// As a value, through [`present_value`].
    AsValue,
}

/// The wide spelling of the table's first row, read as `reading` says.
///
/// # Specification
/// - requires: the finite fixture's layout fits default ceilings.
/// - ensures: the first row is presented in the requested position; text
///   contains no carriage return or tab and reports node-derived fidelity.
/// - provides: exact observations over deliberately malformed sources.
/// - panics: if layout refuses.
///
/// # Adequacy
/// - hypothesis: L3 — type/value misplacement, missing rows and a cycle observe
///   position checking and approximation. Layout-meter exhaustion is outside
///   this helper's finite fixtures.
/// - witness: `tests::goldens::misplaced_and_unreadable_nodes_spell_unknown`
#[spec(ensures: |ref ret| !ret.0.contains(['\r', '\t']))]
fn table_spelling(
    rows: Vec<Former<'static, Row>>,
    reading: Reading,
) -> (String, Fidelity)
{
    let table = Table(rows);
    let presentation = match reading {
        Reading::AsType => present_type(&table, Row(0), wide(), Form::Explicit.into()),
        Reading::AsValue => present_value(&table, Row(0), wide(), Form::Explicit.into()),
    }
    .expect("a table presentation lays out");
    (presentation.to_string(), presentation.fidelity())
}

/// The approximate spelling `text`.
///
/// # Specification
/// trivial.
fn approximate(text: Written) -> (String, Fidelity)
{
    (text.0.into(), Fidelity::Approximate)
}

/// The faithful spelling `text`.
///
/// # Specification
/// trivial.
fn faithful(text: Written) -> (String, Fidelity)
{
    (text.0.into(), Fidelity::Faithful)
}

/// A small dependent arrow stays on one line at both pages: the binder,
/// its universe, and a codomain that reads the binder by its name.
#[test]
fn dependent_function_type_breaks_before_codomain()
{
    let mut core = CoreArena::new();
    let universe = small_universe(&mut core);
    let element = bound(&mut core, DeBruijnIndex::from(0_u32));
    let returner = core.comp_type_returner(element);
    let pi = core.comp_type_pi(universe, returner);
    pin(
        &CoreSource::new(&core, &[]),
        Root::Type(CoreNode::CompType(pi)),
        Pinned {
            name: "pi_dependent",
            flat: "(a : Type) -> -F a",
            fidelity: Fidelity::Faithful,
        },
    );
}

/// Two dependent arrows over an application's type break after the
/// arrows at the narrow page, each continuation two columns in, the
/// binders named in order and read by the codomain.
#[test]
fn long_dependent_function_type_breaks_at_the_narrow_page()
{
    let mut core = CoreArena::new();
    let universe = small_universe(&mut core);
    let outer = bound(&mut core, DeBruijnIndex::from(1_u32));
    let inner = bound(&mut core, DeBruijnIndex::from(0_u32));
    let returns_inner = core.comp_type_returner(inner);
    let function = core.comp_type_arrow(outer, returns_inner);
    let suspended = core.value_type_thunk(function);
    let applied = core.comp_type_arrow(outer, returns_inner);
    let body = core.comp_type_arrow(suspended, applied);
    let pi_inner = core.comp_type_pi(universe, body);
    let pi_outer = core.comp_type_pi(universe, pi_inner);
    pin(
        &CoreSource::new(&core, &[]),
        Root::Type(CoreNode::CompType(pi_outer)),
        Pinned {
            name: "pi_long",
            flat: "(a : Type) -> (b : Type) -> +U (a -> -F b) -> a -> -F b",
            fidelity: Fidelity::Faithful,
        },
    );
}

/// An arrow chain is right-associative and written without parentheses.
#[test]
fn arrow_chain_breaks_before_each_continuation()
{
    let mut core = CoreArena::new();
    let integer = core.value_type_base(BaseType::Integer);
    let string = core.value_type_base(BaseType::String);
    let unit = core.value_type_unit();
    let returns_unit = core.comp_type_returner(unit);
    let inner = core.comp_type_arrow(string, returns_unit);
    let chain = core.comp_type_arrow(integer, inner);
    pin(
        &CoreSource::new(&core, &[]),
        Root::Type(CoreNode::CompType(chain)),
        Pinned {
            name: "arrow_chain",
            flat: "Integer -> String -> -F Unit",
            fidelity: Fidelity::Faithful,
        },
    );
}

/// A string holding a line feed, a tab, a quote and a backslash stays one
/// escaped literal at both pages.
#[test]
fn string_controls_stay_in_one_escaped_literal()
{
    let mut core = CoreArena::new();
    let literal = text(&mut core, Written("line\n\t\"\\tail"));
    let read = normal_form(&mut core, literal);
    pin(&CoreSource::new(&core, &[]), Root::Value(read), Pinned {
        name: "escaped_string",
        flat: "\"line\\n\\t\\\"\\\\tail\"",
        fidelity: Fidelity::Faithful,
    });
}

/// A pair of a left and a right injection pins the pair and the sum
/// notation together.
#[test]
fn pair_of_injections_pins_sum_notation()
{
    let mut core = CoreArena::new();
    let one = integer(&mut core, Sign::NonNegative, Written("1"));
    let two = text(&mut core, Written("two"));
    let left = core.value_injection(Side::Left.into(), one);
    let right = core.value_injection(Side::Right.into(), two);
    let pair = core.value_tuple(&[left, right]);
    let read = normal_form(&mut core, pair);
    pin(&CoreSource::new(&core, &[]), Root::Value(read), Pinned {
        name: "pair_injections",
        flat: "#{+{.0 = 1}, +{.1 = \"two\"}}",
        fidelity: Fidelity::Faithful,
    });
}

/// A value nested past the depth limit is its outer formers around one
/// `<deep>` leaf, not a bare `<deep>`, and the presentation says it is
/// approximate.
#[test]
fn beyond_the_depth_limit_renders_deep()
{
    let limit = usize::try_from(u32::from(DEPTH_LIMIT)).expect("the limit fits a usize");
    let mut core = CoreArena::new();
    let mut value = core.value_unit();
    for _ in 0 .. limit.saturating_add(8) {
        value = core.value_injection(Side::Left.into(), value);
    }
    let read = normal_form(&mut core, value);
    let flat = format!("{}<deep>{}", "+{.0 = ".repeat(limit), "}".repeat(limit));
    pin(&CoreSource::new(&core, &[]), Root::Value(read), Pinned {
        name: "deep_value",
        flat: flat.as_str(),
        fidelity: Fidelity::Approximate,
    });
}

/// A record too long for the narrow page breaks after a comma, its
/// continuation two columns in, its fields in label order whatever order
/// they were given in.
#[test]
fn record_value_breaks_fields_at_the_narrow_page()
{
    let mut core = CoreArena::new();
    let machine = text(&mut core, Written("analytical engine"));
    let name = text(&mut core, Written("ada lovelace"));
    let year = integer(&mut core, Sign::NonNegative, Written("1843"));
    let record = core.value_record(BTreeMap::from([
        (FieldLabel::from(String::from("year")), year),
        (FieldLabel::from(String::from("name")), name),
        (FieldLabel::from(String::from("engine")), machine),
    ]));
    let read = normal_form(&mut core, record);
    pin(&CoreSource::new(&core, &[]), Root::Value(read), Pinned {
        name: "record_value",
        flat: "#{.engine = \"analytical engine\", .name = \"ada lovelace\", .year = 1843}",
        fidelity: Fidelity::Faithful,
    });
}

/// At zero columns, the inline space and the two-column indentation both
/// exceed the computation width; their choice keeps the broken separator.
#[test]
fn doubly_tainted_pair_keeps_the_broken_separator()
{
    let mut core = CoreArena::new();
    let first = text(&mut core, Written("abcdefghijklmnopq"));
    let second = text(&mut core, Written("rstuvwxyzabcdefgh"));
    let pair = core.value_tuple(&[first, second]);
    let read = normal_form(&mut core, pair);
    let presentation = presented(
        &CoreSource::new(&core, &[]),
        Root::Value(read),
        PageWidth::from(0_u32),
    );
    assert_eq!(presentation.fidelity(), Fidelity::Faithful);
    expect_file!["golden/tainted_pair.zero.txt"].assert_eq(&format!("{presentation}\n"));
}

/// A nominal type without arguments is its bare name at both pages: the
/// prior nullary declared data, carried by the fragment as an abstract
/// type.
#[test]
fn nullary_declared_data_uses_its_bare_name()
{
    let names = [Name::from("Celsius")];
    let mut core = CoreArena::new();
    let celsius = core.value_type_abstract(ConstantIndex::from(0_usize));
    pin(
        &CoreSource::new(&core, &names),
        Root::Type(CoreNode::ValueType(celsius)),
        Pinned {
            name: "data_nullary",
            flat: "Celsius",
            fidelity: Fidelity::Faithful,
        },
    );
}

/// A codata family is its name applied to its arguments, and its bare name
/// with none; a thunk of one is written `+U` before it.
#[test]
fn a_codata_family_spells_as_its_name_applied()
{
    let names = [Name::from("Stream"), Name::from("Spot")];
    let mut core = CoreArena::new();
    let integer = core.value_type_base(BaseType::Integer);
    let code = core.value_quote(integer);
    let stream = core.comp_type_codata(ConstantIndex::from(0_usize), Vec::from([code]));
    let spot = core.comp_type_codata(ConstantIndex::from(1_usize), Vec::new());
    let thunk = core.value_type_thunk(stream);
    let source = CoreSource::new(&core, &names);
    for (root, spelling) in [
        (CoreNode::CompType(stream), "Stream(Integer)"),
        (CoreNode::CompType(spot), "Spot"),
        (CoreNode::ValueType(thunk), "+U Stream(Integer)"),
    ] {
        assert_eq!(
            spelled(&source, Root::Type(root)),
            faithful(Written(spelling)),
            "{root:?} spells as its family applied"
        );
    }
}

/// A product or a sum of any arity from one spells its components between
/// its braces, a nested product or sum one component among them; the
/// 0-ary product and sum spell `Unit` and `Void`, and the sum of two units
/// `Bool`.
#[test]
fn n_ary_products_and_sums_spell_between_their_braces()
{
    let mut core = CoreArena::new();
    let integer = core.value_type_base(BaseType::Integer);
    let string = core.value_type_base(BaseType::String);
    let unit = core.value_type_product(&[]);
    let void = core.value_type_sum(&[]);
    let boolean = core.value_type_sum(&[unit, unit]);
    let lonely = core.value_type_product(&[integer]);
    let only = core.value_type_sum(&[integer]);
    let triple = core.value_type_product(&[integer, string, unit]);
    let choice = core.value_type_sum(&[integer, string, void]);
    let pair = core.value_type_product(&[integer, string]);
    let nested = core.value_type_product(&[pair, integer, pair]);
    let either = core.value_type_sum(&[integer, string]);
    let mixed = core.value_type_sum(&[pair, either, triple]);
    let flags = core.value_type_product(&[boolean, boolean]);
    let not_bool = core.value_type_sum(&[unit, integer]);
    let returns_choice = core.comp_type_returner(choice);
    let source = CoreSource::new(&core, &[]);
    for (root, spelling) in [
        (CoreNode::ValueType(void), "Void"),
        (CoreNode::ValueType(boolean), "Bool"),
        (CoreNode::ValueType(lonely), "#{Integer}"),
        (CoreNode::ValueType(only), "+{Integer}"),
        (CoreNode::ValueType(triple), "#{Integer, String, Unit}"),
        (CoreNode::ValueType(choice), "+{Integer, String, Void}"),
        (
            CoreNode::ValueType(nested),
            "#{#{Integer, String}, Integer, #{Integer, String}}",
        ),
        (
            CoreNode::ValueType(mixed),
            "+{#{Integer, String}, +{Integer, String}, #{Integer, String, Unit}}",
        ),
        (CoreNode::ValueType(flags), "#{Bool, Bool}"),
        (CoreNode::ValueType(not_bool), "+{Unit, Integer}"),
        (
            CoreNode::CompType(returns_choice),
            "-F +{Integer, String, Void}",
        ),
    ] {
        assert_eq!(
            spelled(&source, Root::Type(root)),
            faithful(Written(spelling)),
            "{root:?} spells between its braces"
        );
    }
}

/// A session type spells its protocol as the grammar writes it, each
/// payload where its send or receive reads it, parenthesized past an
/// atom; a state inside a recursion unfolds its binder once, so the
/// spelling stays closed; a returner over a session type parenthesizes
/// it as it does an arrow.
#[test]
fn session_types_spell_their_protocol_and_payloads()
{
    use gandr_core_term::session::PayloadCount;
    use gandr_core_term::session::PayloadSlot;
    use gandr_core_term::session::Protocol;
    use gandr_core_term::session::ProtocolState;
    use gandr_core_term::session::ProtocolSyntax;
    use gandr_core_term::session::RecursionIndex;
    use gandr_core_term::session::SessionType;
    let mut core = CoreArena::new();
    let integer = core.value_type_base(BaseType::Integer);
    let string = core.value_type_base(BaseType::String);
    let unit = core.value_type_unit();
    let returner = core.comp_type_returner(unit);
    let suspended = core.value_type_thunk(returner);
    let state = ProtocolState::from;
    let label = |text: &str| FieldLabel::from(String::from(text));
    // ?A. mu t. +{handoff : !C. end, report : !B. &{next : t, retire : end}}
    let protocol = Arc::new(
        Protocol::new(
            alloc::vec![
                ProtocolSyntax::Receive {
                    payload: PayloadSlot::from(0_usize),
                    next: state(1),
                },
                ProtocolSyntax::Mu(state(2)),
                ProtocolSyntax::Select(BTreeMap::from([
                    (label("handoff"), state(6)),
                    (label("report"), state(3)),
                ])),
                ProtocolSyntax::Send {
                    payload: PayloadSlot::from(1_usize),
                    next: state(4),
                },
                ProtocolSyntax::Offer(BTreeMap::from([
                    (label("next"), state(5)),
                    (label("retire"), state(7)),
                ])),
                ProtocolSyntax::Recur(RecursionIndex::from(0_usize)),
                ProtocolSyntax::Send {
                    payload: PayloadSlot::from(2_usize),
                    next: state(8),
                },
                ProtocolSyntax::End,
                ProtocolSyntax::End,
            ],
            state(0),
            PayloadCount::from(3_usize),
        )
        .expect("a contractive protocol"),
    );
    let seat = SessionType::new(
        Arc::clone(&protocol),
        Arc::from([integer, string, suspended]),
    )
    .expect("three payloads");
    let inside = seat.at(state(4)).expect("the offer after a report");
    let ended = SessionType::new(
        Arc::new(
            Protocol::new(
                alloc::vec![ProtocolSyntax::End],
                state(0),
                PayloadCount::default(),
            )
            .expect("end"),
        ),
        Arc::from([]),
    )
    .expect("no payloads");
    let peer = core.value_type_session(seat.dual());
    let seat = core.value_type_session(seat);
    let inside = core.value_type_session(inside);
    let ended = core.value_type_session(ended);
    let returns_seat = core.comp_type_returner(seat);
    let returns_end = core.comp_type_returner(ended);
    let source = CoreSource::new(&core, &[]);
    for (root, spelling) in [
        (
            CoreNode::ValueType(seat),
            "?Integer. mu t. +{handoff : !(+U (-F Unit)). end, report : !String. &{next : t, retire : end}}",
        ),
        (
            CoreNode::ValueType(peer),
            "!Integer. mu t. &{handoff : ?(+U (-F Unit)). end, report : ?String. +{next : t, retire : end}}",
        ),
        (
            CoreNode::ValueType(inside),
            "&{next : mu t. +{handoff : !(+U (-F Unit)). end, report : !String. &{next : t, retire : end}}, retire : end}",
        ),
        (CoreNode::ValueType(ended), "end"),
        (
            CoreNode::CompType(returns_seat),
            "-F (?Integer. mu t. +{handoff : !(+U (-F Unit)). end, report : !String. &{next : t, retire : end}})",
        ),
        (CoreNode::CompType(returns_end), "-F end"),
    ] {
        assert_eq!(
            spelled(&source, Root::Type(root)),
            faithful(Written(spelling)),
            "{root:?} spells its protocol"
        );
    }
}

/// A fork's child and an offer's arm keep the exit they end in: the surface
/// reads a value bare there as a value where a computation is expected
/// (#815).
#[test]
fn a_fork_and_an_offer_keep_the_exits_they_end_in_815()
{
    use gandr_core_term::session::PayloadCount;
    use gandr_core_term::session::Protocol;
    use gandr_core_term::session::ProtocolState;
    use gandr_core_term::session::ProtocolSyntax;
    use gandr_core_term::session::SessionAction;
    use gandr_core_term::session::SessionType;
    let mut core = CoreArena::new();
    let ended = SessionType::new(
        Arc::new(
            Protocol::new(
                alloc::vec![ProtocolSyntax::End],
                ProtocolState::from(0),
                PayloadCount::default(),
            )
            .expect("end"),
        ),
        Arc::from([]),
    )
    .expect("no payloads");
    let protocol = core.value_type_session(ended);
    let unit = core.value_unit();
    let returns_unit = core.computation_return(unit);
    let endpoint = DeBruijnIndex::from(0_u32);
    let closed = core.computation_session(SessionAction::Close { endpoint });
    let offered = core.computation_session(SessionAction::Offer {
        endpoint,
        arms: BTreeMap::from([
            (FieldLabel::from(String::from("next")), closed),
            (FieldLabel::from(String::from("retire")), returns_unit),
        ]),
    });
    let fork = |core: &mut CoreArena, child| {
        core.computation_session(SessionAction::Fork {
            protocol,
            child,
            parent: closed,
        })
    };
    let returned = fork(&mut core, returns_unit);
    let offering = fork(&mut core, offered);
    let source = CoreSource::new(&core, &[]);
    let body = |id| Root::Computation(CoreNode::Computation(id));
    assert_eq!(
        spelled(&source, body(returned)),
        faithful(Written("fork (a : end) { pure unit } as a ; close(a)"))
    );
    assert_eq!(
        spelled(&source, body(offering)),
        faithful(Written(
            "fork (a : end) { offer(a) { next => close(a), retire => pure unit } } as a ; close(a)"
        ))
    );
}

/// A tuple of any arity from one spells its components between `#{` and
/// `}`, a nested tuple one component among them; an injection spells the
/// summand it enters, the third as readily as the first.
#[test]
fn n_ary_tuples_and_injections_spell_between_their_braces()
{
    let mut core = CoreArena::new();
    let one = integer(&mut core, Sign::NonNegative, Written("1"));
    let two = text(&mut core, Written("two"));
    let unit = core.value_unit();
    let single = core.value_tuple(&[one]);
    let triple = core.value_tuple(&[one, two, unit]);
    let pair = core.value_tuple(&[one, two]);
    let nested = core.value_tuple(&[single, pair]);
    let third = core.value_injection(Summand::from(2_usize), one);
    let values = [single, triple, nested, third].map(|value| normal_form(&mut core, value));
    let source = CoreSource::new(&core, &[]);
    for (root, expected) in values.into_iter().zip([
        "#{1}",
        "#{1, \"two\", unit}",
        "#{#{1}, #{1, \"two\"}}",
        "+{.2 = 1}",
    ]) {
        assert_eq!(
            spelled(&source, Root::Value(root)),
            faithful(Written(expected)),
            "{root:?} spells between its braces"
        );
    }
}

/// The sugared form writes the value-function alias for a thunked chain
/// of non-dependent arrows ending in a pure returner, at no, one and more
/// domains, and the thunk over any other computation type; the infix
/// product, sum and lazy product at two components or more, every operand
/// tighter than the chain, so an inner chain keeps its parentheses; and the
/// tuple at two components or more. A product, sum, lazy product and tuple
/// of fewer components keep their braces, and the explicit form writes every
/// one as the core holds it.
#[test]
fn the_sugared_form_writes_every_sugar_its_shape_admits()
{
    let mut core = CoreArena::new();
    let one = integer(&mut core, Sign::NonNegative, Written("1"));
    let integer = core.value_type_base(BaseType::Integer);
    let string = core.value_type_base(BaseType::String);
    let unit = core.value_type_unit();
    let returns_integer = core.comp_type_returner(integer);
    let returns_string = core.comp_type_returner(string);
    let returns_unit = core.comp_type_returner(unit);
    let nullary = core.value_type_thunk(returns_integer);
    let unary_arrow = core.comp_type_arrow(integer, returns_string);
    let unary = core.value_type_thunk(unary_arrow);
    let binary_tail = core.comp_type_arrow(string, returns_unit);
    let binary_arrow = core.comp_type_arrow(integer, binary_tail);
    let binary = core.value_type_thunk(binary_arrow);
    let higher_arrow = core.comp_type_arrow(unary, returns_unit);
    let higher = core.value_type_thunk(higher_arrow);
    let returns_unary = core.comp_type_returner(unary);
    let curried_arrow = core.comp_type_arrow(integer, returns_unary);
    let curried = core.value_type_thunk(curried_arrow);
    let universe = small_universe(&mut core);
    let variable = bound(&mut core, DeBruijnIndex::from(0_u32));
    let returns_variable = core.comp_type_returner(variable);
    let dependent_arrow = core.comp_type_pi(universe, returns_variable);
    let dependent = core.value_type_thunk(dependent_arrow);
    let pair = core.value_type_product(&[integer, string]);
    let triple = core.value_type_product(&[integer, string, unit]);
    let lonely = core.value_type_product(&[integer]);
    let nested_pair = core.value_type_product(&[pair, unit]);
    let either = core.value_type_sum(&[integer, string]);
    let only = core.value_type_sum(&[integer]);
    let sum_of_pair = core.value_type_sum(&[pair, unit]);
    let pair_of_sum = core.value_type_product(&[either, unit]);
    let nested_sum = core.value_type_sum(&[either, unit]);
    let boolean = core.value_type_sum(&[unit, unit]);
    let lazy = core.comp_type_with(&[returns_integer, returns_string]);
    let right = core.comp_type_with(&[returns_integer, lazy]);
    let left = core.comp_type_with(&[lazy, returns_unit]);
    let lazy_triple = core.comp_type_with(&[returns_integer, returns_string, returns_unit]);
    let lazy_single = core.comp_type_with(&[returns_integer]);
    let lazy_empty = core.comp_type_with(&[]);
    let paired_domain = core.comp_type_arrow(pair, returns_unit);
    let returns_pair = core.comp_type_returner(pair);
    let returns_either = core.comp_type_returner(either);
    let aliased_pair_arrow = core.comp_type_arrow(pair, returns_either);
    let aliased_pair = core.value_type_thunk(aliased_pair_arrow);
    let two = text(&mut core, Written("two"));
    let single = core.value_tuple(&[one]);
    let tuple = core.value_tuple(&[one, two]);
    let nested_tuple = core.value_tuple(&[one, tuple]);
    let values = [single, tuple, nested_tuple].map(|value| normal_form(&mut core, value));
    let source = CoreSource::new(&core, &[]);
    let types = [
        (nullary, "() => Integer", "+U (-F Integer)"),
        (unary, "Integer => String", "+U (Integer -> -F String)"),
        (
            binary,
            "(Integer, String) => Unit",
            "+U (Integer -> String -> -F Unit)",
        ),
        (
            higher,
            "(Integer => String) => Unit",
            "+U (+U (Integer -> -F String) -> -F Unit)",
        ),
        (
            curried,
            "Integer => Integer => String",
            "+U (Integer -> -F (+U (Integer -> -F String)))",
        ),
        (dependent, "(a : Type) => a", "+U ((a : Type) -> -F a)"),
        (pair, "Integer * String", "#{Integer, String}"),
        (
            triple,
            "Integer * String * Unit",
            "#{Integer, String, Unit}",
        ),
        (lonely, "#{Integer}", "#{Integer}"),
        (
            nested_pair,
            "(Integer * String) * Unit",
            "#{#{Integer, String}, Unit}",
        ),
        (either, "Integer + String", "+{Integer, String}"),
        (only, "+{Integer}", "+{Integer}"),
        (
            sum_of_pair,
            "Integer * String + Unit",
            "+{#{Integer, String}, Unit}",
        ),
        (
            pair_of_sum,
            "(Integer + String) * Unit",
            "#{+{Integer, String}, Unit}",
        ),
        (
            nested_sum,
            "(Integer + String) + Unit",
            "+{+{Integer, String}, Unit}",
        ),
        (boolean, "Bool", "Bool"),
        (
            aliased_pair,
            "Integer * String => Integer + String",
            "+U (#{Integer, String} -> -F +{Integer, String})",
        ),
    ]
    .map(|(root, sugared, explicit)| (CoreNode::ValueType(root), sugared, explicit));
    let computations = [
        (lazy, "-F Integer & -F String", "&{-F Integer, -F String}"),
        (
            right,
            "-F Integer & (-F Integer & -F String)",
            "&{-F Integer, &{-F Integer, -F String}}",
        ),
        (
            left,
            "(-F Integer & -F String) & -F Unit",
            "&{&{-F Integer, -F String}, -F Unit}",
        ),
        (
            lazy_triple,
            "-F Integer & -F String & -F Unit",
            "&{-F Integer, -F String, -F Unit}",
        ),
        (lazy_single, "&{-F Integer}", "&{-F Integer}"),
        (lazy_empty, "&{}", "&{}"),
        (
            paired_domain,
            "Integer * String -> -F Unit",
            "#{Integer, String} -> -F Unit",
        ),
        (
            returns_pair,
            "-F (Integer * String)",
            "-F #{Integer, String}",
        ),
    ]
    .map(|(root, sugared, explicit)| (CoreNode::CompType(root), sugared, explicit));
    for (root, sugared, explicit) in types.into_iter().chain(computations) {
        for (form, expected) in [(Form::Sugared, sugared), (Form::Explicit, explicit)] {
            let presented = presented_in(&source, Root::Type(root), wide(), form);
            assert_eq!(
                (presented.as_ref(), presented.fidelity()),
                (expected, Fidelity::Faithful),
                "{root:?} in the {form:?} form"
            );
        }
    }
    for (root, (sugared, explicit)) in values.into_iter().zip([
        ("#{1}", "#{1}"),
        ("(1, \"two\")", "#{1, \"two\"}"),
        ("(1, (1, \"two\"))", "#{1, #{1, \"two\"}}"),
    ]) {
        for (form, expected) in [(Form::Sugared, sugared), (Form::Explicit, explicit)] {
            let presented = presented_in(&source, Root::Value(root), wide(), form);
            assert_eq!(
                (presented.as_ref(), presented.fidelity()),
                (expected, Fidelity::Faithful),
                "{root:?} in the {form:?} form"
            );
        }
    }
}

/// The sugared form breaks after an infix symbol, after the alias's `=>`
/// and after each comma of its domain list and of a tuple, as the
/// explicit form breaks after an arrow and a comma.
#[test]
fn the_sugared_form_breaks_its_infix_and_lists_at_the_narrow_page()
{
    let mut core = CoreArena::new();
    let integer = core.value_type_base(BaseType::Integer);
    let string = core.value_type_base(BaseType::String);
    let unit = core.value_type_unit();
    let triple = core.value_type_product(&[integer, string, unit]);
    let either = core.value_type_sum(&[string, unit]);
    let returns_either = core.comp_type_returner(either);
    let tail = core.comp_type_arrow(triple, returns_either);
    let chain = core.comp_type_arrow(integer, tail);
    let alias = core.value_type_thunk(chain);
    pin_in(
        &CoreSource::new(&core, &[]),
        Root::Type(CoreNode::ValueType(alias)),
        Pinned {
            name: "sugared_alias",
            flat: "(Integer, Integer * String * Unit) => String + Unit",
            fidelity: Fidelity::Faithful,
        },
        Form::Sugared,
    );
}

/// A quoted type stands where an expression is read: the sugared form
/// takes the alias there only over one bare domain, and writes any other
/// as the thunk it stands for, which reads back (#815).
#[test]
fn a_quoted_alias_is_written_as_an_expression_reads_it_815()
{
    let mut core = CoreArena::new();
    let integer = core.value_type_base(BaseType::Integer);
    let string = core.value_type_base(BaseType::String);
    let returns_integer = core.comp_type_returner(integer);
    let one = core.comp_type_arrow(integer, returns_integer);
    let two = core.comp_type_arrow(string, one);
    for (body, expected) in [
        (returns_integer, "+U (-F Integer)"),
        (one, "Integer => Integer"),
        (two, "+U (String -> Integer -> -F Integer)"),
    ] {
        let thunked = core.value_type_thunk(body);
        let quoted = core.value_quote(thunked);
        let source = CoreSource::new(&core, &[]);
        let presented = presented_in(
            &source,
            Root::Value(CoreNode::Value(quoted)),
            wide(),
            Form::Sugared,
        );
        assert_eq!(
            (presented.as_ref(), presented.fidelity()),
            (expected, Fidelity::Faithful),
            "a code of {expected}"
        );
        let typed = presented_in(
            &source,
            Root::Type(CoreNode::ValueType(thunked)),
            wide(),
            Form::Sugared,
        );
        assert!(
            typed.as_ref().contains("=>"),
            "a type position keeps the alias: {}",
            typed.as_ref()
        );
    }
}

/// A record type and a record spell each field after its own label, in
/// label order whatever order they were given in; the empty record type
/// is the unit type and the empty record the unit, as the grammar writes
/// them.
#[test]
fn records_spell_their_fields_in_label_order()
{
    let mut core = CoreArena::new();
    let integer_type = core.value_type_base(BaseType::Integer);
    let string_type = core.value_type_base(BaseType::String);
    let record_type = core.value_type_record(BTreeMap::from([
        (FieldLabel::from(String::from("b")), string_type),
        (FieldLabel::from(String::from("a")), integer_type),
    ]));
    let returns_record = core.comp_type_returner(record_type);
    let empty_type = core.value_type_record(BTreeMap::new());
    let one = integer(&mut core, Sign::NonNegative, Written("1"));
    let two = text(&mut core, Written("two"));
    let record = core.value_record(BTreeMap::from([
        (FieldLabel::from(String::from("b")), two),
        (FieldLabel::from(String::from("a")), one),
    ]));
    let record = normal_form(&mut core, record);
    let empty = core.value_record(BTreeMap::new());
    let source = CoreSource::new(&core, &[]);
    for (root, expected) in [
        (
            Root::Type(CoreNode::ValueType(record_type)),
            faithful(Written("#{a : Integer, b : String}")),
        ),
        (
            Root::Type(CoreNode::CompType(returns_record)),
            faithful(Written("-F #{a : Integer, b : String}")),
        ),
        (
            Root::Value(record),
            faithful(Written("#{.a = 1, .b = \"two\"}")),
        ),
        (
            Root::Type(CoreNode::ValueType(empty_type)),
            faithful(Written("Unit")),
        ),
        (
            Root::Value(CoreNode::Value(empty)),
            faithful(Written("unit")),
        ),
    ] {
        assert_eq!(
            spelled(&source, root),
            expected,
            "{root:?} spells its labels"
        );
    }
}

/// Every value-type and computation-type former of the core spells as the
/// grammar parses it: the two bridges with their operand parenthesized
/// unless atomic, a product, a sum or a lazy product between its braces with
/// any former bare among its entries, the arrow's domain bare up to a
/// bridge, a decode as the code it reads, an abstract type by its name, a
/// family bare when nullary and applied to its arguments otherwise, and a
/// path type over its carrier and both endpoints. A free variable reads
/// its context binder's name, past the binders the type opens itself. A
/// type the source records as a written relation spells as that relation,
/// its operands read off the forward map or the flow's codes; the same
/// record unrecorded spells as the record.
#[test]
fn every_type_former_spells_as_the_grammar_writes_it()
{
    let names = [
        Name::from("Accumulator"),
        Name::from("Carry"),
        Name::from("small"),
        Name::from("Tree"),
        Name::from("List"),
    ];
    let mut core = CoreArena::new();
    let integer = core.value_type_base(BaseType::Integer);
    let string = core.value_type_base(BaseType::String);
    let unit = core.value_type_unit();
    let accumulator = core.value_type_abstract(ConstantIndex::from(0_usize));
    let returns_integer = core.comp_type_returner(integer);
    let thunk = core.value_type_thunk(returns_integer);
    let returns_unit = core.comp_type_returner(unit);
    let suspended_unit = core.value_type_thunk(returns_unit);
    let returns_thunk = core.comp_type_returner(suspended_unit);
    let string_unit = core.value_type_product(&[string, unit]);
    let right_nested = core.value_type_product(&[integer, string_unit]);
    let integer_string = core.value_type_product(&[integer, string]);
    let left_nested = core.value_type_product(&[integer_string, unit]);
    let product_then_sum = core.value_type_sum(&[integer_string, unit]);
    let sum_of_product = core.value_type_sum(&[integer, string_unit]);
    let integer_or_string = core.value_type_sum(&[integer, string]);
    let sum_then_product = core.value_type_product(&[integer_or_string, unit]);
    let string_or_unit = core.value_type_sum(&[string, unit]);
    let sum_chain = core.value_type_sum(&[integer, string_or_unit]);
    let sum_left = core.value_type_sum(&[integer_or_string, unit]);
    let thunk_in_product = core.value_type_product(&[thunk, unit]);
    let sum_domain = core.comp_type_arrow(integer_or_string, returns_unit);
    let function = core.comp_type_arrow(integer, returns_unit);
    let suspended_function = core.value_type_thunk(function);
    let thunk_domain = core.comp_type_arrow(suspended_function, returns_unit);
    let returns_product = core.comp_type_returner(integer_string);
    let quoted = core.value_quote(integer_string);
    let decoded = core.value_type_element(quoted, Level::zero());
    let returns_decoded = core.comp_type_returner(decoded);
    let alias = core.value_constant(ConstantIndex::from(2_usize));
    let named = core.value_type_element(alias, Level::zero());
    let returns_named = core.comp_type_returner(named);
    let quoted_returner = core.value_quote_computation(returns_integer);
    let decoded_returner = core.comp_type_element(quoted_returner, Level::zero());
    let lazy = core.comp_type_with(&[returns_integer, returns_unit]);
    let lazy_chain = core.comp_type_with(&[function, lazy]);
    let suspended_lazy = core.value_type_thunk(lazy);
    let tree = core.value_type_data(ConstantIndex::from(3_usize), Vec::new());
    let integer_code = core.value_quote(integer);
    let list = core.value_type_data(ConstantIndex::from(4_usize), vec![integer_code]);
    let one = self::integer(&mut core, Sign::NonNegative, Written("1"));
    let path = core.value_type_path(list, alias, one);
    let returns_path = core.comp_type_returner(path);
    let flow = core.value_type_flow(list, alias, one);
    let returns_flow = core.comp_type_returner(flow);
    let opened = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let outer = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(1_u32));
    let inner = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(2_u32));
    let between = core.value_type_path(integer, opened, outer);
    let returns_between = core.comp_type_returner(between);
    let over_context = core.comp_type_pi(integer, returns_between);
    let unnamed = core.value_type_path(integer, inner, outer);
    let returns_string = core.comp_type_returner(string);
    let to_string = core.comp_type_arrow(integer, returns_string);
    let forward = core.value_type_thunk(to_string);
    let record = core.value_type_sigma(forward, unit);
    let written = core.value_type_sigma(forward, unit);
    let equivalence = core.value_type_sigma(forward, string_unit);
    let universe = small_universe(&mut core);
    let string_code = core.value_quote(string);
    let directed = core.value_type_flow(universe, integer_code, string_code);
    let mut relations = [
        (record, Relation::Isomorphism),
        (equivalence, Relation::Equivalence),
        (directed, Relation::Flow),
    ];
    relations.sort_unstable_by_key(|&(id, _)| id);
    let source = CoreSource::new(&core, &names);
    for (root, spelling) in [
        (CoreNode::ValueType(integer), "Integer"),
        (CoreNode::ValueType(string), "String"),
        (CoreNode::ValueType(unit), "Unit"),
        (CoreNode::ValueType(accumulator), "Accumulator"),
        (CoreNode::ValueType(thunk), "+U (-F Integer)"),
        (CoreNode::CompType(returns_thunk), "-F (+U (-F Unit))"),
        (
            CoreNode::ValueType(right_nested),
            "#{Integer, #{String, Unit}}",
        ),
        (
            CoreNode::ValueType(left_nested),
            "#{#{Integer, String}, Unit}",
        ),
        (
            CoreNode::ValueType(product_then_sum),
            "+{#{Integer, String}, Unit}",
        ),
        (
            CoreNode::ValueType(sum_of_product),
            "+{Integer, #{String, Unit}}",
        ),
        (
            CoreNode::ValueType(sum_then_product),
            "#{+{Integer, String}, Unit}",
        ),
        (
            CoreNode::ValueType(sum_chain),
            "+{Integer, +{String, Unit}}",
        ),
        (CoreNode::ValueType(sum_left), "+{+{Integer, String}, Unit}"),
        (
            CoreNode::ValueType(thunk_in_product),
            "#{+U (-F Integer), Unit}",
        ),
        (
            CoreNode::CompType(sum_domain),
            "+{Integer, String} -> -F Unit",
        ),
        (
            CoreNode::CompType(thunk_domain),
            "+U (Integer -> -F Unit) -> -F Unit",
        ),
        (CoreNode::CompType(returns_product), "-F #{Integer, String}"),
        (CoreNode::CompType(returns_decoded), "-F #{Integer, String}"),
        (CoreNode::CompType(lazy), "&{-F Integer, -F Unit}"),
        (
            CoreNode::CompType(lazy_chain),
            "&{Integer -> -F Unit, &{-F Integer, -F Unit}}",
        ),
        (
            CoreNode::ValueType(suspended_lazy),
            "+U &{-F Integer, -F Unit}",
        ),
        (CoreNode::CompType(returns_named), "-F small"),
        (CoreNode::CompType(decoded_returner), "-F Integer"),
        (CoreNode::ValueType(tree), "Tree"),
        (CoreNode::ValueType(list), "List(Integer)"),
        (
            CoreNode::CompType(returns_path),
            "-F Path(List(Integer), small, 1)",
        ),
        (
            CoreNode::CompType(returns_flow),
            "-F Flow(List(Integer), small, 1)",
        ),
    ] {
        assert_eq!(
            spelled(&source, Root::Type(root)),
            faithful(Written(spelling)),
            "{root:?} spells as the grammar writes it"
        );
    }
    let context = [Some(Name::from("x")), None, Some(Name::from("y"))];
    let within = CoreSource::new(&core, &names).within(&context);
    assert_eq!(
        spelled(&within, Root::Type(CoreNode::CompType(over_context))),
        faithful(Written("(a : Integer) -> -F Path(Integer, a, y)")),
        "a variable past the opened binder reads its context binder's name"
    );
    assert_eq!(
        spelled(&within, Root::Type(CoreNode::ValueType(unnamed))),
        approximate(Written("Path(Integer, x, ?)")),
        "an unnamed context binder spells `?`"
    );
    for unprintable in ["", "x\ty"] {
        let context = [Some(Name::from(unprintable)), None, Some(Name::from("y"))];
        let within = CoreSource::new(&core, &names).within(&context);
        assert_eq!(
            spelled(&within, Root::Type(CoreNode::ValueType(unnamed))),
            approximate(Written("Path(Integer, ?, ?)")),
            "a context binder named {unprintable:?} spells `?`"
        );
    }
    let related = CoreSource::new(&core, &names).relating(&relations);
    for (root, spelling) in [
        (CoreNode::ValueType(record), "Integer ≅ String"),
        (CoreNode::ValueType(equivalence), "Integer ≃ String"),
        (CoreNode::ValueType(directed), "Integer ⇝ String"),
    ] {
        assert_eq!(
            spelled(&related, Root::Type(root)),
            faithful(Written(spelling)),
            "{root:?} spells as the relation it was written as"
        );
    }
    assert_eq!(
        spelled(&related, Root::Type(CoreNode::ValueType(written))),
        spelled(&source, Root::Type(CoreNode::ValueType(record))),
        "the same record unrecorded spells as the record"
    );
}

/// The wide-page spelling and fidelity of `root` in `spelling`, explicit,
/// with why each `?` was written.
///
/// # Specification
/// trivial.
fn spelled_as<S>(
    source: &S,
    root: Root,
    spelling: Spelling,
) -> ((String, Fidelity), Vec<Unspelled>)
where
    S: Source<Node = CoreNode>,
{
    let presentation = presented_in(source, root, wide(), Style {
        form: Form::Explicit,
        spelling,
    });
    (
        (presentation.to_string(), presentation.fidelity()),
        presentation.unspelled().iter().copied().collect(),
    )
}

/// Each former the grammar writes with a glyph is written in the spelling
/// asked: the relations infix with `≃` and `⇝` or `<~>` and `~~>`, the
/// isomorphism infix with `≅` or as the call `Iso(A, B)`, and a word's
/// letters consed with `∷` or `::` (#782).
#[test]
fn each_glyph_former_is_written_in_the_spelling_asked_782()
{
    let names = [Name::from("Loops")];
    let mut core = CoreArena::new();
    let integer = core.value_type_base(BaseType::Integer);
    let string = core.value_type_base(BaseType::String);
    let unit = core.value_type_unit();
    let string_unit = core.value_type_product(&[string, unit]);
    let returns_string = core.comp_type_returner(string);
    let to_string = core.comp_type_arrow(integer, returns_string);
    let forward = core.value_type_thunk(to_string);
    let record = core.value_type_sigma(forward, unit);
    let equivalence = core.value_type_sigma(forward, string_unit);
    let universe = small_universe(&mut core);
    let integer_code = core.value_quote(integer);
    let string_code = core.value_quote(string);
    let directed = core.value_type_flow(universe, integer_code, string_code);
    let mut relations = [
        (record, Relation::Isomorphism),
        (equivalence, Relation::Equivalence),
        (directed, Relation::Flow),
    ];
    relations.sort_unstable_by_key(|&(id, _)| id);
    let loops = core.value_type_data(ConstantIndex::from(0_usize), Vec::new());
    let nil = core.value_constructor(loops, ConstructorTag::from(0_usize), Vec::new());
    let once = core.value_constructor(loops, ConstructorTag::from(1_usize), vec![nil]);
    let word = core.value_constructor(loops, ConstructorTag::from(1_usize), vec![once]);
    let mut constructors = Constructors::default();
    constructors.words(
        Name::from("Loops"),
        [
            (Name::from("base"), Arity::from(0_usize)),
            (Name::from("loop"), Arity::from(1_usize)),
        ],
        Name::from("base"),
    );
    let source = CoreSource::new(&core, &names)
        .naming(&constructors)
        .relating(&relations);
    for (root, unicode, ascii) in [
        (
            Root::Type(CoreNode::ValueType(record)),
            "Integer ≅ String",
            "Iso(Integer, String)",
        ),
        (
            Root::Type(CoreNode::ValueType(equivalence)),
            "Integer ≃ String",
            "Integer <~> String",
        ),
        (
            Root::Type(CoreNode::ValueType(directed)),
            "Integer ⇝ String",
            "Integer ~~> String",
        ),
        (
            Root::Value(CoreNode::Value(word)),
            "loop ∷ loop ∷ base",
            "loop :: loop :: base",
        ),
    ] {
        for (spelling, expected) in [(Spelling::Unicode, unicode), (Spelling::Ascii, ascii)] {
            assert_eq!(
                spelled_as(&source, root, spelling),
                (faithful(Written(expected)), Vec::new()),
                "{root:?} in {spelling:?}"
            );
        }
    }
}

/// A name holding the prime is written as it stands in Unicode; in ASCII,
/// which has no spelling for the prime, a constant or a context binder so
/// named is written `?`, approximate and recorded primed, and a binder the
/// source named so takes a generated name (#782).
#[test]
fn a_primed_name_has_no_ascii_spelling_782()
{
    let names = [Name::from("f′")];
    let mut core = CoreArena::new();
    let integer = core.value_type_base(BaseType::Integer);
    let constant = core.value_constant(ConstantIndex::from(0_usize));
    let opened = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let outer = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(1_u32));
    let between = core.value_type_path(integer, opened, outer);
    let returns_between = core.comp_type_returner(between);
    let over_context = core.comp_type_pi(integer, returns_between);
    let context = [Some(Name::from("y′"))];
    let arrows = [(over_context, Name::from("n′"))];
    let source = CoreSource::new(&core, &names)
        .within(&context)
        .naming_arrows(&arrows);
    for (root, unicode, ascii) in [
        (
            Root::Value(CoreNode::Value(constant)),
            faithful(Written("f′")),
            approximate(Written("?")),
        ),
        (
            Root::Type(CoreNode::CompType(over_context)),
            faithful(Written("(n′ : Integer) -> -F Path(Integer, n′, y′)")),
            approximate(Written("(a : Integer) -> -F Path(Integer, a, ?)")),
        ),
    ] {
        assert_eq!(
            spelled_as(&source, root, Spelling::Unicode),
            (unicode, Vec::new()),
            "{root:?} in Unicode"
        );
        assert_eq!(
            spelled_as(&source, root, Spelling::Ascii),
            (ascii, vec![Unspelled::Primed]),
            "{root:?} in ASCII"
        );
    }
}

/// Each universe spells its sort and its constant level as the grammar
/// writes them, and a parameter sort or a variable level, which the
/// surface cannot write, is `?`.
#[test]
fn universes_spell_their_sort_and_level()
{
    let mut core = CoreArena::new();
    let value_zero = core.value_type_universe(Sort::Ground(GroundSort::Value), Level::zero());
    let computation_zero =
        core.value_type_universe(Sort::Ground(GroundSort::Computation), Level::zero());
    let value_one = core.value_type_universe(
        Sort::Ground(GroundSort::Value),
        Level::constant(LevelConstant::from(1_u64)),
    );
    let computation_two = core.value_type_universe(
        Sort::Ground(GroundSort::Computation),
        Level::constant(LevelConstant::from(2_u64)),
    );
    let parametric =
        core.value_type_universe(Sort::Parameter(SortParameter::from(0_u32)), Level::zero());
    let variable = core.value_type_universe(
        Sort::Ground(GroundSort::Value),
        Level::var(LevelVar::from(LevelVarIndex::from(0_u32))),
    );
    let source = CoreSource::new(&core, &[]);
    for (root, expected) in [
        (value_zero, faithful(Written("Type"))),
        (computation_zero, faithful(Written("Type[-]"))),
        (value_one, faithful(Written("Type[+, 1]"))),
        (computation_two, faithful(Written("Type[-, 2]"))),
        (parametric, approximate(Written("?"))),
        (variable, approximate(Written("?"))),
    ] {
        assert_eq!(
            spelled(&source, Root::Type(CoreNode::ValueType(root))),
            expected,
            "{root:?} spells its sort and level"
        );
    }
}

/// A dependent arrow's binders take the first names the type does not
/// already spell: an abstract type named `a` moves the first binder to
/// `b` and the next to `c`.
#[test]
fn a_binder_skips_the_names_the_type_mentions()
{
    let names = [Name::from("a")];
    let mut core = CoreArena::new();
    let pi_outer = two_binders(&mut core);
    assert_eq!(
        spelled(
            &CoreSource::new(&core, &names),
            Root::Type(CoreNode::CompType(pi_outer))
        ),
        faithful(Written("(b : Type) -> (c : Type) -> a -> c -> -F b")),
        "the binders skip the abstract type `a`"
    );
}

/// `(x : Type) -> (y : Type) -> a -> y -> -F x`, over the abstract type
/// `a`: two dependent arrows, each binder occurring in the codomain.
///
/// # Specification
/// trivial.
fn two_binders(core: &mut CoreArena) -> CompTypeId
{
    let universe = small_universe(core);
    let abstract_a = core.value_type_abstract(ConstantIndex::from(0_usize));
    let outer = bound(core, DeBruijnIndex::from(1_u32));
    let inner = bound(core, DeBruijnIndex::from(0_u32));
    let returns_outer = core.comp_type_returner(outer);
    let body = core.comp_type_arrow(inner, returns_outer);
    let body = core.comp_type_arrow(abstract_a, body);
    let pi_inner = core.comp_type_pi(universe, body);
    core.comp_type_pi(universe, pi_inner)
}

/// A dependent arrow whose codomain names no binder — what a decode
/// substituting a constant family leaves (#577) — has no spelling of its
/// own: the surface reads `(x : A) -> C` as the plain arrow where `C`
/// does not name `x`, so it is written as that arrow; one whose codomain
/// names its binder keeps it.
#[test]
fn a_dependent_arrow_ignoring_its_binder_spells_as_the_arrow_398()
{
    let names = [Name::from("a")];
    let mut core = CoreArena::new();
    let universe = small_universe(&mut core);
    let abstract_a = core.value_type_abstract(ConstantIndex::from(0_usize));
    let returns_a = core.comp_type_returner(abstract_a);
    let ignoring = core.comp_type_pi(universe, returns_a);
    let own = bound(&mut core, DeBruijnIndex::from(0_u32));
    let returns_own = core.comp_type_returner(own);
    let naming = core.comp_type_pi(universe, returns_own);
    for (root, expected, what) in [
        (ignoring, "Type -> -F a", "a binder no occurrence names"),
        (naming, "(a : Type) -> -F a", "a binder its codomain names"),
    ] {
        assert_eq!(
            spelled(
                &CoreSource::new(&core, &names),
                Root::Type(CoreNode::CompType(root))
            ),
            faithful(Written(expected)),
            "{what}"
        );
    }
}

/// A dependent pair whose second factor names no binder — what a decode
/// reducing its family away leaves (#771) — has no spelling of its own: the
/// surface reads a record whose later field names no earlier one as a
/// record of labels, so it is written as the product it reads as, `A * B`
/// sugared and `#{A, B}` explicit; one whose second factor names its binder
/// keeps the record.
#[test]
fn a_dependent_pair_ignoring_its_binder_spells_as_the_product_771()
{
    let names = [Name::from("a")];
    let mut core = CoreArena::new();
    let universe = small_universe(&mut core);
    let abstract_a = core.value_type_abstract(ConstantIndex::from(0_usize));
    let arrow = core.comp_type_returner(abstract_a);
    let arrow = core.comp_type_arrow(abstract_a, arrow);
    let function = core.value_type_thunk(arrow);
    let ignoring = core.value_type_sigma(universe, function);
    let pair = core.value_type_product(&[abstract_a, abstract_a]);
    let nested = core.value_type_sigma(function, pair);
    let own = bound(&mut core, DeBruijnIndex::from(0_u32));
    let naming = core.value_type_sigma(universe, own);
    let source = CoreSource::new(&core, &names);
    for (root, form, expected, what) in [
        (
            ignoring,
            Form::Sugared,
            "Type * (a => a)",
            "a binder no occurrence names",
        ),
        (
            ignoring,
            Form::Explicit,
            "#{Type, +U (a -> -F a)}",
            "explicitly",
        ),
        (
            nested,
            Form::Sugared,
            "(a => a) * (a * a)",
            "an inner product parenthesized",
        ),
        (
            naming,
            Form::Sugared,
            "#{a : Type, b : a}",
            "a binder its second factor names",
        ),
    ] {
        let rendered = presented_in(&source, Root::Type(CoreNode::ValueType(root)), wide(), form);
        assert_eq!(
            (rendered.as_ref(), rendered.fidelity()),
            (expected, Fidelity::Faithful),
            "{what}"
        );
    }
}

/// A dependent arrow's binder spells as the source names it where that
/// name captures nothing: a name the type mentions, or one a binder
/// around it took, falls back to a generated name, and a generated name
/// skips the written ones around it (#418).
#[test]
fn an_arrow_binder_spells_as_the_source_names_it()
{
    let names = [Name::from("a")];
    let mut core = CoreArena::new();
    let pi_outer = two_binders(&mut core);
    let Some(&gandr_core_term::CompType::Pi {
        codomain: pi_inner, ..
    }) = core.comp_type(pi_outer)
    else {
        panic!("two dependent arrows");
    };
    for (outer_name, inner_name, expected, what) in [
        (
            Some("presented"),
            Some("other"),
            "(presented : Type) -> (other : Type) -> a -> other -> -F presented",
            "both binders as written",
        ),
        (
            Some("a"),
            Some("other"),
            "(b : Type) -> (other : Type) -> a -> other -> -F b",
            "a name the type mentions falls back",
        ),
        (
            Some("b"),
            None,
            "(b : Type) -> (c : Type) -> a -> c -> -F b",
            "a generated name skips a written one around it",
        ),
        (
            Some("x"),
            Some("x"),
            "(x : Type) -> (b : Type) -> a -> b -> -F x",
            "a name a binder around it took falls back",
        ),
    ] {
        let mut arrows: Vec<(CompTypeId, Name<'_>)> =
            [(pi_outer, outer_name), (pi_inner, inner_name)]
                .into_iter()
                .filter_map(|(arrow, name)| name.map(|name| (arrow, Name::from(name))))
                .collect();
        arrows.sort_by_key(|&(arrow, _)| arrow);
        assert_eq!(
            spelled(
                &CoreSource::new(&core, &names).naming_arrows(&arrows),
                Root::Type(CoreNode::CompType(pi_outer))
            ),
            faithful(Written(expected)),
            "{what}"
        );
    }
}

/// The static formers spell as the grammar writes them: a static Pi as an
/// arrow between value types, a static abstraction as `\a. v` with its
/// binder named as a dependent arrow's is, and a spine of static
/// applications as one application of its operator, whether read as a
/// value or as the type its decode denotes.
#[test]
fn static_operators_spell_as_the_grammar_writes_them()
{
    let names = [Name::from("t")];
    let mut core = CoreArena::new();
    let small = small_universe(&mut core);
    let negative = core.value_type_universe(Sort::Ground(GroundSort::Computation), Level::zero());
    let family = core.value_type_static_pi(small, negative);
    let rest = core.value_type_static_pi(small, small);
    let classifier = core.value_type_static_pi(family, rest);

    let element = bound(&mut core, DeBruijnIndex::from(0_u32));
    let squared = core.value_type_product(&[element, element]);
    let returns_squared = core.comp_type_returner(squared);
    let squared_code = core.value_quote_computation(returns_squared);
    let squaring = core.value_static_lambda(squared_code);

    let outer = bound(&mut core, DeBruijnIndex::from(1_u32));
    let inner = bound(&mut core, DeBruijnIndex::from(0_u32));
    let both = core.value_type_product(&[outer, inner]);
    let both_code = core.value_quote(both);
    let over_inner = core.value_static_lambda(both_code);
    let nested = core.value_static_lambda(over_inner);

    let integer = core.value_type_base(BaseType::Integer);
    let integer_code = core.value_quote(integer);
    let operator = core.value_constant(ConstantIndex::from(0_usize));
    let at_family = core.value_static_application(operator, squaring);
    let at_carrier = core.value_static_application(at_family, integer_code);
    let applied = core.value_static_application(at_carrier, integer_code);
    let decoded = core.value_type_element(applied, Level::zero());
    let once = core.value_static_application(operator, integer_code);

    let source = CoreSource::new(&core, &names);
    for (root, spelling) in [
        (
            Root::Type(CoreNode::ValueType(classifier)),
            "(Type -> Type[-]) -> Type -> Type",
        ),
        (Root::Value(CoreNode::Value(squaring)), "\\a. -F #{a, a}"),
        (Root::Value(CoreNode::Value(nested)), "\\a. \\b. #{a, b}"),
        (Root::Value(CoreNode::Value(once)), "t(Integer)"),
        (
            Root::Value(CoreNode::Value(applied)),
            "t(\\a. -F #{a, a}, Integer, Integer)",
        ),
        (
            Root::Type(CoreNode::ValueType(decoded)),
            "t(\\a. -F #{a, a}, Integer, Integer)",
        ),
    ] {
        assert_eq!(
            spelled(&source, root),
            faithful(Written(spelling)),
            "{root:?} spells as the grammar writes it"
        );
    }
}

/// A call collects its arguments into one list, up to `DEPTH_LIMIT` of
/// them; an application past the limit applies the call it heads.
#[test]
fn a_call_collects_its_arguments_up_to_the_depth_limit()
{
    let limit = usize::try_from(u32::from(DEPTH_LIMIT)).expect("the limit fits a usize");
    let names = [Name::from("kept")];
    let mut core = CoreArena::new();
    let bound = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let head = core.value_constant(ConstantIndex::from(0_usize));
    let forced = core.computation_force(head);
    let applied = |core: &mut CoreArena, count: usize| {
        let mut call = forced;
        for _ in 0 .. count {
            call = core.computation_application(call, bound);
        }
        core.computation_lambda(call)
    };
    let twice = applied(&mut core, 2);
    let past = applied(&mut core, limit.saturating_add(1));
    let source = CoreSource::new(&core, &names);
    let body = |id| Root::Computation(CoreNode::Computation(id));
    assert_eq!(
        spelled(&source, body(twice)),
        faithful(Written("fn (a) { kept(a, a) }"))
    );
    assert_eq!(
        spelled(&source, body(past)),
        (
            format!(
                "fn (a) {{ kept(a)({}a,\n    a, a, a, a) }}",
                "a, ".repeat(27)
            ),
            Fidelity::Faithful
        ),
        "the innermost application past the limit heads the call"
    );
}

/// A body in braces holds a sequence bare: the braces a block writes are
/// the sequence's own, never doubled.
#[test]
fn a_block_body_holds_its_sequence_bare()
{
    let mut core = CoreArena::new();
    let one = integer(&mut core, Sign::NonNegative, Written("1"));
    let pure_one = core.computation_return(one);
    let bound = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let returned = core.computation_return(bound);
    let sequence = core.computation_bind(pure_one, returned);
    let recursive =
        core.computation_fixpoint(sequence, gandr_kernel_term::FixpointEvidence::Partial);
    let source = CoreSource::new(&core, &[]);
    assert_eq!(
        spelled(&source, Root::Computation(CoreNode::Computation(recursive))),
        approximate(Written("rec a { run b <- pure 1 ; b }"))
    );
}

/// A static redex prints as its reduct, each binder of the abstraction
/// written as the argument it takes, in the order applied; arguments past
/// the abstraction's chain apply to the reduct, and an abstraction given
/// fewer arguments than its chain keeps the binders left open; and a
/// thunk over an arrow
/// into a decoded redex of a returner takes the value-function alias over
/// the reduct's result, as the same type written plainly does.
#[test]
fn a_static_redex_prints_as_its_reduct_401()
{
    let names = [Name::from("t")];
    let mut core = CoreArena::new();
    let integer = core.value_type_base(BaseType::Integer);
    let integer_code = core.value_quote(integer);
    let unit = core.value_type_product(&[]);
    let unit_code = core.value_quote(unit);
    let operator = core.value_constant(ConstantIndex::from(0_usize));

    let variable = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let identity = core.value_static_lambda(variable);
    let once = core.value_static_application(identity, integer_code);
    let past = core.value_static_application(identity, operator);
    let past = core.value_static_application(past, integer_code);

    let outer = bound(&mut core, DeBruijnIndex::from(1_u32));
    let inner = bound(&mut core, DeBruijnIndex::from(0_u32));
    let both = core.value_type_product(&[outer, inner]);
    let both_code = core.value_quote(both);
    let pairing = core.value_static_lambda(both_code);
    let pairing = core.value_static_lambda(pairing);
    let paired = core.value_static_application(pairing, integer_code);
    let paired = core.value_static_application(paired, unit_code);
    let half = core.value_static_application(pairing, integer_code);

    let element = bound(&mut core, DeBruijnIndex::from(0_u32));
    let squared = core.value_type_product(&[element, element]);
    let returns_squared = core.comp_type_returner(squared);
    let squared_code = core.value_quote_computation(returns_squared);
    let squaring = core.value_static_lambda(squared_code);
    let squares = core.value_static_application(squaring, integer_code);
    let decoded = core.comp_type_element(squares, Level::zero());
    let arrow = core.comp_type_arrow(integer, decoded);
    let function = core.value_type_thunk(arrow);

    let source = CoreSource::new(&core, &names);
    for (root, spelling) in [
        (Root::Value(CoreNode::Value(once)), "Integer"),
        (Root::Value(CoreNode::Value(past)), "t(Integer)"),
        (Root::Value(CoreNode::Value(paired)), "#{Integer, Unit}"),
        (Root::Value(CoreNode::Value(half)), "\\a. #{Integer, a}"),
    ] {
        assert_eq!(
            spelled(&source, root),
            faithful(Written(spelling)),
            "{root:?} spells as its reduct"
        );
    }
    let presented = presented_in(
        &source,
        Root::Type(CoreNode::ValueType(function)),
        wide(),
        Form::Sugared,
    );
    assert_eq!(
        (presented.as_ref(), presented.fidelity()),
        ("Integer => Integer * Integer", Fidelity::Faithful),
        "the alias reads through the redex its codomain decodes"
    );
}

/// #675: a call of a function literal prints as the value it returns,
/// each abstraction's binder written as the argument it takes, the first
/// argument the outermost; a literal whose body does more than return
/// stays a call.
#[test]
fn a_called_function_literal_prints_as_what_it_returns_675()
{
    let names = [Name::from("t"), Name::from("u")];
    let mut core = CoreArena::new();
    let t = core.value_constant(ConstantIndex::from(0_usize));
    let u = core.value_constant(ConstantIndex::from(1_usize));
    let bound = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let outer = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(1_u32));

    let returns = core.computation_return(bound);
    let identity = core.computation_lambda(returns);
    let identity = core.value_thunk(identity);
    let identity = core.computation_force(identity);
    let called = core.computation_application(identity, t);
    let called = core.value_nested(called);

    let first = core.computation_return(outer);
    let first = core.computation_lambda(first);
    let first = core.computation_lambda(first);
    let first = core.value_thunk(first);
    let first = core.computation_force(first);
    let projected = core.computation_application(first, t);
    let projected = core.computation_application(projected, u);
    let projected = core.value_returned(projected);

    let forced = core.computation_force(bound);
    let forcing = core.computation_lambda(forced);
    let forcing = core.value_thunk(forcing);
    let forcing = core.computation_force(forcing);
    let forcing = core.computation_application(forcing, t);
    let forcing = core.value_nested(forcing);

    let source = CoreSource::new(&core, &names);
    for (root, spelling) in [
        (Root::Value(CoreNode::Value(called)), "t"),
        (Root::Value(CoreNode::Value(projected)), "t"),
    ] {
        assert_eq!(
            spelled(&source, root),
            faithful(Written(spelling)),
            "{root:?} spells as what it returns"
        );
    }
    assert_eq!(
        spelled(&source, Root::Value(CoreNode::Value(forcing))),
        approximate(Written("<thunk>(t)")),
        "a body that does more than return stays a call"
    );
}

/// #676: a run the lowering binds a nested call by, `a ← t(u); t(a)`,
/// prints as the nested call, `t(t(u))`, and two runs, the second's call
/// naming the first's binder, as `t(t(t(u)))`.
#[test]
fn a_run_bound_call_in_a_type_prints_nested_676()
{
    let names = [Name::from("t"), Name::from("u")];
    let mut core = CoreArena::new();
    let t = core.value_constant(ConstantIndex::from(0_usize));
    let u = core.value_constant(ConstantIndex::from(1_usize));
    let a = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let forced = core.computation_force(t);
    let bound = core.computation_application(forced, u);
    let rest = core.computation_application(forced, a);
    let one = core.computation_bind(bound, rest);
    let one = core.value_nested(one);
    let two = core.computation_bind(rest, rest);
    let two = core.computation_bind(bound, two);
    let two = core.value_returned(two);
    let source = CoreSource::new(&core, &names);
    for (root, spelling) in [
        (Root::Value(CoreNode::Value(one)), "t(t(u))"),
        (Root::Value(CoreNode::Value(two)), "t(t(t(u)))"),
    ] {
        assert_eq!(
            spelled(&source, root),
            faithful(Written(spelling)),
            "{root:?} spells as the nested call"
        );
    }
}

/// #736: a dependent arrow whose codomain decodes a called function literal
/// prints its binder only where the literal's result names it. The binder
/// handed to a literal returning `⌜Unit⌝` is spelled as the call's argument
/// and dropped with it, so the arrow is the plain `Unit -> -F Unit` and the
/// thunk over it the alias `Unit => Unit`; a literal returning its argument
/// keeps it, `(a : Type) -> -F a`, and the alias over that names it.
#[test]
fn a_binder_only_a_dropped_argument_names_is_unnamed_736()
{
    let mut core = CoreArena::new();
    let unit = core.value_type_product(&[]);
    let unit_code = core.value_quote(unit);
    let binder = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));

    let returns_unit = core.computation_return(unit_code);
    let constant = core.computation_lambda(returns_unit);
    let constant = core.value_thunk(constant);
    let constant = core.computation_force(constant);
    let dropped = core.computation_application(constant, binder);
    let dropped = core.value_returned(dropped);
    let dropped = core.value_type_element(dropped, Level::zero());
    let dropped = core.comp_type_returner(dropped);
    let dropped = core.comp_type_pi(unit, dropped);

    let universe = small_universe(&mut core);
    let returns_bound = core.computation_return(binder);
    let identity = core.computation_lambda(returns_bound);
    let identity = core.value_thunk(identity);
    let identity = core.computation_force(identity);
    let kept = core.computation_application(identity, binder);
    let kept = core.value_returned(kept);
    let kept = core.value_type_element(kept, Level::zero());
    let kept = core.comp_type_returner(kept);
    let kept = core.comp_type_pi(universe, kept);
    let dropped_thunk = core.value_type_thunk(dropped);
    let kept_thunk = core.value_type_thunk(kept);

    let source = CoreSource::new(&core, &[]);
    for (root, spelling) in [
        (CoreNode::CompType(dropped), "Unit -> -F Unit"),
        (CoreNode::CompType(kept), "(a : Type) -> -F a"),
        (CoreNode::ValueType(dropped_thunk), "Unit => Unit"),
        (CoreNode::ValueType(kept_thunk), "(a : Type) => a"),
    ] {
        let presented = presented_in(&source, Root::Type(root), wide(), Form::Sugared);
        assert_eq!(
            (presented.as_ref(), presented.fidelity()),
            (spelling, Fidelity::Faithful),
            "the binder is named exactly where the printed codomain names it"
        );
    }
}

/// #839: a quoted type that holds a part no expression reads — a sum or a
/// lazy product written between braces, at its head or as a product's
/// component — is written `type(T)` where an expression stands, as an
/// argument and alone, so the lowering reads it back to the same code.
/// `Bool` and a base type are read where an expression stands and stay bare,
/// and so does any quote a type position reads, as the decoded code there.
#[test]
fn a_type_no_expression_reads_is_quoted_839()
{
    let mut core = CoreArena::new();
    let integer = core.value_type_base(BaseType::Integer);
    let unit = core.value_type_product(&[]);
    let only = core.value_type_sum(&[integer]);
    let unit_only = core.value_type_sum(&[unit]);
    let holding = core.value_type_product(&[unit, unit_only]);
    let boolean = core.value_type_sum(&[unit, unit]);
    let returns = core.comp_type_returner(integer);
    let lazy_one = core.comp_type_with(&[returns]);
    let only = core.value_quote(only);
    let holding = core.value_quote(holding);
    let boolean = core.value_quote(boolean);
    let integer = core.value_quote(integer);
    let lazy_one = core.value_quote_computation(lazy_one);
    let argument = core.value_stay(only);
    let decoded = core.value_type_element(only, Level::zero());
    let source = CoreSource::new(&core, &[]);
    for form in [Form::Sugared, Form::Explicit] {
        let presented = presented_in(
            &source,
            Root::Type(CoreNode::ValueType(decoded)),
            wide(),
            form,
        );
        assert_eq!(
            (presented.as_ref(), presented.fidelity()),
            ("+{Integer}", Fidelity::Faithful),
            "a decoded quote in a type position stands bare in the {form:?} form"
        );
    }
    for (root, sugared, explicit) in [
        (only, "type(+{Integer})", "type(+{Integer})"),
        (holding, "type(Unit * +{Unit})", "type(#{Unit, +{Unit}})"),
        (boolean, "Bool", "Bool"),
        (integer, "Integer", "Integer"),
        (lazy_one, "type(&{-F Integer})", "type(&{-F Integer})"),
        (argument, "stay(type(+{Integer}))", "stay(type(+{Integer}))"),
    ] {
        for (form, expected) in [(Form::Sugared, sugared), (Form::Explicit, explicit)] {
            let presented = presented_in(&source, Root::Value(CoreNode::Value(root)), wide(), form);
            assert_eq!(
                (presented.as_ref(), presented.fidelity()),
                (expected, Fidelity::Faithful),
                "{root:?} in the {form:?} form"
            );
        }
    }
}

/// #1127: an expression reads a sugared chain's `*`, `+` and `&` as
/// operators over the components, so a quoted product, sum or lazy product
/// of two or more components is written `type(T)` where an expression
/// stands in the sugared form, alone, as an argument and under a type
/// former; the explicit form's `#{A, B}` reads as the product's code and
/// stays bare. A static abstraction's body is read as a type, where the chain
/// stands bare: `\a. type(a * a)` does not parse.
#[test]
fn a_quoted_chain_is_quoted_1127()
{
    let mut core = CoreArena::new();
    let integer = core.value_type_base(BaseType::Integer);
    let unit = core.value_type_product(&[]);
    let pair = core.value_type_product(&[unit, integer]);
    let either = core.value_type_sum(&[integer, unit]);
    let pairs = core.value_type_list(pair);
    let returns = core.comp_type_returner(integer);
    let returns_unit = core.comp_type_returner(unit);
    let lazy = core.comp_type_with(&[returns, returns_unit]);
    let pair = core.value_quote(pair);
    let either = core.value_quote(either);
    let pairs = core.value_quote(pairs);
    let lazy = core.value_quote_computation(lazy);
    let argument = core.value_stay(pair);
    let variable = bound(&mut core, DeBruijnIndex::from(0_u32));
    let squared = core.value_type_product(&[variable, variable]);
    let squared = core.value_quote(squared);
    let operator = core.value_static_lambda(squared);
    let source = CoreSource::new(&core, &[]);
    for (root, sugared, explicit) in [
        (pair, "type(Unit * Integer)", "#{Unit, Integer}"),
        (either, "type(Integer + Unit)", "type(+{Integer, Unit})"),
        (
            pairs,
            "type(List(Unit * Integer))",
            "List(#{Unit, Integer})",
        ),
        (
            lazy,
            "type(-F Integer & -F Unit)",
            "type(&{-F Integer, -F Unit})",
        ),
        (
            argument,
            "stay(type(Unit * Integer))",
            "stay(#{Unit, Integer})",
        ),
        (operator, "\\a. a * a", "\\a. #{a, a}"),
    ] {
        for (form, expected) in [(Form::Sugared, sugared), (Form::Explicit, explicit)] {
            let presented = presented_in(&source, Root::Value(CoreNode::Value(root)), wide(), form);
            assert_eq!(
                (presented.as_ref(), presented.fidelity()),
                (expected, Fidelity::Faithful),
                "{root:?} in the {form:?} form"
            );
        }
    }
}

/// #800: the sugared form writes a thunk over a dependent arrow chain as the
/// dependent alias, naming each binder its codomain reads and writing every
/// other domain bare, where it wrote the explicit thunk before; the explicit
/// form is unchanged.
#[test]
fn a_dependent_alias_names_each_binder_its_codomain_reads_800()
{
    let mut core = CoreArena::new();
    let universe = small_universe(&mut core);
    let integer = core.value_type_base(BaseType::Integer);
    let outer = bound(&mut core, DeBruijnIndex::from(1_u32));
    let inner = bound(&mut core, DeBruijnIndex::from(0_u32));
    let returns_outer = core.comp_type_returner(outer);
    let returns_inner = core.comp_type_returner(inner);
    let first = bound(&mut core, DeBruijnIndex::from(0_u32));
    let ignoring = core.comp_type_pi(first, returns_outer);
    let ignoring = core.comp_type_pi(universe, ignoring);
    let ignoring = core.value_type_thunk(ignoring);
    let reading = core.comp_type_pi(first, returns_inner);
    let reading = core.comp_type_pi(universe, reading);
    let reading = core.value_type_thunk(reading);
    let returns_after = core.comp_type_returner(outer);
    let after = core.comp_type_pi(universe, returns_after);
    let after = core.comp_type_arrow(integer, after);
    let after = core.comp_type_pi(universe, after);
    let after = core.value_type_thunk(after);
    let source = CoreSource::new(&core, &[]);
    for (root, sugared, explicit) in [
        (
            ignoring,
            "(a : Type, a) => a",
            "+U ((a : Type) -> a -> -F a)",
        ),
        (
            reading,
            "(a : Type, b : a) => b",
            "+U ((a : Type) -> (b : a) -> -F b)",
        ),
        (
            after,
            "(a : Type, Integer, Type) => a",
            "+U ((a : Type) -> Integer -> Type -> -F a)",
        ),
    ] {
        for (form, expected) in [(Form::Sugared, sugared), (Form::Explicit, explicit)] {
            let presented =
                presented_in(&source, Root::Type(CoreNode::ValueType(root)), wide(), form);
            assert_eq!(
                (presented.as_ref(), presented.fidelity()),
                (expected, Fidelity::Faithful),
                "{root:?} in the {form:?} form"
            );
        }
    }
}

/// Every value leaf spells as the surface writes it — a signed integer,
/// a numeric literal with and without a fraction, a string's escapes, the
/// unit and a constant by its name — and a thunk, whose body a reader
/// cannot see, is `<thunk>` and approximate. A constructor spells by the
/// name its family's table gives its tag, bare when nullary and applied
/// to its fields otherwise; a source without the table spells its head
/// `?` and still spells its fields. A word's letter conses before the rest
/// of the word, nested to the right, and inside a call it needs no
/// parentheses.
#[test]
fn every_value_leaf_spells_as_the_surface_writes_it()
{
    let names = [
        Name::from("Accumulator"),
        Name::from("Carry"),
        Name::from("Nat"),
        Name::from("Loops"),
    ];
    let mut core = CoreArena::new();
    let negative = integer(&mut core, Sign::Negative, Written("42"));
    let fraction = core.value_literal(Literal::Numeric(NumericLiteral::new(
        Sign::Negative,
        Magnitude::from_decimal_text("3".into()).expect("decimal digits"),
        FractionDigits::from_decimal_text("25".into()).expect("decimal digits"),
    )));
    let integral = core.value_literal(Literal::Numeric(NumericLiteral::new(
        Sign::NonNegative,
        Magnitude::from_decimal_text("7".into()).expect("decimal digits"),
        FractionDigits::none(),
    )));
    let controls = text(&mut core, Written("\r\0"));
    let unit = core.value_unit();
    let carry = core.value_constant(ConstantIndex::from(1_usize));
    let returned = core.computation_return(unit);
    let thunk = core.value_thunk(returned);
    let leaves = [negative, fraction, integral, controls, unit, carry, thunk]
        .map(|value| normal_form(&mut core, value));
    let source = CoreSource::new(&core, &names);
    for (root, expected) in leaves.into_iter().zip([
        faithful(Written("-42")),
        faithful(Written("-3.25")),
        faithful(Written("7")),
        faithful(Written("\"\\r\\0\"")),
        faithful(Written("unit")),
        faithful(Written("Carry")),
        approximate(Written("<thunk>")),
    ]) {
        assert_eq!(
            spelled(&source, Root::Value(root)),
            expected,
            "{root:?} spells as the surface writes it"
        );
    }
    let nat = core.value_type_data(ConstantIndex::from(2_usize), Vec::new());
    let zero = core.value_constructor(nat, ConstructorTag::from(0_usize), Vec::new());
    let one = core.value_constructor(nat, ConstructorTag::from(1_usize), vec![zero]);
    let loops = core.value_type_data(ConstantIndex::from(3_usize), Vec::new());
    let nil = core.value_constructor(loops, ConstructorTag::from(0_usize), Vec::new());
    let once = core.value_constructor(loops, ConstructorTag::from(1_usize), vec![nil]);
    let word = core.value_constructor(loops, ConstructorTag::from(2_usize), vec![once]);
    let counted = core.value_constructor(nat, ConstructorTag::from(1_usize), vec![word]);
    let mut constructors = Constructors::default();
    constructors.family(Name::from("Nat"), [
        (Name::from("Zero"), Arity::from(0_usize)),
        (Name::from("Succ"), Arity::from(1_usize)),
    ]);
    constructors.words(
        Name::from("Loops"),
        [
            (Name::from("here"), Arity::from(0_usize)),
            (Name::from("loop"), Arity::from(1_usize)),
            (Name::from("back(loop)"), Arity::from(1_usize)),
        ],
        Name::from("here(Base)"),
    );
    let unnamed = CoreSource::new(&core, &names);
    let named = CoreSource::new(&core, &names).naming(&constructors);
    for (source, root, expected) in [
        (&named, zero, faithful(Written("Zero"))),
        (&named, one, faithful(Written("Succ(Zero)"))),
        (&unnamed, one, approximate(Written("?(?)"))),
        (&named, nil, faithful(Written("here(Base)"))),
        (
            &named,
            word,
            faithful(Written("back(loop) ∷ loop ∷ here(Base)")),
        ),
        (
            &named,
            counted,
            faithful(Written("Succ(back(loop) ∷ loop ∷ here(Base))")),
        ),
        (&unnamed, word, approximate(Written("?(?(?))"))),
    ] {
        assert_eq!(
            spelled(source, Root::Value(CoreNode::Value(root))),
            expected,
            "{root:?} spells its constructor"
        );
    }
}

/// A former reads each child at the sort it takes, and a node the printer
/// cannot read spells `?` at exactly that node: `+U` over a value type,
/// `-F` over a computation type, an arrow from a computation type, a term
/// where a type is read, a type where a value is read, a free variable, a
/// dangling row, a constant past the name table, and a cycle.
#[test]
fn misplaced_and_unreadable_nodes_spell_unknown()
{
    let integer = Former::BaseType(BaseType::Integer);
    for (rows, reading, expected) in [
        (
            vec![Former::ThunkType(Row(1)), integer],
            Reading::AsType,
            "+U ?",
        ),
        (
            vec![Former::Returner(Row(1)), Former::Returner(Row(2)), integer],
            Reading::AsType,
            "-F ?",
        ),
        (
            vec![
                Former::Arrow {
                    domain: Row(1),
                    codomain: Row(1),
                },
                Former::Returner(Row(2)),
                integer,
            ],
            Reading::AsType,
            "? -> -F Integer",
        ),
        (vec![Former::Unit], Reading::AsType, "?"),
        (vec![integer], Reading::AsValue, "?"),
        (
            vec![Former::Variable {
                zone: Zone::Intuitionistic,
                index: DeBruijnIndex::from(0_u32),
            }],
            Reading::AsValue,
            "?",
        ),
        (vec![Former::ThunkType(Row(7))], Reading::AsType, "+U ?"),
        (Vec::new(), Reading::AsType, "?"),
        // A product whose components the source does not answer.
        (
            vec![Former::Product(Arity::from(3_usize))],
            Reading::AsType,
            "#{?, ?, ?}",
        ),
        // A record whose labels the source does not answer.
        (
            vec![Former::Record(Arity::from(2_usize))],
            Reading::AsValue,
            "#{.? = ?, .? = ?}",
        ),
        (
            vec![Former::ThunkType(Row(1)), Former::Arrow {
                domain: Row(0),
                codomain: Row(1),
            }],
            Reading::AsType,
            "?",
        ),
    ] {
        assert_eq!(
            table_spelling(rows, reading),
            approximate(Written(expected)),
            "the unreadable node spells `?`"
        );
    }
    let mut core = CoreArena::new();
    let unit = core.value_unit();
    let returned = core.computation_return(unit);
    let past = core.value_type_abstract(ConstantIndex::from(3_usize));
    let source = CoreSource::new(&core, &[]);
    assert_eq!(
        spelled(&source, Root::Type(CoreNode::Computation(returned))),
        approximate(Written("?")),
        "a computation where a type is read spells `?`"
    );
    assert_eq!(
        spelled(&source, Root::Type(CoreNode::ValueType(past))),
        approximate(Written("?")),
        "an abstract type past the name table spells `?`"
    );
}

/// A name spelled with a `?` stays faithful: fidelity follows the nodes
/// the surface cannot write, not the characters a name holds.
#[test]
fn fidelity_follows_nodes_not_the_characters_of_a_name()
{
    let names = [Name::from("Maybe?")];
    let mut core = CoreArena::new();
    let maybe = core.value_type_abstract(ConstantIndex::from(0_usize));
    let lifted = core.value_type_lift(maybe, Level::constant(LevelConstant::from(1_u64)));
    let source = CoreSource::new(&core, &names);
    assert_eq!(
        spelled(&source, Root::Type(CoreNode::ValueType(maybe))),
        faithful(Written("Maybe?")),
        "a name's own `?` is no approximation"
    );
    assert_eq!(
        spelled(&source, Root::Type(CoreNode::ValueType(lifted))),
        approximate(Written("?")),
        "a lift, which the surface does not write, spells `?`"
    );
}

/// Element identity spells `here(a)`, and a pair inside it uses the
/// grammar's tuple spelling, not the binary sugar.
#[test]
fn here_witness_pins_identity_notation()
{
    let mut core = CoreArena::new();
    let two = integer(&mut core, Sign::NonNegative, Written("2"));
    let pair = core.value_tuple(&[two, two]);
    let witness = core.value_here(pair);
    let source = CoreSource::new(&core, &[]);
    let root = Root::Value(CoreNode::Value(witness));
    for page in [narrow(), wide()] {
        let rendered = presented(&source, root, page);
        assert_eq!(
            rendered.as_ref(),
            "here(#{2, 2})",
            "identity notation is `here` around the point, at {page:?}"
        );
        assert_eq!(
            rendered.fidelity(),
            Fidelity::Faithful,
            "the grammar parses `here`, so the spelling is faithful"
        );
    }
}

/// Function extensionality spells `funext(f, g)`, its functions in the
/// order the core holds them, and is faithful: the grammar parses it.
#[test]
fn funext_spells_its_functions_in_order()
{
    let mut core = CoreArena::new();
    let twice = core.value_constant(ConstantIndex::from(0_usize));
    let same = core.value_constant(ConstantIndex::from(1_usize));
    let witness = core.value_funext(twice, same);
    let names = [Name::from("twice"), Name::from("same")];
    let source = CoreSource::new(&core, &names);
    assert_eq!(
        spelled(&source, Root::Value(CoreNode::Value(witness))),
        faithful(Written("funext(twice, same)")),
        "the first function is the path's source"
    );
}

/// A universe equivalence spells `equiv(f, g)` and a native list
/// `cons(h, t)` over `nil` in `List(A)`, each faithful: the lowering reads
/// every one of them back.
#[test]
fn an_equivalence_and_a_list_spell_as_written()
{
    let mut core = CoreArena::new();
    let not = core.value_constant(ConstantIndex::from(0_usize));
    let equivalence = core.value_equiv(not, not);
    let unit = core.value_tuple(&[]);
    let nil = core.value_list_nil();
    let cell = core.value_list_cons(unit, nil);
    let element = core.value_type_unit();
    let list = core.value_type_list(element);
    let names = [Name::from("not")];
    let source = CoreSource::new(&core, &names);
    for (root, expected) in [
        (Root::Value(CoreNode::Value(equivalence)), "equiv(not, not)"),
        (Root::Value(CoreNode::Value(cell)), "cons(unit, nil)"),
        (Root::Type(CoreNode::ValueType(list)), "List(Unit)"),
    ] {
        assert_eq!(
            spelled(&source, root),
            faithful(Written(expected)),
            "the surface writes it so"
        );
    }
}

/// Univalence at a stratum spells `ua[n, k](a, b, f, g)`, its stratum and
/// its descriptions in the head and its records in label order, faithful:
/// the lowering reads it back. At the narrow page it breaks after the head
/// and between the records.
#[test]
fn univalence_spells_its_stratum_and_descriptions()
{
    let mut core = CoreArena::new();
    let exchange = core.value_constant(ConstantIndex::from(0_usize));
    let keep = core.value_constant(ConstantIndex::from(1_usize));
    let label = |text: &str| FieldLabel::from(String::from(text));
    let [forward, backward] = [(); 2].map(|()| {
        core.value_record(BTreeMap::from([
            (label("one"), keep),
            (label("mul"), exchange),
        ]))
    });
    let magma = || Description {
        name: gandr_theory_levitation::Name::from("Magma"),
        generators: Box::from([
            Generator {
                label: label("mul"),
                profile: Profile {
                    inputs: PortCount::from(2_usize),
                    outputs: PortCount::from(1_usize),
                },
            },
            Generator {
                label: label("one"),
                profile: Profile {
                    inputs: PortCount::from(0_usize),
                    outputs: PortCount::from(1_usize),
                },
            },
        ]),
    };
    let statement = core.value_ua(
        Stratum {
            degree: Degree::from(1_usize),
            bound: ShapeSize::from(4_usize),
        },
        Arc::new(Sides {
            source: magma(),
            target: magma(),
        }),
        forward,
        backward,
    );
    let names = [Name::from("exchange"), Name::from("keep")];
    pin(
        &CoreSource::new(&core, &names),
        Root::Value(CoreNode::Value(statement)),
        Pinned {
            name: "ua_corolla",
            flat: "ua[1, 4](Magma, Magma, #{.mul = exchange, .one = keep}, #{.mul = exchange, .one = keep})",
            fidelity: Fidelity::Faithful,
        },
    );
}

/// Native introductions retain endpoint and map order but cannot claim
/// surface round-trip fidelity, because the parser has no syntax for them;
/// a product over them is as approximate as its components.
#[test]
fn native_paths_preserve_ordered_endpoints_and_maps()
{
    let mut core = CoreArena::new();
    let unit = core.value_type_unit();
    let integer = core.value_type_base(BaseType::Integer);
    let unit_code = core.value_quote(unit);
    let integer_code = core.value_quote(integer);
    let path_type = core.value_type_path_universe(unit_code, integer_code);
    let first = core.value_path_refl(unit_code);
    let second = core.value_path_refl(integer_code);
    let product = core.value_path_product(first, second);
    let forward = core.value_constant(ConstantIndex::from(0_usize));
    let backward = core.value_constant(ConstantIndex::from(1_usize));
    let equiv = core.value_path_equiv(path_type, forward, backward, Arc::default());
    let names = [Name::from("forward"), Name::from("backward")];
    let source = CoreSource::new(&core, &names);
    for (root, expected) in [
        (
            Root::Type(CoreNode::ValueType(path_type)),
            "Path_U(Unit, Integer)",
        ),
        (Root::Value(CoreNode::Value(first)), "refl(Unit)"),
        (
            Root::Value(CoreNode::Value(product)),
            "pathProduct(refl(Unit), refl(Integer))",
        ),
        (
            Root::Value(CoreNode::Value(equiv)),
            "equiv(forward, backward)",
        ),
    ] {
        let rendered = presented(&source, root, wide());
        assert_eq!(rendered.as_ref(), expected);
        assert_eq!(rendered.fidelity(), Fidelity::Approximate);
    }
}

/// The product of written universe paths spells `pathProduct(p, q)`,
/// nested to the right as written, faithful: the lowering reads the call
/// back to the same node.
#[test]
fn a_product_of_written_paths_spells_as_written()
{
    let mut core = CoreArena::new();
    let keep = core.value_constant(ConstantIndex::from(0_usize));
    let exchange = core.value_constant(ConstantIndex::from(1_usize));
    let unit = core.value_type_unit();
    let unit_code = core.value_quote(unit);
    let here = core.value_here(unit_code);
    let kept = core.value_equiv(keep, keep);
    let exchanged = core.value_equiv(exchange, exchange);
    let corollas = core.value_path_product(kept, exchanged);
    let telescope = core.value_path_product(here, corollas);
    let names = [Name::from("keep"), Name::from("exchange")];
    let source = CoreSource::new(&core, &names);
    let rendered = presented(&source, Root::Value(CoreNode::Value(telescope)), wide());
    assert_eq!(
        rendered.as_ref(),
        "pathProduct(here(Unit), pathProduct(equiv(keep, keep), equiv(exchange, exchange)))"
    );
    assert_eq!(rendered.fidelity(), Fidelity::Faithful);
}

/// The product of two universe flows spells `flowProduct(p, q)`, nested
/// to the right as written, faithful as the path product is.
#[test]
fn a_product_of_flows_spells_as_written()
{
    let mut core = CoreArena::new();
    let keep = core.value_constant(ConstantIndex::from(0_usize));
    let exchange = core.value_constant(ConstantIndex::from(1_usize));
    let unit = core.value_type_unit();
    let unit_code = core.value_quote(unit);
    let stay = core.value_stay(unit_code);
    let kept = core.value_forward(keep);
    let exchanged = core.value_forward(exchange);
    let corollas = core.value_flow_product(kept, exchanged);
    let telescope = core.value_flow_product(stay, corollas);
    let names = [Name::from("keep"), Name::from("exchange")];
    let source = CoreSource::new(&core, &names);
    let rendered = presented(&source, Root::Value(CoreNode::Value(telescope)), wide());
    assert_eq!(
        rendered.as_ref(),
        "flowProduct(stay(Unit), flowProduct(forward(keep), forward(exchange)))"
    );
    assert_eq!(rendered.fidelity(), Fidelity::Faithful);
}

/// A flow composite spells infix, `f then g`, as the surface writes it and
/// the lowering reads it back (#631); a composite operand stands in
/// parentheses.
#[test]
fn a_composite_of_flows_spells_infix()
{
    let mut core = CoreArena::new();
    let keep = core.value_constant(ConstantIndex::from(0_usize));
    let exchange = core.value_constant(ConstantIndex::from(1_usize));
    let kept = core.value_forward(keep);
    let exchanged = core.value_forward(exchange);
    let composite = core.value_then(kept, exchanged);
    let nested = core.value_then(composite, kept);
    let names = [Name::from("keep"), Name::from("exchange")];
    let source = CoreSource::new(&core, &names);
    for (root, expected) in [
        (composite, "forward(keep) then forward(exchange)"),
        (
            nested,
            "(forward(keep) then forward(exchange)) then forward(keep)",
        ),
    ] {
        let rendered = presented(&source, Root::Value(CoreNode::Value(root)), wide());
        assert_eq!(
            (rendered.as_ref(), rendered.fidelity()),
            (expected, Fidelity::Faithful)
        );
    }
}

/// A returned composite of paths spells infix in the sugared form, `p then
/// q`, as the surface writes it and the lowering derives its transport;
/// the explicit form writes the transport. A transport whose fixed endpoint
/// names the motive's binder is no composite and keeps its spelling (#754).
#[test]
fn a_returned_composite_of_paths_is_written_infix_754()
{
    let mut core = CoreArena::new();
    let circle = core.value_type_abstract(ConstantIndex::from(0_usize));
    let base = core.value_constant(ConstantIndex::from(1_usize));
    let around = core.value_constant(ConstantIndex::from(2_usize));
    let twice = gandr_core_term::identity::then(&mut core, circle, base, around, around);
    let composite = core.value_returned(twice);
    let bound = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let lifted =
        gandr_core_term::shift_value_type(&mut core, circle, gandr_core_term::Binders::ONE)
            .settle(&mut core);
    let diagonal = core.value_type_path(lifted, bound, bound);
    let moved = core.computation_path_transport(diagonal, around, around);
    let transported = core.value_returned(moved);
    let names = [Name::from("Circle"), Name::from("base"), Name::from("loop")];
    let source = CoreSource::new(&core, &names);
    for (root, form, expected) in [
        (composite, Form::Sugared, "loop then loop"),
        (
            composite,
            Form::Explicit,
            "transport(\\a. Path(Circle, base, a), loop, loop)",
        ),
        (
            transported,
            Form::Sugared,
            "transport(\\a. Path(Circle, a, a), loop, loop)",
        ),
    ] {
        let rendered = presented_in(&source, Root::Value(CoreNode::Value(root)), wide(), form);
        assert_eq!(rendered.as_ref(), expected, "{form:?}");
    }
}

/// A composite a transport reads as its path or as the value it moves stays
/// the transport it derives: nothing there states the composite's type, and
/// the lowering reads `p then q` only where something does, as a call's
/// argument (#815).
#[test]
fn a_composite_a_transport_moves_stays_explicit_815()
{
    let mut core = CoreArena::new();
    let circle = core.value_type_abstract(ConstantIndex::from(0_usize));
    let base = core.value_constant(ConstantIndex::from(1_usize));
    let around = core.value_constant(ConstantIndex::from(2_usize));
    let twice = gandr_core_term::identity::then(&mut core, circle, base, around, around);
    let composite = core.value_returned(twice);
    let bound = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let lifted =
        gandr_core_term::shift_value_type(&mut core, circle, gandr_core_term::Binders::ONE)
            .settle(&mut core);
    let diagonal = core.value_type_path(lifted, bound, bound);
    let moved = core.computation_path_transport(diagonal, composite, composite);
    let transported = core.value_returned(moved);
    let function = core.value_constant(ConstantIndex::from(3_usize));
    let forced = core.computation_force(function);
    let called = core.computation_application(forced, composite);
    let names = [
        Name::from("Circle"),
        Name::from("base"),
        Name::from("loop"),
        Name::from("sect"),
    ];
    let source = CoreSource::new(&core, &names);
    let rendered = presented_in(
        &source,
        Root::Value(CoreNode::Value(transported)),
        PageWidth::from(1_000_u32),
        Form::Sugared,
    );
    assert_eq!(
        rendered.as_ref(),
        "transport(\\a. Path(Circle, a, a), transport(\\a. Path(Circle, base, a), loop, loop), \
         transport(\\a. Path(Circle, base, a), loop, loop))"
    );
    let rendered = presented_in(
        &source,
        Root::Computation(CoreNode::Computation(called)),
        wide(),
        Form::Sugared,
    );
    assert_eq!(rendered.as_ref(), "sect(loop then loop)");
}

/// A returned inverse and a returned action on a path spell as written in
/// the sugared form, `back(p)` and `cong(f, p)`, as the lowering derives
/// their transports; the explicit form writes the transports. A map the
/// action reads off its motive one binder deeper is spelled as the source
/// names it, a parameter among them; a transport whose fixed endpoint is no
/// image of the map keeps its spelling (#778).
#[test]
fn an_inverse_and_an_action_on_a_path_are_written_as_derived_778()
{
    let mut core = CoreArena::new();
    let circle = core.value_type_abstract(ConstantIndex::from(0_usize));
    let base = core.value_constant(ConstantIndex::from(1_usize));
    let around = core.value_constant(ConstantIndex::from(2_usize));
    let spin = core.value_constant(ConstantIndex::from(3_usize));
    let inverse = gandr_core_term::identity::back(&mut core, circle, base, around);
    let inverse = core.value_returned(inverse);
    let forced = core.computation_force(spin);
    let applied = core.computation_application(forced, base);
    let start = core.value_returned(applied);
    let action = gandr_core_term::identity::cong(&mut core, circle, spin, start, around);
    let action = core.value_returned(action);
    let parameter = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let forced = core.computation_force(parameter);
    let applied = core.computation_application(forced, base);
    let start = core.value_returned(applied);
    let mapped = gandr_core_term::identity::cong(&mut core, circle, parameter, start, around);
    let mapped = core.value_returned(mapped);
    // A transport whose fixed endpoint is no image of the map is no action:
    // `cong(spin, loop)` would derive `Path(Circle, spin(base), spin(a))`.
    let bound = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let forced = core.computation_force(spin);
    let applied = core.computation_application(forced, bound);
    let image = core.value_returned(applied);
    let motive = core.value_type_path(circle, base, image);
    let reflexivity = core.value_here(base);
    let unmapped = core.computation_path_transport(motive, around, reflexivity);
    let unmapped = core.value_returned(unmapped);
    let names = [
        Name::from("Circle"),
        Name::from("base"),
        Name::from("loop"),
        Name::from("spin"),
    ];
    let context = [Some(Name::from("f"))];
    let source = CoreSource::new(&core, &names).within(&context);
    for (root, form, expected) in [
        (inverse, Form::Sugared, "back(loop)"),
        (
            inverse,
            Form::Explicit,
            "transport(\\a. Path(Circle, a, base), loop, here(base))",
        ),
        (action, Form::Sugared, "cong(spin, loop)"),
        (
            action,
            Form::Explicit,
            "transport(\\a. Path(Circle, spin(base), spin(a)), loop, here(spin(base)))",
        ),
        (mapped, Form::Sugared, "cong(f, loop)"),
        (
            unmapped,
            Form::Sugared,
            "transport(\\a. Path(Circle, base, spin(a)), loop, here(base))",
        ),
    ] {
        let rendered = presented_in(&source, Root::Value(CoreNode::Value(root)), wide(), form);
        assert_eq!(rendered.as_ref(), expected, "{form:?}");
    }
}

/// An elaborated body spells as the grammar writes it, its exits elided:
/// a returner at the end of a block bare, a call by its head, a thunk in
/// a body spelled; a case binds its summand's payload, a split its
/// components, a data case each constructor's fields under the
/// constructor's name; a projection and a primitive call as written.
#[test]
fn an_elaborated_body_prints_with_its_exits_elided()
{
    let mut core = CoreArena::new();
    let bound = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let kept = core.value_constant(ConstantIndex::from(0_usize));
    let one = integer(&mut core, Sign::NonNegative, Written("1"));
    let two = integer(&mut core, Sign::NonNegative, Written("2"));
    // `{ return n }` and `{ n }` lower to this one body.
    let returned = core.computation_return(bound);
    let identity = core.computation_lambda(returned);
    // `{ become kept(n) }` and `{ kept(n) }` lower to this one body.
    let forced = core.computation_force(kept);
    let call = core.computation_application(forced, bound);
    let calling = core.computation_lambda(call);
    // A returner where the body goes on is `pure`, the end of a block a
    // bind runs among them; a bind run by a bind is a block of its own.
    let pure_one = core.computation_return(one);
    let inner = core.computation_bind(pure_one, returned);
    let outer = core.computation_bind(inner, call);
    let sequenced = core.computation_lambda(outer);
    // A returner at a call's head stands in parentheses, and a thunk in a
    // body is spelled.
    let applied = core.computation_application(pure_one, two);
    let suspended = core.value_thunk(applied);
    let suspends = core.computation_return(suspended);
    // A case binds the payload of its summand, a split the components it
    // opens, and a data case each constructor's fields.
    let case = core.computation_case(bound, &[returned, returned]);
    let analysed = core.computation_lambda(case);
    let split = core.computation_split(bound, ComponentCount::from(2_usize), returned);
    let opened = core.computation_lambda(split);
    let nat = core.value_type_data(ConstantIndex::from(1_usize), Vec::new());
    let returns_nat = core.comp_type_returner(nat);
    let zero = core.value_constructor(nat, ConstructorTag::from(0_usize), Vec::new());
    let returns_zero = core.computation_return(zero);
    let field = core.computation_lambda(returned);
    let data_case = core.computation_data_case(bound, returns_nat, vec![returns_zero, field]);
    let matched = core.computation_lambda(data_case);
    let projection = core.computation_record_projection(bound, FieldLabel::from(String::from("x")));
    let projected = core.computation_lambda(projection);
    let primitive = core.computation_primitive(PRELUDE[0], Arguments::Unary(bound));
    let primitive_call = core.computation_lambda(primitive);
    // A recorded run spells its moves, and a ride its motive under the
    // binder it opens.
    let recorded = core.value_recorded(Arc::from(vec![
        RecordedMove::Received(one),
        RecordedMove::Selected(FieldLabel::from(String::from("report"))),
        RecordedMove::Sent(two),
        RecordedMove::Offered(FieldLabel::from(String::from("retire"))),
        RecordedMove::Closed,
    ]));
    let motive_point = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let motive = core.value_type_run(motive_point);
    let ride = core.computation_ride(motive, bound, bound);
    let riding = core.computation_lambda(ride);
    // A lazy product is the positional copattern block the lowering reads
    // back as that product, one clause per component.
    let pure_two = core.computation_return(two);
    let paired = core.computation_with(&[pure_one, pure_two]);
    let chained = core.computation_with(&[pure_one, paired]);
    let tripled = core.computation_with(&[pure_one, pure_two, pure_one]);
    let single = core.computation_with(&[pure_one]);
    let empty = core.computation_with(&[]);
    let names = [Name::from("kept"), Name::from("Nat")];
    let mut constructors = Constructors::default();
    constructors.family(Name::from("Nat"), [
        (Name::from("Zero"), Arity::from(0_usize)),
        (Name::from("Succ"), Arity::from(1_usize)),
    ]);
    constructors.case(data_case, Name::from("Nat"));
    let source = CoreSource::new(&core, &names).naming(&constructors);
    let body = |id| Root::Computation(CoreNode::Computation(id));
    for (root, expected, fidelity) in [
        (body(identity), "fn (a) { a }", Fidelity::Faithful),
        (body(calling), "fn (a) { kept(a) }", Fidelity::Faithful),
        (body(forced), "force kept", Fidelity::Faithful),
        (body(pure_one), "1", Fidelity::Faithful),
        (body(suspends), "thunk { (pure 1)(2) }", Fidelity::Faithful),
        (
            body(analysed),
            "fn (a) { case a { +{.0 = b} => b, +{.1 = b} => b } }",
            Fidelity::Faithful,
        ),
        (
            body(opened),
            "fn (a) { case a { #{b, c} => c } }",
            Fidelity::Faithful,
        ),
        (
            body(matched),
            "fn (a) { case a { Zero => Zero, Succ(b) => b } }",
            Fidelity::Faithful,
        ),
        (body(projected), "fn (a) { a.x }", Fidelity::Faithful),
        (
            body(primitive_call),
            "fn (a) { prim.id(a) }",
            Fidelity::Faithful,
        ),
        (
            body(riding),
            "fn (a) { ride(\\b. Run(b), a, a) }",
            Fidelity::Faithful,
        ),
        (
            body(paired),
            "&{.0 => pure 1, .1 => pure 2}",
            Fidelity::Faithful,
        ),
        (
            body(chained),
            "&{.0 => pure 1, .1 => &{.0 => pure 1, .1 => pure 2}}",
            Fidelity::Faithful,
        ),
        (
            body(tripled),
            "&{.0 => pure 1, .1 => pure 2, .2 => pure 1}",
            Fidelity::Faithful,
        ),
        (body(single), "&{.0 => pure 1}", Fidelity::Faithful),
        (body(empty), "&{}", Fidelity::Faithful),
    ] {
        assert_eq!(
            spelled(&source, root),
            (expected.to_owned(), fidelity),
            "{expected}"
        );
    }
    assert_eq!(
        spelled(&source, Root::Value(CoreNode::Value(recorded))),
        (
            "recorded(received(1), selected(report), sent(2), offered(retire), closed)".to_owned(),
            Fidelity::Faithful
        ),
        "a recorded run spells each move as written"
    );
    assert_eq!(
        spelled(&source, Root::Value(CoreNode::Value(suspended))),
        ("<thunk>".to_owned(), Fidelity::Approximate),
        "a value presented alone keeps its thunks opaque"
    );
    pin(&source, body(sequenced), Pinned {
        name: "elided-body",
        flat: "fn (a) { run b <- { run b <- pure 1 ; pure b } ; kept(b) }",
        fidelity: Fidelity::Faithful,
    });
    // Written on one line, each body is its layout at a page no line
    // overflows.
    for id in [
        identity,
        calling,
        forced,
        pure_one,
        suspends,
        analysed,
        opened,
        matched,
        projected,
        primitive_call,
        riding,
        paired,
        chained,
        tripled,
        single,
        empty,
        sequenced,
    ] {
        let root = CoreNode::Computation(id);
        let wide = present_computation(
            &source,
            root,
            PageWidth::from(4_096_u32),
            Form::Explicit.into(),
        )
        .expect("the body lays out");
        let line = present_computation_line(&source, root, Form::Explicit.into())
            .expect("the body writes");
        assert_eq!(
            (line.as_ref(), line.fidelity()),
            (wide.as_ref(), wide.fidelity()),
            "one line is the wide layout"
        );
    }
}

/// The body of `def rec down(n : Nat) -> -F Nat { case n { Zero => z, Succ(p)
/// => down[<](p) } }` under its fixpoint, `z` the value the zero arm returns,
/// and the type it is stated at.
///
/// # Specification
/// trivial.
fn descent(
    core: &mut CoreArena,
    zero: Option<ValueId>,
    evidence: gandr_kernel_term::FixpointEvidence,
) -> (gandr_core_term::ComputationId, ValueId)
{
    let nat = core.value_type_data(ConstantIndex::from(0_usize), Vec::new());
    let returns_nat = core.comp_type_returner(nat);
    // Under the fixpoint and its abstraction the parameter is the innermost
    // binder and the fixpoint's own the next; the successor's field binds
    // one more.
    let parameter = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let itself = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(2_u32));
    let returned = core.computation_return(zero.unwrap_or(parameter));
    let forced = core.computation_force(itself);
    let call = core.computation_application(forced, parameter);
    let field = core.computation_lambda(call);
    let case = core.computation_data_case(parameter, returns_nat, vec![returned, field]);
    let abstraction = core.computation_lambda(case);
    let fixpoint = core.computation_fixpoint(abstraction, evidence);
    (case, core.value_thunk(fixpoint))
}

/// The body of `def rec down(m : Nat, n : Nat) -> -F Nat { case m { Zero =>
/// n, Succ(p) => down[<](p, n) } }` under its fixpoint.
///
/// # Specification
/// trivial.
fn two_parameters(
    core: &mut CoreArena,
    evidence: gandr_kernel_term::FixpointEvidence,
) -> (gandr_core_term::ComputationId, ValueId)
{
    let nat = core.value_type_data(ConstantIndex::from(0_usize), Vec::new());
    let returns_nat = core.comp_type_returner(nat);
    // Under the fixpoint and both abstractions: the second parameter, the
    // first, the fixpoint's own; the successor's field binds one more.
    let variable = |core: &mut CoreArena, index: u32| {
        core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(index))
    };
    let (second, first) = (variable(core, 0_u32), variable(core, 1_u32));
    let (field, kept, itself) = (
        variable(core, 0_u32),
        variable(core, 1_u32),
        variable(core, 3_u32),
    );
    let returned = core.computation_return(second);
    let forced = core.computation_force(itself);
    let applied = core.computation_application(forced, field);
    let call = core.computation_application(applied, kept);
    let succeeded = core.computation_lambda(call);
    let case = core.computation_data_case(first, returns_nat, vec![returned, succeeded]);
    let inner = core.computation_lambda(case);
    let outer = core.computation_lambda(inner);
    let fixpoint = core.computation_fixpoint(outer, evidence);
    (case, core.value_thunk(fixpoint))
}

/// A definition's presentation as a `def rec`: its text and fidelity, or why
/// it is no recursive definition.
///
/// # Specification
/// trivial.
fn recursive(
    source: &CoreSource<'_>,
    defined: (ValueTypeId, ValueId),
    page: PageWidth,
) -> Maybe<(String, Fidelity), recursive::Absent>
{
    match present_recursive(
        source,
        Name::from("down"),
        defined,
        page,
        Form::Explicit.into(),
    )
    .expect("the definition lays out")
    {
        Maybe::Present(presentation) => {
            Maybe::Present((presentation.as_ref().to_owned(), presentation.fidelity()))
        },
        Maybe::Absent(reason) => Maybe::Absent(reason),
    }
}

/// A recursive definition spells whole as the `def rec` that declares it:
/// the header with every parameter its fixpoint abstracts, the body two
/// columns in, each call of its own binder with its claim — `down[<](b)` for
/// a fixpoint descending on any parameter, `down[>](b)` for one claiming
/// nothing. A body that is no fixpoint and a type that is no function are no
/// `def rec` (#941).
#[test]
fn a_recursive_definition_spells_as_written_941()
{
    use gandr_kernel_term::FixpointEvidence;
    let names = [Name::from("Nat")];
    let mut core = CoreArena::new();
    let nat = core.value_type_data(ConstantIndex::from(0_usize), Vec::new());
    let returns_nat = core.comp_type_returner(nat);
    let function = core.comp_type_arrow(nat, returns_nat);
    let ty = core.value_type_thunk(function);
    let curried = core.comp_type_arrow(nat, function);
    let ty_two = core.value_type_thunk(curried);
    let (case, descending) = descent(&mut core, None, FixpointEvidence::StructuralDescent);
    let (partial_case, productive) = descent(&mut core, None, FixpointEvidence::Partial);
    let (first_case, on_first) = two_parameters(&mut core, FixpointEvidence::StructuralDescent);
    let (staged_case, staged) = two_parameters(&mut core, FixpointEvidence::Staged {
        position: StagedPosition::from(1_usize),
    });
    let zero = core.value_constructor(nat, ConstructorTag::from(0_usize), Vec::new());
    let mut constructors = Constructors::default();
    constructors.family(Name::from("Nat"), [
        (Name::from("Zero"), Arity::from(0_usize)),
        (Name::from("Succ"), Arity::from(1_usize)),
    ]);
    for case in [case, partial_case, first_case, staged_case] {
        constructors.case(case, Name::from("Nat"));
    }
    let source = CoreSource::new(&core, &names).naming(&constructors);
    let written = |text: &str| Maybe::Present((text.to_owned(), Fidelity::Faithful));
    let (wide, narrow) = (PageWidth::from(100_u32), PageWidth::from(30_u32));
    assert_eq!(
        recursive(&source, (ty, descending), wide),
        written(
            "def rec down(a : Nat) -> -F Nat {\n  case a { Zero => a, Succ(b) => down[<](b) }\n}"
        ),
        "a descending call writes its claim"
    );
    assert_eq!(
        recursive(&source, (ty, productive), wide),
        written(
            "def rec down(a : Nat) -> -F Nat {\n  case a { Zero => a, Succ(b) => down[>](b) }\n}"
        ),
        "a fixpoint claiming nothing writes its call productive"
    );
    assert_eq!(
        recursive(&source, (ty, descending), narrow),
        written(
            "def rec down(a : Nat) -> -F Nat {\n  case a {\n    Zero => a,\n    Succ(b) => down[<](b)\n  }\n}"
        ),
        "the body breaks at the page two columns in"
    );
    let both = "def rec down(a : Nat, b : Nat) -> -F Nat {\n  case a { Zero => b, Succ(c) => down[<](c, b) }\n}";
    assert_eq!(
        recursive(&source, (ty_two, on_first), wide),
        written(both),
        "every parameter the fixpoint abstracts stands in the header"
    );
    assert_eq!(
        recursive(&source, (ty_two, staged), wide),
        written(both),
        "a fixpoint staged on a later parameter writes the same claim"
    );
    assert_eq!(
        recursive(&source, (ty, zero), wide),
        Maybe::Absent(recursive::Absent::NotAFixpoint),
        "a constructor is no recursive definition"
    );
    assert_eq!(
        recursive(&source, (nat, descending), wide),
        Maybe::Absent(recursive::Absent::NotAFunction),
        "a definition stated at no function type is no recursive definition"
    );
}

/// A recursive definition's parameter takes the name its arrow writes when
/// nothing in the definition mentions it, and otherwise the first generated
/// name the definition does not mention; the body's own binders then avoid
/// it (#941).
#[test]
fn a_recursive_parameter_skips_the_names_its_body_mentions_941()
{
    use gandr_kernel_term::FixpointEvidence;
    let names = [Name::from("Nat"), Name::from("a")];
    let mut core = CoreArena::new();
    let nat = core.value_type_data(ConstantIndex::from(0_usize), Vec::new());
    let returns_nat = core.comp_type_returner(nat);
    let arrow = core.comp_type_arrow(nat, returns_nat);
    let unnamed = core.value_type_thunk(arrow);
    let pi = core.comp_type_pi(nat, returns_nat);
    let dependent = core.value_type_thunk(pi);
    let mentioned = core.value_constant(ConstantIndex::from(1_usize));
    let (case, mentioning) = descent(
        &mut core,
        Some(mentioned),
        FixpointEvidence::StructuralDescent,
    );
    let (plain, quiet) = descent(&mut core, None, FixpointEvidence::StructuralDescent);
    let mut constructors = Constructors::default();
    constructors.family(Name::from("Nat"), [
        (Name::from("Zero"), Arity::from(0_usize)),
        (Name::from("Succ"), Arity::from(1_usize)),
    ]);
    constructors.case(case, Name::from("Nat"));
    constructors.case(plain, Name::from("Nat"));
    let written = |text: &str| Maybe::Present((text.to_owned(), Fidelity::Faithful));
    let wide = PageWidth::from(100_u32);
    let source = CoreSource::new(&core, &names).naming(&constructors);
    assert_eq!(
        recursive(&source, (unnamed, mentioning), wide),
        written(
            "def rec down(b : Nat) -> -F Nat {\n  case b { Zero => a, Succ(c) => down[<](c) }\n}"
        ),
        "the parameter passes over a constant the body mentions"
    );
    let arrows = [(pi, Name::from("n"))];
    let named = source.naming_arrows(&arrows);
    assert_eq!(
        recursive(&named, (dependent, quiet), wide),
        written(
            "def rec down(n : Nat) -> -F Nat {\n  case n { Zero => n, Succ(a) => down[<](a) }\n}"
        ),
        "the parameter takes the name its arrow writes"
    );
    let mentioned_arrows = [(pi, Name::from("a"))];
    let shadowing = source.naming_arrows(&mentioned_arrows);
    assert_eq!(
        recursive(&shadowing, (dependent, mentioning), wide),
        written(
            "def rec down(b : Nat) -> -F Nat {\n  case b { Zero => a, Succ(c) => down[<](c) }\n}"
        ),
        "an arrow's name the body mentions is passed over"
    );
}

/// A data case writes its motive where nothing states its type — the
/// computation a bind runs, a body in a thunk a constructor holds — and
/// leaves it where the body's type is stated or the motive names the
/// scrutinee its binder stands for (#815).
#[test]
fn a_case_nothing_types_writes_its_motive_815()
{
    let mut core = CoreArena::new();
    let bound = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let returned = core.computation_return(bound);
    let nat = core.value_type_data(ConstantIndex::from(0_usize), Vec::new());
    let returns_nat = core.comp_type_returner(nat);
    let zero = core.value_constructor(nat, ConstructorTag::from(0_usize), Vec::new());
    let returns_zero = core.computation_return(zero);
    let field = core.computation_lambda(returned);
    let case = core.computation_data_case(bound, returns_nat, vec![returns_zero, field]);
    // `run b <- case a -> -F Nat { … } ; b`: a bind's run states no type.
    let run = core.computation_bind(case, returned);
    let running = core.computation_lambda(run);
    // `Succ(thunk { fn (a) { case a -> -F Nat { … } } })`: nor does a
    // thunk a constructor holds.
    let matched = core.computation_lambda(case);
    let held = core.value_thunk(matched);
    let succ = core.value_constructor(nat, ConstructorTag::from(1_usize), vec![held]);
    let holding = core.computation_return(succ);
    // A motive naming the scrutinee's binder is left, as is one where the
    // body's type is stated.
    let point = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let run_of = core.value_type_run(point);
    let returns_run = core.comp_type_returner(run_of);
    let dependent = core.computation_data_case(bound, returns_run, vec![returns_zero, field]);
    let dependent_run = core.computation_bind(dependent, returned);
    let depending = core.computation_lambda(dependent_run);
    let names = [Name::from("Nat")];
    let mut constructors = Constructors::default();
    constructors.family(Name::from("Nat"), [
        (Name::from("Zero"), Arity::from(0_usize)),
        (Name::from("Succ"), Arity::from(1_usize)),
    ]);
    constructors.case(case, Name::from("Nat"));
    constructors.case(dependent, Name::from("Nat"));
    let source = CoreSource::new(&core, &names).naming(&constructors);
    let body = |id| Root::Computation(CoreNode::Computation(id));
    for (root, expected) in [
        (
            running,
            "fn (a) { run b <- case a -> -F Nat { Zero => pure Zero, Succ(b) => pure b } ; b }",
        ),
        (
            holding,
            "Succ(thunk { fn (a) { case a -> -F Nat { Zero => Zero, Succ(b) => b } } })",
        ),
        (matched, "fn (a) { case a { Zero => Zero, Succ(b) => b } }"),
        (
            depending,
            "fn (a) { run b <- case a { Zero => pure Zero, Succ(b) => pure b } ; b }",
        ),
    ] {
        assert_eq!(
            spelled(&source, body(root)),
            (expected.to_owned(), Fidelity::Faithful),
            "{expected}"
        );
    }
}

/// A constructor of exactly `DEPTH_LIMIT` fields still binds its pattern:
/// the limit is the most fields a branch is read under, not one past it.
#[test]
fn a_constructor_at_the_depth_limit_binds_every_field()
{
    let limit = usize::try_from(u32::from(DEPTH_LIMIT)).expect("the limit fits a usize");
    let mut core = CoreArena::new();
    let bound = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let returned = core.computation_return(bound);
    let wide = core.value_type_data(ConstantIndex::from(0_usize), Vec::new());
    let returns_wide = core.comp_type_returner(wide);
    let mut branch = returned;
    for _ in 0 .. limit {
        branch = core.computation_lambda(branch);
    }
    let data_case = core.computation_data_case(bound, returns_wide, vec![branch]);
    let matched = core.computation_lambda(data_case);
    let names = [Name::from("Wide")];
    let mut constructors = Constructors::default();
    constructors.family(Name::from("Wide"), [(
        Name::from("Wide"),
        Arity::from(limit),
    )]);
    constructors.case(data_case, Name::from("Wide"));
    let source = CoreSource::new(&core, &names).naming(&constructors);
    let (text, fidelity) = spelled(&source, Root::Computation(CoreNode::Computation(matched)));
    assert_eq!(Fidelity::Faithful, fidelity, "{text}");
    assert!(
        text.contains("case a {\n    Wide(b, c, ") && text.contains(", f1, g1) => g1\n"),
        "the branch binds its fields under the constructor: {text}"
    );
}

/// A hole is written `?` faithfully, as a value and as a computation: it
/// reads back as the same hole, named by its place among its source's holes
/// (#893). Before, each was marked approximate.
#[test]
fn a_hole_is_written_faithfully_893()
{
    let mut core = CoreArena::new();
    let value = core.value_hole(HoleId::from(0_u32));
    let computation = core.computation_hole(HoleId::from(1_u32));
    let source = CoreSource::new(&core, &[]);
    for root in [
        Root::Value(CoreNode::Value(value)),
        Root::Computation(CoreNode::Computation(computation)),
    ] {
        assert_eq!(
            spelled(&source, root),
            ("?".to_owned(), Fidelity::Faithful),
            "{root:?}"
        );
    }
}

/// Arms that share one body bind distinct fields: the body walks once,
/// under the last arm, so a wider arm before it holds no recorded name for
/// its last binders and each takes the next generated one, never the same
/// one twice (`Bound(b, c, d, e, e)` read back as a duplicate binder, #815).
#[test]
fn arms_sharing_a_body_bind_distinct_fields_815()
{
    let mut core = CoreArena::new();
    let theory = core.value_type_data(ConstantIndex::from(0_usize), Vec::new());
    let returns_theory = core.comp_type_returner(theory);
    let scrutinee = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let unit = core.value_unit();
    let shared = core.computation_return(unit);
    let mut branches = Vec::new();
    for fields in [5_usize, 3_usize] {
        let mut branch = shared;
        for _ in 0 .. fields {
            branch = core.computation_lambda(branch);
        }
        branches.push(branch);
    }
    let data_case = core.computation_data_case(scrutinee, returns_theory, branches);
    let matched = core.computation_lambda(data_case);
    let names = [Name::from("Theory")];
    let mut constructors = Constructors::default();
    constructors.family(Name::from("Theory"), [
        (Name::from("Bound"), Arity::from(5_usize)),
        (Name::from("Sort"), Arity::from(3_usize)),
    ]);
    constructors.case(data_case, Name::from("Theory"));
    let source = CoreSource::new(&core, &names).naming(&constructors);
    let (text, fidelity) = spelled(&source, Root::Computation(CoreNode::Computation(matched)));
    assert_eq!(Fidelity::Faithful, fidelity, "{text}");
    assert!(
        text.contains("Sort(b, c, d) => unit") && text.contains("Bound(b, c, d, e, f) => unit"),
        "each arm binds distinct fields: {text}"
    );
}

/// A case over words writes each arm as the surface reads it back: the empty
/// word bare, `here`, though a value writes it at its point, `here(Base)`, and
/// each letter before the rest of the word, `back(loop) ∷ b`, never applied to
/// it (`back(loop)(b)` does not parse, #815).
#[test]
fn a_case_over_words_writes_each_arm_as_the_surface_does_815()
{
    let mut core = CoreArena::new();
    let loops = core.value_type_data(ConstantIndex::from(0_usize), Vec::new());
    let returns_loops = core.comp_type_returner(loops);
    let scrutinee = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let unit = core.value_unit();
    let returned = core.computation_return(unit);
    let lettered = core.computation_lambda(returned);
    let data_case =
        core.computation_data_case(scrutinee, returns_loops, vec![returned, lettered, lettered]);
    let matched = core.computation_lambda(data_case);
    let names = [Name::from("Loops")];
    let mut constructors = Constructors::default();
    constructors.words(
        Name::from("Loops"),
        [
            (Name::from("here"), Arity::from(0_usize)),
            (Name::from("loop"), Arity::from(1_usize)),
            (Name::from("back(loop)"), Arity::from(1_usize)),
        ],
        Name::from("here(Base)"),
    );
    constructors.case(data_case, Name::from("Loops"));
    let source = CoreSource::new(&core, &names).naming(&constructors);
    let (text, fidelity) = spelled(&source, Root::Computation(CoreNode::Computation(matched)));
    assert_eq!(Fidelity::Faithful, fidelity, "{text}");
    for arm in [
        "{ here => unit,",
        "loop ∷ b => unit",
        "back(loop) ∷ b => unit",
    ] {
        assert!(text.contains(arm), "the case writes `{arm}`: {text}");
    }
}

/// A case over a family with a loop writes the loop's arm under the loop's
/// name, after the constructors' arms, as the surface spells it: the case's
/// branches past the constructors are its loop arms, in the family's order,
/// and a table naming the constructors alone left that arm `?` (#813).
#[test]
fn a_loop_arm_is_written_under_its_loop_813()
{
    let mut core = CoreArena::new();
    let circle = core.value_type_data(ConstantIndex::from(0_usize), Vec::new());
    let returns_circle = core.comp_type_returner(circle);
    let scrutinee = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let unit = core.value_unit();
    let returned = core.computation_return(unit);
    let data_case = core.computation_data_case(scrutinee, returns_circle, vec![returned, returned]);
    let matched = core.computation_lambda(data_case);
    let names = [Name::from("Circle")];
    let mut constructors = Constructors::default();
    constructors.family(Name::from("Circle"), [(
        Name::from("Base"),
        Arity::from(0_usize),
    )]);
    constructors.loops(Name::from("Circle"), [Name::from("loop")]);
    constructors.case(data_case, Name::from("Circle"));
    let source = CoreSource::new(&core, &names).naming(&constructors);
    assert_eq!(
        spelled(&source, Root::Computation(CoreNode::Computation(matched))),
        faithful(Written("fn (a) { case a { Base => unit, loop => unit } }"))
    );
}

/// What an endpoint receives is bound as the surface reads a receive,
/// `recv(e) as x ; rest`, the rest under the payload's linear binder: under
/// `run x <- …` a receive reads as a statement that cannot stand there, and
/// the source does not parse (#815).
#[test]
fn a_received_payload_is_bound_as_the_surface_reads_it_815()
{
    let mut core = CoreArena::new();
    let payload = core.value_variable(Zone::Linear, DeBruijnIndex::from(0_u32));
    let returned = core.computation_return(payload);
    let received = core.computation_session(gandr_core_term::session::SessionAction::Receive {
        endpoint: DeBruijnIndex::from(0_u32),
        body: returned,
    });
    let source = CoreSource::new(&core, &[]);
    let (text, _fidelity) = spelled(&source, Root::Computation(CoreNode::Computation(received)));
    assert!(
        text.contains(") as a ;") && text.ends_with('a') && !text.contains("<-"),
        "the receive binds its payload with `as`, and the rest reads it: {text}"
    );
}

/// A hold of a value at its world is written parenthesized, as the surface
/// writes it: bare at a block's head, `hold` would open a hold statement and
/// the block would not parse (#815).
#[test]
fn a_held_handle_is_written_parenthesized_815()
{
    let mut core = CoreArena::new();
    let bound = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let held = core.computation_world(gandr_core_term::world::WorldForm::Hold { value: bound });
    let holds = core.computation_lambda(held);
    let source = CoreSource::new(&core, &[]);
    assert_eq!(
        spelled(&source, Root::Computation(CoreNode::Computation(holds))),
        faithful(Written("fn (a) { (hold a) }"))
    );
}

/// A returner over a row of two interfaces lists them between brackets,
/// a comma between each and the next and none before the first.
#[test]
fn a_returner_lists_each_interface_of_its_row_between_commas()
{
    use gandr_core_term::effect::EffectName;
    use gandr_core_term::effect::EffectOp;
    use gandr_core_term::effect::EffectRow;
    use gandr_core_term::effect::EffectSig;

    let mut core = CoreArena::new();
    let unit = core.value_type_product(&[]);
    let interface = |name: &str| {
        EffectSig::new(EffectName::from(name), [EffectOp {
            name: "go".into(),
            payload: unit,
            reply: unit,
        }])
        .expect("one operation is a signature")
    };
    let row = EffectRow::from_signatures([interface("Proc"), interface("Store")])
        .expect("two interfaces of distinct names");
    let returner = core.comp_type_returner_with_effects(unit, row);
    let source = CoreSource::new(&core, &[]);
    assert_eq!(
        spelled(&source, Root::Type(CoreNode::CompType(returner))),
        faithful(Written("-F [Proc, Store] Unit"))
    );
}

/// Where the spelling is source a reader reads back, a parameterised
/// constructor is written against its family, except as a family's
/// argument, whose parameter states its type; a value presented alone is
/// never annotated.
#[test]
fn a_parameterised_constructor_is_written_against_its_family_where_source_reads_it()
{
    let mut core = CoreArena::new();
    let three = integer(&mut core, Sign::NonNegative, Written("3"));
    let ix = core.value_type_data(ConstantIndex::from(0_usize), vec![three]);
    let made = core.value_constructor(ix, ConstructorTag::from(0_usize), Vec::new());
    let returned = core.computation_return(made);
    let indexed = core.value_type_data(ConstantIndex::from(1_usize), vec![made]);
    let quoted = core.value_quote(indexed);
    let returns_code = core.computation_return(quoted);
    let names = [Name::from("Ix"), Name::from("Vec")];
    let mut constructors = Constructors::default();
    constructors.family(Name::from("Ix"), [(
        Name::from("MkIx"),
        Arity::from(0_usize),
    )]);
    let source = CoreSource::new(&core, &names).naming(&constructors);
    let body = |id| Root::Computation(CoreNode::Computation(id));
    assert_eq!(
        spelled(&source, body(returned)),
        faithful(Written("(MkIx : Ix(3))")),
        "a body's constructor reads back against its family"
    );
    assert_eq!(
        spelled(&source, body(returns_code)),
        faithful(Written("pure Vec(MkIx)")),
        "a family's argument is classified by the family's parameter"
    );
    assert_eq!(
        spelled(&source, Root::Value(CoreNode::Value(made))),
        faithful(Written("MkIx")),
        "a value presented alone is not source"
    );
}

/// A definition's value is source: a parameterised constructor below its
/// root is written against its family, which the lowering needs to read it
/// back, while the root's own type is the definition's; a thunk inside is
/// written whole (#815).
#[test]
fn a_definition_writes_its_constructors_against_their_family_815()
{
    let mut core = CoreArena::new();
    let three = integer(&mut core, Sign::NonNegative, Written("3"));
    let ix = core.value_type_data(ConstantIndex::from(0_usize), vec![three]);
    let made = core.value_constructor(ix, ConstructorTag::from(0_usize), Vec::new());
    let returned = core.computation_return(three);
    let thunked = core.value_thunk(returned);
    let pair = core.value_tuple(&[made, thunked]);
    let names = [Name::from("Ix")];
    let mut constructors = Constructors::default();
    constructors.family(Name::from("Ix"), [(
        Name::from("MkIx"),
        Arity::from(0_usize),
    )]);
    let source = CoreSource::new(&core, &names).naming(&constructors);
    assert_eq!(
        spelled(&source, Root::Definition(CoreNode::Value(pair))),
        faithful(Written("#{(MkIx : Ix(3)), thunk { 3 }}")),
        "a constructor below the root reads back against its family"
    );
    assert_eq!(
        spelled(&source, Root::Definition(CoreNode::Value(made))),
        faithful(Written("MkIx")),
        "the root's type is the definition's"
    );
}

/// A body that ends answering a type's code keeps its `pure`, which the
/// lowering reads back where it refuses the bare type by sort; one that ends
/// answering any other value elides it (#815).
#[test]
fn a_body_answering_a_type_keeps_its_pure_815()
{
    let mut core = CoreArena::new();
    let integer_type = core.value_type_base(BaseType::Integer);
    let integer_code = core.value_quote(integer_type);
    let returns_code = core.computation_return(integer_code);
    let answers_code = core.computation_lambda(returns_code);
    let returns_integer = core.comp_type_returner(integer_type);
    let returner_code = core.value_quote_computation(returns_integer);
    let returns_returner = core.computation_return(returner_code);
    let one = integer(&mut core, Sign::NonNegative, Written("1"));
    let returns_one = core.computation_return(one);
    let answers_one = core.computation_lambda(returns_one);
    let source = CoreSource::new(&core, &[]);
    let body = |id| Root::Computation(CoreNode::Computation(id));
    assert_eq!(
        spelled(&source, body(answers_code)),
        faithful(Written("fn (a) { pure Integer }"))
    );
    assert_eq!(
        spelled(&source, body(returns_returner)),
        faithful(Written("pure (-F Integer)"))
    );
    assert_eq!(
        spelled(&source, body(answers_one)),
        faithful(Written("fn (a) { 1 }"))
    );
}

/// A body that ends answering a `run` keeps its `pure`: bare at a statement's
/// head, `run down(a)` opens a bind, `run x <- c ; …`, and does not parse
/// (#815).
#[test]
fn a_body_answering_a_run_keeps_its_pure_815()
{
    let mut core = CoreArena::new();
    let one = integer(&mut core, Sign::NonNegative, Written("1"));
    let returns_one = core.computation_return(one);
    let ran = core.value_run(returns_one);
    let returns_run = core.computation_return(ran);
    let answers_run = core.computation_lambda(returns_run);
    let source = CoreSource::new(&core, &[]);
    assert_eq!(
        spelled(
            &source,
            Root::Computation(CoreNode::Computation(answers_run))
        ),
        faithful(Written("fn (a) { pure (run (pure 1)) }"))
    );
}

/// A prelude primitive the surface writes as an operator is written so: an
/// infix one between its operands, a prefix one before its operand.
#[test]
fn a_prelude_operator_is_written_as_its_operator()
{
    let named = |name: &str| {
        PRELUDE
            .iter()
            .copied()
            .find(|primitive| <&'static str>::from(primitive.name()) == name)
            .expect("the prelude holds the primitive")
    };
    let mut core = CoreArena::new();
    let bound = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let added = core.computation_primitive(named("add"), Arguments::Binary([bound, bound]));
    let adds = core.computation_lambda(added);
    let negated = core.computation_primitive(named("neg"), Arguments::Unary(bound));
    let negates = core.computation_lambda(negated);
    let source = CoreSource::new(&core, &[]);
    let body = |id| Root::Computation(CoreNode::Computation(id));
    assert_eq!(
        spelled(&source, body(adds)),
        faithful(Written("fn (a) { a + a }"))
    );
    assert_eq!(
        spelled(&source, body(negates)),
        faithful(Written("fn (a) { -a }"))
    );
}

/// A bind of a computation ascribed a pure returner spells as the typed
/// bind it lowered from, its value type written after the binder; an
/// ascription anywhere else stands as its body, approximately, for the
/// surface writes it nowhere else.
#[test]
fn a_typed_bind_spells_as_written()
{
    let mut core = CoreArena::new();
    let bound = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let one = integer(&mut core, Sign::NonNegative, Written("1"));
    let integer_type = core.value_type_base(BaseType::Integer);
    let returns_integer = core.comp_type_returner(integer_type);
    let pure_one = core.computation_return(one);
    let ascribed = core.computation_ascribe(pure_one, returns_integer);
    let returned = core.computation_return(bound);
    let typed = core.computation_bind(ascribed, returned);
    let body = |id| Root::Computation(CoreNode::Computation(id));
    let source = CoreSource::new(&core, &[]);
    assert_eq!(
        spelled(&source, body(typed)),
        (
            "run a : Integer <- pure 1 ; a".to_owned(),
            Fidelity::Faithful
        ),
        "the typed bind spells its annotation"
    );
    assert_eq!(
        spelled(&source, body(ascribed)),
        ("1".to_owned(), Fidelity::Approximate),
        "a lone ascription stands as its body"
    );
}

/// An approximate printing names why it is approximate (#820): a fixpoint
/// written in the printer's `rec` notation, an ascription standing as its
/// body and a thunk left opaque each record their reason, so no printing is
/// approximate with nothing to say why.
#[test]
fn an_approximate_printing_names_its_reason_820()
{
    let mut core = CoreArena::new();
    let one = integer(&mut core, Sign::NonNegative, Written("1"));
    let pure_one = core.computation_return(one);
    let recursive =
        core.computation_fixpoint(pure_one, gandr_kernel_term::FixpointEvidence::Partial);
    let integer_type = core.value_type_base(BaseType::Integer);
    let returns_integer = core.comp_type_returner(integer_type);
    let ascribed = core.computation_ascribe(pure_one, returns_integer);
    let suspended = core.value_thunk(pure_one);
    let source = CoreSource::new(&core, &[]);
    let body = |id| Root::Computation(CoreNode::Computation(id));
    for (root, expected, reason) in [
        (
            body(recursive),
            "rec a { 1 }",
            Unspelled::Notation(Notation::Fixpoint),
        ),
        (body(ascribed), "1", Unspelled::Elided(Elided::Ascription)),
        (
            Root::Value(CoreNode::Value(suspended)),
            "<thunk>",
            Unspelled::Elided(Elided::Thunk),
        ),
    ] {
        assert_eq!(
            spelled_as(&source, root, Spelling::Unicode),
            ((expected.to_owned(), Fidelity::Approximate), vec![reason]),
            "{expected}"
        );
    }
}

/// A capability living in a scope's region names that scope, `at c`,
/// counted from the outermost scope the source names; one in a region
/// past the named scopes spells without it, approximately, and a held
/// one never names a scope.
#[test]
#[expect(
    clippy::literal_string_with_formatting_args,
    reason = "a capability's authority is spelled `Cap {op}`, which reads as a format argument"
)]
fn a_scoped_capability_names_its_scope_400()
{
    use gandr_core_term::effect::EffectName;
    use gandr_core_term::effect::EffectOp;
    use gandr_core_term::effect::EffectRow;
    use gandr_core_term::effect::EffectSig;
    use gandr_core_term::effect::capability::CapabilityGrade;
    use gandr_core_term::effect::capability::Region;
    use gandr_core_term::effect::capability::RegionDepth;

    let mut core = CoreArena::new();
    let integer = core.value_type_base(BaseType::Integer);
    let unit = core.value_type_product(&[]);
    let exit = EffectRow::singleton(
        EffectSig::new(EffectName::from("Proc"), [EffectOp {
            name: "exit".into(),
            payload: integer,
            reply: unit,
        }])
        .expect("one operation is a signature"),
    );
    let mut at =
        |region| core.value_type_capability(exit.clone(), CapabilityGrade::Durable, region);
    let outer = at(Region::Scoped(RegionDepth::from(1_u32)));
    let inner = at(Region::Scoped(RegionDepth::from(2_u32)));
    let held = at(Region::Held);
    let ty = |id| Root::Type(CoreNode::ValueType(id));
    let both = [Some(Name::from("c")), Some(Name::from("e"))];
    let named = CoreSource::new(&core, &[]).scoped(&both);
    assert_eq!(
        spelled(&named, ty(outer)),
        faithful(Written("Cap {exit} at c"))
    );
    assert_eq!(
        spelled(&named, ty(inner)),
        faithful(Written("Cap {exit} at e"))
    );
    assert_eq!(spelled(&named, ty(held)), faithful(Written("Cap {exit}")));
    let one = [Some(Name::from("c"))];
    let short = CoreSource::new(&core, &[]).scoped(&one);
    assert_eq!(
        spelled(&short, ty(inner)),
        approximate(Written("Cap {exit}")),
        "a region past the named scopes goes unwritten"
    );
    for unwritable in ["", "c d"] {
        let names = [Some(Name::from(unwritable))];
        let blank = CoreSource::new(&core, &[]).scoped(&names);
        assert_eq!(
            spelled(&blank, ty(outer)),
            approximate(Written("Cap {exit}")),
            "a scope named {unwritable:?} has no name the region could be written by"
        );
    }
}
