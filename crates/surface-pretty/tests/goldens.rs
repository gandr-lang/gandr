//! The printer through its public surface: every former at its exact
//! spelling, and representative types and values pinned at two page widths.
//!
//! Paired goldens present one node at the narrow page (40 columns) and the wide
//! page (100 columns). The wide page must hold exactly the one-line spelling
//! written beside the fixture — the flattened image of every document is that
//! line — and both pages are compared whole against `tests/golden/`.
//! A zero-column pair pins fallback when both separator branches are tainted.
//! Regenerate with `UPDATE_EXPECT=1` and review the diff.

extern crate alloc;

#[cfg(test)]
mod tests
{
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
    use gandr_core_term::CoreArena;
    use gandr_core_term::DefinitionalEnvironment;
    use gandr_core_term::Sort;
    use gandr_core_term::SortParameter;
    use gandr_core_term::ValueId;
    use gandr_core_term::ValueTypeId;
    use gandr_core_term::Zone;
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
    use gandr_kernel_term::StringLiteral;
    use gandr_kernel_term::Summand;
    use gandr_surface_pretty::Arity;
    use gandr_surface_pretty::Component;
    use gandr_surface_pretty::CoreNode;
    use gandr_surface_pretty::CoreSource;
    use gandr_surface_pretty::DEPTH_LIMIT;
    use gandr_surface_pretty::Fidelity;
    use gandr_surface_pretty::Former;
    use gandr_surface_pretty::Name;
    use gandr_surface_pretty::PageWidth;
    use gandr_surface_pretty::Presentation;
    use gandr_surface_pretty::Source;
    use gandr_surface_pretty::present_computation;
    use gandr_surface_pretty::present_type;
    use gandr_surface_pretty::present_value;
    use gandr_theory_sites::Degree;
    use gandr_theory_sites::PortCount;
    use gandr_theory_sites::Profile;
    use gandr_theory_sites::ShapeSize;

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

    /// `root` of `source` laid out at `page`.
    ///
    /// # Specification
    /// - requires: the fixture fits the default build and render ceilings.
    /// - ensures: the selected type or value presentation has no carriage
    ///   return or tab; layout-owned line endings are line feeds.
    /// - provides: a presentation for exact fixture observations.
    /// - panics: if the presentation refuses.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — finite type, value and control-string fixtures expose
    ///   wrong root selection or unescaped controls. Meter exhaustion is
    ///   outside these fixtures, whose helper deliberately treats refusal as
    ///   failure.
    /// - witness: `goldens::tests::every_type_former_spells_as_the_grammar_writes_it`
    /// - witness: `goldens::tests::every_value_leaf_spells_as_the_surface_writes_it`
    /// - witness: `goldens::tests::string_controls_stay_in_one_escaped_literal`
    #[spec(ensures: |ref ret| !ret.as_ref().contains(['\r', '\t']))]
    fn presented<S>(
        source: &S,
        root: Root,
        page: PageWidth,
    ) -> Presentation
    where
        S: Source<Node = CoreNode>,
    {
        match root {
            | Root::Type(node) => present_type(source, node, page),
            | Root::Value(node) => present_value(source, node, page),
            | Root::Computation(node) => present_computation(source, node, page),
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
    ///   spelling without a line ending or tab. The source fits default
    ///   ceilings.
    /// - ensures: both pages match their files and expected fidelity; a
    ///   spelling that fits the wide page appears there unchanged.
    /// - provides: independent byte-for-byte layout observations.
    /// - panics: on a layout refusal, unreadable golden or mismatched
    ///   observation.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — finite narrow and wide arrow, bracket and
    ///   control-string fixtures expose wrong breaks, omitted escapes and
    ///   changed fidelity. Filesystem failure and arbitrary fixture keys are
    ///   not exercised.
    /// - witness: `goldens::tests::arrow_chain_breaks_before_each_continuation`
    /// - witness: `goldens::tests::pair_of_injections_pins_sum_notation`
    /// - witness: `goldens::tests::string_controls_stay_in_one_escaped_literal`
    #[spec(requires: !pinned.name.is_empty()
        && !pinned.name.contains(['/', '\\']) && !pinned.flat.contains(['\r', '\n', '\t'])
    )]
    fn pin(
        source: &CoreSource<'_>,
        root: Root,
        pinned: Pinned<'_>,
    )
    {
        let at_narrow = presented(source, root, narrow());
        let at_wide = presented(source, root, wide());
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
    /// - ensures: wide-page text contains no carriage return or tab, and
    ///   carries the presentation's node-derived fidelity.
    /// - provides: an observation independent of the golden-file helper.
    /// - panics: if presentation refuses.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — exact type, literal and malformed-source observations
    ///   distinguish wrong spelling and fidelity. Other page widths are outside
    ///   this wide-page helper's evidence.
    /// - witness: `goldens::tests::every_type_former_spells_as_the_grammar_writes_it`
    /// - witness: `goldens::tests::every_value_leaf_spells_as_the_surface_writes_it`
    /// - witness: `goldens::tests::misplaced_and_unreadable_nodes_spell_unknown`
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
    /// - requires: a held closed value whose evaluation and unfolding readback
    ///   fit 4,096 fuel steps and the fixture arena.
    /// - ensures: a live core value handle denoting the fixture's normal form.
    /// - provides: the values the concrete reader sees after normalization.
    /// - panics: if evaluation or readback refuses.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the finite literal, pair, injection and thunk
    ///   fixtures observe their evaluated presentation. Dangling inputs, fuel
    ///   exhaustion and arbitrary closed values are outside this fixture
    ///   helper's domain.
    /// - witness: `goldens::tests::every_value_leaf_spells_as_the_surface_writes_it`
    /// - witness: `goldens::tests::pair_of_injections_pins_sum_notation`
    /// - witness: `goldens::tests::record_value_breaks_fields_at_the_narrow_page`
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
        let evaluated = eval_value(core, &mut domain, definitions, fuel, value)
            .expect("a closed value evaluates");
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
    /// - ensures: a held integer literal with canonical magnitude; a zero
    ///   magnitude is non-negative, otherwise the supplied sign is retained.
    /// - provides: concrete signed literals for presentation observations.
    /// - panics: if decimal construction or arena allocation refuses.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — signed integer and injection fixtures observe the
    ///   stored literal through exact presentation. Padded digits, negative
    ///   zero and malformed decimal input are outside these fixtures.
    /// - witness: `goldens::tests::every_value_leaf_spells_as_the_surface_writes_it`
    /// - witness: `goldens::tests::pair_of_injections_pins_sum_notation`
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
    /// - ensures: an element type at level zero whose code is the
    ///   intuitionistic variable at the supplied de Bruijn index.
    /// - provides: dependent types referring to their enclosing fixture
    ///   binders.
    /// - panics: if arena allocation refuses.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — nested dependent arrows and static abstractions
    ///   observe the correct binder reference, distinguishing shifted indices
    ///   and the wrong variable zone. Other level targets are not fixture
    ///   inputs.
    /// - witness: `goldens::tests::long_dependent_function_type_breaks_at_the_narrow_page`
    /// - witness: `goldens::tests::a_binder_skips_the_names_the_type_mentions`
    /// - witness: `goldens::tests::static_operators_spell_as_the_grammar_writes_them`
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
        /// - ensures: the stored former at a held row, unreadable beyond the
        ///   table.
        /// - provides: deliberately malformed graphs for the public reader.
        /// - fails: never.
        /// - panics: none.
        ///
        /// # Adequacy
        /// - hypothesis: L3 — misplaced children, an empty table, a dangling
        ///   child and a cycle distinguish shifted lookup and fabricated
        ///   formers. Other hand-built graphs are outside the finite
        ///   malformed-source fixtures.
        /// - witness: `goldens::tests::misplaced_and_unreadable_nodes_spell_unknown`
        #[spec(ensures: |ret| self.0.get(node.0).map_or(
            matches!(ret, Former::Unreadable),
            |held| core::mem::discriminant(held) == core::mem::discriminant(&ret),
        ))]
        fn read(
            &self,
            node: Row,
        ) -> Former<'_, Row>
        {
            self.0.get(node.0).copied().unwrap_or(Former::Unreadable)
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
    /// - hypothesis: L3 — type/value misplacement, missing rows and a cycle
    ///   observe position checking and approximation. Layout-meter exhaustion
    ///   is outside this helper's finite fixtures.
    /// - witness: `goldens::tests::misplaced_and_unreadable_nodes_spell_unknown`
    #[spec(ensures: |ref ret| !ret.0.contains(['\r', '\t']))]
    fn table_spelling(
        rows: Vec<Former<'static, Row>>,
        reading: Reading,
    ) -> (String, Fidelity)
    {
        let table = Table(rows);
        let presentation = match reading {
            | Reading::AsType => present_type(&table, Row(0), wide()),
            | Reading::AsValue => present_value(&table, Row(0), wide()),
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

    /// A record type and a record spell each field after its own label, in
    /// label order whatever order they were given in; the surface writes no
    /// empty record, `#{}` being the unit, so one spells `?`.
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
                approximate(Written("?")),
            ),
            (
                Root::Value(CoreNode::Value(empty)),
                approximate(Written("?")),
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
    /// unless atomic, a product, a sum or a lazy pair between its braces with
    /// any former bare among its entries, the arrow's domain bare up to a
    /// bridge, a decode as the code it reads, and an abstract type by its
    /// name.
    #[test]
    fn every_type_former_spells_as_the_grammar_writes_it()
    {
        let names = [
            Name::from("Accumulator"),
            Name::from("Carry"),
            Name::from("small"),
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
        let lazy = core.comp_type_with(returns_integer, returns_unit);
        let lazy_chain = core.comp_type_with(function, lazy);
        let suspended_lazy = core.value_type_thunk(lazy);
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
        ] {
            assert_eq!(
                spelled(&source, Root::Type(root)),
                faithful(Written(spelling)),
                "{root:?} spells as the grammar writes it"
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
        let universe = small_universe(&mut core);
        let abstract_a = core.value_type_abstract(ConstantIndex::from(0_usize));
        let outer = bound(&mut core, DeBruijnIndex::from(1_u32));
        let returns_outer = core.comp_type_returner(outer);
        let body = core.comp_type_arrow(abstract_a, returns_outer);
        let pi_inner = core.comp_type_pi(universe, body);
        let pi_outer = core.comp_type_pi(universe, pi_inner);
        assert_eq!(
            spelled(
                &CoreSource::new(&core, &names),
                Root::Type(CoreNode::CompType(pi_outer))
            ),
            faithful(Written("(b : Type) -> (c : Type) -> a -> -F b")),
            "the binders skip the abstract type `a`"
        );
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
        let negative =
            core.value_type_universe(Sort::Ground(GroundSort::Computation), Level::zero());
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

        let variable = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
        let identity = core.value_static_lambda(variable);
        let redex = core.value_static_application(identity, integer_code);

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
            (Root::Value(CoreNode::Value(redex)), "(\\a. a)(Integer)"),
        ] {
            assert_eq!(
                spelled(&source, root),
                faithful(Written(spelling)),
                "{root:?} spells as the grammar writes it"
            );
        }
    }

    /// Every value leaf spells as the surface writes it — a signed integer,
    /// a numeric literal with and without a fraction, a string's escapes, the
    /// unit and a constant by its name — and a thunk, whose body a reader
    /// cannot see, is `<thunk>` and approximate.
    #[test]
    fn every_value_leaf_spells_as_the_surface_writes_it()
    {
        let names = [Name::from("Accumulator"), Name::from("Carry")];
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
    /// surface round-trip fidelity, because the parser has no path syntax.
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
        // A case analysis has no spelling here.
        let case = core.computation_case(bound, &[returned, returned]);
        let analysed = core.computation_lambda(case);
        let names = [Name::from("kept")];
        let source = CoreSource::new(&core, &names);
        let body = |id| Root::Computation(CoreNode::Computation(id));
        for (root, expected, fidelity) in [
            (body(identity), "fn (a) { a }", Fidelity::Faithful),
            (body(calling), "fn (a) { kept(a) }", Fidelity::Faithful),
            (body(forced), "force kept", Fidelity::Faithful),
            (body(pure_one), "1", Fidelity::Faithful),
            (body(suspends), "thunk { (pure 1)(2) }", Fidelity::Faithful),
            (body(analysed), "fn (a) { ? }", Fidelity::Approximate),
        ] {
            assert_eq!(
                spelled(&source, root),
                (expected.to_owned(), fidelity),
                "{expected}"
            );
        }
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
    }
}
