//! The printer through its public surface: every former at its exact
//! spelling, and representative types and values pinned at two page widths.
//!
//! Paired goldens present one node at the narrow page (40 columns) and the wide
//! page (100 columns). The wide page must hold exactly the one-line spelling
//! written beside the fixture — the flattened image of every document is that
//! line — and both pages are compared whole against `tests/golden/`.
//! A zero-column pair pins fallback when both separator branches are tainted.
//! Regenerate with `UPDATE_EXPECT=1` and review the diff.

#[cfg(test)]
mod tests
{
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
    use gandr_kernel_strata::Level;
    use gandr_kernel_strata::LevelConstant;
    use gandr_kernel_strata::LevelVar;
    use gandr_kernel_strata::LevelVarIndex;
    use gandr_kernel_term::BaseType;
    use gandr_kernel_term::ConstantIndex;
    use gandr_kernel_term::DeBruijnIndex;
    use gandr_kernel_term::FractionDigits;
    use gandr_kernel_term::GroundSort;
    use gandr_kernel_term::IntegerLiteral;
    use gandr_kernel_term::Literal;
    use gandr_kernel_term::Magnitude;
    use gandr_kernel_term::NumericLiteral;
    use gandr_kernel_term::Side;
    use gandr_kernel_term::Sign;
    use gandr_kernel_term::StringLiteral;
    use gandr_surface_pretty::CoreNode;
    use gandr_surface_pretty::CoreSource;
    use gandr_surface_pretty::DEPTH_LIMIT;
    use gandr_surface_pretty::Fidelity;
    use gandr_surface_pretty::Former;
    use gandr_surface_pretty::Name;
    use gandr_surface_pretty::PageWidth;
    use gandr_surface_pretty::Presentation;
    use gandr_surface_pretty::Source;
    use gandr_surface_pretty::present_type;
    use gandr_surface_pretty::present_value;

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
        let left = core.value_injection(Side::Left, one);
        let right = core.value_injection(Side::Right, two);
        let pair = core.value_pair(left, right);
        let read = normal_form(&mut core, pair);
        pin(&CoreSource::new(&core, &[]), Root::Value(read), Pinned {
            name: "pair_injections",
            flat: "(Inl(1), Inr(\"two\"))",
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
            value = core.value_injection(Side::Left, value);
        }
        let read = normal_form(&mut core, value);
        let flat = format!("{}<deep>{}", "Inl(".repeat(limit), ")".repeat(limit));
        pin(&CoreSource::new(&core, &[]), Root::Value(read), Pinned {
            name: "deep_value",
            flat: flat.as_str(),
            fidelity: Fidelity::Approximate,
        });
    }

    /// A value too long for the narrow page breaks after a comma, its
    /// continuation two columns in: the prior record of three fields, carried
    /// by the fragment as a right-nested pair of the same three values.
    #[test]
    fn record_value_breaks_fields_at_the_narrow_page()
    {
        let mut core = CoreArena::new();
        let machine = text(&mut core, Written("analytical engine"));
        let name = text(&mut core, Written("ada lovelace"));
        let year = integer(&mut core, Sign::NonNegative, Written("1843"));
        let rest = core.value_pair(name, year);
        let record = core.value_pair(machine, rest);
        let read = normal_form(&mut core, record);
        pin(&CoreSource::new(&core, &[]), Root::Value(read), Pinned {
            name: "record_value",
            flat: "(\"analytical engine\", (\"ada lovelace\", 1843))",
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
        let pair = core.value_pair(first, second);
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

    /// Every value-type and computation-type former of the core spells as the
    /// grammar parses it: the two bridges with their operand parenthesized
    /// unless atomic, product and sum right-associative with the product
    /// binding tighter, the arrow's domain bare up to a sum, a decode as the
    /// code it reads, and an abstract type by its name.
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
        let string_unit = core.value_type_product(string, unit);
        let right_nested = core.value_type_product(integer, string_unit);
        let integer_string = core.value_type_product(integer, string);
        let left_nested = core.value_type_product(integer_string, unit);
        let product_then_sum = core.value_type_sum(integer_string, unit);
        let sum_of_product = core.value_type_sum(integer, string_unit);
        let integer_or_string = core.value_type_sum(integer, string);
        let sum_then_product = core.value_type_product(integer_or_string, unit);
        let string_or_unit = core.value_type_sum(string, unit);
        let sum_chain = core.value_type_sum(integer, string_or_unit);
        let sum_left = core.value_type_sum(integer_or_string, unit);
        let thunk_in_product = core.value_type_product(thunk, unit);
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
        let source = CoreSource::new(&core, &names);
        for (root, spelling) in [
            (CoreNode::ValueType(integer), "Integer"),
            (CoreNode::ValueType(string), "String"),
            (CoreNode::ValueType(unit), "Unit"),
            (CoreNode::ValueType(accumulator), "Accumulator"),
            (CoreNode::ValueType(thunk), "+U (-F Integer)"),
            (CoreNode::CompType(returns_thunk), "-F (+U (-F Unit))"),
            (CoreNode::ValueType(right_nested), "Integer * String * Unit"),
            (
                CoreNode::ValueType(left_nested),
                "(Integer * String) * Unit",
            ),
            (
                CoreNode::ValueType(product_then_sum),
                "Integer * String + Unit",
            ),
            (
                CoreNode::ValueType(sum_of_product),
                "Integer + String * Unit",
            ),
            (
                CoreNode::ValueType(sum_then_product),
                "(Integer + String) * Unit",
            ),
            (CoreNode::ValueType(sum_chain), "Integer + String + Unit"),
            (CoreNode::ValueType(sum_left), "(Integer + String) + Unit"),
            (
                CoreNode::ValueType(thunk_in_product),
                "+U (-F Integer) * Unit",
            ),
            (
                CoreNode::CompType(sum_domain),
                "Integer + String -> -F Unit",
            ),
            (
                CoreNode::CompType(thunk_domain),
                "+U (Integer -> -F Unit) -> -F Unit",
            ),
            (CoreNode::CompType(returns_product), "-F (Integer * String)"),
            (CoreNode::CompType(returns_decoded), "-F (Integer * String)"),
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
        let squared = core.value_type_product(element, element);
        let returns_squared = core.comp_type_returner(squared);
        let squared_code = core.value_quote_computation(returns_squared);
        let squaring = core.value_static_lambda(squared_code);

        let outer = bound(&mut core, DeBruijnIndex::from(1_u32));
        let inner = bound(&mut core, DeBruijnIndex::from(0_u32));
        let both = core.value_type_product(outer, inner);
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
            (Root::Value(CoreNode::Value(squaring)), "\\a. -F (a * a)"),
            (Root::Value(CoreNode::Value(nested)), "\\a. \\b. a * b"),
            (Root::Value(CoreNode::Value(once)), "t(Integer)"),
            (
                Root::Value(CoreNode::Value(applied)),
                "t(\\a. -F (a * a), Integer, Integer)",
            ),
            (
                Root::Type(CoreNode::ValueType(decoded)),
                "t(\\a. -F (a * a), Integer, Integer)",
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
            faithful(Written("()")),
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
}
