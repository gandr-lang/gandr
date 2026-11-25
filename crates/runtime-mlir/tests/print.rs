//! The print of a term of a signature as MLIR text, against a table of a part
//! of the `llvm` dialect stated by hand, and each refusal of the print.

#[cfg(test)]
mod tests
{
    use gandr_runtime_mlir::Naming;
    use gandr_runtime_mlir::Parameter;
    use gandr_runtime_mlir::Place;
    use gandr_runtime_mlir::PrintError;
    use gandr_runtime_mlir::Spelling;
    use gandr_runtime_mlir::Terminator;
    use gandr_runtime_mlir::ValueName;
    #[cfg(feature = "full")]
    use gandr_runtime_mlir::compile;
    use gandr_runtime_mlir::print_term;
    use gandr_theory_levitation::Attrs;
    use gandr_theory_levitation::BindingTerm;
    use gandr_theory_levitation::BridgeArity;
    use gandr_theory_levitation::DeclPolarity;
    use gandr_theory_levitation::FreeTerm;
    use gandr_theory_levitation::Name;
    use gandr_theory_levitation::NominalId;
    use gandr_theory_levitation::NominalSerial;
    use gandr_theory_levitation::OperDesc;
    use gandr_theory_levitation::SortDesc;
    use gandr_theory_levitation::SortIndex;
    use gandr_theory_levitation::SortRef;
    use gandr_theory_levitation::TheoryDesc;
    use gandr_theory_levitation::VariableIndex;

    /// An operation of one output.
    ///
    /// # Specification
    /// trivial.
    fn op<const N: usize>(
        name: impl Into<Name>,
        inputs: [SortRef; N],
        output: impl Into<Name>,
    ) -> OperDesc
    {
        OperDesc::new(
            name,
            BridgeArity::single_output(inputs, SortRef::new("", output)),
            Attrs::empty(),
        )
    }

    /// The port `name` of a value of the type `index`.
    ///
    /// # Specification
    /// trivial.
    fn val(
        name: impl Into<Name>,
        index: FreeTerm,
    ) -> SortRef
    {
        SortRef::new(name, "Val").applied([index])
    }

    /// The rest of a body that binds `binder` of the type `index`.
    ///
    /// # Specification
    /// trivial.
    fn binds(
        binder: impl Into<Name>,
        index: FreeTerm,
    ) -> SortRef
    {
        SortRef::new("rest", "Body").pi_plus([SortIndex::new(binder, "Val").applied([index])])
    }

    /// A part of the `llvm` dialect, in the forms of the block of `std`: the
    /// types `int1` and `int32`, a value with its type as its index, and the
    /// rest of a body as a port. `cmp`, `bad` and `pair` meet refusals.
    ///
    /// # Specification
    /// trivial.
    fn llvm() -> TheoryDesc<()>
    {
        let t = || FreeTerm::var("t");
        let two = || [SortRef::new("t", "Ty"), val("left", t()), val("right", t())];
        let [ty, left, right] = two();
        let [ty2, left2, right2] = two();
        TheoryDesc::new(
            NominalId::new(NominalSerial::from(0_u64), "Llvm"),
            [],
            [],
            [
                op("int1", [], "Ty"),
                op("int32", [], "Ty"),
                op("add", [ty, left, right, binds("x", t())], "Body"),
                op(
                    "icmp_ult",
                    [ty2, left2, right2, binds("b", FreeTerm::op("int1", []))],
                    "Body",
                ),
                op(
                    "return",
                    [SortRef::new("t", "Ty"), val("value", t())],
                    "Body",
                ),
                op(
                    "cmp",
                    [
                        SortRef::new("predicate", "Predicate"),
                        binds("b", FreeTerm::op("int1", [])),
                    ],
                    "Body",
                ),
                op("bad", [binds("x", FreeTerm::var("u"))], "Body"),
                op("lt", [], "Predicate"),
                op(
                    "aligned",
                    [
                        SortRef::new("alignment", "Integer"),
                        binds("b", FreeTerm::op("int1", [])),
                    ],
                    "Body",
                ),
                op(
                    "region",
                    [
                        SortRef::new("inside", "Region"),
                        binds("b", FreeTerm::op("int1", [])),
                    ],
                    "Body",
                ),
                op(
                    "pair",
                    [SortRef::new("rest", "Body").pi_plus([
                        SortIndex::new("x", "Val").applied([FreeTerm::op("int1", [])]),
                        SortIndex::new("y", "Val").applied([FreeTerm::op("int1", [])]),
                    ])],
                    "Body",
                ),
            ],
            [],
            DeclPolarity::Data,
            Attrs::empty(),
        )
        .with_sorts([
            SortDesc::new("Ty", DeclPolarity::Data),
            SortDesc::family("Val", DeclPolarity::Data, [SortIndex::new("t", "Ty")])
                .representable(),
            SortDesc::new("Body", DeclPolarity::Data),
            SortDesc::new("Predicate", DeclPolarity::Data),
        ])
    }

    /// The node `name` over `arguments`.
    ///
    /// # Specification
    /// trivial.
    fn node<const N: usize>(
        name: impl Into<Name>,
        arguments: [BindingTerm; N],
    ) -> BindingTerm
    {
        BindingTerm::operation(name.into(), arguments)
    }

    /// The variable `index`, from the newest entry of the context.
    ///
    /// # Specification
    /// trivial.
    fn var(index: impl Into<VariableIndex>) -> BindingTerm
    {
        BindingTerm::variable(index.into())
    }

    /// The constant `name`.
    ///
    /// # Specification
    /// trivial.
    fn constant(name: impl Into<Name>) -> BindingTerm
    {
        node(name, [])
    }

    /// The parameters `a` and `b` of the type `i32`.
    ///
    /// # Specification
    /// trivial.
    fn parameters() -> [Parameter<'static>; 2]
    {
        ["a", "b"].map(|name| Parameter {
            name: ValueName::from(name),
            ty: Spelling::from("i32"),
        })
    }

    #[test]
    fn an_addition_prints_as_one_llvm_add()
    {
        // `a` is the variable 1 and `b` the variable 0; under the binder of
        // the result, the result is the variable 0.
        let term = node("add", [
            constant("int32"),
            var(1_usize),
            var(0_usize),
            node("return", [constant("int32"), var(0_usize)]),
        ]);
        let printed = print_term(&llvm(), &Naming::NONE, &term, (&parameters(), Place::ALONE))
            .expect("the addition prints");
        assert_eq!(
            printed.as_ref(),
            concat!(
                "%v0 = \"llvm.add\"(%a, %b) : (i32, i32) -> i32\n",
                "\"llvm.return\"(%v0) : (i32) -> ()\n",
            ),
            "one `llvm.add` with its operands, their types and the type of its result"
        );
        // The verifier of the shim reads the print under the feature `full`.
        #[cfg(feature = "full")]
        {
            let text = format!("llvm.func @add(%a: i32, %b: i32) -> i32 {{\n{printed}}}\n");
            let object = compile(text.as_str().into(), "x86_64-unknown-linux-gnu".into());
            assert!(
                object.is_ok(),
                "the verifier of the shim accepts the print: {object:?}\n{text}"
            );
        }
    }

    #[test]
    fn a_result_is_the_operand_of_the_next_operation()
    {
        let term = node("add", [
            constant("int32"),
            var(1_usize),
            var(0_usize),
            node("icmp_ult", [
                constant("int32"),
                var(0_usize),
                var(2_usize),
                node("return", [constant("int1"), var(0_usize)]),
            ]),
        ]);
        let printed = print_term(&llvm(), &Naming::NONE, &term, (&parameters(), Place::ALONE))
            .expect("the comparison prints");
        assert_eq!(
            printed.as_ref(),
            concat!(
                "%v0 = \"llvm.add\"(%a, %b) : (i32, i32) -> i32\n",
                "%v1 = \"llvm.icmp_ult\"(%v0, %a) : (i32, i32) -> i1\n",
                "\"llvm.return\"(%v1) : (i1) -> ()\n",
            ),
            "the sum is the first operand of the comparison, whose result has the type of the constant `int1`"
        );
    }

    #[test]
    fn a_body_in_place_numbers_its_results_from_the_first_and_omits_its_terminator()
    {
        let term = node("add", [
            constant("int32"),
            var(1_usize),
            var(0_usize),
            node("add", [
                constant("int32"),
                var(0_usize),
                var(2_usize),
                node("return", [constant("int32"), var(0_usize)]),
            ]),
        ]);
        let place = Place {
            first: 7,
            terminator: Terminator::Omit,
        };
        let printed = print_term(&llvm(), &Naming::NONE, &term, (&parameters(), place))
            .expect("the body prints in place");
        assert_eq!(
            (printed.as_ref(), printed.results()),
            (
                concat!(
                    "%v7 = \"llvm.add\"(%a, %b) : (i32, i32) -> i32\n",
                    "%v8 = \"llvm.add\"(%v7, %a) : (i32, i32) -> i32\n",
                ),
                &[String::from("i32"), String::from("i32")][..]
            ),
            "the results count from the first one, the terminator does not print, and each result has its type"
        );
        // The verifier of the shim reads the body under the feature `full`.
        #[cfg(feature = "full")]
        {
            let text = format!(
                "llvm.func @f(%a: i32, %b: i32) -> i32 {{\n{printed}\"llvm.return\"(%v8) : (i32) -> ()\n}}\n"
            );
            let object = compile(text.as_str().into(), "x86_64-unknown-linux-gnu".into());
            assert!(
                object.is_ok(),
                "the verifier of the shim accepts the function that holds the body: {object:?}\n{text}"
            );
        }
    }

    #[test]
    fn each_refusal_has_a_term_that_meets_it()
    {
        let table = llvm();
        let refusal = |term: BindingTerm| {
            print_term(&table, &Naming::NONE, &term, (&parameters(), Place::ALONE))
                .expect_err("the print refuses the term")
        };
        let end = || node("return", [constant("int32"), var(0_usize)]);
        let name = |name: &str| Name::from(name);
        assert_eq!(
            refusal(node("mul", [])),
            PrintError::UnknownOperation(name("mul"))
        );
        assert_eq!(
            refusal(node("add", [constant("int32"), var(1_usize), end()])),
            PrintError::Arity(name("add"))
        );
        assert_eq!(refusal(var(0_usize)), PrintError::NotABody);
        assert_eq!(
            refusal(node("add", [
                constant("int32"),
                var(5_usize),
                var(0_usize),
                end()
            ])),
            PrintError::UnboundVariable(VariableIndex::from(5_usize))
        );
        assert_eq!(
            refusal(node("add", [
                constant("int32"),
                constant("int32"),
                var(0_usize),
                end()
            ])),
            PrintError::NotAValue(name("left"))
        );
        assert_eq!(
            refusal(node("add", [
                var(0_usize),
                var(1_usize),
                var(0_usize),
                end()
            ])),
            PrintError::NotAType(name("t"))
        );
        assert_eq!(
            refusal(node("cmp", [constant("int1"), end()])),
            PrintError::NotAnAttribute(name("predicate")),
            "`int1` is no constant of `Predicate`"
        );
        assert_eq!(
            refusal(node("cmp", [constant("lt"), end()])),
            PrintError::NoMlirValue(name("lt")),
            "with no naming, a constant has no MLIR value"
        );
        assert_eq!(
            refusal(node("aligned", [constant("four"), end()])),
            PrintError::NotAnAttribute(name("alignment")),
            "an integer port takes a decimal literal"
        );
        assert_eq!(
            refusal(node("region", [constant("x"), end()])),
            PrintError::Unprinted(name("inside")),
            "a port of a sort outside the table and the host types"
        );
        assert_eq!(
            refusal(node("bad", [end()])),
            PrintError::Untyped(name("x"))
        );
        assert_eq!(
            refusal(node("pair", [end()])),
            PrintError::Results(name("pair"))
        );
    }
}
