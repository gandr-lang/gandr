//! The read of the facts of a body into a term of the block of `std.llvm`:
//! the read of the print of a term through the shim, and each refusal of the
//! read. They run under the feature `full`, which links the shim.

#![cfg(feature = "full")]

#[cfg(test)]
mod tests
{
    use gandr_core_term::CoreArena;
    use gandr_runtime_mlir::Hole;
    use gandr_runtime_mlir::Naming;
    use gandr_runtime_mlir::Operand;
    use gandr_runtime_mlir::Operation;
    use gandr_runtime_mlir::Parameter;
    use gandr_runtime_mlir::Place;
    use gandr_runtime_mlir::Spelling;
    use gandr_runtime_mlir::TermReadError;
    use gandr_runtime_mlir::Text;
    use gandr_runtime_mlir::ValueName;
    use gandr_runtime_mlir::print_term;
    use gandr_runtime_mlir::read;
    use gandr_runtime_mlir::read_term;
    use gandr_surface_grammar::built_in;
    use gandr_surface_lowering::LoweringBudget;
    use gandr_surface_lowering::description::DescriptionGrade;
    use gandr_surface_lowering::lower_module;
    use gandr_surface_lowering::namespace::Recognition;
    use gandr_surface_parser::parse;
    use gandr_surface_syntax::SourceText;
    use gandr_theory_levitation::BindingTerm;
    use gandr_theory_levitation::Name;
    use gandr_theory_levitation::TheoryDesc;
    use gandr_theory_levitation::VariableIndex;

    /// `std.llvm`, the block of the fragment.
    const LLVM: &str = include_str!("../../../library/std/src/llvm.gandr");

    /// The last line of the print of a term: the terminator that the shim puts
    /// after a body.
    const TERMINATOR: &str = "\"llvm.unreachable\"() : () -> ()\n";

    /// The table of the block of `std.llvm`, from its source.
    ///
    /// # Specification
    /// trivial.
    fn llvm() -> TheoryDesc<DescriptionGrade>
    {
        let pbg = built_in().expect("the built-in surface passes each gate");
        let tree = parse(&pbg, SourceText::from(LLVM))
            .expect("the block parses")
            .into_tree();
        let mut arena = CoreArena::new();
        let module = lower_module(
            &pbg,
            &tree,
            &mut arena,
            LoweringBudget::DEFAULT,
            Recognition::default(),
        )
        .unwrap_or_else(|refusal| panic!("the block lowers: {refusal}"));
        let theories: Vec<_> = module.theories().collect();
        let [ref theory] = *theories.as_slice()
        else {
            panic!("the module has one block");
        };
        theory.description.clone()
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

    /// The variable `index`, from the newest value of the context.
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

    /// The end of a body: the terminator that the shim puts after it.
    ///
    /// # Specification
    /// trivial.
    fn end() -> BindingTerm
    {
        constant("unreachable")
    }

    /// Print `term` with `holes` as its parameters, read the body with the
    /// shim, and read its facts into a term.
    ///
    /// # Specification
    /// trivial.
    fn print_then_read(
        table: &TheoryDesc<DescriptionGrade>,
        term: &BindingTerm,
        holes: &[Hole<'_>],
    ) -> BindingTerm
    {
        let parameters: Vec<Parameter<'_>> = holes
            .iter()
            .map(|hole| Parameter {
                name: ValueName::from(hole.name),
                ty: Spelling::from(hole.ty),
            })
            .collect();
        let printed = print_term(table, &Naming::NONE, term, (&parameters, Place::ALONE))
            .unwrap_or_else(|error| panic!("the term prints: {error}"));
        let body = printed
            .as_ref()
            .strip_suffix(TERMINATOR)
            .unwrap_or_else(|| panic!("the print ends with the terminator:\n{printed}"));
        let operations = read(Text::from(body), holes)
            .unwrap_or_else(|error| panic!("the shim reads the print: {error}\n{body}"));
        read_term(table, &Naming::NONE, &operations, holes)
            .unwrap_or_else(|error| panic!("the facts read: {error}\n{body}"))
    }

    #[test]
    fn the_read_of_the_print_of_a_term_is_that_term()
    {
        let table = llvm();
        let two = [
            Hole {
                name: "a",
                ty: "i32",
            },
            Hole {
                name: "b",
                ty: "i32",
            },
        ];
        let binary = [
            "add", "sub", "mul", "udiv", "sdiv", "urem", "srem", "and", "or", "xor", "shl", "lshr",
            "ashr",
        ];
        for name in binary {
            let term = node(name, [constant("int32"), var(1_usize), var(0_usize), end()]);
            assert_eq!(
                print_then_read(&table, &term, &two),
                term,
                "`{name}`: the read of the print is the term"
            );
        }
        let byte = [Hole {
            name: "a",
            ty: "i8",
        }];
        let word = [Hole {
            name: "a",
            ty: "i64",
        }];
        let casts = [
            ("zext", "int8", "int64", &byte),
            ("sext", "int8", "int64", &byte),
            ("trunc", "int64", "int8", &word),
        ];
        for (name, from, to, holes) in casts {
            let term = node(name, [constant(from), constant(to), var(0_usize), end()]);
            assert_eq!(
                print_then_read(&table, &term, holes),
                term,
                "`{name}`: the read of the print is the term"
            );
        }
        let term = node("inttoptr", [constant("int64"), var(0_usize), end()]);
        assert_eq!(
            print_then_read(&table, &term, &word),
            term,
            "`inttoptr`: the type of the result is the constant `ptr` of the index"
        );
    }

    #[test]
    fn a_result_reads_as_the_operand_of_the_next_operation()
    {
        let table = llvm();
        let holes = [
            Hole {
                name: "a",
                ty: "i8",
            },
            Hole {
                name: "b",
                ty: "i64",
            },
        ];
        // Under the binder of the extension, the extension is the variable 0,
        // `b` the variable 1 and `a` the variable 2.
        let term = node("zext", [
            constant("int8"),
            constant("int64"),
            var(1_usize),
            node("mul", [
                constant("int64"),
                var(0_usize),
                var(1_usize),
                node("inttoptr", [constant("int64"), var(0_usize), end()]),
            ]),
        ]);
        assert_eq!(
            print_then_read(&table, &term, &holes),
            term,
            "each result is a variable of the operations after it"
        );
    }

    #[test]
    fn an_operation_outside_the_block_is_refused_by_its_name()
    {
        let table = llvm();
        let holes = [
            Hole {
                name: "a",
                ty: "f64",
            },
            Hole {
                name: "b",
                ty: "f64",
            },
        ];
        let operations = read(Text::from("%r = llvm.fadd ${a}, ${b} : f64\n"), &holes)
            .unwrap_or_else(|error| panic!("the shim reads the body: {error}"));
        assert_eq!(
            read_term(&table, &Naming::NONE, &operations, &holes),
            Err(TermReadError::UnknownOperation(Name::from("llvm.fadd"))),
            "the block has no `fadd`"
        );
    }

    /// The results of an operation that gives none.
    const NO_RESULT: [&str; 0] = [];

    /// The facts of one operation with `operands` and `results`.
    ///
    /// # Specification
    /// trivial.
    fn fact<R, const N: usize, const M: usize>(
        name: impl Into<String>,
        operands: [Operand; N],
        results: [R; M],
    ) -> Operation
    where
        R: Into<String>,
    {
        Operation {
            name: name.into(),
            operands: operands.into(),
            attributes: Vec::new(),
            results: results.map(Into::into).into(),
        }
    }

    #[test]
    fn each_refusal_has_facts_that_meet_it()
    {
        let table = llvm();
        let name = |name: &'static str| Name::from(name);
        let two = |ty: &'static str| [Hole { name: "a", ty }, Hole { name: "b", ty }];
        let refusal = |operations: &[Operation], holes: &[Hole<'_>]| {
            read_term(&table, &Naming::NONE, operations, holes)
                .expect_err("the read refuses the facts")
        };
        let both = [Operand::Hole(0), Operand::Hole(1)];
        assert_eq!(
            refusal(&[fact("arith.addi", both, ["i32"])], &two("i32")),
            TermReadError::UnknownOperation(name("arith.addi")),
            "an operation of another dialect"
        );
        assert_eq!(
            refusal(
                &[fact("llvm.add", [Operand::Hole(0)], ["i32"])],
                &two("i32")
            ),
            TermReadError::Arity(name("add")),
            "one operand of two"
        );
        assert_eq!(
            refusal(&[fact("llvm.add", both, NO_RESULT)], &two("i32")),
            TermReadError::Arity(name("add")),
            "no result where the rest binds one"
        );
        assert_eq!(
            refusal(
                &[fact("llvm.ret", [Operand::Hole(0)], NO_RESULT)],
                &two("i32")
            ),
            TermReadError::Terminator(name("ret")),
            "an operation with no rest"
        );
        assert_eq!(
            refusal(
                &[fact("llvm.add", [Operand::Hole(0), Operand::Hole(5)], [
                    "i32"
                ])],
                &two("i32")
            ),
            TermReadError::UnboundOperand(name("add")),
            "a hole that the body does not have"
        );
        assert_eq!(
            refusal(
                &[fact(
                    "llvm.add",
                    [Operand::Hole(0), Operand::Result {
                        operation: 0,
                        index: 0
                    }],
                    ["i32"]
                )],
                &two("i32")
            ),
            TermReadError::UnboundOperand(name("add")),
            "a result that is not before the operation"
        );
        let load = [
            fact("llvm.inttoptr", [Operand::Hole(0)], ["!llvm.ptr"]),
            fact(
                "llvm.load",
                [Operand::Result {
                    operation: 0,
                    index: 0,
                }],
                ["i8"],
            ),
        ];
        let one = [Hole {
            name: "a",
            ty: "i64",
        }];
        assert_eq!(
            refusal(&load, &one),
            TermReadError::Unattributed(name("alignment")),
            "an attribute port with no attribute"
        );
        let mut aligned = load;
        if let Some(last) = aligned.last_mut() {
            last.attributes
                .push(("alignment".to_owned(), "4 : i32".to_owned()));
        }
        assert_eq!(
            refusal(&aligned, &one),
            TermReadError::Unattributed(name("alignment")),
            "an integer attribute of another type than `i64`"
        );
        let mut regions = table.clone();
        for port in regions
            .opers
            .iter_mut()
            .filter(|op| op.name.as_ref() == "load")
            .flat_map(|op| op.arity.inputs.iter_mut())
            .filter(|port| port.name.as_ref() == "alignment")
        {
            port.sort = name("Region");
        }
        assert_eq!(
            read_term(&regions, &Naming::NONE, &aligned, &one),
            Err(TermReadError::Unread(name("alignment"))),
            "a port of a sort that is no attribute, such as a region"
        );
        assert_eq!(
            refusal(&[fact("llvm.add", both, ["f64"])], &two("f64")),
            TermReadError::Untyped(name("left")),
            "a type that is the print of no constant"
        );
        assert_eq!(
            refusal(&[fact("llvm.add", both, ["i32"])], &[
                Hole {
                    name: "a",
                    ty: "i32"
                },
                Hole {
                    name: "b",
                    ty: "i64"
                }
            ]),
            TermReadError::Mistyped(name("right")),
            "two operands of one type port with two types"
        );
        assert_eq!(
            refusal(&[fact("llvm.inttoptr", [Operand::Hole(0)], ["i64"])], &[
                Hole {
                    name: "a",
                    ty: "i64"
                }
            ]),
            TermReadError::Mistyped(name("p")),
            "a result whose index is the constant `ptr`"
        );
    }
}
