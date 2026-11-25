//! Each operation of the block of the `llvm` dialect in `std`: the print of a
//! smallest term goes through the verifier of the shim, the same term with one
//! operand less does not, and the facts of the print read back as the term.
//!
//! The test reads the block from its source, through the lowering, so it checks
//! the block itself and not a copy. It runs under the feature `full`, which
//! links the shim.

#![cfg(feature = "full")]

#[cfg(test)]
mod tests
{
    use gandr_core_term::CoreArena;
    use gandr_runtime_mlir::CompileError;
    use gandr_runtime_mlir::Hole;
    use gandr_runtime_mlir::Naming;
    use gandr_runtime_mlir::Operand;
    use gandr_runtime_mlir::Operation;
    use gandr_runtime_mlir::Parameter;
    use gandr_runtime_mlir::Place;
    use gandr_runtime_mlir::Printed;
    use gandr_runtime_mlir::Spelling;
    use gandr_runtime_mlir::Text;
    use gandr_runtime_mlir::ValueName;
    use gandr_runtime_mlir::compile;
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
    use gandr_theory_levitation::BridgeArity;
    use gandr_theory_levitation::Name;
    use gandr_theory_levitation::OperDesc;
    use gandr_theory_levitation::TheoryDesc;
    use gandr_theory_levitation::VariableIndex;

    /// `std.llvm`.
    const LLVM: &str = include_str!("../../../library/std/src/llvm.gandr");

    /// The names of the parameters of the function around a body.
    const NAMES: [&str; 7] = ["p0", "p1", "p2", "p3", "p4", "p5", "p6"];

    /// The smallest term of one operation, and the function around it.
    struct Case
    {
        /// The operation.
        operation: &'static str,
        /// The constant of each type port, in order.
        types: &'static [&'static str],
        /// The literal or the constant of each attribute port, in order.
        attributes: &'static [&'static str],
        /// The type of each parameter of the function. Each operand port takes
        /// the next parameter.
        parameters: &'static [&'static str],
        /// The result of the function: its MLIR type and the constant of that
        /// type. With a result, the rest of the operation returns the value
        /// that the operation binds.
        returns: Option<(&'static str, &'static str)>,
        /// The text before the function, such as the declaration of a callee.
        prelude: &'static str,
        /// The calling convention of the function, with a space after it.
        convention: &'static str,
        /// The term with one operand less is refused by the verifier of LLVM IR
        /// in the translation, not by the verifier of MLIR. The verifier of
        /// MLIR does not compare the constraints of an inline assembly
        /// with its operands.
        refused_in_translation: bool,
    }

    /// A case with no type, no attribute, no parameter and no result.
    const NOTHING: Case = Case {
        operation: "",
        types: &[],
        attributes: &[],
        parameters: &[],
        returns: None,
        prelude: "",
        convention: "",
        refused_in_translation: false,
    };

    /// An integer operation of two operands of `i32`.
    macro_rules! binary {
        ($operation:literal) => {
            Case {
                operation: $operation,
                types: &["int32"],
                parameters: &["i32", "i32"],
                ..NOTHING
            }
        };
    }

    /// An inline assembly of `$count` operands of `i64`, which reads each one
    /// from a register.
    macro_rules! inline_asm {
        ($operation:literal, $constraints:literal, $count:literal) => {
            Case {
                operation: $operation,
                attributes: &["nop", $constraints],
                parameters: &["i64"; $count],
                refused_in_translation: true,
                ..NOTHING
            }
        };
    }

    /// Each operation of a body of the block.
    const CASES: [Case; 36] = [
        Case {
            operation: "constant",
            types: &["int32"],
            attributes: &["1"],
            ..NOTHING
        },
        binary!("add"),
        binary!("sub"),
        binary!("mul"),
        binary!("udiv"),
        binary!("sdiv"),
        binary!("urem"),
        binary!("srem"),
        binary!("and"),
        binary!("or"),
        binary!("xor"),
        binary!("shl"),
        binary!("lshr"),
        binary!("ashr"),
        Case {
            operation: "icmp",
            types: &["int32"],
            attributes: &["ult"],
            parameters: &["i32", "i32"],
            ..NOTHING
        },
        Case {
            operation: "choose",
            types: &["int32"],
            parameters: &["i1", "i32", "i32"],
            ..NOTHING
        },
        Case {
            operation: "zext",
            types: &["int8", "int64"],
            parameters: &["i8"],
            ..NOTHING
        },
        Case {
            operation: "sext",
            types: &["int8", "int64"],
            parameters: &["i8"],
            ..NOTHING
        },
        Case {
            operation: "trunc",
            types: &["int64", "int8"],
            parameters: &["i64"],
            ..NOTHING
        },
        Case {
            operation: "inttoptr",
            types: &["int64"],
            parameters: &["i64"],
            ..NOTHING
        },
        Case {
            operation: "getelementptr",
            types: &["int8"],
            parameters: &["!llvm.ptr", "i64"],
            ..NOTHING
        },
        Case {
            operation: "load",
            types: &["int32"],
            attributes: &["4"],
            parameters: &["!llvm.ptr"],
            ..NOTHING
        },
        Case {
            operation: "store",
            types: &["int32"],
            attributes: &["4"],
            parameters: &["i32", "!llvm.ptr"],
            ..NOTHING
        },
        Case {
            operation: "load_atomic",
            types: &["int32"],
            attributes: &["order_acquire", "4"],
            parameters: &["!llvm.ptr"],
            ..NOTHING
        },
        Case {
            operation: "store_atomic",
            types: &["int32"],
            attributes: &["order_release", "4"],
            parameters: &["i32", "!llvm.ptr"],
            ..NOTHING
        },
        Case {
            operation: "atomicrmw",
            types: &["int32"],
            attributes: &["rmw_add", "order_seq_cst"],
            parameters: &["!llvm.ptr", "i32"],
            ..NOTHING
        },
        inline_asm!("inline_asm1", "=r,r", 1),
        inline_asm!("inline_asm2", "=r,r,r", 2),
        inline_asm!("inline_asm3", "=r,r,r,r", 3),
        inline_asm!("inline_asm4", "=r,r,r,r,r", 4),
        inline_asm!("inline_asm5", "=r,r,r,r,r,r", 5),
        inline_asm!("inline_asm6", "=r,r,r,r,r,r,r", 6),
        inline_asm!("inline_asm7", "=r,r,r,r,r,r,r,r", 7),
        Case {
            operation: "tail_call1",
            types: &["ptr", "int64"],
            attributes: &["next"],
            parameters: &["!llvm.ptr"],
            returns: Some(("i64", "int64")),
            prelude: "llvm.func tailcc @next(!llvm.ptr) -> i64\n",
            convention: "tailcc ",
            refused_in_translation: false,
        },
        Case {
            operation: "ret",
            types: &["int32"],
            parameters: &["i32"],
            returns: Some(("i32", "int32")),
            ..NOTHING
        },
        Case {
            operation: "unreachable",
            ..NOTHING
        },
    ];

    /// The table of the block of `std.llvm`, through the lowering.
    ///
    /// # Specification
    /// trivial.
    fn block() -> TheoryDesc<DescriptionGrade>
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
        assert!(
            module.description_diagnostics().is_empty(),
            "the check admits the block: {:?}",
            module.description_diagnostics()
        );
        let theories: Vec<_> = module.theories().collect();
        let [ref theory] = *theories.as_slice()
        else {
            panic!("one block");
        };
        theory.description.clone()
    }

    /// The smallest term of `operation` for `case`: each type port takes the
    /// next constant, each operand port the next parameter, each attribute port
    /// the next attribute, and the rest returns the bound value or is
    /// `unreachable`.
    ///
    /// # Specification
    /// trivial.
    fn smallest(
        operation: &OperDesc,
        case: &Case,
    ) -> BindingTerm
    {
        let mut types = case.types.iter();
        let mut attributes = case.attributes.iter();
        let mut operand = 0_usize;
        let count = case.parameters.len();
        let leaf = |name: &str| BindingTerm::operation(Name::from(name), []);
        let arguments: Vec<BindingTerm> = operation
            .arity
            .inputs
            .iter()
            .map(|port| match port.sort.as_ref() {
                "Ty" => leaf(types.next().expect("a constant for each type port")),
                "Val" => {
                    let index = count.saturating_sub(operand.saturating_add(1));
                    operand = operand.saturating_add(1);
                    BindingTerm::variable(VariableIndex::from(index))
                },
                "Body" => match case.returns {
                    Some((_, ty)) => BindingTerm::operation(Name::from("ret"), [
                        leaf(ty),
                        BindingTerm::variable(VariableIndex::from(0_usize)),
                    ]),
                    None => leaf("unreachable"),
                },
                _ => leaf(attributes.next().expect("a value for each attribute port")),
            })
            .collect();
        BindingTerm::operation(operation.name.clone(), arguments)
    }

    /// The print of the smallest term of `case` against `table`, in a
    /// function, and the answer of the shim for it.
    ///
    /// # Specification
    /// trivial.
    fn compiled(
        table: &TheoryDesc<DescriptionGrade>,
        case: &Case,
    ) -> (String, Result<(), CompileError>)
    {
        let operation = table
            .opers
            .iter()
            .find(|operation| operation.name.as_ref() == case.operation)
            .unwrap_or_else(|| panic!("the block has `{}`", case.operation));
        let parameters: Vec<Parameter<'_>> = NAMES
            .iter()
            .zip(case.parameters)
            .map(|(&name, &ty)| Parameter {
                name: ValueName::from(name),
                ty: Spelling::from(ty),
            })
            .collect();
        let printed: Printed = print_term(
            table,
            &Naming::LLVM,
            &smallest(operation, case),
            (&parameters, Place::ALONE),
        )
        .unwrap_or_else(|refusal| panic!("`{}` prints: {refusal}", case.operation));
        let signature = NAMES
            .iter()
            .zip(case.parameters)
            .map(|(name, ty)| format!("%{name}: {ty}"))
            .collect::<Vec<_>>()
            .join(", ");
        let result = case
            .returns
            .map_or_else(String::new, |(ty, _)| format!(" -> {ty}"));
        let text = format!(
            "{}llvm.func {}@f({signature}){result} {{\n{printed}}}\n",
            case.prelude, case.convention
        );
        let answer = compile(text.as_str().into(), "x86_64-unknown-linux-gnu".into()).map(drop);
        (text, answer)
    }

    /// `table` with the first operand port of the operation of `case`
    /// removed, or nothing when the operation has no operand.
    ///
    /// # Specification
    /// trivial.
    fn one_operand_less(
        table: &TheoryDesc<DescriptionGrade>,
        case: &Case,
    ) -> Option<TheoryDesc<DescriptionGrade>>
    {
        let mut changed = table.clone();
        let operation = changed
            .opers
            .iter_mut()
            .find(|operation| operation.name.as_ref() == case.operation)?;
        let place = operation
            .arity
            .inputs
            .iter()
            .position(|port| port.sort.as_ref() == "Val")?;
        let mut inputs = operation.arity.inputs.to_vec();
        inputs.remove(place);
        operation.arity = BridgeArity::tupled(inputs, operation.arity.outputs.to_vec());
        Some(changed)
    }

    #[test]
    fn each_operation_passes_the_verifier_and_one_operand_less_does_not()
    {
        let table = block();
        for case in &CASES {
            let (text, answer) = compiled(&table, case);
            assert!(
                answer.is_ok(),
                "the verifier accepts `{}`: {answer:?}\n{text}",
                case.operation
            );
            let Some(less) = one_operand_less(&table, case)
            else {
                assert!(
                    case.parameters.is_empty(),
                    "only an operation with no operand has no smaller term"
                );
                continue;
            };
            let (text, answer) = compiled(&less, case);
            let refused = if case.refused_in_translation {
                matches!(answer, Err(CompileError::Codegen(_)))
            }
            else {
                matches!(answer, Err(CompileError::InvalidText(_)))
            };
            assert!(
                refused,
                "the shim refuses `{}` with one operand less: {answer:?}\n{text}",
                case.operation
            );
        }
    }

    #[test]
    fn each_operation_of_a_body_is_a_case()
    {
        let table = block();
        let mut body: Vec<&str> = table
            .opers
            .iter()
            .filter(|operation| {
                operation
                    .arity
                    .outputs
                    .iter()
                    .any(|port| port.sort.as_ref() == "Body")
            })
            .map(|operation| operation.name.as_ref())
            .collect();
        body.sort_unstable();
        let mut cases: Vec<&str> = CASES.iter().map(|case| case.operation).collect();
        cases.sort_unstable();
        assert_eq!(cases, body, "each operation of a body has its case");
    }

    /// The last line of the print of a term: the terminator that the read entry
    /// of the shim puts after a body.
    const TERMINATOR: &str = "\"llvm.unreachable\"() : () -> ()\n";

    #[test]
    fn each_operation_reads_back_from_its_print()
    {
        let table = block();
        // A case with a result returns it, and the read entry puts its own
        // terminator after a body; so those cases have no term to read back.
        for case in CASES.iter().filter(|case| case.returns.is_none()) {
            let operation = table
                .opers
                .iter()
                .find(|operation| operation.name.as_ref() == case.operation)
                .unwrap_or_else(|| panic!("the block has `{}`", case.operation));
            let term = smallest(operation, case);
            let holes: Vec<Hole<'_>> = NAMES
                .iter()
                .zip(case.parameters)
                .map(|(&name, &ty)| Hole { name, ty })
                .collect();
            let parameters: Vec<Parameter<'_>> = holes
                .iter()
                .map(|hole| Parameter {
                    name: ValueName::from(hole.name),
                    ty: Spelling::from(hole.ty),
                })
                .collect();
            let printed = print_term(&table, &Naming::LLVM, &term, (&parameters, Place::ALONE))
                .unwrap_or_else(|refusal| panic!("`{}` prints: {refusal}", case.operation));
            let body = printed
                .as_ref()
                .strip_suffix(TERMINATOR)
                .unwrap_or_else(|| panic!("the print ends with the terminator:\n{printed}"));
            let facts = read(Text::from(body), &holes).unwrap_or_else(|error| {
                panic!("the shim reads `{}`: {error}\n{body}", case.operation)
            });
            assert_eq!(
                read_term(&table, &Naming::LLVM, &facts, &holes),
                Ok(term),
                "`{}`: the read of the print is the term\n{body}",
                case.operation
            );
        }
        // The callee of a tail call is a function of the module, which the
        // read entry does not have; so its facts are written here.
        let call = Operation {
            name: "llvm.call".to_owned(),
            operands: vec![Operand::Hole(0)],
            attributes: vec![
                ("callee".to_owned(), "@next".to_owned()),
                ("CConv".to_owned(), "#llvm.cconv<tailcc>".to_owned()),
            ],
            results: vec!["i64".to_owned()],
        };
        let leaf = |name: &str| BindingTerm::operation(Name::from(name), []);
        // MLIR prints an integer of `i1` as `true` and one of another width as
        // a signed value.
        let constant = |ty: &str, value: &str| {
            BindingTerm::operation(Name::from("constant"), [
                leaf(ty),
                leaf(value),
                leaf("unreachable"),
            ])
        };
        for (ty, written, read_back) in [("int1", "1", "1"), ("int8", "255", "-1")] {
            let printed = print_term(
                &table,
                &Naming::LLVM,
                &constant(ty, written),
                (&[], Place::ALONE),
            )
            .unwrap_or_else(|refusal| panic!("the constant prints: {refusal}"));
            let body = printed
                .as_ref()
                .strip_suffix(TERMINATOR)
                .unwrap_or_else(|| panic!("the print ends with the terminator:\n{printed}"));
            let facts = read(Text::from(body), &[])
                .unwrap_or_else(|error| panic!("the shim reads the constant: {error}\n{body}"));
            assert_eq!(
                read_term(&table, &Naming::LLVM, &facts, &[]),
                Ok(constant(ty, read_back)),
                "`{written}` at `{ty}` reads back as `{read_back}`\n{body}"
            );
        }
        assert_eq!(
            read_term(&table, &Naming::LLVM, &[call], &[Hole {
                name: "p0",
                ty: "!llvm.ptr",
            }]),
            Ok(BindingTerm::operation(Name::from("tail_call1"), [
                leaf("ptr"),
                leaf("int64"),
                leaf("next"),
                BindingTerm::variable(VariableIndex::from(0_usize)),
                leaf("unreachable"),
            ])),
            "the callee reads as the name of its symbol"
        );
    }
}
