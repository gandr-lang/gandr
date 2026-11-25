//! The lowering of focused definitions to the `gandr` dialect, and its
//! refusals: the fixture `exit-code.gandr`, each native row, each case of a
//! sum, and each node that the lowering has no form for. They run under the
//! feature `full`, which links the shim.

#![cfg(feature = "full")]

#[cfg(test)]
mod tests
{
    use gandr_core_sequent::CommandArena;
    use gandr_core_sequent::CommandNode;
    use gandr_core_sequent::ConstructorTag;
    use gandr_core_sequent::ConsumerNode;
    use gandr_core_sequent::CovariableIndex;
    use gandr_core_sequent::DestructorTag;
    use gandr_core_sequent::ProducerArity;
    use gandr_core_sequent::ProducerNode;
    use gandr_core_sequent::Provenance;
    use gandr_core_sequent::Typed;
    use gandr_core_sequent::Writers;
    use gandr_core_sequent::check_command;
    use gandr_core_sequent::focus_value;
    use gandr_core_term::ComputationId;
    use gandr_core_term::CoreArena;
    use gandr_core_term::ValueId;
    use gandr_core_term::ValueTypeId;
    use gandr_core_term::Zone;
    use gandr_core_term::effect::EffectName;
    use gandr_core_term::effect::EffectOp;
    use gandr_core_term::effect::EffectRow;
    use gandr_core_term::effect::EffectSig;
    use gandr_core_term::effect::OperationName;
    use gandr_core_term::primitive::Arguments;
    use gandr_core_term::primitive::CheckedFixed;
    use gandr_core_term::primitive::PRELUDE;
    use gandr_core_term::primitive::Primitive;
    use gandr_core_term::primitive::PrimitiveType;
    use gandr_core_term::primitive::Scalar;
    use gandr_kernel_term::BaseType;
    use gandr_kernel_term::ConstantIndex;
    use gandr_kernel_term::DeBruijnIndex;
    use gandr_kernel_term::FixedInteger;
    use gandr_kernel_term::FixpointEvidence;
    use gandr_kernel_term::IntegerLiteral;
    use gandr_kernel_term::IntegerWidth;
    use gandr_kernel_term::Literal;
    use gandr_kernel_term::Magnitude;
    use gandr_kernel_term::Summand;
    use gandr_runtime_mlir::Definition;
    use gandr_runtime_mlir::Export;
    use gandr_runtime_mlir::Form;
    use gandr_runtime_mlir::Lowered;
    use gandr_runtime_mlir::Symbol;
    use gandr_runtime_mlir::compile;
    use gandr_runtime_mlir::lower;
    use gandr_theory_cell_complexes::Polarity;

    /// The names of the definitions of the fixture, by admission position.
    const NAMES: [&str; 5] = ["inc", "twice", "wrapped", "answer", "main"];

    /// The admission position of `inc`.
    const INC: usize = 0;
    /// `twice`.
    const TWICE: usize = 1;
    /// `wrapped`.
    const WRAPPED: usize = 2;
    /// `answer`.
    const ANSWER: usize = 3;
    /// `main`.
    const MAIN: usize = 4;

    /// The row `u8.wrapping_add` of the native table.
    ///
    /// # Specification
    /// trivial.
    fn wrapping_add() -> Primitive
    {
        PRELUDE
            .iter()
            .copied()
            .find(|row| row.name().as_ref() == "u8.wrapping_add")
            .unwrap()
    }

    /// A `u8` literal.
    ///
    /// # Specification
    /// trivial.
    fn byte(
        arena: &mut CoreArena,
        value: FixedInteger,
    ) -> ValueId
    {
        arena.value_literal(Literal::Fixed(value))
    }

    /// The intuitionistic variable at `index`.
    ///
    /// # Specification
    /// trivial.
    fn variable(
        arena: &mut CoreArena,
        index: DeBruijnIndex,
    ) -> ValueId
    {
        arena.value_variable(Zone::Intuitionistic, index)
    }

    /// `force c` of the definition at `position`.
    ///
    /// # Specification
    /// trivial.
    fn forced(
        arena: &mut CoreArena,
        position: ConstantIndex,
    ) -> gandr_core_term::ComputationId
    {
        let constant = arena.value_constant(position);
        arena.computation_force(constant)
    }

    /// The two types of the fixture: `U (u8 → F u8)` and `U (F u8)`.
    ///
    /// # Specification
    /// trivial.
    fn types(arena: &mut CoreArena) -> (ValueTypeId, ValueTypeId)
    {
        let word = arena.value_type_base(BaseType::Fixed(IntegerWidth::U8));
        let returner = arena.comp_type_returner(word);
        let function = arena.comp_type_arrow(word, returner);
        (
            arena.value_type_thunk(function),
            arena.value_type_thunk(returner),
        )
    }

    /// The value of each definition of `exit-code.gandr`, a thunk, in the
    /// order of [`NAMES`].
    ///
    /// # Specification
    /// trivial.
    fn fixture(arena: &mut CoreArena) -> Vec<ValueId>
    {
        let mut definitions = Vec::new();

        // def inc(x : u8) -> u8 = u8.wrapping_add x 1u8;
        let x = variable(arena, DeBruijnIndex::from(0));
        let one = byte(arena, FixedInteger::U8(1));
        let call = arena.computation_primitive(wrapping_add(), Arguments::Binary([x, one]));
        let body = arena.computation_lambda(call);
        definitions.push(arena.value_thunk(body));

        // def twice(x : u8) -> u8 = inc (inc x);
        let inner_head = forced(arena, ConstantIndex::from(INC));
        let x = variable(arena, DeBruijnIndex::from(0));
        let inner = arena.computation_application(inner_head, x);
        let outer_head = forced(arena, ConstantIndex::from(INC));
        let sum = variable(arena, DeBruijnIndex::from(0));
        let outer = arena.computation_application(outer_head, sum);
        let bind = arena.computation_bind(inner, outer);
        let body = arena.computation_lambda(bind);
        definitions.push(arena.value_thunk(body));

        // def wrapped() -> u8 = u8.wrapping_add 255u8 3u8;
        let greatest = byte(arena, FixedInteger::U8(255));
        let three = byte(arena, FixedInteger::U8(3));
        let body =
            arena.computation_primitive(wrapping_add(), Arguments::Binary([greatest, three]));
        definitions.push(arena.value_thunk(body));

        // def answer() -> u8 = { let sum = wrapped; twice sum };
        let bound = forced(arena, ConstantIndex::from(WRAPPED));
        let head = forced(arena, ConstantIndex::from(TWICE));
        let sum = variable(arena, DeBruijnIndex::from(0));
        let call = arena.computation_application(head, sum);
        let body = arena.computation_bind(bound, call);
        definitions.push(arena.value_thunk(body));

        // def main() -> u8 = { let code = answer; code };
        let bound = forced(arena, ConstantIndex::from(ANSWER));
        let code = variable(arena, DeBruijnIndex::from(0));
        let returned = arena.computation_return(code);
        let body = arena.computation_bind(bound, returned);
        definitions.push(arena.value_thunk(body));

        definitions
    }

    /// Focus each value of `values` with its signature, name it by
    /// [`NAMES`], and lower the definitions.
    ///
    /// # Specification
    /// trivial.
    fn lowered<'name>(
        core: &CoreArena,
        values: &[(ValueId, ValueTypeId)],
        names: &[Symbol<'name>],
    ) -> Result<Lowered<'name>, Form>
    {
        let mut arena = CommandArena::new();
        let mut provenance = Provenance::new();
        let definitions = values
            .iter()
            .zip(names)
            .map(|(&(value, signature), &name)| Definition {
                name,
                value: focus_value(
                    core,
                    value,
                    &mut arena,
                    &mut provenance,
                    &Writers::NONE,
                    &Typed::NONE,
                )
                .unwrap(),
                signature,
            })
            .collect::<Vec<_>>();
        lower(&arena, core, &definitions)
    }

    /// The MLIR text of the five definitions of the fixture.
    ///
    /// # Specification
    /// trivial.
    fn fixture_text() -> String
    {
        let mut core = CoreArena::new();
        let (function, constant) = types(&mut core);
        let values = fixture(&mut core);
        let typed = values
            .iter()
            .enumerate()
            .map(|(position, &value)| {
                (
                    value,
                    if position < WRAPPED {
                        function
                    }
                    else {
                        constant
                    },
                )
            })
            .collect::<Vec<_>>();
        let names = NAMES.map(Symbol::from);
        lowered(&core, &typed, &names).unwrap().to_string()
    }

    #[test]
    fn each_definition_of_the_fixture_becomes_an_object()
    {
        let text = fixture_text();
        let object = compile(text.as_str().into(), "x86_64-unknown-linux-gnu".into())
            .unwrap_or_else(|error| panic!("{error}\n{text}"));
        let bytes = object.as_ref();
        assert!(bytes.starts_with(b"\x7fELF"), "the object is not ELF");
        for name in NAMES {
            let entry = [b"\0", name.as_bytes(), b"\0"].concat();
            assert!(
                bytes
                    .windows(entry.len())
                    .any(|window| window == entry.as_slice()),
                "the object has no symbol {name}\n{text}"
            );
        }
    }

    #[test]
    fn an_object_with_the_entry_links_and_exits_with_the_answer()
    {
        let mut core = CoreArena::new();
        let (function, constant) = types(&mut core);
        let values = fixture(&mut core);
        let typed = values
            .iter()
            .enumerate()
            .map(|(position, &value)| {
                (
                    value,
                    if position < WRAPPED {
                        function
                    }
                    else {
                        constant
                    },
                )
            })
            .collect::<Vec<_>>();
        let names = NAMES.map(Symbol::from);
        let lowered = lowered(&core, &typed, &names).unwrap();
        let entry = lowered.entry(ConstantIndex::from(MAIN)).unwrap();
        let text = format!("{lowered}{entry}");
        let object = compile(text.as_str().into(), "x86_64-unknown-linux-gnu".into())
            .unwrap_or_else(|error| panic!("{error}\n{text}"));

        let directory = std::env::temp_dir().join(format!("gandr-entry-{}", std::process::id()));
        std::fs::create_dir_all(&directory).unwrap();
        let object_path = directory.join("main.o");
        let executable = directory.join("main");
        std::fs::write(&object_path, object.as_ref()).unwrap();
        let toolchain = std::env::var_os("GANDR_MLIR_TOOLCHAIN")
            .unwrap_or_else(|| panic!("GANDR_MLIR_TOOLCHAIN names the archive of the pin"));
        let linked =
            std::process::Command::new(std::path::Path::new(&toolchain).join("bin").join("ld.lld"))
                .arg("-o")
                .arg(&executable)
                .args(["--entry", gandr_runtime_mlir::ENTRY])
                .arg(&object_path)
                .output()
                .unwrap();
        assert!(
            linked.status.success(),
            "ld.lld refused the object:\n{}\n{text}",
            String::from_utf8_lossy(&linked.stderr)
        );

        let run = std::process::Command::new(&executable).status().unwrap();
        std::fs::remove_dir_all(&directory).unwrap();
        assert_eq!(
            run.code(),
            Some(4_i32),
            "main answers 4: (255 + 3) + 1 + 1 in u8"
        );
    }

    #[test]
    fn an_entry_needs_a_function_with_no_parameter()
    {
        let mut core = CoreArena::new();
        let (function, _) = types(&mut core);
        let values = fixture(&mut core);
        let lowered = lowered(&core, &[(values[INC], function)], &[Symbol::from("inc")]).unwrap();
        assert_eq!(
            lowered.entry(ConstantIndex::from(INC)),
            Err(Form::Signature),
            "inc takes a parameter"
        );
        assert_eq!(
            lowered.entry(ConstantIndex::from(TWICE)),
            Err(Form::Unbound),
            "the module has one function"
        );
    }

    #[test]
    fn twice_calls_inc_and_jumps_to_inc()
    {
        let text = fixture_text();
        let twice = text
            .split("llvm.func")
            .find(|function| function.contains("@twice("))
            .unwrap();
        let call = twice.find("%v1 = gandr.call @inc(%v0) : (i8) -> i8");
        let jump = twice.find("gandr.jump @inc(%v1) : (i8)");
        assert!(
            call.is_some() && jump.is_some() && call < jump,
            "twice does not call inc and then jump to inc:\n{twice}"
        );
    }

    #[test]
    fn wrapped_gives_the_pattern_of_the_greatest_byte()
    {
        let text = fixture_text();
        let wrapped = text
            .split("llvm.func")
            .find(|function| function.contains("@wrapped("))
            .unwrap();
        assert!(
            wrapped.contains("llvm.mlir.constant(-1 : i8) : i8")
                && wrapped.contains("llvm.mlir.constant(3 : i8) : i8")
                && wrapped.contains("gandr.wrapping_add %v0, %v1 : i8")
                && wrapped.contains("gandr.return %v2 : i8"),
            "wrapped does not add 255u8 and 3u8:\n{wrapped}"
        );
    }

    /// The definition of a row of one or two arguments: `thunk (λx. row x)`
    /// with its type `U (w → F r)`, or `thunk (λx. λy. row x y)` with its type
    /// `U (w → w → F r)`, where `r` is `w` for a word row and `w + Unit` for
    /// a checked row.
    ///
    /// # Specification
    /// trivial.
    fn native_definition(
        arena: &mut CoreArena,
        row: Primitive,
    ) -> (ValueId, ValueTypeId)
    {
        let (word, result) = match row.result() {
            PrimitiveType::Fixed(width) => {
                let word = arena.value_type_base(BaseType::Fixed(width));
                (word, word)
            },
            PrimitiveType::Checked(width) => {
                let word = arena.value_type_base(BaseType::Fixed(width));
                let unit = arena.value_type_unit();
                (word, arena.value_type_sum(&[word, unit]))
            },
            PrimitiveType::Integer
            | PrimitiveType::Boolean
            | PrimitiveType::Text
            | PrimitiveType::Float64 => {
                panic!("{}: a row with no width", <&str>::from(row.name()))
            },
        };
        let returner = arena.comp_type_returner(result);
        let (call, arrows) = match row.arguments().len() {
            1 => {
                let x = variable(arena, DeBruijnIndex::from(0));
                (arena.computation_primitive(row, Arguments::Unary(x)), 1_u8)
            },
            2 => {
                let x = variable(arena, DeBruijnIndex::from(1));
                let y = variable(arena, DeBruijnIndex::from(0));
                (
                    arena.computation_primitive(row, Arguments::Binary([x, y])),
                    2,
                )
            },
            arity => panic!("{}: a row of {arity} arguments", <&str>::from(row.name())),
        };
        let (mut body, mut signature) = (call, returner);
        for _ in 0_u8 .. arrows {
            body = arena.computation_lambda(body);
            signature = arena.comp_type_arrow(word, signature);
        }
        (arena.value_thunk(body), arena.value_type_thunk(signature))
    }

    #[test]
    fn each_row_of_the_native_table_becomes_an_object()
    {
        let mut core = CoreArena::new();
        // The rows with an operation of a machine or a checked operation:
        // seven and five for each of the ten widths.
        let rows = PRELUDE
            .iter()
            .copied()
            .filter(|row| row.machine_operation().is_some() || row.checked_operation().is_some())
            .collect::<Vec<_>>();
        assert_eq!(120, rows.len(), "twelve rows for each of ten widths");
        let typed = rows
            .iter()
            .map(|&row| native_definition(&mut core, row))
            .collect::<Vec<_>>();
        let names = rows
            .iter()
            .map(|row| row.name().as_ref().replace('.', "_"))
            .collect::<Vec<_>>();
        let symbols = names
            .iter()
            .map(|name| Symbol::from(name.as_str()))
            .collect::<Vec<_>>();
        let count = rows.len();

        let missing = rows
            .iter()
            .zip(typed.iter().zip(&symbols))
            .filter(|&(_, (&definition, &symbol))| {
                lowered(&core, &[definition], &[symbol]).is_err()
            })
            .map(|(row, _)| <&str>::from(row.name()))
            .collect::<Vec<_>>();
        assert!(
            missing.is_empty(),
            "{} of the {count} rows of the native table have no lowering: {missing:?}",
            missing.len()
        );

        let text = lowered(&core, &typed, &symbols).unwrap().to_string();
        let object = compile(text.as_str().into(), "x86_64-unknown-linux-gnu".into())
            .unwrap_or_else(|error| panic!("{error}\n{text}"));
        let bytes = object.as_ref();
        let absent = names
            .iter()
            .filter(|name| {
                let entry = [b"\0", name.as_bytes(), b"\0"].concat();
                !bytes
                    .windows(entry.len())
                    .any(|window| window == entry.as_slice())
            })
            .collect::<Vec<_>>();
        assert!(
            absent.is_empty(),
            "the object of the {count} rows has no symbol for {absent:?}"
        );
    }

    #[test]
    fn each_bit_row_of_each_width_becomes_its_operation()
    {
        let widths = [
            (IntegerWidth::U8, "u8"),
            (IntegerWidth::U16, "u16"),
            (IntegerWidth::U32, "u32"),
            (IntegerWidth::U64, "u64"),
            (IntegerWidth::Usize, "usize"),
            (IntegerWidth::I8, "i8"),
            (IntegerWidth::I16, "i16"),
            (IntegerWidth::I32, "i32"),
            (IntegerWidth::I64, "i64"),
            (IntegerWidth::Isize, "isize"),
        ];
        let mut core = CoreArena::new();
        let mut values = Vec::new();
        for (width, prefix) in widths {
            let row = |operation: &str| {
                let name = format!("{prefix}.{operation}");
                PRELUDE
                    .iter()
                    .copied()
                    .find(|row| row.name().as_ref() == name)
                    .unwrap()
            };
            let word = core.value_type_base(BaseType::Fixed(width));
            let returner = core.comp_type_returner(word);
            let inner = core.comp_type_arrow(word, returner);
            let outer = core.comp_type_arrow(word, inner);
            let signature = core.value_type_thunk(outer);
            // def bits(first : w, second : w) -> w = { both ← first & second;
            // either ← both | second; apart ← either ^ first; !apart };
            let first = variable(&mut core, DeBruijnIndex::from(1));
            let second = variable(&mut core, DeBruijnIndex::from(0));
            let both = core.computation_primitive(row("and"), Arguments::Binary([first, second]));
            let both_bound = variable(&mut core, DeBruijnIndex::from(0));
            let second = variable(&mut core, DeBruijnIndex::from(1));
            let either =
                core.computation_primitive(row("or"), Arguments::Binary([both_bound, second]));
            let either_bound = variable(&mut core, DeBruijnIndex::from(0));
            let first = variable(&mut core, DeBruijnIndex::from(3));
            let apart =
                core.computation_primitive(row("xor"), Arguments::Binary([either_bound, first]));
            let apart_bound = variable(&mut core, DeBruijnIndex::from(0));
            let negated = core.computation_primitive(row("not"), Arguments::Unary(apart_bound));
            let body = core.computation_bind(apart, negated);
            let body = core.computation_bind(either, body);
            let body = core.computation_bind(both, body);
            let body = core.computation_lambda(body);
            let body = core.computation_lambda(body);
            values.push((core.value_thunk(body), signature));
        }
        let names = widths.map(|(_, prefix)| Symbol::from(prefix));
        let text = lowered(&core, &values, &names).unwrap().to_string();
        for (_, prefix) in widths {
            let header = format!("@{prefix}(");
            let function = text
                .split("llvm.func")
                .find(|function| function.contains(&header))
                .unwrap();
            for operation in ["gandr.and", "gandr.or", "gandr.xor", "gandr.not"] {
                assert!(
                    function.contains(operation),
                    "the function of {prefix} has no {operation}:\n{function}"
                );
            }
        }
        let object = compile(text.as_str().into(), "x86_64-unknown-linux-gnu".into())
            .unwrap_or_else(|error| panic!("{error}\n{text}"));
        assert!(
            object.as_ref().starts_with(b"\x7fELF"),
            "the object is not ELF"
        );
    }

    #[test]
    fn a_name_that_is_no_identifier_is_refused()
    {
        let mut core = CoreArena::new();
        let (function, _) = types(&mut core);
        let values = fixture(&mut core);
        let refusal = lowered(&core, &[(values[INC], function)], &[Symbol::from(
            "two words",
        )]);
        assert_eq!(
            refusal,
            Err(Form::Symbol),
            "a name with a space is a symbol"
        );
    }

    #[test]
    fn a_thunk_parameter_is_refused()
    {
        let mut core = CoreArena::new();
        let (_, constant) = types(&mut core);
        let returner = core.comp_type_returner(constant);
        let higher = core.comp_type_arrow(constant, returner);
        let signature = core.value_type_thunk(higher);
        let values = fixture(&mut core);
        let refusal = lowered(&core, &[(values[INC], signature)], &[Symbol::from("inc")]);
        assert_eq!(refusal, Err(Form::Signature), "a thunk is no word");
    }

    #[test]
    fn a_value_with_fewer_arms_than_its_type_is_refused()
    {
        let mut core = CoreArena::new();
        let (function, _) = types(&mut core);
        let values = fixture(&mut core);
        let refusal = lowered(&core, &[(values[WRAPPED], function)], &[Symbol::from(
            "wrapped",
        )]);
        assert_eq!(
            refusal,
            Err(Form::Signature),
            "wrapped opens no arm for the parameter of its type"
        );
    }

    #[test]
    fn a_variable_past_the_scope_is_unbound()
    {
        let mut core = CoreArena::new();
        let (function, _) = types(&mut core);
        let outer = variable(&mut core, DeBruijnIndex::from(1));
        let returned = core.computation_return(outer);
        let body = core.computation_lambda(returned);
        let value = core.value_thunk(body);
        let refusal = lowered(&core, &[(value, function)], &[Symbol::from("outer")]);
        assert_eq!(
            refusal,
            Err(Form::Unbound),
            "the index 1 names no parameter"
        );
    }

    #[test]
    fn a_thunk_inside_a_body_is_a_closure()
    {
        let mut core = CoreArena::new();
        let (_, constant) = types(&mut core);
        let one = byte(&mut core, FixedInteger::U8(1));
        let inner = core.computation_return(one);
        let suspended = core.value_thunk(inner);
        let returned = core.computation_return(suspended);
        let value = core.value_thunk(returned);
        let refusal = lowered(&core, &[(value, constant)], &[Symbol::from("suspended")]);
        assert_eq!(refusal, Err(Form::Closure), "the slice has no closure");
    }

    /// The row `u8.wrapping_sub` of the native table.
    ///
    /// # Specification
    /// trivial.
    fn wrapping_sub() -> Primitive
    {
        PRELUDE
            .iter()
            .copied()
            .find(|row| row.name().as_ref() == "u8.wrapping_sub")
            .unwrap()
    }

    #[test]
    fn a_fixpoint_at_the_head_of_a_definition_is_its_function()
    {
        let mut core = CoreArena::new();
        let (function, constant) = types(&mut core);
        // def spin() -> u8 = fix x. force x;
        let itself = variable(&mut core, DeBruijnIndex::from(0));
        let again = core.computation_force(itself);
        let fixpoint = core.computation_fixpoint(again, FixpointEvidence::Partial);
        let spin = core.value_thunk(fixpoint);
        // def down(n : u8) -> u8 = fix count. λn. { let m = u8.wrapping_sub n
        // 1u8; count m };
        let n = variable(&mut core, DeBruijnIndex::from(0));
        let one = byte(&mut core, FixedInteger::U8(1));
        let less = core.computation_primitive(wrapping_sub(), Arguments::Binary([n, one]));
        let count = variable(&mut core, DeBruijnIndex::from(2));
        let head = core.computation_force(count);
        let m = variable(&mut core, DeBruijnIndex::from(0));
        let call = core.computation_application(head, m);
        let bind = core.computation_bind(less, call);
        let lambda = core.computation_lambda(bind);
        let fixpoint = core.computation_fixpoint(lambda, FixpointEvidence::Partial);
        let down = core.value_thunk(fixpoint);
        // def deep(n : u8) -> u8 = fix count. λn. { let r = count n; r };
        let count = variable(&mut core, DeBruijnIndex::from(1));
        let head = core.computation_force(count);
        let n = variable(&mut core, DeBruijnIndex::from(0));
        let call = core.computation_application(head, n);
        let r = variable(&mut core, DeBruijnIndex::from(0));
        let returned = core.computation_return(r);
        let bind = core.computation_bind(call, returned);
        let lambda = core.computation_lambda(bind);
        let fixpoint = core.computation_fixpoint(lambda, FixpointEvidence::Partial);
        let deep = core.value_thunk(fixpoint);

        let names = ["spin", "down", "deep"].map(Symbol::from);
        let text = lowered(
            &core,
            &[(spin, constant), (down, function), (deep, function)],
            &names,
        )
        .unwrap()
        .to_string();
        let mut bodies = text.split("llvm.func");
        let (Some(_), Some(spin), Some(down), Some(deep)) =
            (bodies.next(), bodies.next(), bodies.next(), bodies.next())
        else {
            panic!("the module has no three functions:\n{text}");
        };
        assert!(
            spin.contains("@spin(") && spin.contains("gandr.jump @spin()\n"),
            "spin jumps to itself:\n{text}"
        );
        assert!(
            down.contains("gandr.wrapping_sub %v0, %v1 : i8")
                && down.contains("gandr.jump @down(%v2) : (i8)"),
            "down jumps to itself with the difference, so it uses no stack:\n{text}"
        );
        let call = deep.find("%v1 = gandr.call @deep(%v0) : (i8) -> i8");
        let back = deep.find("gandr.return %v1 : i8");
        assert!(
            call.is_some() && back.is_some() && call < back,
            "deep calls itself in no tail, so it runs with a stack:\n{text}"
        );
        let object = compile(text.as_str().into(), "x86_64-unknown-linux-gnu".into())
            .unwrap_or_else(|error| panic!("{error}\n{text}"));
        for name in ["spin", "down", "deep"] {
            let entry = [b"\0", name.as_bytes(), b"\0"].concat();
            assert!(
                object
                    .as_ref()
                    .windows(entry.len())
                    .any(|window| window == entry.as_slice()),
                "the object has no symbol {name}\n{text}"
            );
        }
    }

    #[test]
    fn a_fixpoint_inside_a_body_is_refused_by_name()
    {
        let mut core = CoreArena::new();
        let (_, constant) = types(&mut core);
        // def inner() -> u8 = { let r = fix x. force x; r };
        let itself = variable(&mut core, DeBruijnIndex::from(0));
        let again = core.computation_force(itself);
        let fixpoint = core.computation_fixpoint(again, FixpointEvidence::Partial);
        let r = variable(&mut core, DeBruijnIndex::from(0));
        let returned = core.computation_return(r);
        let bind = core.computation_bind(fixpoint, returned);
        let inner = core.value_thunk(bind);
        assert_eq!(
            lowered(&core, &[(inner, constant)], &[Symbol::from("inner")]),
            Err(Form::Fixpoint),
            "a fixpoint that is not the body of a definition is a closure"
        );
        // def leak() -> u8 = fix x. return x;
        let itself = variable(&mut core, DeBruijnIndex::from(0));
        let returned = core.computation_return(itself);
        let fixpoint = core.computation_fixpoint(returned, FixpointEvidence::Partial);
        let leak = core.value_thunk(fixpoint);
        assert_eq!(
            lowered(&core, &[(leak, constant)], &[Symbol::from("leak")]),
            Err(Form::Closure),
            "the self binder as a value is a closure"
        );
    }

    #[test]
    fn a_call_with_more_arguments_than_parameters_is_refused()
    {
        let mut core = CoreArena::new();
        let (function, constant) = types(&mut core);
        let values = fixture(&mut core);
        let head = forced(&mut core, ConstantIndex::from(INC));
        let one = byte(&mut core, FixedInteger::U8(1));
        let two = byte(&mut core, FixedInteger::U8(2));
        let first = core.computation_application(head, one);
        let second = core.computation_application(first, two);
        let value = core.value_thunk(second);
        let refusal = lowered(&core, &[(values[INC], function), (value, constant)], &[
            Symbol::from("inc"),
            Symbol::from("over"),
        ]);
        assert_eq!(refusal, Err(Form::Delivery), "inc takes one argument");
    }

    #[test]
    fn a_tuple_or_a_product_with_a_component_is_refused_by_name()
    {
        // def inc(x : *{u8}) -> u8, a parameter of a product of one component.
        let mut core = CoreArena::new();
        let values = fixture(&mut core);
        let word = core.value_type_base(BaseType::Fixed(IntegerWidth::U8));
        let product = core.value_type_product(&[word]);
        let returner = core.comp_type_returner(word);
        let arrow = core.comp_type_arrow(product, returner);
        let signature = core.value_type_thunk(arrow);
        assert_eq!(
            lowered(&core, &[(values[INC], signature)], &[Symbol::from("inc")]),
            Err(Form::Product),
            "a product of one component has no layout"
        );

        // A command that returns the tuple of one field `*{1u8}`.
        let unit_type = core.value_type_unit();
        let gives_unit = core.comp_type_returner(unit_type);
        let unit_signature = core.value_type_thunk(gives_unit);
        let mut arena = CommandArena::new();
        let back = arena
            .mint_consumer(ConsumerNode::Covariable(CovariableIndex::from(0)))
            .unwrap();
        let one = arena
            .mint_producer(ProducerNode::Literal(Literal::Fixed(FixedInteger::U8(1))))
            .unwrap();
        let field = arena.unknown_type();
        let tuple = arena
            .mint_producer(ProducerNode::Constructor {
                tag: ConstructorTag::Tuple(ProducerArity::from(1_usize)),
                producers: Box::from([one]),
                types: Box::from([field]),
                consumers: Box::default(),
            })
            .unwrap();
        let body = arena.mint_cut(Polarity::Positive, tuple, back).unwrap();
        let thunk = arena.mint_producer(ProducerNode::Thunk { body }).unwrap();
        let definitions = [Definition {
            name: Symbol::from("pair"),
            value: thunk,
            signature: unit_signature,
        }];
        assert_eq!(
            lower(&arena, &core, &definitions).map(|_| ()),
            Err(Form::Product),
            "a tuple of one field has no layout"
        );
    }

    #[test]
    fn a_capture_bound_by_name_is_refused_as_a_closure()
    {
        // def bound() -> u8 = ⟨μα. ⟨7u8 |+ α⟩ |ε μ̃x. ⟨x |+ β⟩⟩, at each
        // polarity `ε`, and the capture against the frame `apply(1u8;
        // β)`.
        let mut core = CoreArena::new();
        let word = core.value_type_base(BaseType::Fixed(IntegerWidth::U8));
        let returner = core.comp_type_returner(word);
        let signature = core.value_type_thunk(returner);
        let mut arena = CommandArena::new();
        let back = arena
            .mint_consumer(ConsumerNode::Covariable(CovariableIndex::from(0)))
            .unwrap();
        let seven = arena
            .mint_producer(ProducerNode::Literal(Literal::Fixed(FixedInteger::U8(7))))
            .unwrap();
        let inner = arena.mint_cut(Polarity::Positive, seven, back).unwrap();
        let capture = arena
            .mint_producer(ProducerNode::Mu { body: inner })
            .unwrap();
        let x = arena
            .mint_producer(ProducerNode::Variable {
                zone: Zone::Intuitionistic,
                index: DeBruijnIndex::from(0),
            })
            .unwrap();
        let returned = arena.mint_cut(Polarity::Positive, x, back).unwrap();
        let bound_type = arena.unknown_type();
        let binder = arena
            .mint_consumer(ConsumerNode::MuTilde {
                ty: bound_type,
                body: returned,
            })
            .unwrap();
        let one = arena
            .mint_producer(ProducerNode::Literal(Literal::Fixed(FixedInteger::U8(1))))
            .unwrap();
        let frame = arena
            .mint_consumer(ConsumerNode::Destructor {
                tag: DestructorTag::Apply,
                producers: Box::from([one]),
                consumers: Box::from([back]),
            })
            .unwrap();
        let definition = |arena: &mut CommandArena, polarity, consumer| {
            let body = arena.mint_cut(polarity, capture, consumer).unwrap();
            let thunk = arena.mint_producer(ProducerNode::Thunk { body }).unwrap();
            (body, thunk)
        };
        let (by_name, by_name_thunk) = definition(&mut arena, Polarity::Negative, binder);
        let (by_value, by_value_thunk) = definition(&mut arena, Polarity::Positive, binder);
        let (_, framed_thunk) = definition(&mut arena, Polarity::Negative, frame);
        let lowered_one = |value| {
            let definitions = [Definition {
                name: Symbol::from("bound"),
                value,
                signature,
            }];
            lower(&arena, &core, &definitions).map(|lowered| lowered.to_string())
        };

        assert_eq!(
            check_command(&arena, by_name).map(|free| free.covariables().len()),
            Ok(1),
            "the check admits the by-name bind, which names only the return"
        );
        assert_eq!(
            lowered_one(by_name_thunk),
            Err(Form::Closure),
            "a capture bound by name is suspended, and the lowering has no closure"
        );

        assert!(check_command(&arena, by_value).is_ok());
        let text = lowered_one(by_value_thunk).unwrap();
        compile(text.as_str().into(), "x86_64-unknown-linux-gnu".into())
            .unwrap_or_else(|error| panic!("{error}\n{text}"));

        assert_eq!(
            lowered_one(framed_thunk),
            Err(Form::Delivery),
            "a capture against a frame lowers as before: a word to `apply` is no call"
        );
    }

    #[test]
    fn a_definition_of_unit_returns_no_value()
    {
        let mut core = CoreArena::new();
        let word = core.value_type_base(BaseType::Fixed(IntegerWidth::U8));
        let unit_type = core.value_type_unit();
        let gives_unit = core.comp_type_returner(unit_type);
        let gives_word = core.comp_type_returner(word);
        let takes_unit = core.comp_type_arrow(unit_type, gives_word);
        let passes_unit = core.comp_type_arrow(unit_type, gives_unit);
        let unit_signature = core.value_type_thunk(gives_unit);
        let word_signature = core.value_type_thunk(gives_word);
        let ignore_signature = core.value_type_thunk(takes_unit);
        let same_signature = core.value_type_thunk(passes_unit);

        // def plain() -> Unit = *{};
        let unit = core.value_unit();
        let returned = core.computation_return(unit);
        let plain = core.value_thunk(returned);
        // def ignore(x : Unit) -> u8 = 1u8;
        let one = byte(&mut core, FixedInteger::U8(1));
        let returned = core.computation_return(one);
        let lambda = core.computation_lambda(returned);
        let ignore = core.value_thunk(lambda);
        // def kept() -> u8 = { let done = plain; ignore done };
        let bound = forced(&mut core, ConstantIndex::from(0_usize));
        let head = forced(&mut core, ConstantIndex::from(1_usize));
        let done = variable(&mut core, DeBruijnIndex::from(0));
        let call = core.computation_application(head, done);
        let body = core.computation_bind(bound, call);
        let kept = core.value_thunk(body);
        // def again() -> Unit = plain;
        let jump = forced(&mut core, ConstantIndex::from(0_usize));
        let again = core.value_thunk(jump);
        // def same(x : Unit) -> Unit = x;
        let x = variable(&mut core, DeBruijnIndex::from(0));
        let returned = core.computation_return(x);
        let lambda = core.computation_lambda(returned);
        let same = core.value_thunk(lambda);

        let names = ["plain", "ignore", "kept", "again", "same"].map(Symbol::from);
        let module = lowered(
            &core,
            &[
                (plain, unit_signature),
                (ignore, ignore_signature),
                (kept, word_signature),
                (again, unit_signature),
                (same, same_signature),
            ],
            &names,
        )
        .unwrap_or_else(|form| panic!("the definitions of `Unit` lower: {form}"));
        let text = module.to_string();
        for line in [
            "llvm.func internal tailcc @plain() {\n  gandr.return\n}",
            "llvm.func internal tailcc @ignore() -> i8 {",
            "gandr.call @plain() : () -> ()\n  gandr.jump @ignore()\n",
            "llvm.func internal tailcc @again() {\n  gandr.jump @plain()\n}",
            "llvm.func internal tailcc @same() {\n  gandr.return\n}",
        ] {
            assert!(
                text.contains(line),
                "the text has no `{line}`: a unit has no word\n{text}"
            );
        }
        let object = compile(text.as_str().into(), "x86_64-unknown-linux-gnu".into())
            .unwrap_or_else(|error| panic!("{error}\n{text}"));
        assert!(
            object.as_ref().starts_with(b"\x7fELF"),
            "the object is not ELF"
        );
        assert_eq!(
            module.entry(ConstantIndex::from(0_usize)).map(|_| ()),
            Err(Form::Signature),
            "the entry exits with a word, and `plain` gives none"
        );

        let wrapped = core.computation_primitive(wrapping_add(), Arguments::Binary([unit, one]));
        let wrong = core.value_thunk(wrapped);
        assert_eq!(
            lowered(&core, &[(wrong, word_signature)], &[Symbol::from("wrong")]),
            Err(Form::Delivery),
            "a native operation takes words, and the unit has none"
        );
    }

    #[test]
    fn an_export_calls_its_definition_under_the_c_convention()
    {
        let mut core = CoreArena::new();
        let row = PRELUDE
            .iter()
            .copied()
            .find(|row| row.name().as_ref() == "u64.wrapping_sub")
            .unwrap();
        let (value, signature) = native_definition(&mut core, row);
        let module = lowered(&core, &[(value, signature)], &[Symbol::from("gandr.sub")]).unwrap();
        let export = Export::new(
            &core,
            Symbol::from("sub"),
            Symbol::from("gandr.sub"),
            signature,
        )
        .unwrap();
        let text = format!("{module}{export}");
        assert!(
            text.contains(concat!(
                "llvm.func @sub(%v0: i64, %v1: i64) -> i64 {\n",
                "  %answer = llvm.call tailcc @gandr.sub(%v0, %v1) : (i64, i64) -> i64\n",
                "  llvm.return %answer : i64\n",
                "}\n",
            )),
            "the export passes each parameter in its order, and returns the answer\n{text}"
        );
        let object = compile(text.as_str().into(), "x86_64-unknown-linux-gnu".into())
            .unwrap_or_else(|error| panic!("{error}\n{text}"));
        // The string table keeps `sub` as the tail of `gandr.sub`, so the
        // name of the export has no zero byte before it.
        let entry = b"\0gandr.sub\0";
        assert!(
            object
                .as_ref()
                .windows(entry.len())
                .any(|window| window == entry.as_slice()),
            "the object has no symbol gandr.sub\n{text}"
        );
    }

    #[test]
    fn an_export_outside_the_fragment_is_refused()
    {
        let mut core = CoreArena::new();
        let word = core.value_type_base(BaseType::Fixed(IntegerWidth::U8));
        let unit = core.value_type_unit();
        let gives_word = core.comp_type_returner(word);
        let gives_unit = core.comp_type_returner(unit);
        let takes_unit = core.comp_type_arrow(unit, gives_word);
        let function = core.value_type_thunk(gives_word);
        let takes_function = core.comp_type_arrow(function, gives_word);
        let outside = [
            core.value_type_thunk(gives_unit),
            core.value_type_thunk(takes_unit),
            core.value_type_thunk(takes_function),
            word,
        ];
        let export = |signature: ValueTypeId, symbol: &'static str| {
            Export::new(
                &core,
                Symbol::from(symbol),
                Symbol::from("gandr.f"),
                signature,
            )
            .map(|_| ())
        };
        let refusals = outside.map(|signature| export(signature, "f"));
        assert_eq!(
            refusals,
            [Err(Form::Signature); 4],
            "a result of `Unit`, a parameter of `Unit`, a parameter of a thunk, and a value that is no function are each outside the fragment"
        );
        assert_eq!(
            export(function, "f"),
            Ok(()),
            "a definition of no parameter that gives a word is in the fragment"
        );
        assert_eq!(
            export(function, "f g"),
            Err(Form::Symbol),
            "the name of an export is a bare identifier"
        );
    }

    /// The exit status of the executable of `lowered` with the entry of the
    /// definition at `main`, linked by the `ld.lld` of the pin in a directory
    /// for the test `name`.
    ///
    /// # Specification
    /// trivial.
    fn exit_code(
        lowered: &Lowered<'_>,
        main: ConstantIndex,
        name: Symbol<'_>,
    ) -> std::process::ExitStatus
    {
        let entry = lowered.entry(main).unwrap();
        let text = format!("{lowered}{entry}");
        let object = compile(text.as_str().into(), "x86_64-unknown-linux-gnu".into())
            .unwrap_or_else(|error| panic!("{error}\n{text}"));
        let directory = std::env::temp_dir().join(format!("gandr-{name}-{}", std::process::id()));
        std::fs::create_dir_all(&directory).unwrap();
        let object_path = directory.join("main.o");
        let executable = directory.join("main");
        std::fs::write(&object_path, object.as_ref()).unwrap();
        let toolchain = std::env::var_os("GANDR_MLIR_TOOLCHAIN")
            .unwrap_or_else(|| panic!("GANDR_MLIR_TOOLCHAIN names the archive of the pin"));
        let linked =
            std::process::Command::new(std::path::Path::new(&toolchain).join("bin").join("ld.lld"))
                .arg("-o")
                .arg(&executable)
                .args(["--entry", gandr_runtime_mlir::ENTRY])
                .arg(&object_path)
                .output()
                .unwrap();
        assert!(
            linked.status.success(),
            "ld.lld refused the object:\n{}\n{text}",
            String::from_utf8_lossy(&linked.stderr)
        );
        let run = std::process::Command::new(&executable).status().unwrap();
        std::fs::remove_dir_all(&directory).unwrap();
        run
    }

    #[test]
    fn a_let_of_a_call_with_a_call_as_its_argument_runs()
    {
        let mut core = CoreArena::new();
        let (function, constant) = types(&mut core);
        // def two() -> u8 = 2u8;
        let literal = byte(&mut core, FixedInteger::U8(2));
        let returned = core.computation_return(literal);
        let two = core.value_thunk(returned);
        // def inc(x : u8) -> u8 = u8.wrapping_add x 1u8;
        let x = variable(&mut core, DeBruijnIndex::from(0));
        let one = byte(&mut core, FixedInteger::U8(1));
        let call = core.computation_primitive(wrapping_add(), Arguments::Binary([x, one]));
        let body = core.computation_lambda(call);
        let inc = core.value_thunk(body);
        // def main() -> u8 = { let y = inc two; y };
        let bound = forced(&mut core, ConstantIndex::from(0_usize));
        let head = forced(&mut core, ConstantIndex::from(1_usize));
        let argument = variable(&mut core, DeBruijnIndex::from(0));
        let inner = core.computation_application(head, argument);
        let named = core.computation_bind(bound, inner);
        let y = variable(&mut core, DeBruijnIndex::from(0));
        let returned = core.computation_return(y);
        let outer = core.computation_bind(named, returned);
        let called = core.value_thunk(outer);
        // def main() -> u8 = { let y = u8.wrapping_add two 1u8; y };
        let bound = forced(&mut core, ConstantIndex::from(0_usize));
        let operand = variable(&mut core, DeBruijnIndex::from(0));
        let one = byte(&mut core, FixedInteger::U8(1));
        let inner = core.computation_primitive(wrapping_add(), Arguments::Binary([operand, one]));
        let named = core.computation_bind(bound, inner);
        let y = variable(&mut core, DeBruijnIndex::from(0));
        let returned = core.computation_return(y);
        let outer = core.computation_bind(named, returned);
        let native = core.value_thunk(outer);

        let names = ["two", "inc", "main"].map(Symbol::from);
        let main = ConstantIndex::from(2_usize);
        let exits = [("let-call", called), ("let-native", native)].map(|(name, value)| {
            let module = lowered(
                &core,
                &[(two, constant), (inc, function), (value, constant)],
                &names,
            )
            .unwrap_or_else(|form| panic!("{name}: the naming cut lowers: {form}"));
            exit_code(&module, main, Symbol::from(name)).code()
        });
        assert_eq!(
            exits,
            [Some(3_i32); 2],
            "a `let` of `inc two` and of `u8.wrapping_add two 1u8` each answer 3"
        );
    }

    /// `thunk { let sum = row left right; case sum { present | 7u8 } }`: a
    /// call of the `checked_` row, then a case that returns `present` in its
    /// first branch and 7 in its second.
    ///
    /// # Specification
    /// trivial.
    fn checked_main(
        core: &mut CoreArena,
        row: Primitive,
        [left, right]: [FixedInteger; 2],
        present: ValueId,
    ) -> ValueId
    {
        let left = core.value_literal(Literal::Fixed(left));
        let right = core.value_literal(Literal::Fixed(right));
        let call = core.computation_primitive(row, Arguments::Binary([left, right]));
        let scrutinee = variable(core, DeBruijnIndex::from(0));
        let first = core.computation_return(present);
        let seven = byte(core, FixedInteger::U8(7));
        let second = core.computation_return(seven);
        let case = core.computation_case(scrutinee, &[first, second]);
        let body = core.computation_bind(call, case);
        core.value_thunk(body)
    }

    #[test]
    fn each_branch_of_a_checked_row_runs()
    {
        let mut core = CoreArena::new();
        let (_, gives_word) = types(&mut core);
        let field = variable(&mut core, DeBruijnIndex::from(0));
        let one = byte(&mut core, FixedInteger::U8(1));
        let cases = [
            (
                "u8.checked_add",
                [FixedInteger::U8(200), FixedInteger::U8(55)],
                field,
                255_i32,
            ),
            (
                "u8.checked_add",
                [FixedInteger::U8(255), FixedInteger::U8(1)],
                field,
                7_i32,
            ),
            (
                "u64.checked_sub",
                [FixedInteger::U64(5), FixedInteger::U64(1)],
                one,
                1_i32,
            ),
            (
                "u64.checked_sub",
                [FixedInteger::U64(0), FixedInteger::U64(1)],
                one,
                7_i32,
            ),
            (
                "i8.checked_mul",
                [FixedInteger::I8(-64), FixedInteger::I8(2)],
                one,
                1_i32,
            ),
            (
                "i8.checked_mul",
                [FixedInteger::I8(64), FixedInteger::I8(2)],
                one,
                7_i32,
            ),
            (
                "u8.checked_shl",
                [FixedInteger::U8(3), FixedInteger::U8(2)],
                field,
                12_i32,
            ),
            (
                "u8.checked_shl",
                [FixedInteger::U8(1), FixedInteger::U8(8)],
                field,
                7_i32,
            ),
            (
                "u8.checked_shr",
                [FixedInteger::U8(200), FixedInteger::U8(3)],
                field,
                25_i32,
            ),
            (
                "i32.checked_shr",
                [FixedInteger::I32(-1), FixedInteger::I32(-1)],
                one,
                7_i32,
            ),
        ];
        let answers = cases.map(|(name, operands, present, _)| {
            let row = PRELUDE
                .iter()
                .copied()
                .find(|row| row.name().as_ref() == name)
                .unwrap_or_else(|| panic!("{name} is a row of the native table"));
            let main = checked_main(&mut core, row, operands, present);
            let module = lowered(&core, &[(main, gives_word)], &[Symbol::from("main")])
                .unwrap_or_else(|form| panic!("{name}: the checked row lowers: {form}"));
            exit_code(
                &module,
                ConstantIndex::from(0_usize),
                Symbol::from("checked"),
            )
            .code()
        });
        assert_eq!(
            answers,
            cases.map(|(.., answer)| Some(answer)),
            "each `checked_` row exits with its answer, or with 7 when the answer is absent"
        );
    }

    /// The sign of a width, with the least word of a signed width.
    enum Sign
    {
        /// An unsigned width.
        Unsigned,
        /// A signed width, whose least word is `least`.
        Signed
        {
            /// The least word: only the sign bit is set.
            least: FixedInteger,
        },
    }

    /// The sign of `width`.
    ///
    /// # Specification
    /// trivial.
    fn sign(width: IntegerWidth) -> Sign
    {
        let bits = u32::from(width.bits());
        let least = FixedInteger::try_from((width, 1_u64.wrapping_shl(bits.wrapping_sub(1))))
            .unwrap_or_else(|_wide| panic!("the sign bit is a pattern of {}", width.as_ref()));
        match width {
            IntegerWidth::I8
            | IntegerWidth::I16
            | IntegerWidth::I32
            | IntegerWidth::I64
            | IntegerWidth::Isize => Sign::Signed { least },
            IntegerWidth::U8
            | IntegerWidth::U16
            | IntegerWidth::U32
            | IntegerWidth::U64
            | IntegerWidth::Usize => Sign::Unsigned,
        }
    }

    /// The edge operands of `width`: zero, one, the least word and the
    /// greatest word, and minus one for a signed width. Each edge is in the
    /// list one time.
    ///
    /// # Specification
    /// trivial.
    fn edges(width: IntegerWidth) -> Vec<FixedInteger>
    {
        let bits = u32::from(width.bits());
        let all = u64::MAX.wrapping_shr(64_u32.wrapping_sub(bits));
        let pattern = |bits: u64| {
            FixedInteger::try_from((width, bits))
                .unwrap_or_else(|_wide| panic!("{bits:#x} is a pattern of {}", width.as_ref()))
        };
        match sign(width) {
            Sign::Signed { least } => vec![
                pattern(0),
                pattern(1),
                least,
                pattern(all.wrapping_shr(1)),
                pattern(all),
            ],
            Sign::Unsigned => vec![pattern(0), pattern(1), pattern(all)],
        }
    }

    /// The rows `w.xor` and `w.checked_sub` of `width`, which compare two
    /// words.
    ///
    /// # Specification
    /// trivial.
    fn comparison(width: IntegerWidth) -> [Primitive; 2]
    {
        let find = |operation| {
            let name = format!("{}.{operation}", width.as_ref());
            PRELUDE
                .iter()
                .copied()
                .find(|row| row.name().as_ref() == name)
                .unwrap_or_else(|| panic!("{name} is a row of the native table"))
        };
        [find("xor"), find("checked_sub")]
    }

    /// `next` when the word at the variable 0 is `expected`, and `fail`
    /// otherwise. The test reads each bit: `d = xor v expected` is zero
    /// exactly when the two words are equal. For an unsigned width,
    /// `checked_sub d 1` is absent exactly when `d` is zero. For a signed
    /// width, `checked_sub d least` is absent exactly when `d` is not
    /// negative, and `checked_sub least d` is present exactly when `d` is not
    /// positive.
    ///
    /// # Specification
    /// trivial.
    fn same(
        core: &mut CoreArena,
        expected: FixedInteger,
        [fail, next]: [ComputationId; 2],
    ) -> ComputationId
    {
        let width = expected.width();
        let [xor, checked_sub] = comparison(width);
        let answer = variable(core, DeBruijnIndex::from(0));
        let wanted = core.value_literal(Literal::Fixed(expected));
        let difference = core.computation_primitive(xor, Arguments::Binary([answer, wanted]));
        let zero_test = match sign(width) {
            Sign::Signed { least } => {
                let least = core.value_literal(Literal::Fixed(least));
                let d = variable(core, DeBruijnIndex::from(0));
                let below = core.computation_primitive(checked_sub, Arguments::Binary([d, least]));
                // Under the bind and the branch, `d` is the variable 2.
                let d = variable(core, DeBruijnIndex::from(2));
                let above = core.computation_primitive(checked_sub, Arguments::Binary([least, d]));
                let sum = variable(core, DeBruijnIndex::from(0));
                let not_positive = core.computation_case(sum, &[next, fail]);
                let not_negative = core.computation_bind(above, not_positive);
                let negative = core.computation_case(sum, &[fail, not_negative]);
                core.computation_bind(below, negative)
            },
            Sign::Unsigned => {
                let one = FixedInteger::try_from((width, 1_u64))
                    .unwrap_or_else(|_wide| panic!("1 is a pattern of {}", width.as_ref()));
                let one = core.value_literal(Literal::Fixed(one));
                let d = variable(core, DeBruijnIndex::from(0));
                let less = core.computation_primitive(checked_sub, Arguments::Binary([d, one]));
                let sum = variable(core, DeBruijnIndex::from(0));
                let nonzero = core.computation_case(sum, &[fail, next]);
                core.computation_bind(less, nonzero)
            },
        };
        core.computation_bind(difference, zero_test)
    }

    /// `{ let answer = row operands; … }`: `next` when the compiled answer is
    /// `expected`, and `fail` otherwise. The test reads the summand of a
    /// checked answer, then each bit of its word.
    ///
    /// # Specification
    /// trivial.
    fn check(
        core: &mut CoreArena,
        row: Primitive,
        (operands, expected): (Arguments<FixedInteger>, Scalar),
        [fail, next]: [ComputationId; 2],
    ) -> ComputationId
    {
        let arguments = match operands {
            Arguments::Unary(only) => Arguments::Unary(core.value_literal(Literal::Fixed(only))),
            Arguments::Binary([left, right]) => Arguments::Binary([
                core.value_literal(Literal::Fixed(left)),
                core.value_literal(Literal::Fixed(right)),
            ]),
        };
        let answer = core.computation_primitive(row, arguments);
        let sum = variable(core, DeBruijnIndex::from(0));
        let test = match expected {
            Scalar::Fixed(word) => same(core, word, [fail, next]),
            Scalar::Checked(CheckedFixed::Present(word)) => {
                let present = same(core, word, [fail, next]);
                core.computation_case(sum, &[present, fail])
            },
            Scalar::Checked(CheckedFixed::Absent(_)) => core.computation_case(sum, &[fail, next]),
            Scalar::Integer(_) | Scalar::Boolean(_) | Scalar::Text(_) | Scalar::Float64(_) => {
                panic!("{}: a width row answers a width", <&str>::from(row.name()))
            },
        };
        core.computation_bind(answer, test)
    }

    /// `thunk` of one check of `row` for each pair of edge operands, in
    /// order. The check `k`, from 1, returns `k` when the compiled answer is
    /// not the answer of the evaluator. After the last check, the thunk
    /// returns 0.
    ///
    /// # Specification
    /// trivial.
    fn agreement(
        core: &mut CoreArena,
        row: Primitive,
    ) -> ValueId
    {
        let (PrimitiveType::Fixed(width) | PrimitiveType::Checked(width)) = row.result()
        else {
            panic!("{}: a row with no width", <&str>::from(row.name()));
        };
        let edges = edges(width);
        let operands = if row.arguments().len() == 1 {
            edges
                .iter()
                .map(|&only| Arguments::Unary(only))
                .collect::<Vec<_>>()
        }
        else {
            edges
                .iter()
                .flat_map(|&left| {
                    edges
                        .iter()
                        .map(move |&right| Arguments::Binary([left, right]))
                })
                .collect()
        };
        let zero = byte(core, FixedInteger::U8(0));
        let done = core.computation_return(zero);
        let body = operands
            .iter()
            .enumerate()
            .rev()
            .fold(done, |next, (place, &pair)| {
                let number = u8::try_from(place.saturating_add(1)).unwrap();
                let code = byte(core, FixedInteger::U8(number));
                let fail = core.computation_return(code);
                let scalars = match pair {
                    Arguments::Unary(only) => vec![Scalar::Fixed(only)],
                    Arguments::Binary([left, right]) => {
                        vec![Scalar::Fixed(left), Scalar::Fixed(right)]
                    },
                };
                let expected = row.evaluate(&scalars).unwrap();
                check(core, row, (pair, expected), [fail, next])
            });
        core.value_thunk(body)
    }

    #[test]
    fn the_compiled_answer_of_each_row_is_the_answer_of_the_evaluator()
    {
        // Each row of the native table that the lowering takes: the rows with
        // an operation of a machine or a checked operation.
        let mut core = CoreArena::new();
        let (_, gives_byte) = types(&mut core);
        let rows = PRELUDE
            .iter()
            .copied()
            .filter(|row| row.machine_operation().is_some() || row.checked_operation().is_some())
            .collect::<Vec<_>>();
        let disagreements = rows
            .iter()
            .filter_map(|&row| {
                let name = <&str>::from(row.name());
                let main = agreement(&mut core, row);
                let module = lowered(&core, &[(main, gives_byte)], &[Symbol::from("main")])
                    .unwrap_or_else(|form| panic!("{name}: the check lowers: {form}"));
                let code = exit_code(
                    &module,
                    ConstantIndex::from(0_usize),
                    Symbol::from("agreement"),
                )
                .code();
                (code != Some(0_i32)).then(|| format!("{name}: the check {code:?}"))
            })
            .collect::<Vec<_>>();
        assert_eq!(120, rows.len(), "twelve rows for each of ten widths");
        assert!(
            disagreements.is_empty(),
            "the compiled answer differs from the evaluator: {disagreements:?}"
        );
    }

    /// The types of the case fixtures: `u8 + Unit`, `Unit + Unit`, and the
    /// signatures `U (u8 + Unit → F u8)`, `U (Unit + Unit → F u8)`,
    /// `U (F (u8 + Unit))`, `U (F (Unit + Unit))` and `U (F u8)`.
    ///
    /// # Specification
    /// trivial.
    fn sum_types(core: &mut CoreArena) -> [ValueTypeId; 7]
    {
        let word = core.value_type_base(BaseType::Fixed(IntegerWidth::U8));
        let unit = core.value_type_unit();
        let maybe = core.value_type_sum(&[word, unit]);
        let flag = core.value_type_sum(&[unit, unit]);
        let gives_word = core.comp_type_returner(word);
        let gives_maybe = core.comp_type_returner(maybe);
        let gives_flag = core.comp_type_returner(flag);
        let takes_maybe = core.comp_type_arrow(maybe, gives_word);
        let takes_flag = core.comp_type_arrow(flag, gives_word);
        [
            maybe,
            flag,
            core.value_type_thunk(takes_maybe),
            core.value_type_thunk(takes_flag),
            core.value_type_thunk(gives_maybe),
            core.value_type_thunk(gives_flag),
            core.value_type_thunk(gives_word),
        ]
    }

    /// `thunk (λ. case x {first; second})`, each branch a return of its
    /// value.
    ///
    /// # Specification
    /// trivial.
    fn decide(
        core: &mut CoreArena,
        first: ValueId,
        second: ValueId,
    ) -> ValueId
    {
        let scrutinee = variable(core, DeBruijnIndex::from(0));
        let first = core.computation_return(first);
        let second = core.computation_return(second);
        let case = core.computation_case(scrutinee, &[first, second]);
        let lambda = core.computation_lambda(case);
        core.value_thunk(lambda)
    }

    #[test]
    fn each_branch_of_each_case_runs_and_exits_with_its_answer()
    {
        let mut core = CoreArena::new();
        let [
            _,
            _,
            takes_maybe,
            takes_flag,
            gives_maybe,
            gives_flag,
            gives_word,
        ] = sum_types(&mut core);
        // def clamp(sum : u8 + Unit) -> u8 = match sum { +{.0 = s} => s | +{.1
        // = u} => 255u8 };
        let held = variable(&mut core, DeBruijnIndex::from(0));
        let greatest = byte(&mut core, FixedInteger::U8(255));
        let clamp = decide(&mut core, held, greatest);
        // def pick(flag : Bool) -> u8 = if flag { 3u8 } else { 5u8 };
        let three = byte(&mut core, FixedInteger::U8(3));
        let five = byte(&mut core, FixedInteger::U8(5));
        let pick = decide(&mut core, three, five);
        // def fitting() -> u8 + Unit = +{.0 = 7u8};
        let seven = byte(&mut core, FixedInteger::U8(7));
        let present = core.value_injection(Summand::from(0_usize), seven);
        let returned = core.computation_return(present);
        let fitting = core.value_thunk(returned);
        // def held() -> Bool = false;
        let unit = core.value_unit();
        let absent = core.value_injection(Summand::from(1_usize), unit);
        let returned = core.computation_return(absent);
        let falsity = core.value_thunk(returned);
        // A `let` of a sum that a call gives, then a call of the case.
        let with_let = |core: &mut CoreArena, bound: usize, head: usize| {
            let bound = forced(core, ConstantIndex::from(bound));
            let head = forced(core, ConstantIndex::from(head));
            let argument = variable(core, DeBruijnIndex::from(0));
            let call = core.computation_application(head, argument);
            let body = core.computation_bind(bound, call);
            core.value_thunk(body)
        };
        // A call of the case with an injection as its argument.
        let with_injection = |core: &mut CoreArena, head: usize, summand: usize, body: ValueId| {
            let head = forced(core, ConstantIndex::from(head));
            let argument = core.value_injection(Summand::from(summand), body);
            let call = core.computation_application(head, argument);
            core.value_thunk(call)
        };
        let small = with_let(&mut core, 2, 0);
        let large = with_injection(&mut core, 0, 1, unit);
        let taken = with_injection(&mut core, 1, 0, unit);
        let skipped = with_let(&mut core, 3, 1);
        // A case of an injection takes its arm with no switch.
        let nine = byte(&mut core, FixedInteger::U8(9));
        let known = core.value_injection(Summand::from(0_usize), nine);
        let first = variable(&mut core, DeBruijnIndex::from(0));
        let first = core.computation_return(first);
        let second = core.computation_return(greatest);
        let case = core.computation_case(known, &[first, second]);
        let direct = core.value_thunk(case);

        let names = [
            "clamp", "pick", "fitting", "falsity", "small", "large", "taken", "skipped", "direct",
        ]
        .map(Symbol::from);
        let module = lowered(
            &core,
            &[
                (clamp, takes_maybe),
                (pick, takes_flag),
                (fitting, gives_maybe),
                (falsity, gives_flag),
                (small, gives_word),
                (large, gives_word),
                (taken, gives_word),
                (skipped, gives_word),
                (direct, gives_word),
            ],
            &names,
        )
        .unwrap_or_else(|form| panic!("the case fixtures lower: {form}"));
        let text = module.to_string();
        assert!(
            text.contains(
                "llvm.func internal tailcc @clamp(%v0: !llvm.struct<(i64, i64)>) -> i8 {"
            ),
            "a parameter of a sum is the two words of its layout\n{text}"
        );
        assert!(
            text.contains("llvm.switch"),
            "a case of a parameter switches on its tag\n{text}"
        );
        let direct_function = text
            .split("llvm.func")
            .find(|function| function.contains("@direct("))
            .unwrap_or_default();
        assert!(
            !direct_function.contains("llvm.switch"),
            "a case of an injection takes its arm with no switch\n{text}"
        );
        let exits = [
            (4_usize, "small"),
            (5, "large"),
            (6, "taken"),
            (7, "skipped"),
            (8, "direct"),
        ]
        .map(|(main, name)| {
            exit_code(&module, ConstantIndex::from(main), Symbol::from(name)).code()
        });
        assert_eq!(
            exits,
            [
                Some(7_i32),
                Some(255_i32),
                Some(3_i32),
                Some(5_i32),
                Some(9_i32)
            ],
            "each branch of `clamp` and of `pick` runs, and a case of an injection takes its arm"
        );
    }

    /// `thunk (fix count. λn. { let less = u32.checked_sub n 1u32; match less
    /// { +{.0 = m} => call | +{.1 = u} => 0u8 } })`, where `call` is the call
    /// of `count` on `m` that `call` gives.
    ///
    /// # Specification
    /// trivial.
    fn countdown(
        core: &mut CoreArena,
        call: fn(&mut CoreArena, gandr_core_term::ComputationId) -> gandr_core_term::ComputationId,
    ) -> ValueId
    {
        let row = PRELUDE
            .iter()
            .copied()
            .find(|row| row.name().as_ref() == "u32.checked_sub")
            .unwrap();
        let n = variable(core, DeBruijnIndex::from(0));
        let one = byte(core, FixedInteger::U32(1));
        let less = core.computation_primitive(row, Arguments::Binary([n, one]));
        let count = variable(core, DeBruijnIndex::from(3));
        let head = core.computation_force(count);
        let m = variable(core, DeBruijnIndex::from(0));
        let again = core.computation_application(head, m);
        let first = call(core, again);
        let zero = byte(core, FixedInteger::U8(0));
        let second = core.computation_return(zero);
        let sum = variable(core, DeBruijnIndex::from(0));
        let case = core.computation_case(sum, &[first, second]);
        let bind = core.computation_bind(less, case);
        let lambda = core.computation_lambda(bind);
        let fixpoint = core.computation_fixpoint(lambda, FixpointEvidence::Partial);
        core.value_thunk(fixpoint)
    }

    #[test]
    fn a_countdown_from_a_hundred_million_jumps_and_exits_with_zero()
    {
        let mut core = CoreArena::new();
        let wide = core.value_type_base(BaseType::Fixed(IntegerWidth::U32));
        let word = core.value_type_base(BaseType::Fixed(IntegerWidth::U8));
        let returner = core.comp_type_returner(word);
        let arrow = core.comp_type_arrow(wide, returner);
        let counts = core.value_type_thunk(arrow);
        let gives_word = core.value_type_thunk(returner);
        // The call of itself is the tail of the branch.
        let tail = countdown(&mut core, |_, call| call);
        // The call of itself binds its answer, and the branch returns it.
        let deep = countdown(&mut core, |core, call| {
            let answer = variable(core, DeBruijnIndex::from(0));
            let returned = core.computation_return(answer);
            core.computation_bind(call, returned)
        });
        // def main() -> u8 = countdown start;
        let main = |core: &mut CoreArena, start: u32| {
            let head = forced(core, ConstantIndex::from(0_usize));
            let start = byte(core, FixedInteger::U32(start));
            let call = core.computation_application(head, start);
            core.value_thunk(call)
        };
        let hundred_million = main(&mut core, 100_000_000);
        let thousand = main(&mut core, 1_000);

        let names = ["countdown", "main"].map(Symbol::from);
        let jumps = lowered(
            &core,
            &[(tail, counts), (hundred_million, gives_word)],
            &names,
        )
        .unwrap_or_else(|form| panic!("the countdown lowers: {form}"));
        let text = jumps.to_string();
        assert!(
            text.contains("gandr.jump @countdown(") && !text.contains("gandr.call @countdown("),
            "the countdown calls itself only in a tail\n{text}"
        );
        assert_eq!(
            exit_code(
                &jumps,
                ConstantIndex::from(1_usize),
                Symbol::from("countdown")
            )
            .code(),
            Some(0_i32),
            "the countdown from 100,000,000 ends at 0, with no stack"
        );

        let stacks = lowered(&core, &[(deep, counts), (thousand, gives_word)], &names)
            .unwrap_or_else(|form| panic!("the deep countdown lowers: {form}"));
        assert!(
            stacks.to_string().contains("gandr.call @countdown("),
            "a call of itself that is not a tail is a call\n{stacks}"
        );
        assert_eq!(
            exit_code(&stacks, ConstantIndex::from(1_usize), Symbol::from("deep")).code(),
            Some(0_i32),
            "a countdown that calls itself in no tail runs with a stack"
        );
    }

    #[test]
    fn a_sum_with_no_layout_is_refused_by_name()
    {
        let mut core = CoreArena::new();
        let [maybe, _, takes_maybe, _, _, _, gives_word] = sum_types(&mut core);
        let word = core.value_type_base(BaseType::Fixed(IntegerWidth::U8));
        let unit = core.value_type_unit();
        let held = variable(&mut core, DeBruijnIndex::from(0));
        let greatest = byte(&mut core, FixedInteger::U8(255));
        let clamp = decide(&mut core, held, greatest);

        // A sum of three summands, and a sum with a sum as a summand.
        let gives_word_type = core.comp_type_returner(word);
        let three = core.value_type_sum(&[word, unit, unit]);
        let nested = core.value_type_sum(&[maybe, unit]);
        let refusals = [three, nested].map(|sum| {
            let arrow = core.comp_type_arrow(sum, gives_word_type);
            let signature = core.value_type_thunk(arrow);
            lowered(&core, &[(clamp, signature)], &[Symbol::from("clamp")]).map(|_| ())
        });
        assert_eq!(
            refusals,
            [Err(Form::Sum); 2],
            "a sum of three summands and a sum of a sum have no layout"
        );

        // A case of a word.
        let takes_word = core.comp_type_arrow(word, gives_word_type);
        let takes_word = core.value_type_thunk(takes_word);
        assert_eq!(
            lowered(&core, &[(clamp, takes_word)], &[Symbol::from("clamp")]).map(|_| ()),
            Err(Form::Sum),
            "a word is not a sum"
        );

        // An injection into a third summand, as an argument of `u8 + Unit`.
        let head = forced(&mut core, ConstantIndex::from(0_usize));
        let unit_value = core.value_unit();
        let third = core.value_injection(Summand::from(2_usize), unit_value);
        let call = core.computation_application(head, third);
        let caller = core.value_thunk(call);
        assert_eq!(
            lowered(&core, &[(clamp, takes_maybe), (caller, gives_word)], &[
                Symbol::from("clamp"),
                Symbol::from("caller")
            ])
            .map(|_| ()),
            Err(Form::Sum),
            "a sum of two summands has no third"
        );

        // An injection from a definition of a word.
        let returned = core.computation_return(third);
        let wrong = core.value_thunk(returned);
        assert_eq!(
            lowered(&core, &[(wrong, gives_word)], &[Symbol::from("wrong")]).map(|_| ()),
            Err(Form::Delivery),
            "a word goes where the definition gives a word"
        );
    }

    /// `{ let x = case; u8.wrapping_add x 1u8 }`, the body of a definition
    /// whose case delivers to the binder after it.
    ///
    /// # Specification
    /// trivial.
    fn incremented(
        core: &mut CoreArena,
        case: gandr_core_term::ComputationId,
    ) -> gandr_core_term::ComputationId
    {
        let bound = variable(core, DeBruijnIndex::from(0));
        let one = byte(core, FixedInteger::U8(1));
        let add = core.computation_primitive(wrapping_add(), Arguments::Binary([bound, one]));
        core.computation_bind(case, add)
    }

    #[test]
    fn each_branch_gives_its_answer_to_the_join_after_its_case()
    {
        let mut core = CoreArena::new();
        let [_, _, takes_maybe, takes_flag, _, _, gives_word] = sum_types(&mut core);
        // def after(sum : u8 + Unit) -> u8 =
        //     { let x = match sum { s => s | u => 255u8 }; u8.wrapping_add x
        // 1u8 };
        let scrutinee = variable(&mut core, DeBruijnIndex::from(0));
        let held = variable(&mut core, DeBruijnIndex::from(0));
        let first = core.computation_return(held);
        let greatest = byte(&mut core, FixedInteger::U8(255));
        let second = core.computation_return(greatest);
        let case = core.computation_case(scrutinee, &[first, second]);
        let body = incremented(&mut core, case);
        let lambda = core.computation_lambda(body);
        let after = core.value_thunk(lambda);
        // def nested(sum : u8 + Unit) -> u8 = { let x = match sum {
        //     s => { let y = match sum { t => t | u => 1u8 }; u8.wrapping_add y
        // 1u8 }     | u => 255u8 }; u8.wrapping_add x 1u8 };
        let inner_scrutinee = variable(&mut core, DeBruijnIndex::from(1));
        let inner_held = variable(&mut core, DeBruijnIndex::from(0));
        let inner_first = core.computation_return(inner_held);
        let one = byte(&mut core, FixedInteger::U8(1));
        let inner_second = core.computation_return(one);
        let inner = core.computation_case(inner_scrutinee, &[inner_first, inner_second]);
        let first = incremented(&mut core, inner);
        let scrutinee = variable(&mut core, DeBruijnIndex::from(0));
        let case = core.computation_case(scrutinee, &[first, second]);
        let body = incremented(&mut core, case);
        let lambda = core.computation_lambda(body);
        let nested = core.value_thunk(lambda);
        // def quiet(flag : Bool) -> u8 = { let _ = if flag { () } else { () };
        // 4u8 };
        let unit = core.value_unit();
        let first = core.computation_return(unit);
        let second = core.computation_return(unit);
        let scrutinee = variable(&mut core, DeBruijnIndex::from(0));
        let case = core.computation_case(scrutinee, &[first, second]);
        let four = byte(&mut core, FixedInteger::U8(4));
        let returned = core.computation_return(four);
        let body = core.computation_bind(case, returned);
        let lambda = core.computation_lambda(body);
        let quiet = core.value_thunk(lambda);
        // A call of a definition with an injection as its argument.
        let six = byte(&mut core, FixedInteger::U8(6));
        let mut caller = |head: usize, summand: usize, body: ValueId| {
            let head = forced(&mut core, ConstantIndex::from(head));
            let argument = core.value_injection(Summand::from(summand), body);
            let call = core.computation_application(head, argument);
            core.value_thunk(call)
        };
        let callers = [
            caller(0, 0, six),
            caller(0, 1, unit),
            caller(1, 0, six),
            caller(1, 1, unit),
            caller(2, 0, unit),
            caller(2, 1, unit),
        ];

        let names = [
            "after",
            "nested",
            "quiet",
            "after_six",
            "after_none",
            "nested_six",
            "nested_none",
            "quiet_true",
            "quiet_false",
        ]
        .map(Symbol::from);
        let mut definitions = vec![
            (after, takes_maybe),
            (nested, takes_maybe),
            (quiet, takes_flag),
        ];
        definitions.extend(callers.map(|value| (value, gives_word)));
        let module = lowered(&core, &definitions, &names)
            .unwrap_or_else(|form| panic!("the join fixtures lower: {form}"));
        let text = module.to_string();
        assert!(
            text.contains(": i8):") && text.contains("llvm.br ^bb"),
            "the branches of a case give a word to a block with one argument\n{text}"
        );
        let exits = (3_usize .. 9).map(|main| {
            exit_code(
                &module,
                ConstantIndex::from(main),
                names.get(main).copied().unwrap(),
            )
            .code()
        });
        assert_eq!(
            exits.collect::<Vec<_>>(),
            [7_i32, 0_i32, 8_i32, 0_i32, 4_i32, 4_i32].map(Some),
            "each branch gives its answer to the join, and the join runs on it"
        );
    }

    #[test]
    fn an_injection_to_a_join_is_refused()
    {
        // def pass(sum : u8 + Unit) -> u8 = { let x = match sum {
        //     s => +{.0 = s} | u => +{.1 = u} }; match x { s => s | u => 255u8
        // } };
        let mut core = CoreArena::new();
        let [_, _, takes_maybe, ..] = sum_types(&mut core);
        let scrutinee = variable(&mut core, DeBruijnIndex::from(0));
        let held = variable(&mut core, DeBruijnIndex::from(0));
        let present = core.value_injection(Summand::from(0_usize), held);
        let first = core.computation_return(present);
        let absent = core.value_injection(Summand::from(1_usize), held);
        let second = core.computation_return(absent);
        let case = core.computation_case(scrutinee, &[first, second]);
        let bound = variable(&mut core, DeBruijnIndex::from(0));
        let held = variable(&mut core, DeBruijnIndex::from(0));
        let first = core.computation_return(held);
        let greatest = byte(&mut core, FixedInteger::U8(255));
        let second = core.computation_return(greatest);
        let inspect = core.computation_case(bound, &[first, second]);
        let body = core.computation_bind(case, inspect);
        let lambda = core.computation_lambda(body);
        let pass = core.value_thunk(lambda);
        assert_eq!(
            lowered(&core, &[(pass, takes_maybe)], &[Symbol::from("pass")]).map(|_| ()),
            Err(Form::Sum),
            "a branch does not know the layout of an injection that it gives to a join"
        );
    }

    #[test]
    fn a_definition_whose_row_is_not_empty_lowers_and_runs()
    {
        // def main() -> u8 / {Console} = 42u8, with no effect node in its
        // body.
        let mut core = CoreArena::new();
        let word = core.value_type_base(BaseType::Fixed(IntegerWidth::U8));
        let unit = core.value_type_unit();
        let console = EffectRow::singleton(
            EffectSig::new(EffectName::from("Console"), [EffectOp {
                name: OperationName::from("run"),
                payload: unit,
                reply: unit,
            }])
            .expect("one operation"),
        );
        let returner = core.comp_type_returner_with_effects(word, console);
        let signature = core.value_type_thunk(returner);
        let answer = byte(&mut core, FixedInteger::U8(42));
        let returned = core.computation_return(answer);
        let main = core.value_thunk(returned);
        let module = lowered(&core, &[(main, signature)], &[Symbol::from("main")])
            .unwrap_or_else(|form| panic!("the row does not refuse the definition: {form}"));
        assert_eq!(
            exit_code(&module, ConstantIndex::from(0_usize), Symbol::from("row")).code(),
            Some(42_i32),
            "the definition runs and answers 42"
        );
    }

    #[test]
    fn a_node_outside_the_lowering_is_refused_by_its_name()
    {
        let mut core = CoreArena::new();
        let word = core.value_type_base(BaseType::Fixed(IntegerWidth::U8));
        let returner = core.comp_type_returner(word);
        let signature = core.value_type_thunk(returner);
        let mut arena = CommandArena::new();
        let back = arena
            .mint_consumer(ConsumerNode::Covariable(CovariableIndex::from(0)))
            .unwrap();
        let one = arena
            .mint_producer(ProducerNode::Literal(Literal::Fixed(FixedInteger::U8(1))))
            .unwrap();
        let top = arena.mint_consumer(ConsumerNode::Top).unwrap();
        let decomposed = arena.mint_producer(ProducerNode::Decompose(one)).unwrap();
        let magnitude = Magnitude::from_decimal_text(String::from("1")).unwrap();
        let integer = arena
            .mint_producer(ProducerNode::Literal(Literal::Integer(
                IntegerLiteral::new(gandr_kernel_term::Sign::NonNegative, magnitude),
            )))
            .unwrap();
        let empty = arena
            .mint_producer(ProducerNode::Constructor {
                tag: ConstructorTag::ListNil,
                producers: Box::default(),
                types: Box::default(),
                consumers: Box::default(),
            })
            .unwrap();
        let abandon = arena
            .mint_command(CommandNode::Abandon {
                stack: one,
                continuation: back,
            })
            .unwrap();
        let cuts = [
            (decomposed, back, "ProducerNode::Decompose"),
            (one, top, "ConsumerNode::Top"),
            (integer, back, "Literal::Integer"),
            (empty, back, "ConstructorTag::ListNil"),
        ]
        .map(|(producer, consumer, node)| {
            let body = arena
                .mint_cut(Polarity::Positive, producer, consumer)
                .unwrap();
            (body, node)
        });
        let bodies = cuts
            .into_iter()
            .chain([(abandon, "CommandNode::Abandon")])
            .map(|(body, node)| {
                let thunk = arena.mint_producer(ProducerNode::Thunk { body }).unwrap();
                (thunk, node)
            })
            .collect::<Vec<_>>();
        for (value, node) in bodies {
            let definitions = [Definition {
                name: Symbol::from("outside"),
                value,
                signature,
            }];
            assert_eq!(
                lower(&arena, &core, &definitions).map(|_| ()),
                Err(Form::Outside(node)),
                "the lowering refuses the node by its name"
            );
        }

        // def f(x : Integer) -> u8, a parameter of a type with no form.
        let integer_type = core.value_type_base(BaseType::Integer);
        let arrow = core.comp_type_arrow(integer_type, returner);
        let takes_integer = core.value_type_thunk(arrow);
        let values = fixture(&mut core);
        assert_eq!(
            lowered(&core, &[(values[INC], takes_integer)], &[Symbol::from("f")]).map(|_| ()),
            Err(Form::Outside("BaseType::Integer")),
            "the lowering refuses the type by its name"
        );
    }
}
