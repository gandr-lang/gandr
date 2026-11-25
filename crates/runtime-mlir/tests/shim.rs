//! The tests of the shim in `cxx/CMakeLists.txt`, called from Rust through
//! [`gandr_runtime_mlir::compile`]. Each test reads the same MLIR file as its
//! C++ twin. They run under the feature `full`, which links the shim.

#![cfg(feature = "full")]

#[cfg(test)]
mod tests
{
    use gandr_runtime_mlir::CompileError;
    use gandr_runtime_mlir::Text;
    use gandr_runtime_mlir::Triple;
    use gandr_runtime_mlir::compile;

    /// The triple of the tests on x86-64.
    const X86_64: &str = "x86_64-unknown-linux-gnu";

    /// One function in the `llvm` dialect.
    const ADD: &str = include_str!("../cxx/tests/add.mlir");

    /// Compile `text` for `triple`, and check that the answer is an ELF
    /// object.
    ///
    /// # Specification
    /// trivial.
    fn assert_object(
        text: Text<'_>,
        triple: Triple<'_>,
    )
    {
        let object = compile(text, triple).unwrap_or_else(|error| panic!("{triple:?}: {error}"));
        assert!(
            object.as_ref().starts_with(b"\x7fELF"),
            "{triple:?}: the object is not ELF"
        );
    }

    #[test]
    fn object_x86_64()
    {
        assert_object(ADD.into(), X86_64.into());
    }

    #[test]
    fn object_aarch64()
    {
        assert_object(ADD.into(), "aarch64-unknown-linux-gnu".into());
    }

    #[test]
    fn object_riscv64()
    {
        assert_object(ADD.into(), "riscv64-unknown-linux-gnu".into());
    }

    #[test]
    fn verifier_refuses()
    {
        let error = compile(
            include_str!("../cxx/tests/wrong-return.mlir").into(),
            X86_64.into(),
        )
        .unwrap_err();
        let CompileError::InvalidText(ref text) = error
        else {
            panic!("expected the refusal of the verifier, got {error}");
        };
        assert!(
            text.contains("'llvm.return' op mismatching result types"),
            "{text}"
        );
    }

    #[test]
    fn unknown_target()
    {
        let error = compile(ADD.into(), "nonsense-unknown-none".into()).unwrap_err();
        assert!(matches!(error, CompileError::UnknownTarget(_)), "{error}");
    }

    #[test]
    fn operation_integers()
    {
        assert_object(
            include_str!("../cxx/tests/integers.mlir").into(),
            X86_64.into(),
        );
    }

    #[test]
    fn operation_load_store()
    {
        assert_object(
            include_str!("../cxx/tests/memory.mlir").into(),
            X86_64.into(),
        );
    }

    #[test]
    fn operation_atomic()
    {
        assert_object(
            include_str!("../cxx/tests/atomic.mlir").into(),
            X86_64.into(),
        );
    }

    #[test]
    fn operation_inline_asm()
    {
        assert_object(
            include_str!("../cxx/tests/inline-asm.mlir").into(),
            X86_64.into(),
        );
    }

    #[test]
    fn convention_tailcc_x86_64()
    {
        assert_object(
            include_str!("../cxx/tests/tail-call.mlir").into(),
            X86_64.into(),
        );
    }

    #[test]
    fn convention_preserve_none()
    {
        let error = compile(
            include_str!("../cxx/tests/preserve-none.mlir").into(),
            X86_64.into(),
        )
        .unwrap_err();
        let CompileError::InvalidText(ref text) = error
        else {
            panic!("expected the refusal of the parser, got {error}");
        };
        assert!(text.contains("preserve_nonecc"), "{text}");
    }

    /// Calls on more than one thread at the same time give each its object.
    #[test]
    fn calls_on_threads()
    {
        std::thread::scope(|scope| {
            let handles: Vec<_> = core::iter::repeat_with(|| {
                scope.spawn(|| {
                    compile(ADD.into(), X86_64.into()).map(|object| object.as_ref().len())
                })
            })
            .take(8)
            .collect();
            for handle in handles {
                let len = handle.join().unwrap().unwrap();
                assert!(len > 0, "an empty object");
            }
        });
    }

    /// The fatal error of `tailcc` on riscv64 gives a status. The process
    /// continues, and the next call in it gives an object.
    #[test]
    fn convention_tailcc_riscv64_refused()
    {
        let error = compile(
            include_str!("../cxx/tests/tail-call.mlir").into(),
            "riscv64-unknown-linux-gnu".into(),
        )
        .unwrap_err();
        let CompileError::Codegen(ref text) = error
        else {
            panic!("expected the error of the code generator, got {error}");
        };
        assert!(text.contains("Unsupported calling convention"), "{text}");
        assert_object(ADD.into(), "riscv64-unknown-linux-gnu".into());
    }

    /// The diagnostic of the verifier that refuses `text`.
    ///
    /// # Specification
    /// trivial.
    fn refusal(text: Text<'_>) -> String
    {
        let error = compile(text, X86_64.into()).unwrap_err();
        let CompileError::InvalidText(diagnostic) = error
        else {
            panic!("expected the refusal of the verifier, got {error}");
        };
        diagnostic
    }

    /// Each transition of the `gandr` dialect passes the verifier, and the
    /// lowering leaves no `gandr` operation for the translation.
    #[test]
    fn dialect_transitions()
    {
        assert_object(
            include_str!("../cxx/tests/transitions.mlir").into(),
            X86_64.into(),
        );
    }

    #[test]
    fn dialect_return_wrong_type()
    {
        let diagnostic = refusal(include_str!("../cxx/tests/return-wrong-type.mlir").into());
        assert!(
            diagnostic.contains("'gandr.return' op returns 'i16' from a function of 'i8'"),
            "{diagnostic}"
        );
    }

    #[test]
    fn dialect_call_wrong_operand()
    {
        let diagnostic = refusal(include_str!("../cxx/tests/call-wrong-operand.mlir").into());
        assert!(
            diagnostic.contains(
                "'gandr.call' op gives operand 0 of type 'i16' to @inc, which takes 'i8'"
            ),
            "{diagnostic}"
        );
    }

    #[test]
    fn dialect_jump_wrong_result()
    {
        let diagnostic = refusal(include_str!("../cxx/tests/jump-wrong-result.mlir").into());
        assert!(
            diagnostic.contains("'gandr.jump' op jumps to @wide of 'i16' from a function of 'i8'"),
            "{diagnostic}"
        );
    }
}
