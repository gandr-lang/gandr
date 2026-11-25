//! The tests of the read entry, called from Rust through
//! [`gandr_runtime_mlir::read()`]. Each test reads the same body as its C++
//! twin in `cxx/tests/read/`. They run under the feature `full`, which links
//! the shim.

#![cfg(feature = "full")]

#[cfg(test)]
mod tests
{
    use gandr_runtime_mlir::Hole;
    use gandr_runtime_mlir::Operand;
    use gandr_runtime_mlir::Operation;
    use gandr_runtime_mlir::ReadError;
    use gandr_runtime_mlir::read;

    /// The hole `address`, a word of 64 bits.
    const ADDRESS: Hole<'static> = Hole {
        name: "address",
        ty: "i64",
    };

    /// The cast of the hole `address` to a pointer: the first operation of
    /// each body of a load or a store.
    ///
    /// # Specification
    /// trivial.
    fn assert_cast(operation: &Operation)
    {
        assert_eq!(operation.name, "llvm.inttoptr", "{operation:?}");
        assert_eq!(operation.operands, [Operand::Hole(0)], "{operation:?}");
        assert_eq!(operation.results, ["!llvm.ptr"], "{operation:?}");
    }

    #[test]
    fn read_load()
    {
        let facts = read(include_str!("../cxx/tests/read/load.body").into(), &[
            ADDRESS,
        ])
        .unwrap();
        let [ref cast, ref load] = facts[..]
        else {
            panic!("two operations, got {facts:?}");
        };
        assert_cast(cast);
        assert_eq!(load.name, "llvm.load");
        assert_eq!(load.operands, [Operand::Result {
            operation: 0,
            index: 0
        }]);
        assert_eq!(load.results, ["i8"]);
        assert!(
            load.attributes
                .contains(&("ordering".to_owned(), "0 : i64".to_owned())),
            "not atomic: {load:?}"
        );
    }

    #[test]
    fn read_store()
    {
        let word = Hole {
            name: "word",
            ty: "i64",
        };
        let facts = read(include_str!("../cxx/tests/read/store.body").into(), &[
            ADDRESS, word,
        ])
        .unwrap();
        let [ref cast, ref store] = facts[..]
        else {
            panic!("two operations, got {facts:?}");
        };
        assert_cast(cast);
        assert_eq!(store.name, "llvm.store");
        assert_eq!(store.operands, [Operand::Hole(1), Operand::Result {
            operation: 0,
            index: 0
        }]);
        assert!(store.results.is_empty(), "a store has no result");
    }

    #[test]
    fn read_atomic_load()
    {
        let facts = read(
            include_str!("../cxx/tests/read/atomic-load.body").into(),
            &[ADDRESS],
        )
        .unwrap();
        let [ref cast, ref load] = facts[..]
        else {
            panic!("two operations, got {facts:?}");
        };
        assert_cast(cast);
        assert_eq!(load.results, ["i32"]);
        // 4 is `acquire` in `llvm::AtomicOrdering`.
        assert!(
            load.attributes
                .contains(&("ordering".to_owned(), "4 : i64".to_owned())),
            "{load:?}"
        );
        assert!(
            load.attributes
                .contains(&("alignment".to_owned(), "4 : i64".to_owned())),
            "{load:?}"
        );
    }

    #[test]
    fn read_inline_asm()
    {
        let holes = [
            Hole {
                name: "number",
                ty: "i64",
            },
            Hole {
                name: "a",
                ty: "i64",
            },
        ];
        let facts = read(
            include_str!("../cxx/tests/read/inline-asm.body").into(),
            &holes,
        )
        .unwrap();
        let [ref call] = facts[..]
        else {
            panic!("one operation, got {facts:?}");
        };
        assert_eq!(call.name, "llvm.inline_asm");
        assert_eq!(call.operands, [Operand::Hole(0), Operand::Hole(1)]);
        assert_eq!(call.results, ["i64"]);
        assert!(
            call.attributes
                .contains(&("asm_string".to_owned(), "\"syscall\"".to_owned())),
            "{call:?}"
        );
        assert!(
            call.attributes
                .contains(&("has_side_effects".to_owned(), "unit".to_owned())),
            "{call:?}"
        );
    }

    /// The verifier refuses an atomic load with no alignment, at the line
    /// and the column of the load in the body.
    #[test]
    fn read_verifier_refuses()
    {
        let error = read(
            include_str!("../cxx/tests/read/atomic-no-alignment.body").into(),
            &[ADDRESS],
        )
        .unwrap_err();
        let ReadError::InvalidText(ref diagnostics) = error
        else {
            panic!("expected the refusal of the verifier, got {error}");
        };
        let first = diagnostics.first().unwrap();
        assert_eq!((first.line, first.column), (2, 9), "{error}");
        assert_eq!(first.severity, "error");
        assert!(
            first
                .message
                .contains("expected alignment for atomic access"),
            "{error}"
        );
    }

    /// A hole that the list does not name is a value with no definition, at
    /// its place in the body.
    #[test]
    fn read_unknown_hole()
    {
        let error = read(include_str!("../cxx/tests/read/load.body").into(), &[]).unwrap_err();
        let ReadError::InvalidText(ref diagnostics) = error
        else {
            panic!("expected the refusal of the parser, got {error}");
        };
        let first = diagnostics.first().unwrap();
        assert_eq!((first.line, first.column), (1, 24), "{error}");
    }
}
