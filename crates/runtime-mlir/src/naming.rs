//! The MLIR names of the operations, the attributes and the constants of a
//! block, where they are not the names of the block.
//!
//! A name of a block obeys the grammar of gandr, so it is not always the name
//! in MLIR. `select` and `return` are reserved words, so the block of `std`
//! names them `choose` and `ret`. An operation with a variable count of
//! operands has one operation in the block for each count, such as
//! `inline_asm2`. A constant of an attribute, such as `order_acquire`, is an
//! integer in MLIR.
//!
//! # Items
//!
//! [`Naming`] holds a sorted table of operation forms and a sorted table of
//! constant forms. [`Naming::LLVM`] is the table of the block of `std.llvm`.
//! [`Naming::NONE`] keeps each name of the block.
//!
//! | Form | What it gives |
//! | ---- | ------------- |
//! | [`OperationForm`] | the MLIR name of an operation, the MLIR attribute of each port that needs one, and the attributes that each use of the operation has |
//! | [`AttributeForm`] | the MLIR name of the attribute of a port, and how its value prints |
//! | [`ConstantForm`] | the MLIR value of a constant of a sort of constants |
//!
//! # References
//!
//! - `vault:01a21222-e4bd-74a8-a918-8efd438926aa` — dependency: §
//!   halves-operations, the operations of the dialect that each operation of
//!   the block names.

use gandr_theory_levitation::Name;

/// The name of a port in the block, as a [`Naming`] states it.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct PortName(pub &'static str);

/// How the value of the attribute of a port prints.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum AttributeKind
{
    /// The value as it is: an integer with the type `i64`, a text in quotes,
    /// or the MLIR value of a constant.
    Plain,
    /// An integer with the type that the type port of this name holds.
    TypedBy(PortName),
    /// A text as a reference to a symbol, `@text`.
    Symbol,
    /// The type that a type port holds, as a type attribute.
    Type,
}

/// The MLIR attribute of one port of an operation.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct AttributeForm
{
    /// The name of the port in the block.
    pub port: &'static str,
    /// The name of the attribute in MLIR.
    pub mlir: &'static str,
    /// How the value prints.
    pub kind: AttributeKind,
}

/// The MLIR form of one operation of a block.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct OperationForm
{
    /// The name of the operation in the block.
    pub name: &'static str,
    /// The name of the operation in MLIR, with its dialect.
    pub mlir: &'static str,
    /// The attribute of each port whose attribute is not the port name with
    /// the kind [`AttributeKind::Plain`].
    pub attributes: &'static [AttributeForm],
    /// The attributes that each use of the operation has, as MLIR text, or
    /// nothing.
    pub fixed: &'static str,
}

impl OperationForm
{
    /// The form of the attribute of the port `port`, when the operation names
    /// one.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn attribute(
        &self,
        port: &Name,
    ) -> Option<&AttributeForm>
    {
        self.attributes
            .iter()
            .find(|form| form.port == port.as_ref())
    }
}

/// The MLIR value of one constant of a sort of constants.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct ConstantForm
{
    /// The name of the constant in the block.
    pub name: &'static str,
    /// The value in MLIR, with its type.
    pub value: &'static str,
}

/// The MLIR names of a block: its operation forms and its constant forms, each
/// sorted by the name in the block.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Naming
{
    /// The operation forms, sorted by name.
    operations: &'static [OperationForm],
    /// The constant forms, sorted by name.
    constants: &'static [ConstantForm],
}

/// An attribute with the kind [`AttributeKind::Plain`].
macro_rules! renamed {
    ($port:literal, $mlir:literal) => {
        AttributeForm {
            port: $port,
            mlir: $mlir,
            kind: AttributeKind::Plain,
        }
    };
}

/// The attributes of `inline_asm<N>` that need a form.
const INLINE_ASM: &[AttributeForm] = &[renamed!("text", "asm_string")];

/// The form of `inline_asm<N>`: the operation `llvm.inline_asm` with side
/// effects.
macro_rules! inline_asm {
    ($name:literal) => {
        OperationForm {
            name: $name,
            mlir: "llvm.inline_asm",
            attributes: INLINE_ASM,
            fixed: "has_side_effects",
        }
    };
}

/// The value of a constant of an enum attribute of MLIR.
macro_rules! constant {
    ($name:literal, $value:literal) => {
        ConstantForm {
            name: $name,
            value: $value,
        }
    };
}

impl Naming
{
    /// The MLIR names of the block of `std.llvm`.
    ///
    /// The values of the constants are the enum values of the `llvm` dialect:
    /// `ICmpPredicate`, `AtomicOrdering` and `AtomicBinOp`.
    pub const LLVM: Self = Self {
        operations: &[
            OperationForm {
                name: "atomicrmw",
                mlir: "llvm.atomicrmw",
                attributes: &[
                    renamed!("operation", "bin_op"),
                    renamed!("order", "ordering"),
                ],
                fixed: "",
            },
            OperationForm {
                name: "choose",
                mlir: "llvm.select",
                attributes: &[],
                fixed: "",
            },
            OperationForm {
                name: "constant",
                mlir: "llvm.mlir.constant",
                attributes: &[AttributeForm {
                    port: "value",
                    mlir: "value",
                    kind: AttributeKind::TypedBy(PortName("t")),
                }],
                fixed: "",
            },
            OperationForm {
                name: "getelementptr",
                mlir: "llvm.getelementptr",
                attributes: &[AttributeForm {
                    port: "element",
                    mlir: "elem_type",
                    kind: AttributeKind::Type,
                }],
                // The one index is the operand: the marker of a dynamic index.
                fixed: "rawConstantIndices = array<i32: -2147483648>",
            },
            inline_asm!("inline_asm1"),
            inline_asm!("inline_asm2"),
            inline_asm!("inline_asm3"),
            inline_asm!("inline_asm4"),
            inline_asm!("inline_asm5"),
            inline_asm!("inline_asm6"),
            inline_asm!("inline_asm7"),
            OperationForm {
                name: "load_atomic",
                mlir: "llvm.load",
                attributes: &[renamed!("order", "ordering")],
                fixed: "",
            },
            OperationForm {
                name: "ret",
                mlir: "llvm.return",
                attributes: &[],
                fixed: "",
            },
            OperationForm {
                name: "store_atomic",
                mlir: "llvm.store",
                attributes: &[renamed!("order", "ordering")],
                fixed: "",
            },
            OperationForm {
                name: "tail_call1",
                mlir: "llvm.call",
                attributes: &[AttributeForm {
                    port: "callee",
                    mlir: "callee",
                    kind: AttributeKind::Symbol,
                }],
                fixed: "CConv = #llvm.cconv<tailcc>, TailCallKind = \
                        #llvm.tailcallkind<musttail>, operandSegmentSizes = array<i32: 1, \
                        0>, op_bundle_sizes = array<i32>",
            },
        ],
        constants: &[
            constant!("eq", "0 : i64"),
            constant!("ne", "1 : i64"),
            constant!("order_acq_rel", "6 : i64"),
            constant!("order_acquire", "4 : i64"),
            constant!("order_monotonic", "2 : i64"),
            constant!("order_release", "5 : i64"),
            constant!("order_seq_cst", "7 : i64"),
            constant!("rmw_add", "1 : i64"),
            constant!("rmw_and", "3 : i64"),
            constant!("rmw_or", "5 : i64"),
            constant!("rmw_sub", "2 : i64"),
            constant!("rmw_xchg", "0 : i64"),
            constant!("rmw_xor", "6 : i64"),
            constant!("sge", "5 : i64"),
            constant!("sgt", "4 : i64"),
            constant!("sle", "3 : i64"),
            constant!("slt", "2 : i64"),
            constant!("uge", "9 : i64"),
            constant!("ugt", "8 : i64"),
            constant!("ule", "7 : i64"),
            constant!("ult", "6 : i64"),
        ],
    };
    /// No MLIR name: each operation and each attribute has its name in the
    /// block, and no constant has a value.
    pub const NONE: Self = Self {
        operations: &[],
        constants: &[],
    };

    /// The form of the operation `name`, when the table has one.
    ///
    /// # Specification
    /// - requires: the operation forms are sorted by name, as the test
    ///   `naming::tests::each_table_is_sorted_by_name` checks.
    /// - ensures: the form whose name is `name`, or nothing.
    /// - panics: none.
    /// - executable: none — the answer is a borrow of the table.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — `choose` gives `llvm.select`, and `add` has no form.
    /// - witness: `naming::tests::a_renamed_operation_and_a_constant_have_their_mlir_form`
    #[inline]
    #[must_use]
    pub fn operation(
        &self,
        name: &Name,
    ) -> Option<&OperationForm>
    {
        self.operations.get(
            self.operations
                .binary_search_by(|form| form.name.cmp(name.as_ref()))
                .ok()?,
        )
    }

    /// The form of the constant `name`, when the table has one.
    ///
    /// # Specification
    /// - requires: the constant forms are sorted by name.
    /// - ensures: the form whose name is `name`, or nothing.
    /// - panics: none.
    /// - executable: none — the answer is a borrow of the table.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — `order_acquire` gives `4 : i64`, and an unknown name
    ///   has no form.
    /// - witness: `naming::tests::a_renamed_operation_and_a_constant_have_their_mlir_form`
    #[inline]
    #[must_use]
    pub fn constant(
        &self,
        name: &Name,
    ) -> Option<&ConstantForm>
    {
        self.constants.get(
            self.constants
                .binary_search_by(|form| form.name.cmp(name.as_ref()))
                .ok()?,
        )
    }
}

#[cfg(test)]
mod tests
{
    use super::*;

    #[test]
    fn each_table_is_sorted_by_name()
    {
        let naming = Naming::LLVM;
        assert!(
            naming
                .operations
                .windows(2)
                .all(|pair| matches!(*pair, [ref first, ref second] if first.name < second.name)),
            "the operation forms are sorted, with no name twice"
        );
        assert!(
            naming
                .constants
                .windows(2)
                .all(|pair| matches!(*pair, [ref first, ref second] if first.name < second.name)),
            "the constant forms are sorted, with no name twice"
        );
    }

    #[test]
    fn a_renamed_operation_and_a_constant_have_their_mlir_form()
    {
        let naming = Naming::LLVM;
        assert_eq!(
            naming
                .operation(&Name::from("choose"))
                .map(|form| form.mlir),
            Some("llvm.select")
        );
        assert_eq!(naming.operation(&Name::from("add")), None);
        assert_eq!(
            naming
                .constant(&Name::from("order_acquire"))
                .map(|form| form.value),
            Some("4 : i64")
        );
        assert_eq!(naming.constant(&Name::from("acquire")), None);
        assert_eq!(Naming::NONE.operation(&Name::from("choose")), None);
    }
}
