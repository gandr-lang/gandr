// The `gandr` dialect: the transitions of the L machine that the first slice
// uses, each one an operation. `dialect.cpp` gives each operation its
// verifier and its one lowering to the `llvm` dialect.
//
// A definition is an `llvm.func` with the convention `tailcc`. Its body cuts
// values against continuations:
//
// | Command | Operation |
// | ------- | --------- |
// | `⟨v |+ α⟩`, `α` the return continuation | `gandr.return` |
// | `⟨p(v, w) |+ k⟩`, a native operation of a width | `gandr.wrapping_add`, `gandr.wrapping_sub`, `gandr.wrapping_mul`, `gandr.and`, `gandr.or`, `gandr.xor` |
// | `⟨p(v) |+ k⟩`, a native operation of a width over one word | `gandr.not` |
// | `⟨force c | apply(v̄; α)⟩`, `α` the return continuation | `gandr.jump` |
// | `⟨force c | apply(v̄; μ̃x. s)⟩` | `gandr.call`, then `s` over its result |
//
// A binder `μ̃x` is the SSA value of the operation before it. A value of
// `Unit` has no word: a return of it has no operand, a call that gives it has
// no result, and its function has the result type `void`.

#ifndef GANDR_TD
#define GANDR_TD

include "mlir/IR/OpBase.td"
include "mlir/IR/SymbolInterfaces.td"
include "mlir/Interfaces/InferTypeOpInterface.td"
include "mlir/Interfaces/SideEffectInterfaces.td"

def Gandr_Dialect : Dialect {
  let name = "gandr";
  let cppNamespace = "::gandr";
  let summary = "The transitions of the L machine of gandr.";
  let dependentDialects = ["::mlir::LLVM::LLVMDialect"];
}

class Gandr_Op<string mnemonic, list<Trait> traits = []>
    : Op<Gandr_Dialect, mnemonic, traits>;

// A native operation of a width: two words in, one word out, modulo the
// width.
class Gandr_WrappingOp<string mnemonic, string what>
    : Gandr_Op<mnemonic, [Pure, SameOperandsAndResultType]> {
  let summary = "the " # what # " of two words, modulo their width";
  let arguments = (ins AnySignlessInteger:$lhs, AnySignlessInteger:$rhs);
  let results = (outs AnySignlessInteger:$result);
  let assemblyFormat = "$lhs `,` $rhs attr-dict `:` type($result)";
}

def Gandr_WrappingAddOp : Gandr_WrappingOp<"wrapping_add", "sum">;
def Gandr_WrappingSubOp : Gandr_WrappingOp<"wrapping_sub", "difference">;
def Gandr_WrappingMulOp : Gandr_WrappingOp<"wrapping_mul", "product">;

// A bit operation of a width: two words in, one word out, bit by bit.
class Gandr_BitsOp<string mnemonic, string what>
    : Gandr_Op<mnemonic, [Pure, SameOperandsAndResultType]> {
  let summary = "the " # what # " of two words, bit by bit";
  let arguments = (ins AnySignlessInteger:$lhs, AnySignlessInteger:$rhs);
  let results = (outs AnySignlessInteger:$result);
  let assemblyFormat = "$lhs `,` $rhs attr-dict `:` type($result)";
}

def Gandr_AndOp : Gandr_BitsOp<"and", "conjunction">;
def Gandr_OrOp : Gandr_BitsOp<"or", "disjunction">;
def Gandr_XorOp : Gandr_BitsOp<"xor", "exclusive disjunction">;

def Gandr_NotOp : Gandr_Op<"not", [Pure, SameOperandsAndResultType]> {
  let summary = "the negation of a word, bit by bit";
  let arguments = (ins AnySignlessInteger:$input);
  let results = (outs AnySignlessInteger:$result);
  let assemblyFormat = "$input attr-dict `:` type($result)";
}

def Gandr_ReturnOp
    : Gandr_Op<"return", [Terminator, HasParent<"::mlir::LLVM::LLVMFuncOp">]> {
  let summary = "deliver a value to the return continuation, or no value "
                "from a function of `void`";
  let arguments = (ins Optional<AnyType>:$value);
  let assemblyFormat = "($value^ `:` type($value))? attr-dict";
  let hasVerifier = 1;
}

def Gandr_CallOp
    : Gandr_Op<"call", [DeclareOpInterfaceMethods<SymbolUserOpInterface>]> {
  let summary = "run a definition against a frame whose continuation binds "
                "its result";
  let arguments = (ins FlatSymbolRefAttr:$callee, Variadic<AnyType>:$operands);
  let results = (outs Optional<AnyType>:$result);
  let assemblyFormat =
      "$callee `(` $operands `)` attr-dict `:` functional-type($operands, results)";
}

def Gandr_JumpOp
    : Gandr_Op<"jump", [Terminator, HasParent<"::mlir::LLVM::LLVMFuncOp">,
                        DeclareOpInterfaceMethods<SymbolUserOpInterface>]> {
  let summary = "run a definition against a frame whose continuation is the "
                "return continuation";
  let arguments = (ins FlatSymbolRefAttr:$callee, Variadic<AnyType>:$operands);
  let assemblyFormat =
      "$callee `(` $operands `)` attr-dict (`:` `(` type($operands)^ `)`)?";
}

#endif // GANDR_TD
