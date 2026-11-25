// The verifiers of the `gandr` dialect and its lowering to the `llvm`
// dialect. Each transition has one lowering here, and no other definition.

#include "dialect.h"

#include "mlir/IR/Builders.h"
#include "mlir/IR/OpImplementation.h"
#include "mlir/IR/PatternMatch.h"
#include "mlir/Transforms/DialectConversion.h"

#include "llvm/ADT/STLExtras.h"

#include "GandrDialect.cpp.inc"

/// Register each operation of the dialect.
///
/// # Specification
/// trivial.
void gandr::GandrDialect::initialize() {
  addOperations<
#define GET_OP_LIST
#include "GandrOps.cpp.inc"
      >();
}

#define GET_OP_CLASSES
#include "GandrOps.cpp.inc"

namespace {

namespace LLVM = mlir::LLVM;

/// Check that `callee` names an `llvm.func` with the convention `tailcc` that
/// takes `operands`, and give it in `found`.
///
/// # Specification
/// - ensures: on success `found` is the function of `callee`, and the type of
///   each operand is the type of its parameter.
/// - fails: a diagnostic at `op` when `callee` names no `llvm.func`, when the
///   function has another convention, or when the count or a type of the
///   operands differs from the parameters.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a call with an operand of the wrong width is refused
///   with the index and the two types.
/// - witness: ctest `dialect-call-wrong-operand`
/// - witness: ctest `dialect-transitions`
mlir::LogicalResult verifyCallee(mlir::Operation *op,
                                 mlir::FlatSymbolRefAttr callee,
                                 mlir::ValueRange operands,
                                 mlir::SymbolTableCollection &symbols,
                                 LLVM::LLVMFuncOp &found) {
  auto function = symbols.lookupNearestSymbolFrom<LLVM::LLVMFuncOp>(op, callee);
  if (!function)
    return op->emitOpError() << "names " << callee
                             << ", which is not an llvm.func";
  if (function.getCConv() != LLVM::cconv::CConv::Tail)
    return op->emitOpError() << "needs the convention tailcc of " << callee;
  LLVM::LLVMFunctionType type = function.getFunctionType();
  if (type.isVarArg() || type.getNumParams() != operands.size())
    return op->emitOpError() << "gives " << operands.size()
                             << " operands to " << callee << ", which takes "
                             << type.getNumParams();
  for (auto [index, parameter, operand] :
       llvm::enumerate(type.getParams(), operands.getTypes()))
    if (parameter != operand)
      return op->emitOpError() << "gives operand " << index << " of type "
                               << operand << " to " << callee
                               << ", which takes " << parameter;
  found = function;
  return mlir::success();
}

/// The result type of the function around `op`.
///
/// # Specification
/// trivial.
mlir::Type resultOfParent(mlir::Operation *op) {
  return op->getParentOfType<LLVM::LLVMFuncOp>()
      .getFunctionType()
      .getReturnType();
}

/// The type that `values` deliver: the type of the one value, or `void` for
/// none.
///
/// # Specification
/// trivial.
mlir::Type delivered(mlir::MLIRContext *context, mlir::TypeRange values) {
  if (values.empty())
    return LLVM::LLVMVoidType::get(context);
  return values.front();
}

} // namespace

/// Check that the value has the result type of the function, or that a
/// return with no value is in a function of `void`.
///
/// # Specification
/// - ensures: on success the type of the value, or `void` for no value, is
///   the result type of the function around the operation.
/// - fails: a diagnostic with the two types.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a return of an `i16` from a function of `i8` is
///   refused with the two types, and so is a return with no value from a
///   function of `i8`.
/// - witness: ctest `dialect-return-wrong-type`
/// - witness: ctest `dialect-return-no-value`
/// - witness: ctest `dialect-transitions`
mlir::LogicalResult gandr::ReturnOp::verify() {
  mlir::Type expected = resultOfParent(*this);
  mlir::Type found = delivered(getContext(), getOperation()->getOperandTypes());
  if (found != expected)
    return emitOpError() << "returns " << found << " from a function of "
                         << expected;
  return mlir::success();
}

/// Check the callee of a call, and that the result has its result type.
///
/// # Specification
/// - ensures: on success the callee is an `llvm.func` with `tailcc` that
///   takes the operands, and the result has its result type.
/// - fails: as `verifyCallee`, or a diagnostic with the two result types.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a call with an operand of the wrong width is refused,
///   and the call of `twice` is accepted.
/// - witness: ctest `dialect-call-wrong-operand`
/// - witness: ctest `dialect-transitions`
mlir::LogicalResult
gandr::CallOp::verifySymbolUses(mlir::SymbolTableCollection &symbols) {
  LLVM::LLVMFuncOp function;
  if (mlir::failed(verifyCallee(*this, getCalleeAttr(), getOperands(), symbols,
                                function)))
    return mlir::failure();
  mlir::Type result = function.getFunctionType().getReturnType();
  mlir::Type bound = delivered(getContext(), getOperation()->getResultTypes());
  if (bound != result)
    return emitOpError() << "binds " << bound << ", and " << getCalleeAttr()
                         << " gives " << result;
  return mlir::success();
}

/// Check the callee of a jump: it gives the result type of the function
/// around the jump, and both have the convention `tailcc`.
///
/// # Specification
/// - ensures: on success the callee is an `llvm.func` with `tailcc` that
///   takes the operands and gives the result type of the function around the
///   jump, which also has `tailcc`. So the lowering can be a `musttail` call.
/// - fails: as `verifyCallee`, or a diagnostic for another convention of the
///   function around the jump, or for another result type.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a jump to a function of another result type is refused
///   with the two types, and the jump of `inc` is accepted.
/// - witness: ctest `dialect-jump-wrong-result`
/// - witness: ctest `dialect-transitions`
mlir::LogicalResult
gandr::JumpOp::verifySymbolUses(mlir::SymbolTableCollection &symbols) {
  LLVM::LLVMFuncOp function;
  if (mlir::failed(verifyCallee(*this, getCalleeAttr(), getOperands(), symbols,
                                function)))
    return mlir::failure();
  auto parent = (*this)->getParentOfType<LLVM::LLVMFuncOp>();
  if (parent.getCConv() != LLVM::cconv::CConv::Tail)
    return emitOpError() << "needs the convention tailcc of the function "
                            "around it";
  mlir::Type result = function.getFunctionType().getReturnType();
  mlir::Type expected = parent.getFunctionType().getReturnType();
  if (result != expected)
    return emitOpError() << "jumps to " << getCalleeAttr() << " of " << result
                         << " from a function of " << expected;
  return mlir::success();
}

namespace {

/// The lowering of a native operation of a width over two words: the integer
/// operation of the `llvm` dialect, which wraps or works bit by bit.
///
/// # Specification
/// - ensures: the operation is replaced by `To` over the same operands.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the fixture of the transitions uses each operation, and
///   the translation refuses a module where one is left.
/// - witness: ctest `dialect-transitions`
template <typename From, typename To>
struct Binary : mlir::OpRewritePattern<From> {
  using mlir::OpRewritePattern<From>::OpRewritePattern;

  /// # Specification
  /// trivial.
  mlir::LogicalResult
  matchAndRewrite(From op, mlir::PatternRewriter &rewriter) const override {
    rewriter.replaceOpWithNewOp<To>(op, op.getType(), op.getLhs(),
                                    op.getRhs());
    return mlir::success();
  }
};

/// The lowering of `gandr.not`: `llvm.xor` of the word with the word of all
/// ones.
///
/// # Specification
/// - ensures: the operation is replaced by an exclusive disjunction with the
///   constant whose bits are all one, at the width of the word.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the fixture of the transitions negates a word, and the
///   translation refuses a module where the operation is left.
/// - witness: ctest `dialect-transitions`
struct Not : mlir::OpRewritePattern<gandr::NotOp> {
  using OpRewritePattern::OpRewritePattern;

  /// # Specification
  /// trivial.
  mlir::LogicalResult
  matchAndRewrite(gandr::NotOp op,
                  mlir::PatternRewriter &rewriter) const override {
    mlir::Type type = op.getType();
    auto ones = LLVM::ConstantOp::create(
        rewriter, op.getLoc(), type,
        rewriter.getIntegerAttr(
            type, llvm::APInt::getAllOnes(type.getIntOrFloatBitWidth())));
    rewriter.replaceOpWithNewOp<LLVM::XOrOp>(op, type, op.getInput(), ones);
    return mlir::success();
  }
};

/// The lowering of `gandr.return`: `llvm.return` of the value, or of no value.
///
/// # Specification
/// trivial.
struct Return : mlir::OpRewritePattern<gandr::ReturnOp> {
  using OpRewritePattern::OpRewritePattern;

  /// # Specification
  /// trivial.
  mlir::LogicalResult
  matchAndRewrite(gandr::ReturnOp op,
                  mlir::PatternRewriter &rewriter) const override {
    rewriter.replaceOpWithNewOp<LLVM::ReturnOp>(op, op->getOperands());
    return mlir::success();
  }
};

/// The `llvm.call` with `tailcc` of the callee of `op`, before `op`.
///
/// # Specification
/// trivial.
template <typename Op>
LLVM::CallOp callOf(Op op, mlir::PatternRewriter &rewriter) {
  auto function = mlir::SymbolTable::lookupNearestSymbolFrom<LLVM::LLVMFuncOp>(
      op, op.getCalleeAttr());
  auto call =
      LLVM::CallOp::create(rewriter, op.getLoc(), function, op.getOperands());
  call.setCConv(LLVM::cconv::CConv::Tail);
  return call;
}

/// The lowering of `gandr.call`: an `llvm.call` with `tailcc`, whose result
/// replaces the result of the operation.
///
/// # Specification
/// trivial.
struct Call : mlir::OpRewritePattern<gandr::CallOp> {
  using OpRewritePattern::OpRewritePattern;

  /// # Specification
  /// trivial.
  mlir::LogicalResult
  matchAndRewrite(gandr::CallOp op,
                  mlir::PatternRewriter &rewriter) const override {
    LLVM::CallOp call = callOf(op, rewriter);
    rewriter.replaceOp(op, call.getResults());
    return mlir::success();
  }
};

/// The lowering of `gandr.jump`: an `llvm.call` with `tailcc` and `musttail`,
/// then `llvm.return` of its result.
///
/// # Specification
/// trivial.
struct Jump : mlir::OpRewritePattern<gandr::JumpOp> {
  using OpRewritePattern::OpRewritePattern;

  /// # Specification
  /// trivial.
  mlir::LogicalResult
  matchAndRewrite(gandr::JumpOp op,
                  mlir::PatternRewriter &rewriter) const override {
    LLVM::CallOp call = callOf(op, rewriter);
    call.setTailCallKind(LLVM::tailcallkind::TailCallKind::MustTail);
    rewriter.replaceOpWithNewOp<LLVM::ReturnOp>(op, call.getResults());
    return mlir::success();
  }
};

} // namespace

mlir::LogicalResult gandr::lower(mlir::ModuleOp module) {
  mlir::MLIRContext *context = module.getContext();
  mlir::ConversionTarget target(*context);
  target.addLegalOp<mlir::ModuleOp>();
  target.addLegalDialect<LLVM::LLVMDialect>();
  target.addIllegalDialect<GandrDialect>();
  mlir::RewritePatternSet patterns(context);
  patterns.add<Binary<WrappingAddOp, LLVM::AddOp>,
               Binary<WrappingSubOp, LLVM::SubOp>,
               Binary<WrappingMulOp, LLVM::MulOp>, Binary<AndOp, LLVM::AndOp>,
               Binary<OrOp, LLVM::OrOp>, Binary<XorOp, LLVM::XOrOp>, Not, Return,
               Call, Jump>(context);
  return mlir::applyFullConversion(module, target, std::move(patterns));
}
