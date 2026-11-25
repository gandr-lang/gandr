// A transition calls the next one in tail position under `tailcc`, as the
// stencils of the old tree do. On x86-64 the code generator accepts it.
llvm.func tailcc @next(%state: !llvm.ptr) -> i64

llvm.func tailcc @step(%state: !llvm.ptr) -> i64 {
  %result = llvm.call tailcc musttail @next(%state) : (!llvm.ptr) -> i64
  llvm.return %result : i64
}
