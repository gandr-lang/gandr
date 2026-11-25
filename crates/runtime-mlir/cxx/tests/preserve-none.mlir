// The `llvm` dialect of the pin has no `preserve_nonecc`. The stencils of the
// old tree used `preserve_none`, so the parser refuses this text.
llvm.func preserve_nonecc @step(%state: !llvm.ptr) -> i64 {
  %zero = llvm.mlir.constant(0 : i64) : i64
  llvm.return %zero : i64
}
