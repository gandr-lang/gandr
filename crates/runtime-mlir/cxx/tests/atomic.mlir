// The atomic access of the head and the tail of a ring: an atomic load and an
// atomic store, each with its ordering as an attribute, and a read-modify-write.
llvm.func @advance(%head: !llvm.ptr, %tail: !llvm.ptr) -> i32 {
  %seen = llvm.load %head atomic acquire {alignment = 4 : i64} : !llvm.ptr -> i32
  %one = llvm.mlir.constant(1 : i32) : i32
  %next = llvm.add %seen, %one : i32
  llvm.store %next, %tail atomic release {alignment = 4 : i64} : i32, !llvm.ptr
  %old = llvm.atomicrmw add %head, %one seq_cst : !llvm.ptr, i32
  llvm.return %old : i32
}
