// A load and a store of a word at an address and an offset in bytes, as a
// ring entry needs.
llvm.func @copy_word(%base: !llvm.ptr, %offset: i64, %value: i32) -> i32 {
  %at = llvm.getelementptr %base[%offset] : (!llvm.ptr, i64) -> !llvm.ptr, i8
  llvm.store %value, %at {alignment = 4 : i64} : i32, !llvm.ptr
  %read = llvm.load %at {alignment = 4 : i64} : !llvm.ptr -> i32
  llvm.return %read : i32
}
