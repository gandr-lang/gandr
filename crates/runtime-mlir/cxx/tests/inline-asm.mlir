// Inline assembly: the exit system call of Linux x86-64, as the machine block
// of the slice needs. The block does not return.
llvm.func @exit(%code: i64) {
  %number = llvm.mlir.constant(60 : i64) : i64
  %unused = llvm.inline_asm has_side_effects "syscall", "={rax},{rax},{rdi},~{rcx},~{r11},~{memory}" %number, %code : (i64, i64) -> i64
  llvm.unreachable
}
