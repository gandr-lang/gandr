// The definitions of `exit-code.gandr`, focused, as transitions of the
// `gandr` dialect, the other native operations of a width, and definitions
// with the result `Unit`, which have no word.
llvm.func tailcc @inc(%x: i8) -> i8 {
  %one = llvm.mlir.constant(1 : i8) : i8
  %sum = gandr.wrapping_add %x, %one : i8
  gandr.return %sum : i8
}

llvm.func tailcc @twice(%x: i8) -> i8 {
  %inner = gandr.call @inc(%x) : (i8) -> i8
  gandr.jump @inc(%inner) : (i8)
}

llvm.func tailcc @wrapped() -> i8 {
  %greatest = llvm.mlir.constant(-1 : i8) : i8
  %three = llvm.mlir.constant(3 : i8) : i8
  %sum = gandr.wrapping_add %greatest, %three : i8
  gandr.return %sum : i8
}

llvm.func tailcc @answer() -> i8 {
  %sum = gandr.call @wrapped() : () -> i8
  gandr.jump @twice(%sum) : (i8)
}

llvm.func tailcc @main() -> i8 {
  %code = gandr.call @answer() : () -> i8
  gandr.return %code : i8
}

llvm.func tailcc @widths(%a: i64, %b: i64) -> i64 {
  %difference = gandr.wrapping_sub %a, %b : i64
  %product = gandr.wrapping_mul %difference, %b : i64
  gandr.return %product : i64
}

llvm.func tailcc @bits(%a: i64, %b: i64) -> i64 {
  %both = gandr.and %a, %b : i64
  %either = gandr.or %both, %b : i64
  %one = gandr.xor %either, %a : i64
  %negated = gandr.not %one : i64
  gandr.return %negated : i64
}

llvm.func tailcc @plain() {
  gandr.return
}

llvm.func tailcc @kept() -> i8 {
  gandr.call @plain() : () -> ()
  %one = llvm.mlir.constant(1 : i8) : i8
  gandr.return %one : i8
}

llvm.func tailcc @again() {
  gandr.jump @plain()
}
