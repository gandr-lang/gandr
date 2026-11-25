// A call that gives an operand of the wrong width.
llvm.func tailcc @inc(%x: i8) -> i8 {
  gandr.return %x : i8
}

llvm.func tailcc @caller(%x: i16) -> i8 {
  %result = gandr.call @inc(%x) : (i16) -> i8
  gandr.return %result : i8
}
