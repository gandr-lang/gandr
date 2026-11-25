// A jump to a function of another result type.
llvm.func tailcc @wide(%x: i8) -> i16

llvm.func tailcc @caller(%x: i8) -> i8 {
  gandr.jump @wide(%x) : (i8)
}
