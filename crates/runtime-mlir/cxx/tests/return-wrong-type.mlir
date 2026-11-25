// A return of a value whose type is not the result type of the function.
llvm.func tailcc @narrow(%x: i16) -> i8 {
  gandr.return %x : i16
}
